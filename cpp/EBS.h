#include <array>
#include <atomic>
#include <cstdlib>
#include <optional>
#include <ostream>
#include <vector>
#include <cassert>
#include <chrono>
/*
 *
 * Realization of Elimination backoff stack algorithm.
 *
 * Described here -
 *
 * https://people.csail.mit.edu/shanir/publications/Lock_Free.pdf
 *
 */
namespace ebs {

/*
 *
 * All atomic objects are tagged
 * to resolve ABA problem in CAS.
 *
 */
template <typename T> struct TaggedStruct {
  T val;
  unsigned tag;
};

template <typename T> using TaggedAtomic = std::atomic<TaggedStruct<T>>;

struct Cell {
  TaggedAtomic<Cell *> next;
  int data;
};

struct DebugEvent{
  unsigned tid;
  enum class Type{
    PUSH,
    POP
  } type;
  int data;
};

// ColArSize - size of collision array.
// MaxThreads - upper bound for expected tid to come.
// operations throw exception if bound is violated.
template <unsigned ColArSize, unsigned MaxThreads> class Stack {
private:
  struct TData {
    unsigned tid;
    enum Op { POP, PUSH } op;
    Cell *cell;
  };

  using clock = std::chrono::high_resolution_clock;
  using time_point = std::chrono::time_point<clock>;
public:

  
  // Returns event log.
  // It is sorted chronologically.
  // Call it only no push/pop operations are in progress,
  // access to per-thread event logs are not synchronized.
  auto getLog() const{
    // Merge logs from all threads.
    std::vector<std::pair<DebugEvent, time_point>> merged;
    for(auto& threadLog: m_events)
      std::transform(threadLog.begin(), threadLog.end(), std::back_inserter(merged), [](auto& event){ return event; });

    // sort merged log chronologically.
    std::sort(merged.begin(), merged.end(), [](auto& event1, auto& event2){ return event1.second < event2.second;});

    // strip time point information.
    std::vector<DebugEvent> events;

    std::transform(merged.begin(), merged.end(), std::back_inserter(events), [](auto& event){ return event.first; });

    return events;
  }

  Stack() {
    for (auto &loc : location)
      loc.store(TaggedStruct<TData *>(nullptr, 0u));
    for (auto &col : collision)
      col.store(TaggedStruct<int>(-1, 0u));

    m_Head.store(TaggedStruct<Cell *>(nullptr, 0u));

    // pre-allocate per-thread event storage space.
    for(auto& threadLog: m_events)
       threadLog.reserve(10);
  }

  Stack(Stack const &another) = delete;
  Stack(Stack &&another) = default;
  Stack &operator=(Stack const &another) = delete;
  Stack &operator=(Stack &&another) = default;

  ~Stack() {
    auto temp = m_Head.load().val;
    while (temp) {
      auto next = temp->next.load().val;
      delete temp;
      temp = next;
    }
  }

  void push(unsigned tid, int data) {
    if (tid >= location.size())
      throw std::out_of_range("Unexpected TID");
    // TODO: for now it causes memory leak
    auto *p = new TData;
    p->tid = tid;
    p->op = TData::PUSH;
    p->cell = new Cell{};
    p->cell->data = data;
    // log 'push' before taking action to garantuee it will shows earlier
    // in event log than corresponding 'pop' event.
    m_events.at(tid).emplace_back(std::make_pair(DebugEvent{tid, DebugEvent::Type::PUSH, data}, clock::now()));
    StackOp(p);
  }

  // Pop operation can fail if stack is empty.
  std::optional<int> pop(unsigned tid) {
    if (tid >= location.size())
      throw std::out_of_range("Unexpected TID");
    // TODO: for now it causes memory leak
    auto *p = new TData;
    p->tid = tid;
    p->op = TData::POP;

    StackOp(p);

    if (!p->cell)
      return {};
    auto data = p->cell->data;
    // log 'pop' after taking succsessful action.
    m_events.at(tid).emplace_back(std::make_pair(DebugEvent{tid, DebugEvent::Type::POP, data}, clock::now()));
    delete p->cell;
    return data;
  }

private:
  void StackOp(TData *p) {
    if (!TryPerformStackOp(p))
      LesOp(p);
    return;
  }

  auto GetPosition() { return rand() % collision.size(); }
  void LesOp(TData *p) {
    while (true) {
      auto ptagged =
          TaggedStruct<decltype(p)>(p, location.at(p->tid).load().tag + 10);
      location.at(p->tid).store(ptagged);
      auto pos = GetPosition();
      auto him = collision.at(pos).load();
      while (!collision.at(pos).compare_exchange_strong(
          him, TaggedStruct<int>(p->tid, him.tag + 1)))
        ;
      if (him.val != -1) {
        auto q = location.at(him.val).load();
        if (q.val != nullptr && q.val->tid == him.val && q.val->op != p->op) {
	  auto ptagcopy = ptagged;
          if (location.at(p->tid).compare_exchange_strong(
                  ptagcopy, TaggedStruct<TData *>(nullptr, ptagged.tag + 1))) {
            if (TryCollision(p, q, him.val)) {
              return;
            } else {
              goto stack;
            }
          } else {
            FinishCollision(p);
            return;
          }
        }
      }
      /* delay */
      if (!location.at(p->tid).compare_exchange_strong(
              ptagged, TaggedStruct<TData *>(nullptr, ptagged.tag + 1))) {
        FinishCollision(p);
        return;
      }
    stack:
      if (TryPerformStackOp(p))
        return;
    }
  }

  bool TryPerformStackOp(TData *p) {
    TaggedStruct<Cell *> phead, pnext;

    if (p->op == TData::PUSH) {
      phead = m_Head.load();
      p->cell->next.store(phead);
      return m_Head.compare_exchange_strong(
          phead, TaggedStruct<decltype(p->cell)>(p->cell, phead.tag + 1));
    } else if (p->op == TData::POP) {
      phead = m_Head.load();
      if (phead.val == nullptr) {
        p->cell = nullptr;
        return true;
      }

      pnext = TaggedStruct<Cell *>(phead.val->next.load().val, phead.tag + 1);
      if (m_Head.compare_exchange_strong(phead, pnext)) {
        p->cell = phead.val;
        return true;
      } else {
        p->cell = nullptr;
        return false;
      }
    }
  }

  void FinishCollision(TData *p) {
    if (p->op == TData::POP) {
      p->cell = location.at(p->tid).load().val->cell;
      location.at(p->tid).store(
          TaggedStruct<TData *>(nullptr, location.at(p->tid).load().tag + 10));
    }
  }

  bool TryCollision(TData *p, TaggedStruct<TData *> q, unsigned him) {
    if (p->op == TData::PUSH) {
      return location.at(him).compare_exchange_strong(
          q, TaggedStruct<decltype(p)>(p, q.tag + 1));
    } else if (p->op == TData::POP) {
      if (location.at(him).compare_exchange_strong(
              q, TaggedStruct<decltype(p)>(nullptr, q.tag + 1))) {
        p->cell = q.val->cell;
        return true;
      } else {
        return false;
      }
    }
  }

  TaggedAtomic<Cell *> m_Head;
  std::array<TaggedAtomic<int>, ColArSize> collision;
  std::array<TaggedAtomic<TData *>, MaxThreads> location;

  // per-thread event log storage.
  std::array<std::vector<std::pair<DebugEvent, time_point>>, MaxThreads> m_events;
};

// prints DebugEvent:
// [<tid:unsigned>] - <type:PUSH|POP>(<data:int>)
std::ostream& operator<<(std::ostream& stream, DebugEvent const&event) {
  stream << "[" << event.tid << "] - ";
  std::string typeStr;
  switch(event.type){
    case DebugEvent::Type::PUSH: typeStr = "PUSH"; break;
    case DebugEvent::Type::POP: typeStr = "POP"; break;
    default:
      assert(0 && "Unreachable");
  }
  stream << typeStr << "(" << event.data << ")";
  return stream;
}

} // namespace ebs
