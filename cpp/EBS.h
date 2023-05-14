#include <array>
#include <atomic>
#include <cstdlib>
#include <optional>

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

template <unsigned ColArSize, unsigned MaxThreads> class Stack {
private:
  struct TData {
    unsigned tid;
    enum Op { POP, PUSH } op;
    Cell *cell;
  };

public:
  Stack() {
    for (auto &loc : location)
      loc.store(TaggedStruct<TData *>(nullptr, 0u));
    for (auto &col : collision)
      col.store(TaggedStruct<int>(-1, 0u));

    m_Head.store(TaggedStruct<Cell *>(nullptr, 0u));
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
    TData p;
    p.tid = tid;
    p.op = TData::PUSH;
    p.cell = new Cell{};
    p.cell->data = data;
    StackOp(&p);
  }
  std::optional<int> pop(unsigned tid) {
    if (tid >= location.size())
      throw std::out_of_range("Unexpected TID");
    TData p;
    p.tid = tid;
    p.op = TData::POP;

    StackOp(&p);

    if (!p.cell)
      return {};
    int ret = p.cell->data;
    delete p.cell;
    return ret;
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
          if (location.at(p->tid).compare_exchange_strong(
                  ptagged, TaggedStruct<TData *>(nullptr, ptagged.tag + 1))) {
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
        location.at(p->tid).store(TaggedStruct<TData *>(
            nullptr, location.at(p->tid).load().tag + 10));
        return true;
      } else {
        return false;
      }
    }
  }

  TaggedAtomic<Cell *> m_Head;
  std::array<TaggedAtomic<int>, ColArSize> collision;
  std::array<TaggedAtomic<TData *>, MaxThreads> location;
};

} // namespace ebs
