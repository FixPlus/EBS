#include "EBS.h"
#include <algorithm>
#include <iostream>
#include <thread>
#include <vector>
constexpr unsigned colArraySize = 5;
constexpr unsigned threadsCount = 10;
using StackT = ebs::Stack<colArraySize, threadsCount>;

void push(StackT &stack, unsigned tid, int data) { stack.push(tid, data); }

void pop(StackT &stack, unsigned tid, int *data) {
  std::optional<int> popped;
  // Retry till success.
  do {
    popped = stack.pop(tid);
  } while (!popped.has_value());

  *data = popped.value();
}

// Result array must contain all odd numbers
// in range from 1 to threadsCount - 1
bool check_results(std::vector<int> res) {
  std::sort(res.begin(), res.end());

  for (auto i = 0; i < res.size(); ++i)
    if (res.at(i) != i * 2 + 1) {
      std::cerr << i * 2 + 1 << " message missed" << std::endl;
      return false;
    }
  return true;
}

/*
 * Test suit
 *
 * given N (N must be even) workers do:
 *
 * 1. Each odd worker pushes message(its id) to stack
 * 2. Each even worken pops one message from stack and
 *    stores it to according location in result array.
 * 3. Result array is examined to contain all messages sent
 *    by odd workers and no other messages.
 *
 */

int main() {
  StackT stack;

  std::vector<std::thread> workers;

  // This vector will hold results of pop operations.
  std::vector<int> results;
  results.resize(threadsCount / 2);
  for (auto i = 0u; i < threadsCount; ++i) {
    // Each odd workers does one push, each even - one pop.
    if (i % 2) {
      workers.emplace_back(push, std::ref(stack), i, (int)i);
    } else {
      workers.emplace_back(pop, std::ref(stack), i, results.data() + (i / 2));
    }
  }

  for (auto &w : workers) {
    w.join();
  }

  for (auto &r : results)
    std::cout << r << std::endl;

  if (check_results(results))
    return 0;
  else
    return 1;
}
