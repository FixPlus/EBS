#include "EBS.h"
#include <algorithm>
#include <iostream>
#include <thread>
#include <vector>
#include <span>

constexpr unsigned colArraySize = 5;
constexpr unsigned threadsCount = 10;
static_assert(threadsCount % 2 == 0, "thread count must be even");

using StackT = ebs::Stack<colArraySize, threadsCount>;

void push(StackT &stack, unsigned tid, int data) { stack.push(tid, data); }

void pop(StackT &stack, unsigned tid, int &data) {
  std::optional<int> popped;
  // Retry till success.
  do {
    popped = stack.pop(tid);
  } while (!popped.has_value());

  data = popped.value();
}

// Result array must contain all odd numbers
// in range from 1 to threadsCount - 1
bool check_results(std::vector<int> res) {
  std::sort(res.begin(), res.end());

  for (auto i = 0; i < res.size(); ++i)
    if (res.at(i) != i + 1) {
      std::cerr << i + 1 << " message missed" << std::endl;
      return false;
    }
  return true;
}

/*
 * Test suit
 *
 * given N (N must be even) workers do:
 *
 * 1. Each odd worker pushes k messages to stack
 *    if i \in 1..k -> msg(i) = (wid - 1) / 2 * k + i
 * 2. Each even worker pops k messages from stack and
 *    stores it to according location in result array.
 * 3. Result array is examined to contain all messages sent
 *    by odd workers and no other messages.
 *
 * 1-2 are done concurrently.
 *
 * Overall N * k / 2 messages is sent. They form a set
 * 1..(N * k / 2).
 *
 * Test checks that each sent message is eventually in
 * result array and no other message is not.
 *
 */

int main(int argc, char** argv) {
  auto opsPerThread = 1u;
  if(argc == 2){
    opsPerThread = std::stoi(argv[1]);
  }

  StackT stack;

  std::vector<std::thread> workers;

  // This vector will hold results of pop operations.
  std::vector<int> results;
  results.resize(threadsCount * opsPerThread / 2);
  for (auto i = 0u; i < threadsCount; ++i) {
    // Each odd workers does opsPerThread pushes, 
    // each even - opsPerThread pops.
    if (i % 2) {
      workers.emplace_back([&stack, opsPerThread](unsigned tid, int startData){
			for(int op = 0; op < opsPerThread; ++op){
			  push(stack, tid, startData + op);
			}
			}, i, (int)((i - 1) / 2 * opsPerThread + 1));
    } else {
      workers.emplace_back(
			[&stack, opsPerThread](unsigned tid, std::span<int> destArray){
			  for(auto& loc: destArray){
			    pop(stack, tid, loc);
			  }
			}, i, std::span<int>{results.data() + (i * opsPerThread / 2), opsPerThread});
    }
  }

  for (auto &w : workers) {
    w.join();
  }

  // Print event log.
  auto log = stack.getLog();
  for(auto& event : log)
    std::cout << event << std::endl;

  if (check_results(results))
    return 0;
  else
    return 1;
}
