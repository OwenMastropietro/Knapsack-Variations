#include <iostream>
#include <fstream>
#include <cassert>
#include <cstring>
#include <cstdlib>
#include <list>
#include <cctype>
#include <string>
#include <vector>
#include <stack>
#include <tuple>
#include <algorithm>

struct ITEM
{
  unsigned int id, wt, val;
  double ratio = (double)val / (double)wt;
};

// Return max of two unsigned ints.
unsigned int max(unsigned int a, unsigned int b) { return (a > b) ? a : b; }
// ----------------------------------------------------
unsigned int getCapacity(const std::string &file)
{
  std::fstream in_file(file);
  assert(in_file.is_open());

  unsigned int capacity;
  in_file >> capacity;
  in_file.close();
  return capacity;
}
// ----------------------------------------------------
std::vector<unsigned int> getWeights(const std::string &file)
{
  std::fstream in_file(file);
  assert(in_file.is_open());

  std::vector<unsigned int> wt;
  unsigned int current_wt;
  while (in_file >> current_wt)
  {
    wt.push_back(current_wt);
  }
  in_file.close();

  return wt;
}
// ----------------------------------------------------
std::vector<unsigned int> getValues(const std::string &file)
{
  std::fstream in_file(file);
  assert(in_file.is_open());

  std::vector<unsigned int> val;
  unsigned int current_val;
  while (in_file >> current_val)
  {
    val.push_back(current_val);
  }
  in_file.close();

  return val;
}
// ----------------------------------------------------
void getRatios(std::vector<ITEM> &items)
{
  // WARNING DANGEROUS MUTATION
  for (auto &&current_item : items)
  {
    current_item.ratio = (double)current_item.val / (double)current_item.wt;
  }
}
// ----------------------------------------------------

///////////////////////////////////////////////////////////
// BEGIN: Traditional Dynamic Programming
std::stack<unsigned int> getOptimalSubset(int n, int W,
                                          const std::vector<unsigned int> &wt,
                                          const std::vector<unsigned int> &val,
                                          const std::vector<std::vector<int>> &F,
                                          unsigned long &basic_ops)
{
  assert(basic_ops == 0);

  int f_val = F.at(n).at(W);
  std::stack<unsigned int> optimal_subset;

  int j = W;
  for (int i = n; i > 0 && f_val > 0; i--)
  {
    basic_ops++;
    if (f_val != F.at(i - 1).at(j))
    {
      optimal_subset.push(i);
      f_val -= val.at(i - 1);
      j -= wt.at(i - 1);
    }
  }
  return optimal_subset;
}
// ----------------------------------------------------
void printOptimalSubset(std::stack<unsigned int> optimal_subset)
{
  while (!optimal_subset.empty())
  {
    std::cout << optimal_subset.top();
    optimal_subset.pop();
    if (!optimal_subset.empty())
    {
      std::cout << ", ";
    }
  }
}
// ----------------------------------------------------
unsigned int TKnapsack(unsigned int n, unsigned int W,
                       const std::vector<unsigned int> &wt,
                       const std::vector<unsigned int> &val,
                       std::vector<std::vector<int>> &F,
                       unsigned long &basic_ops)
{
  assert(basic_ops == 0);
  for (unsigned int i = 1; i <= n; i++)
  {
    for (unsigned int j = 1; j <= W; j++)
    {
      basic_ops++;
      if (wt.at(i - 1) <= j)
      {
        basic_ops++;
        F.at(i).at(j) = max(val.at(i - 1) + F.at(i - 1).at(j - wt.at(i - 1)), F.at(i - 1).at(j));
      }
      else
      {
        F.at(i).at(j) = F.at(i - 1).at(j);
      }
    }
  }

  return F.at(n).at(W);
}
// ----------------------------------------------------
void TKnapsack_problem(unsigned int n, unsigned int W,
                       const std::vector<unsigned int> &wt,
                       const std::vector<unsigned int> &val)
{
  unsigned long solution_ops{0}, subset_ops{0};

  // Initialize Matrix/Table F
  std::vector<std::vector<int>> F(n + 1, std::vector<int>(W + 1, -1));
  for (auto &&col : F.at(0))
  {
    col = 0;
  }
  for (auto &&row : F)
  {
    row.at(0) = 0;
  }

  std::cout << "(1a) Traditional Dynamic Programming Optimal value: "
            << TKnapsack(n, W, wt, val, F, solution_ops) << std::endl;
  std::cout << "(1a) Traditional Dynamic Programming Optimal subset: {";
  printOptimalSubset(getOptimalSubset(n, W, wt, val, F, subset_ops));
  std::cout << "}" << std::endl;
  std::cout << "(1a) Traditional Dynamic Programming Total Basic Ops: " << solution_ops + subset_ops << "\n"
            << std::endl;
}
// ----------------------------------------------------

// END: Traditional Dynamic Programming
///////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////
// BEGIN: Memory-Function Dynamic Programming

int MFKnapsack(unsigned int n, unsigned int W,
               const std::vector<unsigned int> &wt,
               const std::vector<unsigned int> &val,
               std::vector<std::vector<int>> &F,
               unsigned long &basic_ops)
{
  if (n == 0 || W == 0)
  {
    return F.at(n).at(W);
  }

  basic_ops++;
  if (W < wt.at(n - 1))
  {
    F.at(n).at(W) = F.at(n - 1).at(W) == -1 ? MFKnapsack(n - 1, W, wt, val, F, basic_ops) : F.at(n - 1).at(W);
  }
  else
  {
    int above = F.at(n - 1).at(W) == -1 ? MFKnapsack(n - 1, W, wt, val, F, basic_ops) : F.at(n - 1).at(W);
    int before = F.at(n - 1).at(W - wt.at(n - 1)) == -1 ? MFKnapsack(n - 1, W - wt.at(n - 1), wt, val, F, basic_ops) : F.at(n - 1).at(W - wt.at(n - 1));
    basic_ops++;
    F.at(n).at(W) = max(above, val.at(n - 1) + before);
  }

  return F.at(n).at(W);
}
// ----------------------------------------------------
unsigned long MFKnapsack_problem(unsigned int n, unsigned int W,
                                 const std::vector<unsigned int> &wt,
                                 const std::vector<unsigned int> &val)
{
  unsigned long solution_ops{0}, subset_ops{0};

  // Initialize Matrix/Table F
  std::vector<std::vector<int>> F(n + 1, std::vector<int>(W + 1, -1));
  for (auto &&col : F.at(0))
  {
    col = 0;
  }
  for (auto &&row : F)
  {
    row.at(0) = 0;
  }

  std::cout << "(1b) Memory-function Dynamic Programming Optimal value: "
            << MFKnapsack(n, W, wt, val, F, solution_ops) << std::endl;
  std::cout << "(1b) Memory-function Dynamic Programming Optimal subset: {";
  printOptimalSubset(getOptimalSubset(n, W, wt, val, F, subset_ops));
  std::cout << "}" << std::endl;
  std::cout << "(1b) Memory-function Dynamic Programming Total Basic Ops: "
            << solution_ops + subset_ops << std::endl;
  return solution_ops;
}
// ----------------------------------------------------

// END: Memory-Function Dynamic Programming
///////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////
// BEGIN: Space-Efficient Approach using Open Hashing

struct HASH_NODE
{
  int i = -1, j = -1;
  int f_value = -1;
};

class HashTable
{
private:
  // Play with _k?
  size_t _k;
  size_t _size;
  size_t _collision;
  std::vector<std::list<HASH_NODE>> _table;

  size_t _W;

  size_t standard_hash(int i, int j) { return ((i - 1) * _W + j) % _k; }

public:
  HashTable(size_t k, size_t W)
  {
    _k = k;
    _W = W;
    _size = 0;
    _collision = 0;
    _table = std::vector<std::list<HASH_NODE>>(_k);
  }

  bool isEmpty() const { return _size == 0; }

  void insert(int i, int j, int f_val)
  {
    std::list<HASH_NODE> &position = _table.at(standard_hash(i, j));
    if (position.front().f_value == -1)
    {
      // front is empty cell, no collision
      position.front() = {i, j, f_val};
    }
    else
    {
      // collision
      _collision++;
      position.push_front({i, j, f_val});
    }
    _size++;
  }

  void printTable()
  {

    for (size_t i = 0; i < _k; i++)
    {
      for (const auto &node : _table.at(i))
      {
        if (node.f_value != -1)
        {
          std::cout << "i: " << node.i << "\tj: " << node.j << "\tf: " << node.f_value << std::endl;
        }
      }
    }
  }

  std::tuple<int, unsigned long> get_f(int i, int j)
  {
    unsigned long basic_ops{0};
    std::list<HASH_NODE> &position = _table.at(standard_hash(i, j));
    for (const auto &node : position)
    {
      basic_ops++;
      if (node.i == i && node.j == j)
      {
        return std::make_tuple(node.f_value, basic_ops);
      }
    }
    return std::make_tuple(-1, basic_ops);
  }

  size_t space() { return _k + _collision; }
};
// ----------------------------------------------------
std::stack<unsigned int> getOptimalSubset_hash(int n, int W,
                                               const std::vector<unsigned int> &wt,
                                               const std::vector<unsigned int> &val,
                                               HashTable &F,
                                               unsigned long &basic_ops)
{
  assert(basic_ops == 0);

  std::stack<unsigned int> optimal_subset;
  auto [f_val, f_ops] = F.get_f(n, W);
  basic_ops += f_ops;

  int j = W;
  for (int i = n; i > 0 && f_val > 0; i--)
  {
    auto [current_f, current_ops] = F.get_f(i - 1, j);

    basic_ops += current_ops;
    if (f_val != current_f)
    {
      optimal_subset.push(i);
      f_val -= val.at(i - 1);
      j -= wt.at(i - 1);
    }
  }
  return optimal_subset;
}
// --------------------------------------------------
int SEMFKnapsack(unsigned int n, unsigned int W,
                 const std::vector<unsigned int> &wt,
                 const std::vector<unsigned int> &val,
                 HashTable &F,
                 unsigned long &basic_ops)
{
  if (n == 0 || W == 0)
  {
    return 0;
  }

  basic_ops++;
  if (W < wt.at(n - 1))
  {
    auto [above, above_ops] = F.get_f(n - 1, W);
    if (above == -1)
    {
      above_ops = 0;
      above = SEMFKnapsack(n - 1, W, wt, val, F, basic_ops);
    }
    // only increment basic_ops by ops in get_f() if we don't recurse
    basic_ops += above_ops;
    F.insert(n, W, above);
  }
  else
  {
    auto [above, above_ops] = F.get_f(n - 1, W);
    if (above == -1)
    {
      above_ops = 0;
      above = SEMFKnapsack(n - 1, W, wt, val, F, basic_ops);
    }
    // increment if value was acquired from get_f()
    basic_ops += above_ops;

    auto [before, before_ops] = F.get_f(n - 1, W - wt.at(n - 1));
    if (before == -1)
    {
      before_ops = 0;
      before = SEMFKnapsack(n - 1, W - wt.at(n - 1), wt, val, F, basic_ops);
    }
    // increment if value was acquired from get_f()
    basic_ops += before_ops;

    // increment for max
    basic_ops++;
    F.insert(n, W, max(above, val.at(n - 1) + before));
  }
  auto [current_f, trash] = F.get_f(n, W);
  return current_f;
}
// ----------------------------------------------------
void SEMFKnapsack_problem(unsigned int n, unsigned int W,
                          const std::vector<unsigned int> &wt,
                          const std::vector<unsigned int> &val,
                          unsigned long k)
{
  unsigned long solution_ops{0}, subset_ops{0};

  // Initialize Matrix/Table F
  // TODO : Mess with k
  HashTable F(k, W);

  std::cout << "\n(1c) Space-efficient Dynamic Programming Optimal value: "
            << SEMFKnapsack(n, W, wt, val, F, solution_ops) << std::endl;
  std::cout << "(1c) Space-efficient Dynamic Programming Optimal subset: {";
  printOptimalSubset(getOptimalSubset_hash(n, W, wt, val, F, subset_ops));
  std::cout << "}" << std::endl;
  std::cout << "(1c) Space-efficient Dynamic Programming Total Basic Ops: "
            << solution_ops + subset_ops << std::endl;
  std::cout << "(1c) Space-efficient Dynamic Programming Space Taken: "
            << F.space() << std::endl;
}
// ----------------------------------------------------

// END: Space-Efficient Approach using Open Hashing
///////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////
// BEGIN: Greedy Approach using Sorting

// ----------------------------------------------------
void DEBUG_display(const std::vector<ITEM> items)
{
  std::cout << "Items ---- ( Identified by <id, wt, val> )" << std::endl;
  for (size_t i = 0; i < items.size(); i++)
  {
    std::cout << "id  wt  val ratio = "
              << items.at(i).id << " "
              << items.at(i).wt << " "
              << items.at(i).val << " "
              << std::endl;
  }
  std::cout << std::endl;
}
void display(const std::vector<int> &optimal_subset)
{
  for (auto &&item : optimal_subset)
  {
    std::cout << item;
    if (item != optimal_subset.at(optimal_subset.size() - 1))
    {
      std::cout << ", ";
    }
  }
}
// ----------------------------------------------------
void merge_items(std::vector<ITEM> &items, int s, unsigned long middle, int e, unsigned long &basic_ops)
{
  std::vector<ITEM> temp;

  int i = s, j = middle + 1;

  while (i <= middle && j <= e)
  {
    basic_ops++;
    if (items.at(i).ratio > items.at(j).ratio)
    {
      temp.push_back(items.at(i));
      ++i;
    }
    else
    {
      temp.push_back(items.at(j));
      ++j;
    }
  }

  while (i <= middle)
  {
    temp.push_back(items.at(i));
    ++i;
  }

  while (j <= e)
  {
    temp.push_back(items.at(j));
    ++j;
  }

  for (int i = s; i <= e; ++i)
  {
    items.at(i) = temp.at(i - s);
  }
}
void merge_sort_items(std::vector<ITEM> &items, int s, int e, unsigned long &basic_ops)
{
  if (s < e)
  {
    unsigned long middle = (s + e) / 2;
    merge_sort_items(items, s, middle, basic_ops);
    merge_sort_items(items, middle + 1, e, basic_ops);
    merge_items(items, s, middle, e, basic_ops);
  }
}
// ----------------------------------------------------
std::tuple<int, std::vector<int>> GSKnapsack(unsigned int n, unsigned int W,
                                             std::vector<ITEM> &items,
                                             unsigned long &basic_ops)
{
  assert(basic_ops == 0);

  // TODO : FIX MERGE SORT
  // DEBUG_display(items);
  // wanna se me sort some shit?
  merge_sort_items(items, 0, n - 1, basic_ops);
  // wanna see me do it again?
  // DEBUG_display(items);

  int used_capacity = 0;
  int opt_val = 0;           // This Guy Right Here.
  std::vector<int> opt_ss{}; // And This Guy Right Here.

  for (size_t i = 0; i < items.size() && W - used_capacity > items.at(i).wt; i++)
  {
    basic_ops++;
    used_capacity += items.at(i).wt;
    opt_val += items.at(i).val;
    opt_ss.push_back(items.at(i).id);
  }

  // This Is Our Guy.
  return std::make_tuple(opt_val, opt_ss);
}
// ----------------------------------------------------
void GSKnapsack_problem(unsigned int n, unsigned int W,
                        const std::vector<unsigned int> &wt,
                        const std::vector<unsigned int> &val)
{
  unsigned long solution_ops{0};

  // Initialize Items <id, wt, val>... class?
  std::vector<ITEM> items(n);
  for (unsigned int i = 0; i < items.size(); i++)
  {
    items.at(i) = {i + 1, wt.at(i), val.at(i)};
  }
  std::cout << std::endl;
  // DEBUG_display(items);

  // keep it Kooshesh
  auto [optimal_value, optimal_subset] = GSKnapsack(n, W, items, solution_ops);

  // Dr. Gill, this use of std::sort is for output purposes only, it does not
  //    assist in solving the problem.
  std::sort(optimal_subset.begin(), optimal_subset.end());

  std::cout << "(2a) Greedy Approach Optimal value: "
            << optimal_value << std::endl;
  std::cout << "(2a) Greedy Approach Optimal subset: {";
  display(optimal_subset);
  std::cout << "}" << std::endl;
  std::cout << "(2a) Greedy Approach Total Basic Ops: "
            << solution_ops << std::endl;
}
// ----------------------------------------------------

// END: GSKnapsack
///////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////
// BEGIN: Greedy Approach (max-heap)

void sift_down(std::vector<ITEM> &items, size_t heap_size, int i, unsigned long &basic_ops)
{
  // while the item has children...
  while (!(i >= heap_size / 2 && i < heap_size))
  {
    // Set tmp_idx to idx of the better kid (kid with greater value).
    int tmp_idx = 2 * i + 1;

    // if right kid is better than left kid, set idx to right kid.
    if (tmp_idx < heap_size - 1 && items.at(tmp_idx).ratio < items.at(tmp_idx + 1).ratio)
    {
      tmp_idx++;
    }
    // else, don't fuck with tmp_idx
    if (items.at(i).ratio >= items.at(tmp_idx).ratio)
    {
      // fuck openDSA
      return;
    }

    basic_ops++;
    std::swap(items.at(i), items.at(tmp_idx));
    i = tmp_idx; // Move down
  }
}

void max_heapify_by_ratio(std::vector<ITEM> &items, unsigned long &basic_ops)
{
  // Iterate Through pre-heaped list
  for (int i = items.size() / 2 - 1; i >= 0; i--)
  {
    sift_down(items, items.size(), i, basic_ops);
  }

  std::vector<double> test_ratios(items.size());
  for (size_t i = 0; i < items.size(); i++)
  {
    test_ratios.at(i) = items.at(i).ratio;
  }
  assert(std::is_heap(test_ratios.begin(), test_ratios.end()));
}

void delete_heap_max(std::vector<ITEM> &items, size_t &heap_size, unsigned long &basic_ops)
{
  std::swap(items.at(0), items.at(heap_size - 1));
  basic_ops++;

  // decrement heap size
  heap_size--;

  // sift new element to re-max-heapify
  sift_down(items, heap_size, 0, basic_ops);

  std::vector<double> test_ratios(heap_size);
  for (size_t i = 0; i < heap_size; i++)
  {
    test_ratios.at(i) = items.at(i).ratio;
  }
  assert(std::is_heap(test_ratios.begin(), test_ratios.end()));
}

// ----------------------------------------------------
std::tuple<int, std::vector<int>> HGSKnapsack(unsigned int n, unsigned int W,
                                              std::vector<ITEM> &items,
                                              unsigned long &basic_ops)
{
  assert(basic_ops == 0);
  // wanna see me heap some shit?
  max_heapify_by_ratio(items, basic_ops);
  unsigned long heap_size = items.size();
  // wanna see me do it again?

  int used_capacity = 0;
  int opt_val = 0;           // This Guy Right Here.
  std::vector<int> opt_ss{}; // And This Guy Right Here.

  while (heap_size && W - used_capacity > items.front().wt)
  {
    basic_ops++;
    used_capacity += items.front().wt;
    opt_val += items.front().val;
    opt_ss.push_back(items.front().id);
    delete_heap_max(items, heap_size, basic_ops);
  }

  // This Is Our Guy.
  return std::make_tuple(opt_val, opt_ss);
}
// ----------------------------------------------------
void HGSKnapsack_problem(unsigned int n, unsigned int W,
                         const std::vector<unsigned int> &wt,
                         const std::vector<unsigned int> &val)
{
  unsigned long solution_ops{0};

  // Initialize Items <id, wt, val>... class?
  std::vector<ITEM> items(n);
  for (unsigned int i = 0; i < items.size(); i++)
  {
    items.at(i) = {i + 1, wt.at(i), val.at(i)};
  }
  std::cout << std::endl;
  // DEBUG_display(items);

  // keep it Kooshesh
  auto [optimal_value, optimal_subset] = HGSKnapsack(n, W, items, solution_ops);

  // Dr. Gill, this use of std::sort is for output purposes only, it does not
  //    assist in solving the problem.
  std::sort(optimal_subset.begin(), optimal_subset.end());

  std::cout << "(2b) Heap-based Greedy Approach Optimal value: "
            << optimal_value << std::endl;
  std::cout << "(2b) Heap-based Greedy Approach Optimal subset: {";
  display(optimal_subset);
  std::cout << "}" << std::endl;
  std::cout << "(2b) Heap-based Greedy Approach Total Basic Ops: "
            << solution_ops << std::endl;
}
// ----------------------------------------------------

// END: Greedy Approach (max-heap)
///////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////
// Lemme Drive Da Bus
int main(int argc, char *argv[])
{
  assert(argc == 2);

  int case_id = atoi(argv[1]);
  std::string why_dude = case_id > 9 ? argv[1] : std::string("0") + argv[1];

  std::cout <<  why_dude <<  std::endl;
  std::string in_file_prefix("KnapsackTestData/p");
  std::string in_file_capacity(why_dude + std::string("_c.txt"));
  std::string in_file_values(why_dude + std::string("_v.txt"));
  std::string in_file_weights(why_dude + std::string("_w.txt"));

  // ----------------------------------------------------
  // Set Significant Variables for the Knapsack Problem.
  std::vector<unsigned int> wt = getWeights(in_file_prefix + in_file_weights);
  std::vector<unsigned int> val = getValues(in_file_prefix + in_file_values);
  unsigned int n = val.size();
  unsigned int W = getCapacity(in_file_prefix + in_file_capacity);
  // ----------------------------------------------------

  // ----------------------------------------------------
  // General Formatting
  std::cout << "File containing the capacity, weights, and values are: "
            << in_file_capacity << ", "
            << in_file_weights << ", and "
            << in_file_values << std::endl;
  std::cout << "\nKnapsack capacity = " << W
            << ". Total number of items = " << n << "\n"
            << std::endl;
  ;
  // ----------------------------------------------------

  // ----------------------------------------------------
  // Traditional Dynamic Programming Approach
  TKnapsack_problem(n, W, wt, val);
  // ----------------------------------------------------

  // ----------------------------------------------------
  // Memory-Function Dynamic Programming Approach
  unsigned long mf_ops = MFKnapsack_problem(n, W, wt, val);
  // ----------------------------------------------------

  // ----------------------------------------------------
  // Space-Efficient Approach using Hash Tables
  SEMFKnapsack_problem(n, W, wt, val, mf_ops / 2);
  // ----------------------------------------------------

  // ----------------------------------------------------
  // Greedy Approach using Sorting
  GSKnapsack_problem(n, W, wt, val);
  // ----------------------------------------------------

  // ----------------------------------------------------
  // Greedy Approach using Heapificationals
  HGSKnapsack_problem(n, W, wt, val);
  // ----------------------------------------------------

  return 0;
}
///////////////////////////////////////////////////////////