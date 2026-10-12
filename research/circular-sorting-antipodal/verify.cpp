// Exact regression checks for the antipodal-centralizer circular-sorting theorem.
// Copyright (c) 2026 Yongxian Zhang. All rights reserved.
// These finite checks do not substitute for the universal written proof.
#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>

using std::vector;

static int cycle_count_shift(const vector<int>& p, int j) {
  const int n = static_cast<int>(p.size());
  vector<unsigned char> used(n, 0);
  int cycles = 0;
  for (int i = 0; i < n; ++i) {
    if (used[i]) continue;
    ++cycles;
    int x = i;
    while (!used[x]) {
      used[x] = 1;
      x = p[(x + j) % n];
    }
  }
  return cycles;
}

static void fail(const char* message) {
  std::cerr << "FAIL: " << message << '\n';
  std::exit(1);
}

static void exhaustive(int m) {
  vector<int> f(m);
  std::iota(f.begin(), f.end(), 0);
  const int n = 2 * m;
  int min_max_cycles = n;
  long long checked = 0, attaining = 0;
  do {
    for (int mask = 0; mask < (1 << m); ++mask) {
      vector<int> p(n);
      for (int i = 0; i < m; ++i) {
        const int bit = (mask >> i) & 1;
        p[i] = f[i] + m * bit;
        p[i + m] = f[i] + m * (1 - bit);
      }
      int max_cycles = 0;
      for (int j = 0; j < n; ++j)
        max_cycles = std::max(max_cycles, cycle_count_shift(p, j));
      if (max_cycles < 4) fail("counterexample to Theorem 1");
      min_max_cycles = std::min(min_max_cycles, max_cycles);
      if (max_cycles == 4) ++attaining;
      ++checked;
    }
  } while (std::next_permutation(f.begin(), f.end()));
  long long factorial = 1;
  for (int k = 2; k <= m; ++k) factorial *= k;
  if (checked != ((1LL << m) * factorial)) fail("incorrect enumeration cardinality");
  if (min_max_cycles != 4) fail("missing sharp example in this degree");
  std::cout << "m=" << m << ": " << checked << " centralizer permutations; "
            << "min_pi max_j cycles=" << min_max_cycles << "; "
            << "attaining=" << attaining << '\n';
}

static bool is_prime(int p) {
  if (p < 2) return false;
  for (int d = 2; d * d <= p; ++d)
    if (p % d == 0) return false;
  return true;
}

static int odd_primitive_root(int p) {
  for (int a = 2; a < 2 * p; ++a) {
    if ((a % 2) == 0 || a % p == 0) continue;
    int x = 1, period = 0;
    do {
      x = (x * a) % p;
      ++period;
    } while (x != 1 && period <= p);
    if (period == p - 1) return a;
  }
  fail("no odd primitive root found");
  return -1;
}

static void sharp_affine(int p) {
  if (!is_prime(p) || p == 2) fail("sharpness parameter must be odd prime");
  const int n = 2 * p;
  const int a = odd_primitive_root(p);
  vector<int> v(n);
  for (int x = 0; x < n; ++x) v[x] = (a * x) % n;
  for (int j = 0; j < n; ++j) {
    const int expected = (j & 1) ? 3 : 4;
    if (cycle_count_shift(v, j) != expected)
      fail("affine sharpness or shift parity failed");
  }
  std::cout << "p=" << p << ": affine multiplier a=" << a
            << "; cycle counts 4 (even j), 3 (odd j) verified\n";
}

int main() {
  for (int m : {3, 5, 7}) exhaustive(m);
  for (int p : {3, 5, 7, 11, 13, 17, 19, 23, 29, 31}) sharp_affine(p);
  std::cout << "PASS: all independent finite checks succeeded\n";
}
