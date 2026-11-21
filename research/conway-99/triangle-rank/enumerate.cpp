#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <utility>
using namespace std;
using U = uint64_t;
using Matching = array<int, 12>;
int mod7(int x) {
  x %= 7;
  return x < 0 ? x + 7 : x;
}
int reciprocal(int x) {
  int t[] = {0, 1, 4, 5, 2, 3, 6};
  return t[x];
}
struct PackedRow {
  U a = 0, b = 0;
};
// Sixteen four-bit lanes hold field elements in [0,6]. After a sum, the high
// bit of (sum+1) marks exactly those lanes from which seven must be subtracted.
constexpr U ones = 0x1111111111111111ULL, hi = ones * 8;
U plus7(U a, U b) {
  U t = a + b;
  return t - 7 * (((t + ones) & hi) >> 3);
}
PackedRow add(PackedRow a, PackedRow b) {
  return {plus7(a.a, b.a), plus7(a.b, b.b)};
}
int entry(PackedRow a, int j) {
  return ((j < 16 ? a.a : a.b) >> (4 * (j % 16))) & 15;
}
void set(PackedRow &a, int j, int v) {
  (j < 16 ? a.a : a.b) |= U(v) << (4 * (j % 16));
}
struct ShellSearch {
  int id;
  Matching p, q, r, perm{}, order{};
  int mat[156][156]{}, nullity = 0, rank = 0, maximum_rank = 0, chosen[24]{},
                       depth = 0, used = 0;
  ShellSearch(int ident, Matching x, Matching y, Matching z)
      : id(ident), p(x), q(y), r(z) {
    // Eliminate the middle 12 vertices of the wing Laplacian. Its diagonal
    // block (3I-Q) is invertible. Remaining diagonal blocks have signs removed;
    // the cross block is 3I+Q+permutation.
    int m[12][12]{}, transform[12][12]{}, pivots[12]{}, outside_pivots[12]{};
    for (int i = 0; i < 12; i++)
      for (int j = 0; j < 12; j++) {
        m[i][j] = (p[i] == j) + (q[i] == j);
      }
    for (int j = 0; j < 12; j++) {
      int a = rank;
      while (a < 12 && !m[a][j])
        a++;
      if (a == 12) {
        outside_pivots[nullity++] = j;
        continue;
      }
      swap(m[rank], m[a]);
      int u = reciprocal(m[rank][j]);
      for (int v = 0; v < 12; v++) {
        m[rank][v] = mod7(m[rank][v] * u);
      }
      for (int i = 0; i < 12; i++)
        if (i != rank) {
          int u = m[i][j];
          for (int v = 0; v < 12; v++) {
            m[i][v] = mod7(m[i][v] - u * m[rank][v]);
          }
        }
      pivots[rank++] = j;
    }
    maximum_rank = 30 - 13 - rank;
    // Select the same pivot indices for rows and columns in this symmetric
    // block.
    for (int i = 0; i < rank; i++)
      for (int j = 0; j < rank; j++) {
        m[i][j] = (p[pivots[i]] == pivots[j]) + (q[pivots[i]] == pivots[j]);
        transform[i][j] = i == j;
      }
    for (int t = 0; t < rank; t++) {
      int a = t;
      while (a < rank && !m[a][t])
        a++;
      if (a == rank)
        abort();
      swap(m[a], m[t]);
      swap(transform[a], transform[t]);
      int u = reciprocal(m[t][t]);
      for (int j = 0; j < rank; j++) {
        m[t][j] = mod7(m[t][j] * u);
        transform[t][j] = mod7(transform[t][j] * u);
      }
      for (int i = 0; i < rank; i++)
        if (i != t) {
          u = m[i][t];
          for (int j = 0; j < rank; j++) {
            m[i][j] = mod7(m[i][j] - u * m[t][j]);
            transform[i][j] = mod7(transform[i][j] - u * transform[t][j]);
          }
        }
    }
    int v[144][12]{}, projected[144][12]{};
    for (int c = 0; c < 144; c++) {
      int j = c / 12, a = c % 12;
      for (int i = 0; i < 12; i++)
        v[c][i] = 3 * (i == j) + (q[i] == j) + (i == a);
      for (int i = 0; i < rank; i++)
        for (int k = 0; k < rank; k++)
          projected[c][i] += transform[i][k] * v[c][pivots[k]];
      for (int i = 0; i < nullity; i++) {
        int t = v[c][outside_pivots[i]];
        for (int k = 0; k < rank; k++)
          t -= projected[c][k] * ((p[outside_pivots[i]] == pivots[k]) +
                                  (q[outside_pivots[i]] == pivots[k]));
        mat[i][nullity + c] = mat[nullity + c][i] = mod7(t);
      }
      for (int d = 0; d <= c; d++) {
        int h = d / 12, t = (q[j] == h) + (r[j] == h);
        for (int i = 0; i < rank; i++)
          t -= projected[c][i] * v[d][pivots[i]];
        mat[nullity + c][nullity + d] = mat[nullity + d][nullity + c] = mod7(t);
      }
    }
    for (int i = 0; i < nullity; i++)
      chosen[i] = i;
    // Independent insertion order paired by the third wing's internal matching.
    int b = 0;
    for (int j = 11; j >= 0; j--)
      if (r[j] < j) {
        order[b++] = j;
        order[b++] = r[j];
      }
  }
  int residual_rank() const {
    int n = nullity + depth;
    PackedRow a[24], mult[7];
    int rk = 0;
    for (int i = 0; i < n; i++)
      for (int j = 0; j < n; j++)
        set(a[i], j, mat[chosen[i]][chosen[j]]);
    for (int j = 0; j < n; j++) {
      int i = rk;
      while (i < n && !entry(a[i], j))
        i++;
      if (i == n)
        continue;
      swap(a[i], a[rk]);
      int u = reciprocal(entry(a[rk], j));
      mult[1] = a[rk];
      for (int t = 2; t < 7; t++)
        mult[t] = add(mult[t - 1], a[rk]);
      for (int k = rk + 1; k < n; k++) {
        int t = entry(a[k], j);
        if (t)
          a[k] = add(a[k], mult[7 - (t * u % 7)]);
      }
      if (++rk > maximum_rank)
        return rk;
    }
    return rk;
  }
  // A principal submatrix can only increase in rank when vertices are added.
  void enumerate_permutations() {
    int rk = residual_rank();
    if (rk > maximum_rank)
      return;
    if (depth == 12) {
      cout << id << " " << 13 + rank + rk;
      for (int j : perm)
        cout << " " << j;
      cout << "\n";
      return;
    }
    int j = order[depth];
    for (int a = 0; a < 12; a++)
      if (!(used >> a & 1)) {
        chosen[nullity + depth] = nullity + 12 * j + a;
        perm[j] = a;
        used ^= 1 << a;
        depth++;
        enumerate_permutations();
        depth--;
        used ^= 1 << a;
      }
  }
};
int main() {
  std::ios::sync_with_stdio(false);
  int chart = 0;
  Matching p, q, r;
  while (cin >> p[0]) {
    for (int j = 1; j < 12; j++)
      if (!(cin >> p[j]))
        return 2;
    for (auto *a : {&q, &r})
      for (int &x : *a)
        if (!(cin >> x))
          return 2;
    ShellSearch search(chart++, p, q, r);
    search.enumerate_permutations();
  }
  return cin.eof() ? 0 : 2;
}
