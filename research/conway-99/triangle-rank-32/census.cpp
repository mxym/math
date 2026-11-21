#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>

#include <cstdlib>

#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using Matching = array<int, 12>;
int mod7(int x) { return (x % 7 + 7) % 7; }
int inverse(int x) {
  int t[] = {0, 1, 4, 5, 2, 3, 6};
  return t[mod7(x)];
}
struct State {
  int r = 0, z = 0;
  int p[22]{}, q[22]{}, B[22][22]{};
}; // inverse on independent principal indices, other indices are redundant
struct Census {
  int id, residual_cap, base_rank, base_nullity;
  static constexpr int goal = 32;
  Matching P, Q, R, perm;
  int table[160][160]{}, G[40][40]{}, border_columns[40][144]{},
      restricted[144][27]{}, projected[144][27]{};
  int lift[160][39]{}, component[12]{}, possible_image[12]{},
      wing_pairs[3][60][2]{};
  int used_sources = 0, used_targets = 0;
  Census(int i, Matching p, Matching q, Matching r) : id(i), P(p), Q(q), R(r) {
    perm.fill(-1);
  }
  // Eliminate a nonsingular principal block on the parents and first two wings.
  // Construct the 144 possible third-wing columns once for this chart.
  void prepare() {
    for (int i = 0; i < 27; i++)
      for (int j = 0; j < 27; j++)
        G[i][j] = i == j ? 0 : -1;
    auto edge = [&](int a, int b) { G[a][b] = G[b][a] = 1; };
    edge(0, 1);
    edge(0, 2);
    edge(1, 2);
    for (int i = 0; i < 12; i++) {
      edge(0, 3 + i);
      edge(1, 15 + i);
      edge(3 + i, 3 + P[i]);
      edge(15 + i, 15 + Q[i]);
      edge(3 + i, 15 + i);
    }
    int H[27][27], I[27][27]{};
    for (int i = 0; i < 27; i++)
      for (int j = 0; j < 27; j++)
        H[i][j] = mod7(G[i][j]);
    vector<int> pivots, null_indices;
    for (int j = 0; j < 27; j++) {
      int k = pivots.size(), a = k;
      while (a < 27 && !H[a][j])
        a++;
      if (a == 27) {
        null_indices.push_back(j);
        continue;
      }
      swap(H[a], H[k]);
      int t = inverse(H[k][j]);
      for (int v = j; v < 27; v++)
        H[k][v] = mod7(t * H[k][v]);
      for (int u = k + 1; u < 27; u++) {
        t = H[u][j];
        for (int v = j; v < 27; v++)
          H[u][v] = mod7(H[u][v] - t * H[k][v]);
      }
      pivots.push_back(j);
    }
    base_rank = pivots.size();
    residual_cap = goal - base_rank;
    base_nullity = null_indices.size();
    assert(base_nullity + 12 <= 22);
    for (int i = 0; i < base_rank; i++)
      for (int j = 0; j < base_rank; j++) {
        H[i][j] = mod7(G[pivots[i]][pivots[j]]);
        I[i][j] = i == j;
      }
    for (int j = 0; j < base_rank; j++) {
      int a = j;
      while (!H[a][j])
        a++;
      swap(H[a], H[j]);
      swap(I[a], I[j]);
      int t = inverse(H[j][j]);
      for (int v = 0; v < base_rank; v++) {
        I[j][v] = mod7(I[j][v] * t);
        H[j][v] = mod7(H[j][v] * t);
      }
      for (int u = 0; u < base_rank; u++)
        if (u != j) {
          t = H[u][j];
          for (int v = 0; v < base_rank; v++) {
            I[u][v] = mod7(I[u][v] - t * I[j][v]);
            H[u][v] = mod7(H[u][v] - t * H[j][v]);
          }
        }
    }
    for (int j = 0; j < 12; j++)
      for (int a = 0; a < 12; a++) {
        int c = 12 * j + a;
        for (int u = 0; u < 27; u++)
          border_columns[u][c] = (u == 2 || u == 15 + j || u == 3 + a) ? 1 : -1;
        for (int t = 0; t < base_rank; t++)
          restricted[c][t] = border_columns[pivots[t]][c];
        for (int t = 0; t < base_rank; t++)
          for (int h = 0; h < base_rank; h++)
            projected[c][t] += I[t][h] * restricted[c][h];
        for (int t = 0; t < base_rank; t++)
          projected[c][t] = mod7(projected[c][t]);
        for (int h = 0; h < base_nullity; h++) {
          int z = border_columns[null_indices[h]][c];
          for (int t = 0; t < base_rank; t++)
            z -= G[null_indices[h]][pivots[t]] * projected[c][t];
          table[h][base_nullity + c] = table[base_nullity + c][h] = mod7(z);
        }
      }
    for (int h = 0; h < base_nullity + 144; h++) {
      int target =
          h < base_nullity ? null_indices[h] : 27 + (h - base_nullity) / 12;
      lift[h][target] = 1;
      for (int j = 0; j < base_rank; j++) {
        int a = 0;
        if (h < base_nullity) {
          for (int k = 0; k < base_rank; k++)
            a += I[j][k] * G[pivots[k]][target];
        } else
          a = projected[h - base_nullity][j];
        lift[h][pivots[j]] = mod7(-a);
      }
    }
    // The image of a single vertex determines a color-preserving map of its
    // connected component. Record which roots are related by an isomorphism.
    for (int i = 0; i < 12; i++)
      for (int j = 0; j < 12; j++) {
        int mapping[12];
        fill(mapping, mapping + 12, -1);
        int queue[12]{i}, len = 1;
        mapping[i] = j;
        bool ok = true;
        for (int k = 0; k < len && ok; k++) {
          int a = queue[k], b = mapping[a];
          for (const auto *m : {&P, &Q, &R}) {
            int x = (*m)[a], y = (*m)[b];
            if (mapping[x] == -1) {
              mapping[x] = y;
              queue[len++] = x;
            } else if (mapping[x] != y)
              ok = false;
          }
        }
        if (!ok)
          continue;
        int reach = 0, image = 0;
        for (int k = 0; k < len; k++) {
          reach |= 1 << queue[k];
          image |= 1 << mapping[queue[k]];
        }
        if (__builtin_popcount(image) == len)
          possible_image[i] |= 1 << j;
        if (i == j)
          component[i] = reach;
      }
    for (int t = 0; t < 3; t++) {
      int count = 0;
      auto &m = t == 0 ? P : t == 1 ? Q : R;
      for (int i = 0; i < 12; i++)
        for (int j = 0; j < i; j++)
          if (m[i] != j) {
            wing_pairs[t][count][0] = 3 + 12 * t + i;
            wing_pairs[t][count++][1] = 3 + 12 * t + j;
          }
    }
    for (int c = 0; c < 144; c++)
      for (int d = 0; d <= c; d++) {
        int q = c == d ? 0 : (R[c / 12] == d / 12 ? 1 : -1);
        for (int t = 0; t < base_rank; t++)
          q -= projected[c][t] * restricted[d][t];
        table[base_nullity + c][base_nullity + d] =
            table[base_nullity + d][base_nullity + c] = mod7(q);
      }
  }
  // Bordering a symmetric matrix raises rank by 2 on pairing with its radical,
  // or by 1 for a nonzero norm after orthogonal projection, or by 0.
  struct Border {
    int step = 0, z = -1, norm = 0, b = 0, t[22]{};
  };
  Border test(const State &a, int c) {
    Border e;
    for (int i = 0; i < a.r; i++) {
      int t = 0;
      for (int j = 0; j < a.r; j++)
        t += a.B[i][j] * table[a.p[j]][c];
      e.t[i] = mod7(t);
    }
    int norm = table[c][c];
    for (int i = 0; i < a.r; i++)
      norm -= e.t[i] * table[a.p[i]][c];
    e.norm = mod7(norm);
    for (int k = 0; k < a.z; k++) {
      int h = a.q[k], v = table[h][c];
      for (int i = 0; i < a.r; i++)
        v -= table[h][a.p[i]] * e.t[i];
      if (mod7(v)) {
        e.step = 2;
        e.z = k;
        e.b = mod7(v);
        break;
      }
    }
    if (e.step == 0)
      e.step = e.norm != 0;
    return e;
  }
  // Update the inverse Gram matrix of the principal pivot set by bordering.
  State add(const State &a, int c, Border &e) {
    State b = a;
    int r = a.r;
    if (e.step == 0) {
      b.q[b.z++] = c;
      return b;
    }
    int invs[2][2]{};
    int extra[2];
    int trans[2][22]{};
    if (e.step == 1) {
      extra[0] = c;
      invs[0][0] = inverse(e.norm);
      copy(e.t, e.t + r, trans[0]);
    } else {
      int z = a.q[e.z];
      extra[0] = z;
      extra[1] = c;
      swap(b.q[e.z], b.q[--b.z]);
      int v = inverse(e.b);
      invs[0][0] = mod7(-e.norm * v * v);
      invs[1][0] = invs[0][1] = v;
      for (int i = 0; i < r; i++) {
        int t = 0;
        for (int j = 0; j < r; j++)
          t += a.B[i][j] * table[a.p[j]][z];
        trans[0][i] = mod7(t);
      }
      copy(e.t, e.t + r, trans[1]);
    }
    for (int i = 0; i < e.step; i++) {
      b.p[r + i] = extra[i];
      for (int j = 0; j < e.step; j++)
        b.B[r + i][r + j] = invs[i][j];
      for (int j = 0; j < r; j++) {
        int w = 0;
        for (int k = 0; k < e.step; k++)
          w -= invs[i][k] * trans[k][j];
        b.B[j][r + i] = b.B[r + i][j] = mod7(w);
      }
    }
    for (int i = 0; i < r; i++)
      for (int j = 0; j < r; j++) {
        int w = a.B[i][j];
        for (int k = 0; k < e.step; k++)
          w -= trans[k][i] * b.B[r + k][j];
        b.B[i][j] = mod7(w);
      }
    b.r += e.step;
    return b;
  }
  using U = uint64_t;
  static U plus(U a, U b) {
    constexpr U one = 0x1111111111111111ULL, hi = one * 8;
    U c = a + b;
    return c - 7 * (((c + one) & hi) >> 3);
  }
  // At shell rank 31 or 32 every exterior column pairs trivially with the
  // radical. Test the 60 prescriptions of the first wing before emitting.
  bool admits_columns(const State &a) {
    if (base_rank + a.r < goal - 1)
      return true;
    assert(a.z <= 15);
    U pos[39]{}, minus[39]{}, bias = 0;
    for (int t = 0; t < a.z; t++) {
      int h = a.q[t], mul[22]{}, sum = 0;
      for (int j = 0; j < a.r; j++)
        for (int k = 0; k < a.r; k++)
          mul[j] += a.B[j][k] * table[a.p[k]][h];
      int v[39];
      copy(lift[h], lift[h] + 39, v);
      for (int j = 0; j < a.r; j++) {
        int m = mod7(mul[j]);
        if (m)
          for (int i = 0; i < 39; i++)
            v[i] -= m * lift[a.p[j]][i];
      }
      for (int i = 0; i < 39; i++) {
        int x = mod7(v[i]);
        sum += x;
        pos[i] |= U(mod7(2 * x)) << (4 * t);
        minus[i] |= U(mod7(-2 * x)) << (4 * t);
      }
      bias |= U(mod7(sum)) << (4 * t);
    }
    U pair[3][60];
    for (int j = 0; j < 3; j++)
      for (int i = 0; i < 60; i++) {
        auto &f = wing_pairs[j][i];
        pair[j][i] = j == 2 ? plus(pos[f[0]], pos[f[1]])
                            : plus(minus[f[0]], minus[f[1]]);
      }
    U set[256];
    fill(set, set + 256, ~U(0));
    auto hash = [](U x) { return (x * 11400714819323198485ull) >> 56; };
    for (U x : pair[2]) {
      int j = hash(x);
      while (set[j] != ~U(0) && set[j] != x)
        j = (j + 1) & 255;
      set[j] = x;
    }
    for (U x : pair[0]) {
      bool ok = false;
      x = plus(bias, x);
      for (U y : pair[1]) {
        U need = plus(x, y);
        int j = hash(need);
        while (set[j] != ~U(0) && set[j] != need)
          j = (j + 1) & 255;
        if (set[j] == need) {
          ok = true;
          break;
        }
      }
      if (!ok)
        return false;
    }
    return true;
  }
  void enumerate(const State &a, int depth) {

    if (depth == 12) {
      if (!admits_columns(a))
        return;
      cout << id << " " << base_rank + a.r;
      for (int x : perm)
        cout << " " << x;
      cout << "\n";
      return;
    }
    int site = -1, targets = 0, mincount = 13;
    for (int j = 0; j < 12; j++)
      if (!(used_sources >> j & 1)) {
        int mask = 0;
        for (int v = 0; v < 12; v++)
          if (!(used_targets >> v & 1)) {
            if (test(a, base_nullity + 12 * j + v).step + a.r <= residual_cap)
              mask |= 1 << v;
          }
        int num = __builtin_popcount(mask);
        if (!num)
          return;
        if (num < mincount) {
          mincount = num;
          targets = mask;
          site = j;
        }
        if (residual_cap - a.r >= 2)
          break;
      }
    // Fix every component touched by a source or target, including the new
    // source. Untouched isomorphic components may still be permuted.
    int frozen = 0;
    for (int i = 0; i < 12; i++)
      if (((used_sources | used_targets | (1 << site)) >> i) & 1)
        frozen |= component[i];
    used_sources ^= 1 << site;
    while (targets) {
      int v = __builtin_ctz(targets);
      if (frozen >> v & 1)
        targets &= targets - 1;
      else
        targets &= ~(possible_image[v] & ~frozen);
      int c = base_nullity + 12 * site + v;
      auto e = test(a, c);
      auto b = add(a, c, e);
      used_targets ^= 1 << v;
      perm[site] = v;
      enumerate(b, depth + 1);
      used_targets ^= 1 << v;
    }
    used_sources ^= 1 << site;
  }
  void run() {
    prepare();
    State s;
    s.z = base_nullity;
    iota(s.q, s.q + base_nullity, 0);
    enumerate(s, 0);
  }
};
int main() {
  std::ios::sync_with_stdio(false);
  int id;
  while (cin >> id) {
    Matching p, q, r;
    for (auto *m : {&p, &q, &r}) {
      for (int &x : *m)
        if (!(cin >> x) || x < 0 || x >= 12)
          return 2;
      for (int i = 0; i < 12; i++)
        if ((*m)[i] == i || (*m)[(*m)[i]] != i)
          return 2;
    }
    Census search(id, p, q, r);
    search.run();
  }
  return cin.eof() ? 0 : 2;
}
