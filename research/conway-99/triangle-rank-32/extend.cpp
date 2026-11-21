#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <vector>
using namespace std;
using U = uint64_t;
using Matching = array<int, 12>;
using Coverage = array<U, 3>;
int mod(int x) { return (x % 7 + 7) % 7; }
int inv(int a) {
  int ii[] = {0, 1, 4, 5, 2, 3, 6};
  return ii[mod(a)];
}
constexpr U one = 0x1111111111111111ULL, top = 0x8888888888888888ULL;
U add(U x, U y) {
  U z = x + y;
  U k = ((z + one) & top) >> 3;
  return z - 7 * k;
}
U neg(U x, int k) {
  U a = 0;
  for (int i = 0; i < k; i++)
    a |= U((7 - (int(x >> (4 * i)) & 15)) % 7) << (4 * i);
  return a;
}
U normalize(U x, int n) {
  if (!x)
    return 0;
  int lead = __builtin_ctzll(x) / 4;
  int c = inv(int(x >> (4 * lead)) & 15);
  U v = 0;
  for (int j = 0; j < n; j++)
    v |= U((c * (int(x >> (4 * j)) & 15)) % 7) << (4 * j);
  return v;
}
struct ExtensionTest {
  int A[39][39]{}, H[39][39]{}, G[39][39]{}, T[39][39]{};
  int r = 0, nullity = 0, p[39]{}, s = 0;
  int pairs[3][60][2]{}, w[3][60][39]{}, dual[3][60][39]{},
      linear_norm[3][60]{};
  U pairing[3][60]{}, bias = 0;
  int origin_norm = 0, cross[3][3][60][60]{};
  ExtensionTest(const Matching &P0, const Matching &Q, const Matching &R,
                const Matching &b) {
    auto edge = [&](int i, int j) { A[i][j] = A[j][i] = 1; };
    edge(0, 1);
    edge(0, 2);
    edge(1, 2);
    for (int i = 0; i < 12; i++) {
      edge(0, 3 + i);
      edge(1, 15 + i);
      edge(2, 27 + i);
      edge(3 + i, 3 + P0[i]);
      edge(15 + i, 15 + Q[i]);
      edge(27 + i, 27 + R[i]);
      edge(3 + i, 15 + i);
      edge(15 + i, 27 + i);
      edge(27 + i, 3 + b[i]);
    }
    for (int i = 0; i < 39; i++)
      for (int j = 0; j < 39; j++) {
        H[i][j] = G[i][j] = mod(2 * A[i][j] - 1 + (i == j));
        T[i][j] = (i == j);
      }
    for (int j = 0; j < 39; j++) {
      int k = r;
      while (k < 39 && !H[k][j])
        k++;
      if (k == 39)
        continue;
      swap(H[k], H[r]);
      swap(T[k], T[r]);
      int x = inv(H[r][j]);
      for (int i = 0; i < 39; i++) {
        H[r][i] = mod(H[r][i] * x);
        T[r][i] = mod(T[r][i] * x);
      }
      for (int k = 0; k < 39; k++)
        if (k != r) {
          x = H[k][j];
          if (!x)
            continue;
          for (int i = 0; i < 39; i++) {
            H[k][i] = mod(H[k][i] - x * H[r][i]);
            T[k][i] = mod(T[k][i] - x * T[r][i]);
          }
        }
      p[r++] = j;
    }
    nullity = 39 - r;
    if (nullity > 15)
      abort();
    // RREF row transformation at pivots need not be supported in the principal
    // block. Invert it directly.
    for (int i = 0; i < r; i++)
      for (int j = 0; j < r; j++) {
        H[i][j] = G[p[i]][p[j]];
        T[i][j] = (i == j);
      }
    for (int j = 0; j < r; j++) {
      int k = j;
      while (k < r && !H[k][j])
        k++;
      if (k == r)
        abort();
      swap(H[k], H[j]);
      swap(T[k], T[j]);
      int x = inv(H[j][j]);
      for (int i = 0; i < r; i++) {
        H[j][i] = mod(H[j][i] * x);
        T[j][i] = mod(T[j][i] * x);
      }
      for (int k = 0; k < r; k++)
        if (k != j) {
          x = H[k][j];
          if (!x)
            continue;
          for (int i = 0; i < r; i++) {
            H[k][i] = mod(H[k][i] - x * H[j][i]);
            T[k][i] = mod(T[k][i] - x * T[j][i]);
          }
        }
    }
    int bc[39]{};
    for (int i = 0; i < r; i++) {
      for (int j = 0; j < r; j++)
        bc[i] -= T[i][j];
      bc[i] = mod(bc[i]);
      origin_norm -= bc[i];
    }
    for (int i = 0; i < nullity; i++) {
      int z = 0;
      for (int j = 0; j < 39; j++)
        z -= T[r + i][j];
      bias |= U(mod(z)) << (4 * i);
    }
    for (int h = 0; h < 3; h++) {
      int t = 0;
      for (int i = 3 + 12 * h; i < 15 + 12 * h; i++)
        for (int j = 3 + 12 * h; j < i; j++)
          if (!A[i][j]) {
            pairs[h][t][0] = i;
            pairs[h][t][1] = j;
            for (int x = 0; x < nullity; x++)
              pairing[h][t] |= U(mod(2 * (T[r + x][i] + T[r + x][j])))
                               << (4 * x);
            for (int x = 0; x < r; x++)
              if (p[x] == i || p[x] == j)
                w[h][t][x] = 2;
            for (int x = 0; x < r; x++) {
              int y = 0;
              for (int k = 0; k < r; k++)
                y += T[x][k] * w[h][t][k];
              dual[h][t][x] = mod(y);
              linear_norm[h][t] += w[h][t][x] * (y + 2 * bc[x]);
            }
            linear_norm[h][t] = mod(linear_norm[h][t]);
            t++;
          }
      if (t != 60)
        abort();
    }
    for (int i = 0; i < 3; i++)
      for (int j = 0; j < i; j++)
        for (int a = 0; a < 60; a++)
          for (int b = 0; b < 60; b++) {
            int v = 0;
            for (int k = 0; k < r; k++)
              v += w[i][a][k] * dual[j][b][k];
            cross[i][j][a][b] = mod(2 * v);
          }
  }
  // Return a positive value only when every far pair may occur with all radical
  // pairings in a common subspace of the permitted dimension. The Python stage
  // handles dimension two and the remaining real and geometric conditions.
  int check(int rank) {
    if (r > rank)
      return 0;
    int gap = rank - r;
    if (gap >= 4)
      return 3;
    Coverage zero{};
    map<U, Coverage> lines;
    int cap[39][39]{};
    for (int u = 3; u < 39; u++)
      for (int v = 3; v < u; v++) {
        int n = 0;
        for (int k = 0; k < 39; k++)
          n += A[u][k] * A[v][k];
        cap[u][v] = cap[v][u] = 2 - A[u][v] - n;
      }
    bool ok[3][3][60][60]{};
    for (int u = 0; u < 3; u++)
      for (int v = 0; v < u; v++)
        for (int a = 0; a < 60; a++)
          for (int b = 0; b < 60; b++) {
            bool z = true;
            for (int i : pairs[u][a])
              for (int j : pairs[v][b])
                z &= cap[i][j] > 0;
            ok[u][v][a][b] = z;
          }
    // When the radical pairing has to vanish, index the third wing by its
    // value.
    map<U, vector<int>> by_pairing;
    for (int c = 0; c < 60; c++)
      by_pairing[pairing[2][c]].push_back(c);
    vector<int> all_pairs(60);
    for (int i = 0; i < 60; i++)
      all_pairs[i] = i;
    for (int a = 0; a < 60; a++) {
      bool alive = false;
      for (int b = 0; b < 60; b++)
        if (ok[1][0][b][a]) {
          U u = add(add(bias, pairing[0][a]), pairing[1][b]);
          auto it = by_pairing.find(neg(u, nullity));
          if (gap < 2 && it == by_pairing.end())
            continue;
          for (int c : gap < 2 ? it->second : all_pairs) {
            if (!ok[2][0][c][a] || !ok[2][1][c][b])
              continue;
            U syndrome = add(u, pairing[2][c]);
            int q = mod(origin_norm + linear_norm[0][a] + linear_norm[1][b] +
                        linear_norm[2][c] + cross[1][0][b][a] +
                        cross[2][0][c][a] + cross[2][1][c][b]);
            if (!gap && q)
              continue;
            Coverage &z = syndrome ? lines[normalize(syndrome, nullity)] : zero;
            z[0] |= U(1) << a;
            z[1] |= U(1) << b;
            z[2] |= U(1) << c;
            alive = true;
          }
        }
      if (!alive)
        return 0;
    }
    U full = (U(1) << 60) - 1;
    if ((zero[0] & zero[1] & zero[2]) == full)
      return 1;
    for (auto &[v, z] : lines)
      if (((z[0] | zero[0]) & (z[1] | zero[1]) & (z[2] | zero[2])) == full)
        return 2;
    return 0;
  }
};
int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  std::ifstream charts_file(argv[1]);
  std::vector<std::array<Matching, 3>> charts;
  int id;
  while (charts_file >> id) {
    if (id != int(charts.size()))
      return 2;
    std::array<Matching, 3> m;
    for (auto &p : m)
      for (int &x : p)
        if (!(charts_file >> x) || x < 0 || x >= 12)
          return 2;
    charts.push_back(m);
  }
  if (!charts_file.eof() || charts.size() != 3580)
    return 2;
  int rank;
  while (std::cin >> id >> rank) {
    Matching p, seen{};
    for (int &x : p)
      if (!(std::cin >> x) || x < 0 || x >= 12 || seen[x]++)
        return 2;
    if (id < 0 || id >= int(charts.size()))
      return 2;
    auto &m = charts[id];
    ExtensionTest test(m[0], m[1], m[2], p);
    if (rank != test.r)
      return 3;
    if (test.check(32)) {
      std::cout << id << " " << rank;
      for (int x : p)
        std::cout << " " << x;
      std::cout << "\n";
    }
  }
  return std::cin.eof() ? 0 : 2;
}
