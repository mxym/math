// Local matching and integral marginal enumeration for the twelve fibers of K6 minus a matching.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>

using Mask = std::uint64_t;
using Pair = std::array<int, 2>;
using Triple = std::array<int, 3>;
using Quart = std::array<int, 4>;
using Margins = std::array<int, 27>;

constexpr int sites = 36;
std::array<Pair, 12> duads, ends;
std::array<Quart, 6> stars;
std::array<std::array<Pair, 2>, 3> rungs;
std::array<Triple, 6> perm;
std::array<int, 12> chart;
std::array<int, 6> rung_map;
std::array<Mask, sites> adj;
int deficit[sites][sites];
long long tested = 0, core_ok = 0, caps_ok = 0, complete = 0;

Mask bit(int i) { return Mask(1) << i; }
int count(Mask v) { return __builtin_popcountll(v); }
void toggle(int i, int j) { adj[i] ^= bit(j); adj[j] ^= bit(i); }
bool contains(Pair p, int i) { return p[0] == i || p[1] == i; }
bool incident(int a, int b) {
    return contains(duads[a], duads[b][0]) || contains(duads[a], duads[b][1]);
}
int cap_group(int f) { return 3 - duads[f][0] / 2 - duads[f][1] / 2; }

struct Caps {
    int alignment;
    std::array<Mask, 3> words{};
};

std::vector<Caps> possible_caps(int group) {
    std::vector<Caps> options;
    for (int p = 0; p < 6; ++p) {
        Caps c{p};
        bool fits = true;
        for (int label = 0; label < 3; ++label) {
            Quart v{};
            for (int j = 0; j < 2; ++j) {
                auto [a, b] = rungs[group][j];
                int x = j == 0 ? label : perm[p][label];
                v[2*j] = 3*a + x;
                v[2*j+1] = 3*b + perm[rung_map[2*group+j]][x];
            }
            for (int i : v) c.words[label] |= bit(i);
            for (int i = 0; i < 2; ++i)
                for (int j = 2; j < 4; ++j)
                    if (deficit[v[i]][v[j]] < 1) fits = false;
        }
        if (fits) options.push_back(c);
    }
    return options;
}

struct Slice {
    std::array<Mask, 3> words{};
    Margins pairs{};
};
bool triple_conflict(const Slice& a, const Slice& b) {
    for (Mask u : a.words) for (Mask v : b.words)
        if (count(u & v) > 2) return true;
    return false;
}

// Fix the value on the first fiber. The three other coordinate multisets of
// the three words in this slice are all prescribed by pair margins.
bool admits_star(const Quart& fibers, const Caps& c, const Caps& d) {
    int m[4][4][3][3]{};
    for (int i = 0; i < 4; ++i) for (int j = i+1; j < 4; ++j)
        for (int x = 0; x < 3; ++x) for (int y = 0; y < 3; ++y) {
            int s = 3*fibers[i]+x, t = 3*fibers[j]+y;
            int n = deficit[s][t];
            Mask pair = bit(s) | bit(t);
            for (const Caps* caps : {&c,&d}) for (Mask w : caps->words)
                if ((w & pair) == pair) --n;
            if (n < 0) return false;
            m[i][j][x][y] = n;
        }
    Margins target{};
    int r = 0;
    for (int i = 1; i < 4; ++i) for (int j = i+1; j < 4; ++j)
        for (int x = 0; x < 3; ++x) for (int y = 0; y < 3; ++y)
            target[r++] = m[i][j][x][y];

    std::array<std::vector<Slice>,3> slices;
    for (int anchor = 0; anchor < 3; ++anchor) {
        std::array<Triple,3> cols{};
        for (int k = 0; k < 3; ++k) {
            int n = 0;
            for (int y = 0; y < 3; ++y) for (int l = 0; l < m[0][k+1][anchor][y]; ++l) {
                if (n == 3) return false;
                cols[k][n++] = y;
            }
            if (n != 3) return false;
        }
        do {
            do {
                Slice s{};
                bool ok = true;
                for (int i = 0; i < 3; ++i) {
                    s.words[i] = bit(3*fibers[0]+anchor);
                    for (int j = 0; j < 3; ++j) s.words[i] |= bit(3*fibers[j+1]+cols[j][i]);
                    for (int j = 0; j < i; ++j)
                        if (count(s.words[i] & s.words[j]) > 2) ok = false;
                    int block = 0;
                    for (int j = 0; j < 3; ++j) for (int k = j+1; k < 3; ++k) {
                        int t = 9*block++ + 3*cols[j][i] + cols[k][i];
                        if (++s.pairs[t] > target[t]) ok = false;
                    }
                    for (int t = 0; t < sites; ++t)
                        if (count(adj[t] & s.words[i]) + int((s.words[i] >> t) & 1) > 2)
                            ok = false;
                }
                if (ok) slices[anchor].push_back(s);
            } while (std::next_permutation(cols[2].begin(), cols[2].end()));
        } while (std::next_permutation(cols[1].begin(), cols[1].end()));
        if (slices[anchor].empty()) return false;
    }
    for (const auto& a : slices[0]) for (const auto& b : slices[1]) {
        if (triple_conflict(a,b)) continue;
        Margins need{};
        bool possible = true;
        for (int i = 0; i < 27; ++i) {
            need[i] = target[i] - a.pairs[i] - b.pairs[i];
            if (need[i] < 0) possible = false;
        }
        if (!possible) continue;
        for (const auto& z : slices[2])
            if (z.pairs == need && !triple_conflict(a,z) && !triple_conflict(b,z)) return true;
    }
    return false;
}

void test_core(int id) {
    ++tested;
    for (int a = 0; a < 12; ++a) for (int b = a+1; b < 12; ++b) if (incident(a,b))
        for (int i = 3*a; i < 3*a+3; ++i) for (int j = 3*b; j < 3*b+3; ++j) {
            int v = 2-count(adj[i]&adj[j]);
            if (v < 0) return;
            deficit[i][j] = deficit[j][i] = v;
        }
    ++core_ok;
    std::array<std::vector<Caps>,3> caps;
    for (int h = 0; h < 3; ++h) {
        caps[h] = possible_caps(h);
        if (caps[h].empty()) return;
    }
    ++caps_ok;
    bool pass[3][6][6]{};
    for (int h = 0; h < 3; ++h) {
        int u = (h+1)%3, v = (h+2)%3;
        bool any = false;
        for (const auto& c : caps[u]) for (const auto& d : caps[v]) {
            bool ok = admits_star(stars[2*h],c,d) && admits_star(stars[2*h+1],c,d);
            pass[h][c.alignment][d.alignment] = ok;
            any |= ok;
        }
        if (!any) return;
    }
    for (const auto& a : caps[0]) for (const auto& b : caps[1]) for (const auto& c : caps[2]) {
        int i=a.alignment, j=b.alignment, k=c.alignment;
        if (pass[0][j][k] && pass[1][k][i] && pass[2][i][j]) {
            std::cout << id;
            for (int t : rung_map) std::cout << ' ' << t;
            std::cout << ' ' << i << ' ' << j << ' ' << k << '\n';
            ++complete;
        }
    }
}
void fill_rungs(int level, int id) {
    if (level == 6) { test_core(id); return; }
    auto [a,b] = rungs[level/2][level%2];
    for (int p = 0; p < 6; ++p) {
        rung_map[level] = p;
        for (int x = 0; x < 3; ++x) toggle(3*a+x,3*b+perm[p][x]);
        fill_rungs(level+1,id);
        for (int x = 0; x < 3; ++x) toggle(3*a+x,3*b+perm[p][x]);
    }
}
int main() {
    int n;
    std::cin >> n;
    for (auto& p : duads) std::cin >> p[0] >> p[1];
    for (auto& p : ends) std::cin >> p[0] >> p[1];
    Triple t{0,1,2};
    for (auto& p : perm) { p=t; std::next_permutation(t.begin(),t.end()); }
    std::array<int,3> nr{};
    for (int a = 0; a < 12; ++a) for (int b = a+1; b < 12; ++b)
        if (!incident(a,b) && !contains(ends[a],ends[b][0]) && !contains(ends[a],ends[b][1])) {
            int h = cap_group(a);
            rungs.at(h).at(nr[h]++) = {a,b};
        }
    for (int a = 0; a < 6; ++a) {
        int k=0; for (int i=0; i<12; ++i) if (contains(duads[i],a)) stars[a].at(k++)=i;
        if (k!=4) throw std::logic_error("invalid star");
    }
    for (int id = 0; id < n; ++id) {
        for (int& x : chart) std::cin >> x;
        if (!std::cin) throw std::runtime_error("incomplete gauge list");
        adj.fill(0);
        for (int a=0; a<12; ++a) for (int i=0; i<3; ++i) toggle(3*a+i,3*a+(i+1)%3);
        for (int a=0; a<12; ++a) for (int b=a+1; b<12; ++b)
            for (int v : ends[a]) if (contains(ends[b],v))
                for (int i=0; i<3; ++i) for (int j=0; j<3; ++j) {
                    int x = v==ends[a][0] ? i : perm[chart[a]][i];
                    int y = v==ends[b][0] ? j : perm[chart[b]][j];
                    if (x==y) toggle(3*a+i,3*b+j);
                }
        fill_rungs(0,id);
    }
    if (tested != 3685824 || core_ok != 31371 || caps_ok != 11713 || complete != 15)
        throw std::runtime_error("unexpected core census");
    std::cerr << "Core assignments " << tested << ", pair quotas " << core_ok
              << ", cap candidates " << caps_ok << ", literal star survivors " << complete << '\n';
}
