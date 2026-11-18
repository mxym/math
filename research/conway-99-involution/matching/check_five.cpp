// Lift four of the eight free rows of a quotient under a 5-cycle of axes.
#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

namespace {
constexpr int n = 8, p = 5, quota_count = 7 + 3*p;
using Word = std::array<int,p>;
using Row = std::array<int,n>;
using Quota = std::array<int,quota_count>;
struct Choice { Word word; bool twice; Quota use{}; };

int rotated(int support, int shift) {
    int moving = support & 31;
    return (support & ~31) | (((moving << shift) | (moving >> (p-shift))) & 31);
}

struct Search {
    std::array<Row,n> quotient{};
    std::array<std::array<Word,n>,n> blocks{};
    Row support{}, mate{};
    std::array<std::vector<Choice>,4> patterns;
    unsigned long long nodes = 0;
    Search() {
        mate.fill(-1);
        for (int v = 0; v < 243; ++v) {
            Word word{};
            int number = v, total = 0, doubles = 0;
            for (int& digit : word) {
                digit = number % 3;
                number /= 3;
                total += digit;
                doubles += digit == 2;
            }
            if (total <= 3 && doubles <= 1) patterns[total].push_back({word, doubles == 1});
        }
    }

    bool extend(int i) {
        ++nodes;
        if (i == 4) return true;
        Quota target{};
        for (int h = 0; h < p; ++h) target[h] = 4 - 2*((support[i] >> h) & 1);
        int entries = p;
        for (int k = 0; k < i; ++k) for (int h = 0; h < p; ++h)
            target[entries++] = 4 - __builtin_popcount(support[i] & rotated(support[k],h))
                                  - blocks[i][k][h];
        for (int h = 1; h <= 2; ++h)
            target[entries++] = 4 - __builtin_popcount(support[i] & rotated(support[i],h));

        std::array<std::vector<Choice>,n> allowed;
        Row order{};
        std::iota(order.begin(),order.end(),0);
        for (int j = 0; j < n; ++j) {
            for (Choice c : patterns.at(quotient[i][j])) {
                const auto& w = c.word;
                if (i == j && (w[0] || w[1] != w[4] || w[2] != w[3] || c.twice)) continue;
                if (j < i && w != blocks[i][j]) continue;
                if (c.twice && ((mate[i] >= 0 && mate[i] != j)
                                || (mate[j] >= 0 && mate[j] != i))) continue;
                for (int h = 0; h < p; ++h) for (int a = 0; a < p; ++a)
                    if ((rotated(support[j],h) >> a) & 1) c.use[a] += w[h];
                int q = p;
                for (int k = 0; k < i; ++k) for (int h = 0; h < p; ++h, ++q)
                    for (int t = 0; t < p; ++t) c.use[q] += w[t]*blocks[k][j][(t+p-h)%p];
                for (int h = 1; h <= 2; ++h, ++q) {
                    if (i == j) c.use[q] += w[h];
                    for (int t = 0; t < p; ++t) c.use[q] += w[t]*w[(t+p-h)%p];
                }
                bool fits = true;
                for (int z = 0; z < entries; ++z) fits &= c.use[z] <= target[z];
                if (fits) allowed[j].push_back(c);
            }
            if (allowed[j].empty()) return false;
        }
        std::stable_sort(order.begin(),order.end(),[&](int j,int k) {
            return allowed[j].size() < allowed[k].size();
        });
        std::array<Quota,n+1> low{},high{};
        for (int h = n-1; h >= 0; --h) for (int z = 0; z < entries; ++z) {
            int least = 5, greatest = 0;
            for (const auto& c : allowed[order[h]]) {
                least = std::min(least,c.use[z]);
                greatest = std::max(greatest,c.use[z]);
            }
            low[h][z] = low[h+1][z] + least;
            high[h][z] = high[h+1][z] + greatest;
        }
        auto assign = [&](auto&& self, int h, int double_j) -> bool {
            for (int z = 0; z < entries; ++z)
                if (target[z] < low[h][z] || target[z] > high[h][z]) return false;
            if (h == n) {
                if (double_j < 0) return false;
                int old_i = mate[i], old_j = mate[double_j];
                mate[i] = double_j;
                mate[double_j] = i;
                bool found = extend(i+1);
                mate[i] = old_i;
                mate[double_j] = old_j;
                return found;
            }
            int j = order[h];
            for (const auto& c : allowed[j]) {
                if (c.twice && double_j >= 0) continue;
                blocks[i][j] = c.word;
                for (int t = 0; t < p; ++t) blocks[j][i][(p-t)%p] = c.word[t];
                for (int z = 0; z < entries; ++z) target[z] -= c.use[z];
                if (self(self,h+1,c.twice ? j : double_j)) return true;
                for (int z = 0; z < entries; ++z) target[z] += c.use[z];
            }
            return false;
        };
        return assign(assign,0,-1);
    }
};
}

int main() {
    int cases = 0, layout;
    unsigned long long nodes = 0;
    while (std::cin >> layout) {
        Search search;
        for (int i = 0; i < n; ++i) {
            search.support[i] = i < 4 ? 1 | (1 << (5+i/2)) : 1 | (1 << (1+((layout>>(i-4))&1)));
            for (int& v : search.quotient[i]) if (!(std::cin >> v)) return 2;
        }
        if (search.extend(0)) {
            std::cerr << "four compatible cyclic rows in case " << cases << '\n';
            return 1;
        }
        nodes += search.nodes;
        ++cases;
    }
    if (cases != 96) return 2;
    std::cout << cases << " cyclic lift cases, " << nodes << " prefixes, no four rows\n";
}
