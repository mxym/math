// Fourteen orbit rows for two 3-cycles of axes and one fixed axis.
#include <algorithm>
#include <array>
#include <bitset>
#include <iostream>
#include <numeric>
#include <vector>

namespace {
constexpr int n = 14;
using Row = std::array<int, n>;
using Totals = std::array<int, n + 5>;
constexpr Row groups{0,0,1,1,2,2,3,3,4,4,4,4,4,4};
constexpr int weights[5][3] = {{1,1,0},{1,0,1},{0,2,0},{0,0,2},{0,1,1}};

struct Search {
    Row group{};
    std::array<Row,n> matrix{}, common{};
    unsigned long long nodes = 0;

    bool extend(int i) {
        ++nodes;
        if (i == n) return true;
        int diagonal = matrix[i][i];
        Totals target{12, 4 - 2*weights[group[i]][0], 12 - 2*weights[group[i]][1],
                      12 - 2*weights[group[i]][2], 24 - common[i][i] - diagonal};
        for (int j = 0; j < i; ++j) target[5+j] = 12 - common[i][j] - matrix[i][j];
        std::array<Totals,n> column{};
        for (int j = 0; j < n; ++j) {
            auto& c = column[j];
            c[0] = 1;
            for (int a = 0; a < 3; ++a) c[1+a] = weights[group[j]][a];
            for (int k = 0; k < i; ++k) c[5+k] = matrix[k][j];
            if (j <= i) {
                int v = matrix[i][j];
                for (int k = 0; k < 5+i; ++k) target[k] -= k == 4 ? v*v : c[k]*v;
            }
        }
        Row equivalent{};
        equivalent.fill(-1);
        for (int j = i+1; j < n; ++j) {
            for (int h = i+1; h < j; ++h) {
                if (group[j] != group[h] || matrix[j][j] != matrix[h][h]) continue;
                bool equal = true;
                for (int k = 0; k < i; ++k) equal &= matrix[k][j] == matrix[k][h];
                if (equal) equivalent[j] = h;
            }
        }
        std::array<Totals,n+1> upper{};
        for (int j = n-1; j > i; --j)
            for (int k = 0; k < 5+i; ++k)
                upper[j][k] = upper[j+1][k] + (k == 4 ? 16 : 4*column[j][k]);
        auto assign = [&](auto&& self, int j) -> bool {
            for (int k = 0; k < 5+i; ++k)
                if (target[k] < 0 || target[k] > upper[j][k]) return false;
            if (j == n) return extend(i+1);
            int limit = equivalent[j] < 0 ? 4 : matrix[i][equivalent[j]];
            for (int v = 0; v <= limit; ++v) {
                matrix[i][j] = matrix[j][i] = v;
                for (int k = 0; k < 5+i; ++k) target[k] -= k == 4 ? v*v : column[j][k]*v;
                if (self(self, j+1)) return true;
                for (int k = 0; k < 5+i; ++k) target[k] += k == 4 ? v*v : column[j][k]*v;
            }
            return false;
        };
        return assign(assign, i+1);
    }

    bool run(unsigned mask) {
        Row order{};
        std::iota(order.begin(), order.end(), 0);
        auto selected = [&](int j) { return (mask >> j) & 1U; };
        std::stable_sort(order.begin(), order.end(), [&](int j, int k) {
            return selected(j) > selected(k);
        });
        for (int i = 0; i < n; ++i) {
            group[i] = groups[order[i]];
            matrix[i][i] = 2*selected(order[i]);
        }
        for (int i = 0; i < n; ++i) for (int j = 0; j < n; ++j) {
            const int *x = weights[group[i]], *y = weights[group[j]];
            common[i][j] = 3*x[0]*y[0] + x[1]*y[1] + x[2]*y[2];
        }
        return extend(0);
    }
};
}

int main() {
    unsigned long long nodes = 0;
    int cases = 0;
    for (unsigned mask = 0; mask < (1U << n); ++mask) {
        int size = std::bitset<n>(mask).count();
        if (size != 3 && size != 10) continue;
        bool canonical = true;
        for (int i = 1; i < n; ++i)
            if (groups[i] == groups[i-1] && ((mask >> i) & 1U) > ((mask >> (i-1)) & 1U))
                canonical = false;
        if (!canonical) continue;
        Search search;
        if (search.run(mask)) {
            std::cerr << "surviving quotient for mask " << mask << '\n';
            return 1;
        }
        ++cases;
        nodes += search.nodes;
    }
    std::cout << cases << " diagonal patterns, " << nodes << " prefixes, no quotient\n";
}
