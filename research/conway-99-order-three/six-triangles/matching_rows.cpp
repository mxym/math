// Residual quotient rows for the 3K2 branch. Input is a stream of blocks of
// 20 lines, each containing the seven weights followed by seven mixed targets.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

namespace {
constexpr int size = 20;
using Mask = std::uint32_t;
using Profile = std::array<int, 7>;

int popcount(Mask mask) {
    return __builtin_popcount(mask);
}

struct Row {
    Mask support = 0;
    Mask doubles = 0;

    int at(int j) const {
        return ((support >> j) & 1u) + ((doubles >> j) & 1u);
    }
};

int dot(Row a, Row b) {
    return popcount(a.support & b.support) + popcount(a.support & b.doubles)
         + popcount(a.doubles & b.support) + popcount(a.doubles & b.doubles);
}

struct Search {
    std::array<Profile, size> weights{}, targets{};
    std::array<std::array<int, size>, size> overlap{};
    using Domains = std::array<std::vector<Row>, size>;

    void make_rows(int i, int j, int degree, int doubles, Profile needed,
                   Row row, std::vector<Row>& result) const {
        if (doubles < 0 || degree < 2 * doubles || degree - doubles > size - j) return;
        if (degree == 0) {
            if (std::all_of(needed.begin(), needed.end(), [](int x) { return x == 0; }))
                result.push_back(row);
            return;
        }
        if (j == size) return;
        make_rows(i, j + 1, degree, doubles, needed, row, result);
        if (j == i) return;

        for (int v = 1; v <= 2; ++v) {
            if (v > degree || (v == 2 && doubles == 0) || overlap[i][j] + v > 6) break;
            for (int h = 0; h < 7; ++h) needed[h] -= weights[j][h];
            if (*std::min_element(needed.begin(), needed.end()) < 0) break;
            row.support |= Mask{1} << j;
            if (v == 2) row.doubles |= Mask{1} << j;
            make_rows(i, j + 1, degree - v, doubles - (v == 2), needed, row, result);
        }
    }

    bool compatible_rows(const Domains& domains, Mask fixed) const {
        int i = -1;
        for (int j = 0; j < size; ++j) {
            if ((fixed >> j) & 1u) continue;
            if (i < 0 || domains[j].size() < domains[i].size()) i = j;
        }
        if (i < 0) return true;
        fixed |= Mask{1} << i;
        for (Row a : domains[i]) {
            Domains next;
            bool possible = true;
            for (int j = 0; j < size && possible; ++j) {
                if ((fixed >> j) & 1u) continue;
                const int value = a.at(j);
                for (Row b : domains[j]) {
                    if (value != b.at(i)) continue;
                    int sum = overlap[i][j] + value + dot(a, b);
                    if (3 <= sum && sum <= 6) next[j].push_back(b);
                }
                possible = !next[j].empty();
            }
            if (possible && compatible_rows(next, fixed)) return true;
        }
        return false;
    }

    bool admits_completion() {
        Domains domains;
        for (int i = 0; i < size; ++i) {
            for (int j = 0; j < size; ++j)
                overlap[i][j] = std::inner_product(weights[i].begin(), weights[i].end(),
                                                  weights[j].begin(), 0);
            int doubles = 2 - std::count(weights[i].begin(), weights[i].end(), 2);
            make_rows(i, 0, 8 - 2 * weights[i][0], doubles, targets[i], {}, domains[i]);
            if (domains[i].empty()) return false;
        }
        return compatible_rows(domains, 0);
    }
};
} // namespace

int main() {
    int checked = 0;
    for (;;) {
        Search search;
        std::cin >> std::ws;
        if (std::cin.eof()) break;
        for (int i = 0; i < size; ++i) {
            for (int& x : search.weights[i]) if (!(std::cin >> x)) return 2;
            for (int& x : search.targets[i]) if (!(std::cin >> x)) return 2;
        }
        if (search.admits_completion()) {
            std::cerr << "Compatible residual rows at input block " << checked << '\n';
            return 1;
        }
        ++checked;
    }
    std::cout << "Residual blocks exhausted: " << checked << '\n';
    return checked ? 0 : 2;
}
