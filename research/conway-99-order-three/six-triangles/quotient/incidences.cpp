// Enumerate binary 6-by-27 matrices up to column permutations and Aut(C).
// The input is the connection graph, XX^t, and the admissibility flag of
// each of the 64 possible columns, in bit-mask order.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

namespace {
using Six = std::array<int, 6>;
using Graph = std::array<Six, 6>;
using Counts = std::array<int, 64>;

int support_size(int mask) {
    int result = 0;
    while (mask) {
        mask &= mask - 1;
        ++result;
    }
    return result;
}

class Enumeration {
public:
    Graph c{}, moment{};
    Counts allowed{};
    std::uint64_t total = 0, representatives = 0, orbit_sum = 0;

    void run() {
        Six p{0, 1, 2, 3, 4, 5};
        do {
            bool preserves = true;
            for (int i = 0; i < 6; ++i)
                for (int j = 0; j < 6; ++j)
                    if (c[i][j] != c[p[i]][p[j]]) preserves = false;
            if (!preserves) continue;
            Counts action{};
            for (int mask = 0; mask < 64; ++mask)
                for (int i = 0; i < 6; ++i)
                    if ((mask >> i) & 1) action[mask] |= 1 << p[i];
            permutations.push_back(action);
        } while (std::next_permutation(p.begin(), p.end()));
        for (int mask = 0; mask < 64; ++mask) {
            if (!allowed[mask]) continue;
            for (int r = 0; r <= 6; ++r) prefix[r][mask % (1 << r)] = true;
        }
        count[0] = 27;
        next_row(0);
    }

private:
    Counts count{};
    std::array<std::array<bool, 64>, 7> prefix{};
    std::vector<Counts> permutations;

    void record() {
        ++total;
        unsigned stabilizer = 0;
        for (const Counts& p : permutations) {
            bool equal = true;
            for (int m = 0; m < 64; ++m) {
                if (count[m] == count[p[m]]) continue;
                if (count[m] > count[p[m]]) return;
                equal = false;
                break;
            }
            stabilizer += equal;
        }
        orbit_sum += permutations.size() / stabilizer;
        ++representatives;
        for (int n : count) std::cout << n << " ";
        std::cout << "\n";
    }

    void next_row(int r) {
        if (r == 6) { record(); return; }
        std::vector<int> cells;
        for (int mask = 0; mask < (1 << r); ++mask)
            if (count[mask]) cells.push_back(mask);
        int bit = 1 << r;
        auto options = [&](int m) { return int(prefix[r + 1][m]) + prefix[r + 1][m + bit]; };
        std::sort(cells.begin(), cells.end(), [&](int a, int b) {
            if (options(a) != options(b)) return options(a) < options(b);
            return support_size(a) > support_size(b);
        });
        // Entry r counts all ones in this row. Earlier entries count overlap
        // with the already assigned rows.
        Six needed = moment[r];
        std::vector<Six> lower(cells.size() + 1), upper(cells.size() + 1);
        for (int k = int(cells.size()) - 1; k >= 0; --k) {
            int m = cells[k];
            for (int j = 0; j <= r; ++j) {
                int contribution = (j == r || ((m >> j) & 1)) ? count[m] : 0;
                lower[k][j] = lower[k + 1][j] + (prefix[r + 1][m] ? 0 : contribution);
                upper[k][j] = upper[k + 1][j] + (prefix[r + 1][m + bit] ? contribution : 0);
            }
        }

        auto split = [&](auto&& self, std::size_t k) -> void {
            if (k == cells.size()) { next_row(r + 1); return; }
            int m = cells[k], size = count[m];
            int lo = prefix[r + 1][m] ? 0 : size;
            int hi = prefix[r + 1][m + bit] ? size : 0;
            for (int j = 0; j <= r; ++j) {
                if (j == r || ((m >> j) & 1)) {
                    lo = std::max(lo, needed[j] - upper[k + 1][j]);
                    hi = std::min(hi, needed[j] - lower[k + 1][j]);
                } else if (needed[j] < lower[k + 1][j] || needed[j] > upper[k + 1][j]) {
                    return;
                }
            }
            for (int n = lo; n <= hi; ++n) {
                for (int j = 0; j <= r; ++j)
                    if (j == r || ((m >> j) & 1)) needed[j] -= n;
                count[m] = size - n;
                count[m + bit] = n;
                self(self, k + 1);
                count[m] = size;
                count[m + bit] = 0;
                for (int j = 0; j <= r; ++j)
                    if (j == r || ((m >> j) & 1)) needed[j] += n;
            }
        };
        split(split, 0);
    }
};
} // namespace

int main() {
    Enumeration e;
    for (auto& row : e.c)
        for (int& x : row) if (!(std::cin >> x)) return 2;
    for (auto& row : e.moment)
        for (int& x : row) if (!(std::cin >> x)) return 2;
    for (int& x : e.allowed) if (!(std::cin >> x) || (x != 0 && x != 1)) return 2;
    e.run();
    if (e.orbit_sum != e.total) return 1;
    std::cerr << e.total << " " << e.representatives << "\n";
    return 0;
}
