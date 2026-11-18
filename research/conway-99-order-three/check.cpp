// Finite lemma in the proof. A position is a point of F_3^4 in base 3.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <vector>

using Matrix = std::vector<std::vector<int>>;
constexpr int point_count = 81;

Matrix squared_distances(int last_coefficient) {
    Matrix distances(point_count, std::vector<int>(point_count));
    for (int a = 0; a < point_count; ++a) {
        for (int b = 0; b < point_count; ++b) {
            int x = a, y = b, norm = 0;
            for (int coord = 0; coord < 4; ++coord) {
                int delta = x % 3 - y % 3;
                norm += (coord == 3 ? last_coefficient : 1) * delta * delta;
                x /= 3;
                y /= 3;
            }
            distances[a][b] = norm % 3;
        }
    }
    return distances;
}

struct Pattern {
    std::vector<int> diagonal, singles;
    Matrix doubles;
};

Pattern cycle_pattern(const std::vector<int>& cycles) {
    Pattern pattern{std::vector<int>(12, 2), std::vector<int>(12, 5),
                    Matrix(12, std::vector<int>(12))};
    int start = 0;
    for (int length : cycles) {
        for (int k = 0; k < length; ++k) {
            int i = start + k, j = start + (k + 1) % length;
            pattern.diagonal[i] = 0;
            pattern.singles[i] = 3;
            pattern.doubles[i][j] = pattern.doubles[j][i] = 1;
        }
        start += length;
    }
    return pattern;
}

// Count embeddings with the first point at the origin (translation invariance).
// A call at depth i has chosen the images of labels 0,...,i-1.
struct Search {
    const Pattern& pattern;
    const Matrix& distances;
    std::vector<int> point, remaining;
    std::array<bool, point_count> used{};
    std::uint64_t prefixes = 0, complete = 0;

    Search(const Pattern& p, const Matrix& d)
        : pattern(p), distances(d), point(p.diagonal.size()), remaining(p.singles) {}

    void visit(int i) {
        ++prefixes;
        int n = static_cast<int>(point.size());
        if (i == n) {
            if (std::all_of(remaining.begin(), remaining.end(), [](int x) { return x == 0; }))
                ++complete;
            return;
        }

        std::array<int, 12> single_neighbors{};
        for (int x = 0; x < (i == 0 ? 1 : point_count); ++x) {
            if (used[x]) continue;
            int singles_here = 0;
            bool feasible = true;
            for (int j = 0; j < i; ++j) {
                int entry = (distances[x][point[j]] + 7
                             - pattern.diagonal[i] - pattern.diagonal[j]) % 3;
                if ((entry == 2) != (pattern.doubles[i][j] == 1)) {
                    feasible = false;
                    break;
                }
                if (entry == 1) single_neighbors[singles_here++] = j;
                int need = remaining[j] - (entry == 1);
                if (need < 0 || need > n - i - 1) {
                    feasible = false;
                    break;
                }
            }
            int need = remaining[i] - singles_here;
            if (!feasible || need < 0 || need > n - i - 1) continue;

            point[i] = x;
            used[x] = true;
            remaining[i] -= singles_here;
            for (int k = 0; k < singles_here; ++k) --remaining[single_neighbors[k]];
            visit(i + 1);
            for (int k = 0; k < singles_here; ++k) ++remaining[single_neighbors[k]];
            remaining[i] += singles_here;
            used[x] = false;
        }
    }
};

int main() {
    const std::vector<std::vector<int>> cycles{
        {3,3}, {6}, {3,3,3}, {3,6}, {9},
        {3,3,3,3}, {3,3,6}, {3,9}, {5,7}, {6,6}, {12}
    };
    for (int coefficient : {1, 2}) {
        Matrix distances = squared_distances(coefficient);
        // For two independent labels, entry 2 is equivalent to squared distance 1.
        // Count the unit sphere independently by separating zero/nonzero coordinates.
        int sphere = 0;
        for (int mask = 0; mask < 16; ++mask) {
            int norm = 0, choices = 1;
            for (int j = 0; j < 4; ++j) {
                if (mask & (1 << j)) {
                    norm += (j == 3 ? coefficient : 1);
                    choices *= 2;
                }
            }
            if (norm % 3 == 1) sphere += choices;
        }
        Pattern edge{{0,0}, {0,0}, {{0,1},{1,0}}};
        Search control(edge, distances);
        control.visit(0);
        if (control.complete != static_cast<unsigned>(sphere) || sphere == 0) return 1;
        std::cout << "last coefficient " << coefficient << ", unit sphere " << sphere << '\n';
        for (const auto& parts : cycles) {
            Pattern p = cycle_pattern(parts);
            Search search(p, distances);
            search.visit(0);
            for (int length : parts) std::cout << length << ' ';
            std::cout << "| " << search.prefixes << " prefixes | " << search.complete
                      << " completions\n";
            if (search.complete != 0) return 1;
        }
    }
}
