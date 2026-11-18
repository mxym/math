// Search the unsigned orbit equations with prescribed invariant grids.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
constexpr int scale = 65536;
static_assert(std::numeric_limits<int>::digits >= 31);
using Wide = std::int64_t;
// Diagonals start below 60 * scale and increase by at most capacity units
// per pivot. Cauchy bounds every accepted cross product before division.

struct Parameters {
    int n, fixed, degree;
    // identity * I + adjacency * T + gram * transpose(X)X + common * J.
    struct Form { int identity, adjacency, gram, common; };
    std::array<Form, 2> forms;
};
constexpr Parameters conway{49, 7, 14, {{{6, -2, -1, 1}, {60, 15, -3, -4}}}};
constexpr Parameters golay{121, 11, 22, {{{60, -15, -5, 4}, {30, 6, -1, -1}}}};

template<int capacity>
class Search {
    using Row = std::array<int, capacity>;
    using Matrix = std::array<Row, capacity>;
    struct Bounds { std::array<Matrix, 2> offset{}; };
    struct Cell {
        std::vector<int> column;
        std::vector<int> labels;
        int mask; // Bit v permits putting weight v on an edge.
    };
public:
    explicit Search(Parameters parameters) : p(parameters), depth(p.fixed), levels(p.n + 1) {
        std::iota(order.begin(), order.end(), 0);
        for (auto& row : given) row.fill(-1);
        int k = p.fixed;
        for (int i = 0; i < p.fixed; ++i) {
            b[i][i] = 1;
            for (int j = i + 1; j < p.fixed; ++j) {
                for (int sign = 0; sign < 2; ++sign, ++k) {
                    b[i][k] = b[k][i] = b[j][k] = b[k][j] = 1;
                    supports[k] = (1 << i) | (1 << j);
                }
            }
        }
        if (k != p.n) throw std::logic_error("number of orbit labels");
    }

    Matrix b{};
    std::uint64_t nodes = 0;
    std::array<bool, capacity> grids{};
    Matrix given{};
    bool fixture = false;

    bool run() {
        Bounds& start = levels[depth];
        for (int f = 0; f < 2; ++f) {
            auto form = p.forms[f];
            for (int i = 0; i < p.n; ++i) {
                for (int j = 0; j < p.n; ++j) {
                    int diagonal = i == j ? form.identity + form.adjacency * b[i][i] : 0;
                    start.offset[f][i][j] = scale * (form.common + diagonal + form.gram * __builtin_popcount(supports[i] & supports[j]));
                }
            }
        }
        return complete(start);
    }

private:
    Parameters p;
    Row order{}, supports{};
    int pair_id(int i) const { return (i - p.fixed) / 2; }
    int twin(int i) const { return p.fixed + ((i - p.fixed) ^ 1); }
    int depth;
    std::vector<Bounds> levels;

    bool eliminate(Bounds& bounds, int i, int first) const {
        for (int f = 0; f < 2; ++f) {
            auto& m = bounds.offset[f];
            int pivot = m[i][i], slope = scale * p.forms[f].adjacency;
            if (pivot < 0) return false;
            std::array<Wide, capacity> cross{};
            for (int a = first; a < p.n; ++a) {
                int j = order[a];
                cross[j] = m[i][j] + slope * b[i][j];
                if (m[j][j] < 0 || cross[j] * cross[j] > Wide(pivot) * m[j][j])
                    return false;
            }
            if (pivot == 0) continue;
            // Replace the exact Schur complement with a PSD upper bound. Each
            // inexact off-diagonal division needs one unit on both diagonals.
            Row padding{};
            for (int a = first; a < p.n; ++a) {
                int j = order[a];
                for (int z = a; z < p.n; ++z) {
                    int k = order[z];
                    Wide numerator = cross[j] * cross[k];
                    Wide quotient = numerator / pivot;
                    m[j][k] -= static_cast<int>(quotient);
                    m[k][j] = m[j][k];
                    if (j != k && quotient * pivot != numerator) {
                        ++padding[j];
                        ++padding[k];
                    }
                }
            }
            for (int a = first; a < p.n; ++a) m[order[a]][order[a]] += padding[order[a]];
        }
        return true;
    }

    int allowed(const Bounds& bounds, int i, int j, int maximum) const {
        int mask = 0;
        int pi = pair_id(i), pj = pair_id(j), known = given[i][j];
        if (pi == pj && grids[pi]) known = 2;
        if (pi != pj && (grids[pi] || grids[pj]))
            maximum = std::min(maximum, (supports[i] & supports[j]) ? 0 : 1);
        for (int v = 0; v <= maximum; ++v) {
            if (known >= 0 && v != known) continue;
            bool valid = true;
            for (int f = 0; f < 2; ++f) {
                const auto& m = bounds.offset[f];
                Wide cross = m[i][j] + scale * p.forms[f].adjacency * v;
                if (m[i][i] < 0 || m[j][j] < 0 || cross * cross > Wide(m[i][i]) * m[j][j]) {
                    valid = false;
                    break;
                }
            }
            if (valid) mask |= 1 << v;
        }
        return mask;
    }

    bool full_matrix() const {
        for (int i = 0; i < p.n; ++i) {
            if (std::accumulate(b[i].begin(), b[i].begin() + p.n, 0) != p.degree - int(i < p.fixed)) return false;
            for (int j = 0; j < p.n; ++j) {
                if (b[i][j] != b[j][i]) return false;
                int products = std::inner_product(b[i].begin(), b[i].begin() + p.n, b[j].begin(), 0);
                if (products + b[i][j] != 4 - 2 * int(i < p.fixed && j < p.fixed) + (p.degree - 2) * (i == j)) return false;
            }
        }
        return true;
    }

    bool complete(const Bounds& bounds) {
        ++nodes;
        if (depth == p.n) {
            if (!full_matrix()) throw std::logic_error("leaf violates orbit identity");
            return true;
        }
        int best = depth, fewest = 3 * capacity + 1;
        for (int a = depth; a < p.n; ++a) {
            int count = 0;
            for (int z = depth; z < p.n; ++z) {
                if (z == a) continue;
                int mask = allowed(bounds, order[a], order[z], 2);
                if (!mask) return false;
                count += (mask & 1) + ((mask >> 1) & 1) + ((mask >> 2) & 1);
            }
            if (count < fewest) {
                best = a;
                fewest = count;
            }
        }
        std::swap(order[depth], order[best]);
        bool found = fill_row(bounds, order[depth]);
        std::swap(order[depth], order[best]);
        return found;
    }

    bool fill_row(const Bounds& bounds, int i) {
        int degree = p.degree, doubles = 1;
        std::vector<int> target(1 + depth);
        for (int a = 0; a < depth; ++a) {
            int j = order[a];
            degree -= b[i][j];
            doubles -= b[i][j] == 2;
            int needed = 4 - b[i][j];
            for (int z = 0; z < depth; ++z)
                needed -= b[i][order[z]] * b[j][order[z]];
            if (needed < 0) return false;
            target[a + 1] = needed;
        }
        int singles = degree - 2 * doubles;
        if (singles < 0 || doubles < 0) return false;
        target[0] = degree;

        std::map<std::vector<int>, std::vector<int>> groups;
        for (int a = depth + 1; a < p.n; ++a) {
            int j = order[a], used = 0, used_doubles = 0, shared = 0;
            std::vector<int> signature{1};
            for (int z = 0; z < depth; ++z) {
                int k = order[z], weight = b[j][k];
                signature.push_back(weight);
                used += weight;
                used_doubles += weight == 2;
                shared += b[i][k] * weight;
            }
            if (used > p.degree || used_doubles > 1 || shared > 4) return false;
            int upper = std::min({2, p.degree - used, 4 - shared, used_doubles == 1 ? 1 : 2});
            int mask = allowed(bounds, i, j, upper);
            if (!(supports[i] & supports[j])) {
                for (int z = p.fixed; z < depth; ++z) {
                    int k = order[z];
                    if (grids[pair_id(j)] && k == twin(j)) mask &= 1 << (1 - b[i][k]);
                    if (grids[pair_id(i)] && k == twin(i)) mask &= 1 << (1 - b[j][k]);
                }
            }
            if (!mask) return false;
            if (mask == 1) {
                b[i][j] = b[j][i] = 0;
            } else {
                signature.push_back(mask);
                if (fixture) signature.push_back(j);
                groups[signature].push_back(j);
            }
        }
        std::vector<Cell> cells;
        for (const auto& [key, labels] : groups)
            cells.push_back({std::vector<int>(key.begin(), key.begin() + 1 + depth), labels, key[1 + depth]});
        auto score = [&](const Cell& c) {
            int weight = 0;
            for (int z = 1; z <= depth; ++z)
                if (c.column[z]) weight += 30 / (1 + target[z]);
            return weight;
        };
        std::sort(cells.begin(), cells.end(), [&](const Cell& a, const Cell& b) {
            return score(a) > score(b);
        });

        std::vector<Row> suffix(cells.size() + 1), largest(cells.size() + 1);
        for (int t = int(cells.size()) - 1; t >= 0; --t) {
            const Cell& c = cells[t];
            for (int z = 0; z <= depth; ++z) {
                suffix[t][z] = suffix[t + 1][z] + c.column[z] * int(c.labels.size())
                             * ((c.mask & 4) ? 2 : 1);
                largest[t][z] = std::max(largest[t + 1][z], c.column[z]);
            }
        }

        auto assign = [&](auto&& self, std::size_t t, int ones, int twos) -> bool {
            if (t == cells.size()) {
                if (ones || twos || std::any_of(target.begin(), target.end(),
                                                [](int n) { return n != 0; })) return false;
                Bounds& next = levels[depth + 1];
                next = bounds;
                for (int j = p.fixed; j < p.n; j += 2)
                    if (grids[pair_id(j)] && !(supports[i] & supports[j])
                        && b[i][j] + b[i][j + 1] != 1) return false;
                if (!eliminate(next, i, depth + 1)) return false;
                ++depth;
                bool found = complete(next);
                --depth;
                return found;
            }
            const Cell& c = cells[t];
            int n = int(c.labels.size());
            for (int two = 0; two <= std::min(n, (c.mask & 4) ? twos : 0); ++two) {
                for (int one = 0; one <= std::min(n - two, (c.mask & 2) ? ones : 0); ++one) {
                    if (n - one - two > 0 && !(c.mask & 1)) continue;
                    int amount = one + 2 * two, left = ones + 2 * twos - amount;
                    bool valid = true;
                    for (int z = 0; z <= depth; ++z) {
                        int needed = target[z] - amount * c.column[z];
                        if (needed < 0 || needed > suffix[t + 1][z]
                            || needed > largest[t + 1][z] * left) {
                            valid = false;
                            break;
                        }
                    }
                    if (!valid) continue;
                    for (int z = 0; z <= depth; ++z) target[z] -= amount * c.column[z];
                    for (int v = 0; v < n; ++v) {
                        int j = c.labels[v];
                        b[i][j] = b[j][i] = (v < two) ? 2 : int(v < two + one);
                    }
                    if (self(self, t + 1, ones - one, twos - two)) return true;
                    for (int z = 0; z <= depth; ++z) target[z] += amount * c.column[z];
                }
            }
            return false;
        };
        return assign(assign, 0, singles, doubles);
    }
};
} // namespace


int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "usage: search GRID_EDGE_MASK | --golay-test\n";
        return 2;
    }
    if (std::string(argv[1]) == "--golay-test") {
        Search<121> search(golay);
        search.fixture = true;
        for (int i = 11; i < 121; ++i) {
            for (int j = 11; j < 121; ++j) {
                int v;
                if (!(std::cin >> v) || v < 0 || v > 2) return 2;
                if (i < 107 || j < 107) search.given[i][j] = v;
            }
        }
        if (!search.run()) throw std::logic_error("missing positive control");
        std::cout << "Golay completion found\n";
        return 0;
    }
    int mask = std::stoi(argv[1]);
    if (mask < 0 || mask >= (1 << 21)) return 2;
    Search<49> search(conway);
    for (int i = 0; i < 21; ++i) search.grids[i] = (mask >> i) & 1;
    if (search.run()) {
        std::cout << "unsigned completion\n";
        for (const auto& row : search.b) {
            for (int value : row) std::cout << value << ' ';
            std::cout << '\n';
        }
        return 1;
    }
    std::cout << mask << " exhausted " << search.nodes << '\n';
}
