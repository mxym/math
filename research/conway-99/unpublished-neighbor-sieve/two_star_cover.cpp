// Verify the supplied subset by inspecting all stars rooted at every omitted row.
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <unordered_set>
#include <vector>

using Mask = uint32_t;
using Graph = std::array<Mask,28>;
using Edge = std::array<int,2>;

struct Seed {
    int selected;
    std::array<int,4> support;
    std::array<Edge,8> row;
};

struct Flags {
    int cost = 0;
    bool covered = false;
};

static int pair_index[12][12];

static Mask bit(int i) { return Mask{1} << i; }

static int first(Mask x) {
    assert(x);
    return std::countr_zero(x);
}

static void join(Graph& graph, int i, int j) {
    graph[i] |= bit(j);
    graph[j] |= bit(i);
}

static bool pair_bounds(const Graph& graph) {
    for (int i=0; i<28; ++i)
        for (int j=0; j<i; ++j)
            if (std::popcount(graph[i] & graph[j]) + bool(graph[i] & bit(j)) > 2)
                return false;
    return true;
}

static uint64_t row_bit(int a, int b) {
    assert(a != b && (a ^ 1) != b);
    return uint64_t{1} << pair_index[a][b];
}

static std::unordered_set<uint64_t> labeled_cover(const std::vector<Seed>& seeds) {
    std::unordered_set<uint64_t> result;
    std::array<int,4> axes{2,3,4,5};
    do {
        for (int reverse=0; reverse<2; ++reverse) {
            for (int signs=0; signs<16; ++signs) {
                std::array<int,12> map{};
                for (int i=0; i<4; ++i) map[i] = i ^ (2*reverse);
                for (int i=4; i<12; ++i) {
                    int axis = (i-4)/2;
                    map[i] = 2*axes[axis] + ((i&1) ^ ((signs>>axis)&1));
                }
                for (const auto& seed : seeds) {
                    if (!seed.selected) continue;
                    uint64_t key = 0;
                    for (auto [a,b] : seed.row) key |= row_bit(map[a],map[b]);
                    result.insert(key);
                }
            }
        }
    } while (std::next_permutation(axes.begin(), axes.end()));
    return result;
}

// Analyze the five triangles through p which are completely nonadjacent to y.
static Flags flags(const Graph& graph, int p, int y, const std::unordered_set<uint64_t>& cover) {
    Flags result;
    Mask common = graph[p] & graph[y];
    assert(std::popcount(common) == 2);
    int a = first(common), b = first(common & (common-1));
    Mask ordinary = graph[p] & ~(common | graph[a] | graph[b]);
    for (Mask choices=ordinary; choices;) {
        int q = first(choices), r = first(graph[q] & graph[p]);
        Mask parents = bit(q) | bit(r);
        choices &= ~parents;
        Mask wing = graph[p] & ~parents;
        Mask extra = (graph[q] | graph[r]) & graph[y];
        assert(std::popcount(extra) == 4 && !(extra & common));
        Mask six = common | extra, used_labels = 0;
        int edge_count_twice = 0;
        for (Mask z=six; z; z &= z-1) edge_count_twice += std::popcount(graph[first(z)] & six);
        for (Mask z=extra; z; z &= z-1) used_labels |= graph[first(z)] & wing;
        int cost = edge_count_twice/2 + 4 - std::popcount(used_labels);
        result.cost += cost;
        if (cost || result.covered) continue;

        std::array<int,28> label{};
        label[a] = 0; label[first(graph[a]&wing)] = 1;
        label[b] = 2; label[first(graph[b]&wing)] = 3;
        Mask rest = ordinary & ~parents;
        for (int i=4; rest; i+=2) {
            int u=first(rest), v=first(graph[u]&wing);
            label[u]=i; label[v]=i+1;
            rest &= ~(bit(u) | bit(v));
        }
        uint64_t key = 0;
        for (Mask z=graph[y]&~six; z; z &= z-1) {
            Mask two = graph[first(z)] & wing;
            assert(std::popcount(two) == 2);
            key |= row_bit(label[first(two)],label[first(two&(two-1))]);
        }
        result.covered = cover.contains(key);
    }
    return result;
}

// Compute the two types of marked paths directly in the bipartite cross graph.
static int path_cost(const Graph& graph, int p, int y) {
    Mask common = graph[p] & graph[y];
    int a=first(common), b=first(common & (common-1));
    Mask x=graph[p]&~common, z=graph[y]&~common;
    Mask marks_x=x&(graph[a]|graph[b]), marks_z=z&(graph[a]|graph[b]);
    assert(std::popcount(marks_x)==2 && std::popcount(marks_z)==2);
    int i=first(marks_x), j=first(marks_x&(marks_x-1));
    int k=first(marks_z), l=first(marks_z&(marks_z-1));
    int h=std::popcount(graph[i]&marks_z)+std::popcount(graph[j]&marks_z);
    int paths=std::popcount(graph[i]&graph[j]&z)+std::popcount(graph[k]&graph[l]&x);
    return 4*h+2*paths;
}

static bool covered_seed(const Seed& seed, const std::unordered_set<uint64_t>& cover) {
    // Parents 0,1,2. First wing 3..14. Four extra contacts 15..18.
    // Root 19. Its eight exterior neighbors 20..27.
    Graph base{};
    join(base,0,1); join(base,0,2); join(base,1,2);
    for (int i=0; i<12; ++i) {
        join(base,0,3+i);
        join(base,3+i,3+(i^1));
    }
    join(base,19,3); join(base,19,5);
    for (int i=0; i<4; ++i) {
        join(base,19,15+i);
        join(base,15+i,3+seed.support[i]);
    }
    std::vector<int> free;
    for (int i=0; i<8; ++i) {
        auto [a,b]=seed.row[i];
        join(base,19,20+i); join(base,20+i,3+a); join(base,20+i,3+b);
        if (a!=0 && a!=2 && b!=2) free.push_back(20+i);
    }
    assert(free.size() == 6);
    for (int second=1; second<4; ++second) {
        Graph split=base;
        for (int i=0; i<4; ++i) join(split,i==0 || i==second ? 1 : 2,15+i);
        do {
            if (free[4] > free[5]) continue;
            Graph chart=split;
            for (int i=0; i<4; ++i) join(chart,15+i,free[i]);
            join(chart,free[4],free[5]);
            if (!pair_bounds(chart)) continue;
            int extra=path_cost(chart,0,19);
            auto left=flags(chart,0,19,cover);
            if (left.covered || extra+left.cost>8) continue;
            auto right=flags(chart,19,0,cover);
            if (!right.covered && extra+left.cost+right.cost<=8) return false;
        } while (std::next_permutation(free.begin(),free.end()));
    }
    return true;
}

int main() {
    int pairs=0;
    for (int a=0; a<12; ++a)
        for (int b=a+1; b<12; ++b)
            if ((a^1)!=b) pair_index[a][b]=pair_index[b][a]=pairs++;
    assert(pairs == 60);
    std::vector<Seed> seeds;
    for (Seed seed; std::cin >> seed.selected;) {
        for (int& i : seed.support) std::cin >> i;
        for (auto& [a,b] : seed.row) std::cin >> a >> b;
        assert(std::cin && (seed.selected==0 || seed.selected==1));
        seeds.push_back(seed);
    }
    assert(seeds.size()==6727);
    auto cover=labeled_cover(seeds);
    int omitted=0;
    for (const auto& seed : seeds) {
        if (seed.selected) continue;
        if (!covered_seed(seed,cover)) return 1;
        ++omitted;
    }
    assert(omitted == 3260);
    std::cout << "Verified all 3260 omitted cases against the 3467 allowed starting rows.\n";
}
