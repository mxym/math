// Enumerate transports between five-point fibers on a 3-by-3 rook graph.
// Build as a shared library for verify.py. No third-party C++ dependencies.
#include <algorithm>
#include <array>
#include <cassert>
#include <vector>

namespace {
using Map = int; // x -> shift + (-1)^reflection x on Z/5
using Grid = std::array<std::array<Map,9>,9>;
using Perm = std::array<int,9>;
constexpr int lines[6][3] = {{0,1,2},{3,4,5},{6,7,8},{0,3,6},{1,4,7},{2,5,8}};

int image(Map f, int x) { return (f%5 + (f<5 ? x : -x) + 5)%5; }
Map compose(Map f, Map g) { return image(f,g%5) + 5*((f>=5)!=(g>=5)); }
Map inverse(Map f) { return f<5 ? (5-f)%5 : f; }
bool adjacent(int p, int q) { return p!=q && (p/3==q/3 || p%3==q%3); }

void edge(Grid &grid, int p, int q, Map f) {
    grid[p][q] = f;
    grid[q][p] = inverse(f);
}

Grid decode(int key) {
    Grid grid{};
    int free[4], numeral = key%10000;
    for (int i=3; i>=0; --i) {
        free[i] = numeral%10;
        numeral /= 10;
    }
    for (int k=0; k<6; ++k) {
        auto [p,q,r] = lines[k];
        Map x = k<4 ? 0 : free[2*(k-4)];
        Map y = k<4 ? 0 : free[2*(k-4)+1];
        Map turn = (key/10000 & (1<<k)) ? 4 : 1;
        edge(grid,p,q,x);
        edge(grid,p,r,y);
        edge(grid,q,r,compose(y,compose(turn,inverse(x))));
    }
    return grid;
}

int normalized(const Grid &grid, const Perm &p, Map initial) {
    Map frame[9];
    frame[0] = initial;
    for (int j : {3,6}) frame[j] = compose(grid[p[0]][p[j]],initial);
    for (int i : {0,3,6}) {
        for (int j : {1,2}) frame[i+j] = compose(grid[p[i]][p[i+j]],frame[i]);
    }
    auto transfer = [&](int i,int j) {
        return compose(inverse(frame[j]),compose(grid[p[i]][p[j]],frame[i]));
    };
    int bits=0, digits=0;
    for (int k=0; k<6; ++k) {
        auto [a,b,c] = lines[k];
        Map x=transfer(a,b), y=transfer(a,c), z=transfer(b,c);
        Map turn=compose(inverse(y),compose(z,x));
        assert(turn==1 || turn==4);
        if (turn==4) bits |= 1<<k;
        if (k>=4) digits=100*digits+10*x+y;
    }
    return bits*10000+digits;
}

struct Choice {
    int pair, tail, head, matched;
};
}

extern "C" int list_charts(int *keys, int *sizes) {
    std::vector<Perm> actions;
    std::array<int,3> rows{0,1,2};
    do {
        std::array<int,3> cols{0,1,2};
        do {
            for (bool transpose : {false,true}) {
                Perm p;
                for (int i=0; i<9; ++i) {
                    int r=rows[i/3], c=cols[i%3];
                    p[i]=transpose ? 3*c+r : 3*r+c;
                }
                actions.push_back(p);
            }
        } while (std::next_permutation(cols.begin(),cols.end()));
    } while (std::next_permutation(rows.begin(),rows.end()));
    std::vector<bool> seen(640000,false);
    int count=0;
    for (int key=0; key<640000; ++key) {
        if (seen[key]) continue;
        Grid grid=decode(key);
        int size=0;
        for (const auto &p : actions) {
            for (Map f=0; f<10; ++f) {
                int n=normalized(grid,p,f);
                assert(key<=n && n<640000);
                if (!seen[n]) { seen[n]=true; ++size; }
            }
        }
        keys[count]=key;
        sizes[count]=size;
        ++count;
    }
    return count;
}

extern "C" int local_words(int key, int center, int orientations, int *output) {
    Grid grid=decode(key);
    int near[4], far[4], n=0, f=0;
    for (int p=0; p<9; ++p) {
        if (p==center) continue;
        if (adjacent(p,center)) near[n++]=p;
        else far[f++]=p;
    }
    int count=0;
    for (int i=0; i<5; ++i) {
        // At the four opposite grid positions record two contacts in different
        // axes. For each contact pair only its head can form an edge with a
        // contact over an adjacent grid position.
        std::array<std::vector<Choice>,4> choices;
        for (int j=0; j<4; ++j) {
            int q=far[j], pair=0;
            for (int a=0; a<5; ++a) {
                for (int b=a+1; b<5; ++b,++pair) {
                    bool forward=(b-a<=2) != bool(orientations & (1<<j));
                    int tail=forward?a:b, head=forward?b:a;
                    int matched=0;
                    bool valid=true;
                    for (int k=0; k<4; ++k) {
                        int p=near[k];
                        if (!adjacent(p,q)) continue;
                        int label=image(grid[p][q],image(grid[center][p],i));
                        if (label==tail) valid=false;
                        if (label==head) matched |= 1<<k;
                    }
                    if (valid && (matched & (matched-1))==0)
                        choices[j].push_back({pair,tail,head,matched});
                }
            }
        }
        Choice selected[4];
        auto visit = [&](auto &self,int j,int used_near,int used_far)->void {
            if (j==4) {
                output[5*count]=i;
                for (int k=0;k<4;++k) output[5*count+1+k]=selected[k].pair;
                ++count;
                return;
            }
            for (const Choice &e : choices[j]) {
                if (used_near & e.matched) continue;
                bool valid=true;
                int occupied=used_far | (e.matched ? 1<<j : 0);
                for (int k=0; k<j; ++k) {
                    if (!adjacent(far[k],far[j])) continue;
                    Map move=grid[far[k]][far[j]];
                    int t=image(move,selected[k].tail), h=image(move,selected[k].head);
                    if (t==e.tail || t==e.head || h==e.tail) { valid=false; break; }
                    if (h==e.head) {
                        int ends=(1<<k)|(1<<j);
                        if (occupied & ends) { valid=false; break; }
                        occupied |= ends;
                    }
                }
                if (!valid) continue;
                selected[j]=e;
                self(self,j+1,used_near|e.matched,occupied);
            }
        };
        visit(visit,0,0,0);
    }
    return count;
}
