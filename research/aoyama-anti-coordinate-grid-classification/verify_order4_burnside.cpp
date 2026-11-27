/* Independent Burnside verification. C++20, no external data. */
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <set>
#include <unordered_set>
#include <vector>

using I = std::uint16_t;
using N = std::uint64_t;
using Part = std::array<I, 4>;
using Perm = std::array<int, 16>;
using Dir = std::array<I, 4>;

static void need(bool b) {
    if (!b) { std::cerr << "validity check failed\n"; std::exit(1); }
}

static int mult(int a, int b) {
    int c=0;
    while (b) {
        if (b&1) c^=a;
        b>>=1; a<<=1;
        if (a&4) a^=7;
    }
    return c;
}

static bool orth(const Part& a, const Part& b) {
    for (I x:a) for (I y:b) if (!std::has_single_bit(I(x&y))) return false;
    return true;
}

static I transport(I m, const Perm& p) {
    I out=0;
    while (m) {
        const auto i=std::countr_zero(m);
        out|=I(1u<<p[i]); m=I(m&(m-1));
    }
    return out;
}

static Part move(const Part& a, const Perm& p) {
    Part b{};
    for (int i=0;i<4;++i) b[i]=transport(a[i],p);
    std::sort(b.begin(),b.end());
    return b;
}

static Perm composition(const Perm& x, const Perm& y) {
    Perm z{};
    for (int i=0;i<16;++i) z[i]=x[y[i]];
    return z;
}

static N code(const Perm& p) {
    N v=0;
    for (int i=0;i<16;++i) v|=N(p[i])<<(i*4);
    return v;
}

static std::vector<Dir> plane() {
    // Generate the five one-dimensional F4 subspaces inside F2^4
    // without using slopes. Their cosets give line-object masks.
    std::set<I> spaces;
    for (int g=1;g<16;++g) {
        I W=0;
        for (int z=0;z<4;++z) W|=I(1u<<(4*mult(g/4,z)+mult(g%4,z)));
        spaces.insert(W);
    }
    need(spaces.size()==5);
    std::vector<Dir> D;
    for (I W:spaces) {
        std::set<I> cls;
        for (int i=0;i<16;++i) {
            I l=0;
            for (int j=0;j<16;++j) if ((W>>j)&1) l|=I(1u<<(i^j));
            cls.insert(l);
        }
        need(cls.size()==4);
        Dir d{}; std::copy(cls.begin(),cls.end(),d.begin()); D.push_back(d);
    }
    return D;
}

static std::vector<I> good_masks(const std::vector<Dir>& D) {
    std::vector<I> B;
    for (unsigned m=0;m<65536;++m) {
        if (std::popcount(m)!=4) continue;
        bool good=true;
        for (const auto& d:D) {
            bool repeat=false;
            for (I l:d) if (std::popcount(unsigned(m&l))>=2) repeat=true;
            if (!repeat) { good=false; break; }
        }
        if (good) B.push_back(I(m));
    }
    return B;
}

static std::vector<Part> all_partitions(const std::vector<I>& B) {
    // Fix the block containing point 0; the next three block masks are
    // in strict numerical order but need not be larger than the first.
    std::vector<Part> V;
    std::array<bool,65536> good{};
    for (I m:B) good[m]=true;
    for (I a:B) if (a&1) {
        for (std::size_t i=0;i<B.size();++i) {
            I b=B[i]; if (a&b) continue;
            for (std::size_t j=i+1;j<B.size();++j) {
                I c=B[j]; if ((a|b)&c) continue;
                I d=I(~(a|b|c));
                if (d<=c || !good[d]) continue;
                Part p{a,b,c,d};
                std::sort(p.begin(),p.end());
                V.push_back(p);
            }
        }
    }
    std::sort(V.begin(),V.end());
    need(std::adjacent_find(V.begin(),V.end())==V.end());
    return V;
}

using Group = std::vector<std::pair<Perm,Perm>>;

static Group collineations() {
    // Enumerate all choices of image of 0 and images A,B of basis directions,
    // and both permutations of the field roots fixing 0 and 1.
    Group G;
    for (int o=0;o<16;++o) for (int A=1;A<16;++A) for (int B=1;B<16;++B) {
        if (mult(A/4,B%4)==mult(B/4,A%4)) continue;
        for (int f=0;f<2;++f) {
            Perm p{},pinv{};
            for (int i=0;i<16;++i) {
                int x=i/4,y=i%4;
                if (f) { x=mult(x,x); y=mult(y,y); }
                p[i]=o^(4*(mult(x,A/4)^mult(y,B/4)))^mult(x,A%4)^mult(y,B%4);
            }
            for (int i=0;i<16;++i) pinv[p[i]]=i;
            G.emplace_back(p,pinv);
        }
    }
    return G;
}

static N all_ordered_pairs(const std::vector<Part>& P,const std::vector<I>& B) {
    // For each row partition independently, collect good transverse blocks.
    // Four such masks partition the points exactly when three disjoint masks
    // have a good transverse complement. Enforce their numerical order.
    std::array<int,65536> stamp{};
    int epoch=0;
    N found=0;
    for (const auto& a:P) {
        ++epoch;
        std::vector<I> X;
        for (I b:B) if (std::all_of(a.begin(),a.end(),[&](I x){
            return std::has_single_bit(I(x&b));})) {
            X.push_back(b); stamp[b]=epoch;
        }
        for (I x:X) if (x&1) {
            for (std::size_t i=0;i<X.size();++i) {
                I y=X[i]; if (x&y) continue;
                for (std::size_t j=i+1;j<X.size();++j) {
                    I z=X[j]; if ((x|y)&z) continue;
                    I w=I(~(x|y|z));
                    if (w>z && stamp[w]==epoch) ++found;
                }
            }
        }
    }
    return found;
}

int main() {
    const auto D=plane();
    const auto B=good_masks(D);
    const auto P=all_partitions(B);
    need(B.size()==720 && P.size()==66960);
    need(!std::binary_search(B.begin(),B.end(),I(15)));
    need(!orth(P.front(),P.front()));
    const auto G=collineations();
    need(G.size()==5760);
    std::unordered_set<N> keys;
    for (const auto& [g,h]:G) keys.insert(code(g));
    need(keys.size()==5760);
    std::set<I> lines;
    for (const auto& d:D) lines.insert(d.begin(),d.end());
    for (const auto& [g,h]:G) for (I m:lines) need(lines.contains(transport(m,g)));

    const N raw=all_ordered_pairs(P,B);
    need(raw==37909440);
    Perm id{};
    for (int i=0;i<16;++i) id[i]=i;
    std::unordered_set<N> seen;
    N rows=0, ord=0, swapped=0, class_count=0;
    for (const auto& [g,gi]:G) {
        if (seen.contains(code(g))) continue;
        ++class_count;
        std::unordered_set<N> cc;
        for (const auto& [h,hi]:G) {
            auto t=code(composition(composition(h,g),hi));
            need(keys.contains(t)); cc.insert(t);
        }
        for (auto t:cc) need(seen.insert(t).second);
        auto gg=composition(g,g);
        std::vector<Part> fixed;
        N s=0;
        for (const auto& p:P) {
            auto u=move(p,g);
            if (u==p) fixed.push_back(p);
            if (move(p,gg)==p && orth(p,u)) ++s;
        }
        N o=0;
        if (g==id) {
            o=raw;
        } else {
            // Order matters: count both orientations of each compatible pair.
            for (std::size_t i=0;i<fixed.size();++i)
                for (std::size_t j=i+1;j<fixed.size();++j)
                    if (orth(fixed[i],fixed[j])) o+=2;
        }
        rows+=N(cc.size())*fixed.size();
        ord+=N(cc.size())*o;
        swapped+=N(cc.size())*s;
    }
    need(seen.size()==G.size());
    need(rows==17*G.size() && ord==6662*G.size() && swapped==80*G.size());
    need((ord+swapped)/(2*G.size())==3371);
    std::cout<<"Good blocks "<<B.size()<<"; partitions "<<P.size()
             <<"; ordered pairs "<<raw<<"\n";
    std::cout<<"Group "<<G.size()<<"; conjugacy classes "<<class_count
             <<"; Burnside sums "<<rows<<","<<ord<<","<<swapped<<"\n";
    std::cout<<"Row orbits 17; ordered orbits 6662; transpose-fixed 80; "
             <<"unoriented 3371\nPASS Burnside census\n";
}
