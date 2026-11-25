// Exact C++17 certificates for scalar realizations of K_4, K_5, K_6.
// Run: c++ -std=c++17 -O3 ep817-clique-projection.cpp -o cert && ./cert
#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <set>
#include <unordered_set>
#include <vector>

using Z = long long;
template<int N> using V = std::array<int,N-1>;
template<int N>
std::array<int,7> check() {
    const int m=N-1, base=4096;
    using T=V<N>;
    auto add=[&](T a,T b){for(int i=0;i<m;i++) a[i]+=b[i]; return a;};
    auto diff=[&](T a,T b){for(int i=0;i<m;i++) a[i]-=b[i]; return a;};
    auto positive=[&](T a){return *std::min_element(a.begin(),a.end())>=0 &&
                                *std::max_element(a.begin(),a.end())>0;};
    std::vector<T> E;
    for(int i=0;i<N;i++) for(int j=i+1;j<N;j++) {
        T a{}; for(int t=i;t<j;t++) a[t]=1;
        E.push_back(a);
    }
    std::set<T> HH{T{}};
    for(T a:E) {
        auto old=HH;
        for(T h:old) HH.insert(add(h,a));
    }
    std::vector<T> H(HH.begin(),HH.end());
    std::set<T> R, R_all;
    for(int i=0;i<(int)H.size();i++) for(int j=0;j<i;j++) {
        T d=diff(H[i],H[j]); // first nonzero coordinate positive (lex order)
        R_all.insert(d);
        if(positive(d)) continue;
        int g=0; for(int x:d) g=std::gcd(g,std::abs(x));
        for(int& x:d) x/=g;
        R.insert(d);
    }
    std::array<int,7> counts{(int)H.size(),(int)R.size(),0,0,0,(int)R_all.size(),0};
    for(T d:R) {
        int j=std::find_if(d.begin(),d.end(),[](int x){return x!=0;})-d.begin();
        auto Q=[&](T a) {
            Z u=0; for(int i=0;i<m;i++) if(i!=j) u=u*base+a[i]*d[j]-a[j]*d[i];
            return u;
        };
        // In Q, |coordinate| <= 162 for H or edges; and <= (2N-1)*162
        // for a+N*(b-a). Comparison with another vector therefore has
        // per-coordinate difference <=2*N*162<=1944<4096. Reduction mod
        // 4096, then induction, proves the code cannot alias in any check.
        std::set<Z> qe; for(T e:E) qe.insert(Q(e));
        if(qe.size()!=E.size()) { ++counts[2]; continue; }
        std::vector<Z> q; for(T h:H) q.push_back(Q(h));
        std::unordered_set<Z> qs(q.begin(),q.end());
        auto match=[&](Z a,Z d) {
            if(!qs.count(a+N*d)) return false;
            for(int k=2;k<N;k++) if(!qs.count(a+k*d)) return false;
            return true;
        };
        bool hit=false;
        for(size_t i=1;i<q.size();i++) // H[i] nonzero and >=0 in each coordinate
            if(match(0,q[i])) { hit=true; break; }
        if(hit) { ++counts[3]; continue; }
        for(size_t i=0;i<q.size()&&!hit;i++) for(size_t j=i+1;j<q.size();j++) {
            if(!qs.count(N*q[j]-(N-1)*q[i])) continue;
            if(positive(diff(H[j],H[i]))&&match(q[i],q[j]-q[i])) {hit=true;break;}
        }
        if(!hit) { std::cerr<<"No projection witness for";for(int x:d)std::cerr<<" "<<x;std::cerr<<"\n";std::exit(1); }
        ++counts[4];
    }
    auto enc=[&](T a){ Z u=0;for(int x:a)u=u*base+x;return u; };
    std::vector<Z> ss;
    for(T h:H) ss.push_back(enc(h));
    for(T d:R_all) {
        Z delta=enc(d);
        std::unordered_set<Z> S;
        for(Z a:ss) { S.insert(a); S.insert(a+delta); }
        // The i-th coordinate span of H is (i+1)(N-i-1), the
        // number of edges crossing gap i. Translating by d increases
        // it by |d_i|. Therefore each step coordinate is bounded above
        // by that combined span divided by N.
        std::vector<T> slopes{T{}};
        for(int i=0;i<m;i++) {
            auto old=slopes;
            int mx=((i+1)*(N-i-1)+std::abs(d[i]))/N;
            for(int t=1;t<=mx;t++) for(T a:old) {a[i]=t;slopes.push_back(a);}
        }
        std::sort(slopes.begin(),slopes.end(),[](T a,T b){
            return std::accumulate(a.begin(),a.end(),0)<std::accumulate(b.begin(),b.end(),0);
        });
        bool hit=false;
        for(T D:slopes) if(positive(D)) {
            Z step=enc(D);
            for(Z a:S) {
                if(!S.count(a+N*step)) continue;
                hit=true;
                for(int k=1;k<N;k++) if(!S.count(a+k*step)){hit=false;break;}
                if(hit)break;
            }
            if(hit)break;
        }
        if(!hit) ++counts[6];
    }
    return counts;
}
int main(){
    auto print=[](int N,std::array<int,7> C) {
        std::cout<<N<<":"; for(int x:C) std::cout<<" "<<x; std::cout<<std::endl;
    };
    auto c4=check<4>();print(4,c4);
    auto c5=check<5>();print(5,c5);
    auto c6=check<6>();print(6,c6);
    if(c4!=std::array<int,7>{38,31,5,26,0,100,0} ||
       c5!=std::array<int,7>{291,666,15,569,82,1540,0} ||
       c6!=std::array<int,7>{2932,17538,35,11429,6074,31341,0})return 1;
}
