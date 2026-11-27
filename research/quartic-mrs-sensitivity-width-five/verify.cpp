// Standalone exact verifier. Standard C++17.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <vector>
using Int = std::int16_t;
constexpr int N = 1024;
constexpr Int neg = -30000;
static std::string label(const std::array<int,4>& mask) {
    std::string s;
    for(auto a:mask) s += char('0'+a);
    return s;
}
static void ck(bool ok, const std::string& msg) {
    if (!ok) throw std::runtime_error(msg);
}
static std::pair<int,int> direct(const std::array<int,4>& support, int n) {
    // No derivative formula; build actual distinct monomials, then flip bits.
    std::set<unsigned> orbit;
    for(int j=0; j<n; ++j) {
        unsigned m = 0;
        for(int p:support) m |= 1U << ((p+j)%n);
        orbit.insert(m);
    }
    std::vector<unsigned char> f(1U<<n);
    for(unsigned x=0; x<f.size(); ++x) {
        unsigned y=0;
        for(unsigned m:orbit) y ^= ((x&m)==m);
        f[x]=y;
    }
    int score=0;
    for(unsigned x=0; x<f.size(); ++x) {
        int s=0;
        for(int j=0; j<n; ++j) s += f[x]!=f[x^(1U<<j)];
        score = std::max(score,s);
    }
    return {score, int(orbit.size())};
}
static std::array<Int,2*N> transitions(const std::array<int,4>& S, int p, int q) {
    // Generate each center-containing monomial from the actual offset sets.
    // Then evaluate its truth contribution twice, rather than assigning a
    // derivative monomial rule. Bit 0 is oldest in this implementation.
    std::array<unsigned,4> monomials{};
    for(int k=0;k<4;++k)
        for(int b:S) monomials[k] |= 1U << (5+b-S[k]);
    std::array<Int,2*N> weight{};
    for(unsigned bits=0; bits<2*N; ++bits) {
        unsigned f=0, g=0;
        for(unsigned m:monomials) {
            f ^= (bits&m)==m;
            g ^= ((bits^(1U<<5))&m)==m;
        }
        weight[bits] = Int(q*int(f!=g)-p);
    }
    return weight;
}
static std::vector<int> powers(const std::array<int,4>& S, int p,int q,
                               int t,int period,bool corrupt=false) {
    auto w=transitions(S,p,q);
    if(corrupt) w[0] += 36;                  // force a positive adjusted loop
    std::vector<Int> A(N*N, neg), B(N*N,neg), record;
    for(int j=0; j<N; ++j) A[j*N+j]=0;
    std::vector<int> out{0};
    for(int k=1; k<=t+period; ++k) {
        for(int row=0;row<N;++row) {
            const int off=row*N;
            for(int dst=0;dst<N;++dst) {
                // Window bit 0 is oldest. Dropping it shifts the window right.
                const int wa=2*dst, wb=2*dst+1;
                Int a=A[off+(wa&(N-1))],b=A[off+(wb&(N-1))];
                int va=a==neg?neg:int(a)+w[wa], vb=b==neg?neg:int(b)+w[wb];
                B[off+dst]=Int(std::max(va,vb));
            }
        }
        A.swap(B);
        int m=neg;
        for(int j=0;j<N;++j) m=std::max(m,int(A[j*N+j]));
        ck((m+p*k)%q==0,"normalized diagonal not divisible");
        out.push_back((m+p*k)/q);
        if(k==t) record=A;
        if(k==t+period)
            ck((A==record)!=corrupt,corrupt?"damaged loop accepted":"matrix power mismatch");
    }
    return out;
}
struct Data {
    std::array<int,4> support;
    int p,q,t,P,from;
    bool correction;
    std::vector<int> mods;
    std::array<int,5> small;
    std::array<int,5> orbits;
};
static int formula(const Data& D, int n) {
    if(D.correction) return 22*(n/24)+D.mods.at(n%24);
    return n-D.mods.at(n%D.P);
}
static void print(const std::vector<int>& a) {
    std::cout << "[";
    for(unsigned j=0;j<a.size();++j) std::cout << (j?",":"") << a[j];
    std::cout << "]";
}
int main() {
    try {
        const std::array<Data,4> examples{{
            {{0,1,2,5},1,1,75,6,35,false,{0,3,2,3,3,2},{6,4,7,8,8},{6,7,8,9,10}},
            {{0,1,3,5},1,1,40,6,11,false,{0,1,1,2,2,2},{6,6,7,8,8},{6,7,8,9,10}},
            {{0,1,4,5},1,1,72,66,11,false,{0,3,2,3,2,1,0,1,2,3,2,1,0,2,2,1,2,1,0,3,2,3,0,1,0,3,2,3,2,1,0,3,2,3,2,1,0,1,2,1,2,1,0,3,0,3,2,1,0,3,2,1,2,1,0,3,2,2,2,1,0,1,2,3,2,1},{6,6,6,6,8},{6,7,4,9,10}},
            {{0,2,3,5},11,12,42,24,17,true,{0,0,0,2,2,4,4,6,6,8,8,10,10,10,12,12,14,14,16,16,18,18,20,20},{4,6,6,8,8},{3,7,8,9,10}}
        }};
        for(const auto& d:examples) {
            const auto s=label(d.support);
            const auto vals=powers(d.support,d.p,d.q,d.t,d.P);
            std::vector<int> tail;
            for(int i=0;i<d.P;++i) tail.push_back(d.q*formula(d,i)-d.p*i);
            for(int m=1;m<d.P;++m) if(d.P%m==0) {
                bool repeats=true;
                for(int i=m;i<d.P;++i) repeats &= tail[i]==tail[i%m];
                ck(!repeats,s+" has a smaller residual period");
            }
            ck(int(d.mods.size())==d.P,"invalid fingerprint");
            for(int n=d.from; n<=d.t+d.P;++n)
                ck(vals.at(n)==formula(d,n),s+" mismatch at n="+std::to_string(n));
            std::cout << s << ": full " << N*N << " matrix entries C^"
                      << d.t << "=C^" << d.t+d.P<<" PASS; ";
            if(d.correction) std::cout<<"s=22*floor(n/24)+e[n mod 24], e=";
            else std::cout<<"s=n-d[n mod "<<d.P<<"], d=";
            print(d.mods);
            std::cout<<" for n>="<<(s=="0145"?6:(s=="0135"?10:d.from))
                     <<"; least normalized tail period "<<d.P<<"\n";
            std::vector<int> carry, low;
            for(int n=11;n<d.from;++n) carry.push_back(vals.at(n));
            if(!carry.empty()) {
                std::cout << s << ": s(n) for n=11.."<<d.from-1<<" = ";
                print(carry);
                std::cout<<"\n";
            }
            for(int n=6; n<=10;++n) {
                auto ans=direct(d.support,n);
                if ((s=="0135" && n==10) || s=="0145")
                    ck(ans.first==formula(d,n),s+" small-length formula extension");
                ck(ans.first==d.small[n-6],s+" distinct small-n sensitivity mismatch");
                ck(ans.second==d.orbits[n-6],s+" distinct small-n orbit mismatch");
                low.push_back(ans.first);
            }
            std::cout << s << ": distinct-orbit s(n) n=6..10 = ";
            print(low);
            std::cout << ", orbit sizes ";
            print(std::vector<int>(d.orbits.begin(),d.orbits.end()));
            std::cout<<"\n";
            for(int n=11;n<=20;++n) {
                auto ans=direct(d.support,n);
                ck(ans.second==n&&ans.first==vals.at(n),s+" independent ANF mismatch");
            }
            std::cout << s << ": direct distinct-ANF optimization n=6..20 PASS.\n";
        }
        auto exceptional=direct({0,2,3,1},4);
        ck(exceptional==std::make_pair(4,1),"exceptional dilation residue");
        std::cout<<"0235 reduced modulo 4: one quartic, s=4, PASS.\n";
        (void)powers(examples[3].support,11,12,42,24,true);
        std::cout<<"Negative control: a corrupted loop breaks the claimed matrix equality, PASS.\n";
    } catch (const std::exception& e) {
        std::cerr<<"FAIL "<<e.what()<<"\n";
        return 1;
    }
}
