#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
using Perm=std::array<int,11>;
constexpr int p=11, F=39916800;
constexpr std::array<int,11> fd={3628800,362880,40320,5040,720,120,24,6,2,1,1};
int rank(const Perm& v){
    unsigned unused=(1U<<p)-1;int code=0;
    for(int i=0;i<p;++i){
        unsigned x=1U<<v[i];
        code+=__builtin_popcount(unused & (x-1))*fd[i];
        unused^=x;
    }
    return code;
}
int card(const Perm& v, const std::array<unsigned,p>& A){
    std::array<unsigned,p> B={};
    for(int k=0;k<p;++k)for(int j=0;j<p;++j)
        if(A[j] & (1U<<v[k]))B[j]|=(1U<<k);
    std::array<unsigned,p*p> sig{};
    int idx=0;
    for(unsigned a:A)for(unsigned b:B)
        sig[idx++]=(a^b)|((a&b)<<p);
    std::sort(sig.begin(),sig.end());
    return std::unique(sig.begin(),sig.end())-sig.begin();
}
int main(){
    bool qr[p]={};for(int i=1;i<p;++i)qr[i*i%p]=true;
    std::vector<Perm> G;
    std::array<unsigned,p> A={};
    for(int i=1;i<p;++i)if(qr[i])for(int t=0;t<p;++t){
        Perm g{};
        for(int k=0;k<p;++k)g[k]=(i*k+t)%p;
        G.push_back(g);
    }
    assert(G.size()==55);
    for(int a=0;a<p;++a)for(int k=0;k<p;++k)
        if(qr[(k-a+p)%p])A[a]|=1U<<k;
    std::vector<bool> seen(F,false);
    std::array<int,122> orbits{}, population{};
    std::array<Perm,122> witness{};
    Perm v{};std::iota(v.begin(),v.end(),0);
    int idx=0, orbit_total=0, covered=0;
    do{
        if(!seen[idx]){
            assert(rank(v)==idx);
            int c=card(v,A), size=0;
            if(orbits[c]++==0)witness[c]=v;
            ++orbit_total;
            for(const Perm& h:G){
                Perm vh{};for(int k=0;k<p;++k)vh[k]=v[h[k]];
                for(const Perm& g:G){
                    Perm w{};for(int k=0;k<p;++k)w[k]=g[vh[k]];
                    int r=rank(w);
                    assert(r>=idx && r<F);
                    if(!seen[r]){++size;seen[r]=true;}
                }
            }
            assert(size && (55*55)%size==0);
            population[c]+=size;
            covered+=size;
        }
        ++idx;
    }while(std::next_permutation(v.begin(),v.end()));
    assert(idx==F && covered==F);
    assert(std::all_of(seen.begin(),seen.end(),[](bool s){return s;}));
    std::cout<<"classified "<<covered<<" coordinate permutations in "<<orbit_total<<" double cosets\n";
    std::cout<<"cardinality orbits permutations lexicographically-first-sigma\n";
    for(int c=0;c<=121;++c)if(orbits[c]){
        std::cout<<c<<" "<<orbits[c]<<" "<<population[c]<<" [";
        for(int k=0;k<p;++k)std::cout<<(k?",":"")<<witness[c][k];
        std::cout<<"]\n";
    }
}
