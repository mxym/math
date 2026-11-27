#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

constexpr int n=11,N=3628800;
using P=std::array<int,n>;
int D[n][n];

void automorphisms(int depth,P& dst,unsigned used,std::vector<P>& G){
    std::array<int,n> left{},right{};
    for(int a=0;a<n;++a)for(int i=0;i<depth;++i){
        left[a]=2*left[a]+D[i][a];
        right[a]=2*right[a]+D[dst[i]][a];
    }
    std::sort(left.begin(),left.end());std::sort(right.begin(),right.end());
    if(left!=right)return;
    if(depth==n){G.push_back(dst);return;}
    for(int j=0;j<n;++j)if(!(used&(1U<<j))){
        dst[depth]=j;automorphisms(depth+1,dst,used|(1U<<j),G);
    }
}
int inv_rank(const P& w){
    P inv{};for(int i=1;i<n;++i)inv[w[i]]=i;
    int r=0;
    for(int a=1;a<n;++a){
        int lower=0;
        for(int c=a+1;c<n;++c)lower+=inv[c]<inv[a];
        r=(n-a)*r+lower;
    }
    return r;
}
int ternary_card(const P& w){
    std::array<int,n*n> values{};
    int j=0;
    for(int a=0;a<n;++a)for(int b=0;b<n;++b){
        int v=0;
        for(int k=0;k<n;++k)v=3*v+D[k][a]+D[w[k]][b];
        values[j++]=v;
    }
    std::sort(values.begin(),values.end());
    return std::unique(values.begin(),values.end())-values.begin();
}
int main(){
    for(int k=0;k<n;++k)for(int a=0;a<n;++a){
        for(int z=1;z<n;++z)
            if((k-a+n)%n==(z*z)%n)D[k][a]=1;
    }
    std::vector<P> G;P w{};automorphisms(0,w,0,G);
    assert(G.size()==660);
    std::vector<P> G0;for(P v:G)if(v[0]==0)G0.push_back(v);
    assert(G0.size()==60);
    std::vector<uint8_t> flag(N,0);
    std::array<int,122> hist{},cosets{};
    P inverse{};std::iota(inverse.begin(),inverse.end(),0);
    int ord=0;
    do{
        if(flag[ord]==0){
            P v{};for(int i=1;i<n;++i)v[inverse[i]]=i;
            assert(inv_rank(v)==ord);
            int c=ternary_card(v);
            ++cosets[c];
            for(const auto& h:G){
                P vh{};for(int k=0;k<n;++k)vh[k]=v[h[k]];
                for(const auto& g:G0){
                    P p{};
                    int off=g[vh[0]];
                    for(int k=1;k<n;++k)p[k]=(g[vh[k]]-off+n)%n;
                    int r=inv_rank(p);
                    assert(r>=ord && r<N);
                    if(!flag[r]){flag[r]=1;++hist[c];}
                }
            }
        }
        ++ord;
    }while(std::next_permutation(inverse.begin()+1,inverse.end()));
    assert(ord==N && std::accumulate(hist.begin(),hist.end(),0)==N);
    std::cout<<"independent incidence-automorphism enumeration: "<<G.size()
             <<" design automorphisms, "<<G0.size()<<" fixing 0\n";
    std::cout<<"classified "<<N<<" normalized permutations in "
             <<std::accumulate(cosets.begin(),cosets.end(),0)<<" double cosets\n";
    std::cout<<"cardinality full-group-orbits population-after-restoring-translations\n";
    for(int c=0;c<=121;++c)if(hist[c])
        std::cout<<c<<" "<<cosets[c]<<" "<<n*hist[c]<<"\n";
}
