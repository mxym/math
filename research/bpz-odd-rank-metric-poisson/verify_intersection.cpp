// Independent check using carryless multiplication and W ∩ cW = {0}.
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <algorithm>
using triple=std::array<unsigned,3>;
unsigned mul(unsigned x,unsigned y,unsigned Q,unsigned M) {
    unsigned z=0;
    while(y) {
        if(y&1) z^=x;
        y>>=1;
        x<<=1;
        if(x&Q) x^=M;
    }
    return z;
}
uint64_t pack(triple v,int m) {return uint64_t(v[0])^(uint64_t(v[1])<<m)^(uint64_t(v[2])<<(2*m));}
bool add(std::vector<uint64_t>& p,uint64_t v) {
    for(int i=int(p.size())-1;i>=0;--i) if((v>>i)&1) {
        if(p[i]) v^=p[i];
        else {p[i]=v; return true;}
    }
    return false;
}
int main() {
    std::ifstream in("WITNESSES.txt");
    assert(in.good());
    std::string line;
    int cases=0;
    while(std::getline(in,line)) {
        if(line.empty()||line[0]=='#') continue;
        std::istringstream row(line);
        int m;unsigned M;
        assert(row>>m>>M);
        unsigned Q=1u<<m, z=1;
        for(unsigned i=1;i<Q-1;++i) {
            z=mul(z,2,Q,M);
            assert(z!=0 && z!=1);
        }
        assert(mul(z,2,Q,M)==1);
        std::vector<triple> c(m+3);
        for(auto& v:c) {
            assert(in>>v[0]>>v[1]>>v[2]);
            for(auto a:v) assert(a<Q);
        }
        std::getline(in,line);
        std::vector<uint64_t> base(3*m);
        for(auto v:c) assert(add(base,pack(v,m)));
        for(unsigned l=2;l<Q;++l) {
            auto p=base;
            for(auto v:c) {
                for(auto& a:v) a=mul(a,l,Q,M);
                assert(add(p,pack(v,m)));
            }
        }
        ++cases;
        std::cout<<"m="<<m<<": independent carryless rank test for all "<<Q-2
                 <<" scalars outside GF(2), rank "<<2*(m+3)<<" PASS\n";
    }
    assert(cases==3);
    std::cout<<"PASS independent intersection checks\n";
}
