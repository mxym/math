#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

using u64=std::uint64_t;
using i64=std::int64_t;

u64 multiply(u64 a,u64 b,u64 p,u64 q) {
    u64 out=0;
    while(b) {
        if(b&1)out^=a;
        b>>=1;
        a<<=1;
        if(a&q)a^=p;
    }
    return out;
}

u64 power(u64 a,u64 n,u64 p,u64 q) {
    u64 out=1;
    for(;n;n>>=1,a=multiply(a,a,p,q))if(n&1)out=multiply(out,a,p,q);
    return out;
}

std::vector<u64> primes(u64 n) {
    std::vector<u64> out;
    for(u64 d=2;d*d<=n;d++) if(n%d==0) {
        out.push_back(d);
        do{n/=d;}while(n%d==0);
    }
    if(n>1)out.push_back(n);
    return out;
}

u64 modulus(int n,int which=0) {
    u64 q=u64(1)<<n;
    if(n==1)return 3;
    auto fs=primes(q-1);
    for(u64 p=q+1;p<2*q;p+=2) {
        if(power(2,q-1,p,q)!=1)continue;
        bool ok=true;
        for(auto d:fs)if(power(2,(q-1)/d,p,q)==1){ok=false;break;}
        if(ok&&which--==0)return p;
    }
    return 0;
}

struct Value {
    u64 word=0,step=0;
    Value operator^(const Value& b) const {return {word^b.word,step^b.step};}
};

struct Block {
    std::array<std::array<Value,256>,5> T{};
    int chunks;
    Block(int n,u64 p,u64 a,u64 trace_mask):chunks((n+7)/8) {
        u64 q=u64(1)<<n;
        std::array<Value,40> basis{};
        for(int i=0;i<n;i++) {
            u64 s=u64(1)<<i,w=0;
            for(int j=0;j<64;j++) {
                w|=u64(std::popcount(s&trace_mask)&1)<<j;
                s=multiply(s,a,p,q);
            }
            basis[i]={w,s};
        }
        for(int i=0;i<chunks;i++)
            for(int j=1;j<256;j++) {
                int k=std::countr_zero(unsigned(j));
                T[i][j]=T[i][j^(1<<k)]^basis[8*i+k];
            }
    }
    Value get(u64 q) const {
        Value a=T[0][q&255];
        if(chunks>=2)a=a^T[1][(q>>8)&255];
        if(chunks>=3)a=a^T[2][(q>>16)&255];
        if(chunks>=4)a=a^T[3][(q>>24)&255];
        if(chunks>=5)a=a^T[4][q>>32];
        return a;
    }
};

u64 trace_mask(int n,u64 p,u64 q) {
    u64 tr=0;
    for(int i=0;i<n;i++) {
        u64 v=u64(1)<<i,t=0;
        for(int j=0;j<n;j++,v=multiply(v,v,p,q))t^=v;
        if(t>1)std::abort();
        tr|=t<<i;
    }
    return tr;
}

i64 count(int n,int k,u64 p) {
    u64 q=u64(1)<<n,L=q-1,g=n==1?1:2,tr=trace_mask(n,p,q);
    Block a(n,p,power(g,(u64(1)<<k)+1,p,q),tr);
    Block b(n,p,power(g,L-1,p,q),tr);
    u64 x=1,y=1,neg=0;
    for(u64 i=0;i<L/64;i++) {
        auto A=a.get(x),B=b.get(y);
        neg+=std::popcount(A.word^B.word);
        x=A.step;y=B.step;
    }
    if(auto rem=L%64)neg+=std::popcount((a.get(x).word^b.get(y).word)&((u64(1)<<rem)-1));
    return i64(L)-2*i64(neg);
}

int main(int argc,char** argv) {
    int ki=argc>1?std::stoi(argv[1]):6, start=argc>2?std::stoi(argv[2]):1;
    int end=argc>3?std::stoi(argv[3]):((1<<(ki-1))+1);
    if(ki<1||ki>6||start<1||end>33||end<start)std::abort();
    for(int n=start;n<=end;n++) {
        auto p=modulus(n);
        if(!p)std::abort();
        std::cout<<ki<<" "<<n<<" "<<p<<" "<<count(n,ki,p)<<std::endl;
    }
}
