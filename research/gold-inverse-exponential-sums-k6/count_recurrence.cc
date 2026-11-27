#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

using U=std::uint64_t;
using H=__uint128_t;

U red(U a,U b) {
    while(a && std::bit_width(a)>=std::bit_width(b))
        a^=b<<(std::bit_width(a)-std::bit_width(b));
    return a;
}

U gcd_poly(U a,U b) {
    while(b) {
        U r=red(a,b);
        a=b; b=r;
    }
    return a;
}

struct Field {
    int n;
    U q,mod;
    U mult(U a,U b) const {
        H z=0;
        if(!a||!b)return 0;
        for(U x=a;x;x&=x-1)z^=H(b)<<std::countr_zero(x);
        for(int j=2*n-2;j>=n;--j)if(z>>j&1)z^=H(mod)<<(j-n);
        return U(z);
    }
    U pow(U a,U e) const {
        U z=1;
        while(e) {
            if(e&1)z=mult(z,a);
            a=mult(a,a);e>>=1;
        }
        return z;
    }
    U tr(U a) const {
        U sum=0;
        for(int j=0;j<n;j++) {
            sum^=a;
            a=mult(a,a);
        }
        if(sum>1)std::abort();
        return sum;
    }
};

std::vector<U> prime_factors(U e) {
    std::vector<U> out;
    for(U d=2;d*d<=e;d+=d==2?1:2)if(e%d==0) {
        out.push_back(d);
        while(e%d==0)e/=d;
    }
    if(e>1)out.push_back(e);
    return out;
}

Field make_field(int n) {
    U q=U(1)<<n;
    if(n==1)return {n,q,3};
    auto nf=prime_factors(n), order_f=prime_factors(q-1);
    for(U p=2*q-1;p>q;p-=2) {
        Field F{n,q,p};
        if(F.pow(2,q)!=2)continue;
        bool ok=true;
        for(auto l:nf)if(gcd_poly(p,F.pow(2,U(1)<<(n/l))^2)!=1){ok=false;break;}
        if(!ok)continue;
        for(auto l:order_f)if(F.pow(2,(q-1)/l)==1){ok=false;break;}
        if(ok)return F;
    }
    std::abort();
}

struct Lfsr {
    int r;
    U mask,init,coeff;
    std::array<std::array<U,256>,5> T{};
    U step(U w) const {
        return (w>>1)|(U(std::popcount(w&coeff)&1)<<(r-1));
    }
    Lfsr(Field F,U a) {
        std::vector<U> p={1};
        U z=a;
        do {
            std::vector<U> pp(p.size()+1);
            for(std::size_t i=0;i<p.size();i++) {
                pp[i]^=F.mult(p[i],z);
                pp[i+1]^=p[i];
            }
            p.swap(pp);
            z=F.mult(z,z);
        }while(z!=a);
        r=int(p.size())-1;
        if(r<1||r>F.n||p.back()!=1)std::abort();
        mask=(U(1)<<r)-1;
        coeff=0; init=0; U v=1,check=0;
        for(int j=0;j<r;j++) {
            if(p[j]>1)std::abort();
            coeff|=p[j]<<j;
            init|=F.tr(v)<<j;
            if(p[j])check^=v;
            v=F.mult(v,a);
        }
        if(check!=v)std::abort();
        // The recurrence follows from p(a)=0; check a deterministic prefix.
        U state=init;v=1;
        for(int j=0;j<2*r+5;j++) {
            if((state&1)!=F.tr(v))std::abort();
            state=step(state);
            v=F.mult(v,a);
        }
        std::array<U,40> basis{};
        for(int i=0;i<r;i++) {
            U s=U(1)<<i,y=0;
            for(int j=0;j<64;j++) {
                y|=(s&1)<<j;
                s=step(s);
            }
            basis[i]=y;
        }
        for(int i=0;i<(r+7)/8;i++)for(unsigned j=1;j<256;j++) {
            int b=std::countr_zero(j);
            T[i][j]=T[i][j^(1u<<b)]^basis[8*i+b];
        }
    }
    U word(U state) const {
        U v=T[0][state&255];
        if(r>8)v^=T[1][(state>>8)&255];
        if(r>16)v^=T[2][(state>>16)&255];
        if(r>24)v^=T[3][(state>>24)&255];
        if(r>32)v^=T[4][state>>32];
        return v;
    }
};

std::int64_t runs(Field F,int k) {
    U g=F.n==1?1:2;
    Lfsr A(F,F.pow(g,(U(1)<<k)+1)),B(F,F.pow(g,F.q-2));
    constexpr int W=31; constexpr U lo=(U(1)<<W)-1;
    U L=F.q-1, x=A.init,y=B.init,bad=0;
    for(U i=0;i<L/W;i++) {
        U a=A.word(x),b=B.word(y);
        bad+=std::popcount((a^b)&lo);
        x=(a>>W)&A.mask;
        y=(b>>W)&B.mask;
    }
    if(auto rem=L%W)bad+=std::popcount((A.word(x)^B.word(y))&((U(1)<<rem)-1));
    return std::int64_t(L)-2*std::int64_t(bad);
}

int main(int argc,char** argv) {
    int k=argc>1?std::stoi(argv[1]):6, start=argc>2?std::stoi(argv[2]):1;
    int end=argc>3?std::stoi(argv[3]):((1<<(k-1))+1);
    if(k<1||k>6||start<1||end>33||end<start)std::abort();
    for(int n=start;n<=end;n++) {
        Field F=make_field(n);
        std::cout<<k<<" "<<n<<" "<<F.mod<<" "<<runs(F,k)<<std::endl;
    }
}
