#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
#ifdef NDEBUG
#error Do not build with NDEBUG
#endif

struct GF {
    unsigned k, n, N, red;
    GF(unsigned k_, unsigned p) : k(k_), n(3*k), N(1U << n), red(p) {
        assert(deg(p) == int(n) && (p & 1));
        unsigned z=2;
        for (unsigned i=1;i<=n;++i) {
            z=prod(z,z);
            if (i<=n/2) assert(gcd(z^2,p)==1);
        }
        assert(z==2);
    }
    static int deg(unsigned x) {
        int j=-1;
        while (x) {x>>=1; ++j;}
        return j;
    }
    static unsigned gcd(unsigned a,unsigned b) {
        while(b) {
            while(a && deg(a)>=deg(b)) a^=b<<(deg(a)-deg(b));
            std::swap(a,b);
        }
        return a;
    }
    unsigned prod(unsigned x,unsigned y) const {
        unsigned w=0;
        for (; y; y>>=1) {
            if (y&1) w^=x;
            x<<=1;
            if (x&N) x^=red;
        }
        return w;
    }
    unsigned frob(unsigned x, unsigned j) const {
        while(j--) x=prod(x,x);
        return x;
    }
    unsigned tr(unsigned x) const {
        unsigned v=x;
        for(unsigned i=1;i<n;++i) {x=prod(x,x); v^=x;}
        assert(v<2);
        return v;
    }
};

void run(unsigned k,unsigned red) {
    GF f(k,red);
    const unsigned N=f.N;
    std::vector<unsigned> tr(N), tau(N), q(N), sq(N), rt(N), phi(N), psi(N), mutant(N);
    std::vector<unsigned> base, ker;
    for(unsigned i=0;i<N;++i) {
        q[i]=f.frob(i,k);
        tr[i]=f.tr(i);
        sq[i]=f.prod(i,i);
        rt[sq[i]]=i;
    }
    for(unsigned i=0;i<N;++i) {
        tau[i]=i^q[i]^q[q[i]];
        if(i==q[i]) base.push_back(i);
        if(tau[i]==0) ker.push_back(i);
        phi[i]=f.prod(i,q[i]);
        psi[i]=i ^ phi[i] ^ f.prod(i,q[q[i]]);
        mutant[i]=i ^ phi[i] ^ f.prod(q[i],q[q[i]]);
    }
    assert(base.size()==1U<<k && ker.size()==1U<<(2*k));
    std::vector<std::vector<unsigned>> inv(N);
    for(unsigned c:base) {
        auto &v=inv[c];
        v.assign(N,N);
        for(unsigned x:ker) {
            const unsigned e=rt[x]^f.prod(c,x);
            assert(tau[e]==0 && v[e]==N);
            v[e]=x;
        }
    }

    const std::size_t count = std::size_t(N)*N;
    std::vector<int> data(count);
    std::size_t wrong=0;
    for(unsigned y=0;y<N;++y) {
        const unsigned t=tau[y], v=y^t;
        for(unsigned x=0;x<N;++x) {
            const unsigned s=tau[x], u=x^s;
            const unsigned a=tr[phi[y]^f.prod(y,psi[x])];
            const unsigned b=tr[f.prod(t,s^1)^f.prod(u,rt[v]^f.prod(s^1,v))^phi[v]];
            assert(a==b);
            if(k==1) wrong+=a!=tr[phi[y]^f.prod(y,mutant[x])];
            data[x+std::size_t(N)*y]=1-2*int(a);
        }
    }
    if(k==1) assert(wrong>0);

    // Recursive butterflies in decreasing block size, with ordinary bit indices.
    for(std::size_t half=count/2;half;half/=2)
        for(std::size_t i=0;i<count;i+=2*half)
            for(std::size_t j=i;j<i+half;++j) {
                const int a=data[j], b=data[j+half];
                data[j]=a+b;
                data[j+half]=a-b;
            }

    std::vector<unsigned> mask(N);
    std::vector<bool> seen(N,false);
    for (unsigned a=0;a<N;++a) {
        unsigned x=0;
        for(unsigned i=0;i<f.n;++i) x|=tr[f.prod(a,1U<<i)]<<i;
        assert(!seen[x]);
        seen[x]=true;
        mask[a]=x;
    }
    std::size_t pos=0, neg=0;
    for(unsigned d=0;d<N;++d) {
        const unsigned D=tau[d];
        for(unsigned a=0;a<N;++a) {
            const unsigned A=tau[a], v=inv[D][a^A];
            assert(v<N);
            const unsigned b=tr[f.prod(A,D^1)^phi[v]^f.prod(d^D,v)];
            const int w=data[mask[a]+std::size_t(N)*mask[d]];
            assert(w==int(N)*(1-2*int(b)));
            if(w>0) ++pos; else ++neg;
        }
    }
    assert(pos+neg==count && pos-neg==N);
    std::cout<<"k="<<k<<": all "<<count<<" inputs and Walsh signs PASS; +"
             <<pos<<" / -"<<neg;
    if(k==1)std::cout<<"; "<<wrong<<" changed-exponent mismatches";
    std::cout<<'\n';
}

int main() {
    run(1,0xb);
    run(2,0x43);
    run(3,0x211);
    run(4,0x1053);
}
