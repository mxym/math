// Exact finite checks for Fernando--Kousik Question 6.6 and its extension.
// C++17 standard library only. No supplied input.
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

using U = std::uint32_t;
using B = std::uint64_t;

struct Field {
    int e;
    U size, mask, modulus;
    std::vector<U> log, exp, trace;
    std::vector<U> subfield;

    Field(int e_, U p) : e(e_), size(1U << (2*e)), mask(size-1), modulus(p),
            log(size, size), exp(2*mask), trace(size) {
        U x=1;
        for (U i=0; i<mask; ++i) {
            assert(x && log[x]==size);
            log[x]=i; exp[i]=exp[i+mask]=x;
            x<<=1;
            if (x&size) x^=modulus;
        }
        assert(x==1);
        for (U a=0; a<size; ++a) {
            if (frob(a,2)==a) subfield.push_back(a);
            trace[a]=partial(a,e);
        }
        assert(subfield.size()==4);
        for (auto t: trace) assert(frob(t,2)==t);
    }
    U mul(U x,U y) const { return (x && y)?exp[log[x]+log[y]]:0; }
    U frob(U x,int i) const {
        if (!x) return 0;
        return exp[(B(log[x]) << (i%(2*e))) % mask];
    }
    U partial(U x,int a) const {
        U t=0;
        for (int i=0;i<a;++i) t^=frob(x,2*i);
        return t;
    }
    U inv(U x) const {
        assert(x);
        return exp[mask-log[x]];
    }
};

using Ring=std::array<U,4>;
Ring rmul(const Field& F,U x,const Ring& a,const Ring& b) {
    std::array<U,7> tmp{};
    for (int i=0;i<4;++i) for (int j=0;j<4;++j)
        tmp[i+j]^=F.mul(a[i],b[j]);
    for (int i=6;i>=4;--i) {
        // T^4+T+x=0. Keep only degrees below four.
        tmp[i-3]^=tmp[i]; tmp[i-4]^=F.mul(tmp[i],x);
    }
    return {tmp[0],tmp[1],tmp[2],tmp[3]};
}
Ring rpow(const Field& F,U x,Ring a,B n) {
    Ring z{1,0,0,0};
    while (n) {
        if (n&1) z=rmul(F,x,z,a);
        a=rmul(F,x,a,a);
        n>>=1;
    }
    return z;
}
U defining_value(const Field& F,U x,B n) {
    Ring sum{};
    // Literal defining sum evaluated in the formal quotient ring.
    for (auto a: F.subfield) {
        auto t=rpow(F,x,{a,1,0,0},n);
        for (int j=0;j<4;++j) sum[j]^=t[j];
    }
    assert(sum[1]==0 && sum[2]==0 && sum[3]==0);
    return sum[0];
}
B degree(int e,int a) {
    return 1+(B(2) << (2*a))+(B(2) << (2*(e-1)))+
             (B(1) << (2*e))+(B(2) << (2*(e+a)));
}
U general(const Field& F,U x,int a) {
    U t=F.trace[x], A=F.partial(x,a), Bv=F.partial(x,F.e-1);
    U C=F.partial(x,F.e+a), pp=F.frob(x,2*(F.e-1));
    U AA=F.frob(A,1), BB=F.frob(Bv,1), CC=F.frob(C,1);
    // Direct coefficient expression from the five factors, before their
    // evaluation on a trace layer.
    U v=AA^BB^CC^F.mul(x,t)^F.mul(t,F.mul(AA,BB)^F.mul(AA,CC)^F.mul(BB,CC));
    if (!t) {
        assert(v==F.frob(pp,1));
    } else {
        U y=F.mul(x,F.inv(t)), z=1;
        assert(F.trace[y]==1);
        for (int i=0;i<=2*a;++i) z^=F.frob(y,i);
        assert(v==F.mul(F.frob(t,1),z));
    }
    return v;
}
U printed_q66(const Field& F,U x,bool drop_duplicate) {
    int h=F.e/2;
    U t=F.trace[x], A=F.partial(x,h-1), Bv=F.partial(x,F.e-1);
    U C=F.partial(x,3*h-1), H=F.partial(x,h);
    U AA=F.frob(A,1), BB=F.frob(Bv,1), CC=F.frob(C,1);
    U tc=F.mul(t,C);
    U val=AA^F.frob(H,2*F.e-1)^tc^F.mul(x,t)^
        F.mul(t,F.mul(BB,AA))^F.mul(t,F.mul(CC,AA^BB));
    return drop_duplicate?val:val^tc;
}
void check(const Field& F,int a,bool q66,bool exhaustive_identity) {
    std::vector<bool> seen(F.size), bad(q66?F.size:0);
    U s=0,different=0,badimage=0;
    B n=degree(F.e,a);
    for (U x=0;x<F.size;++x) {
        U v=general(F,x,a);
        seen[v]=true;
        if (q66) {
            assert(v==printed_q66(F,x,false));
            U z=printed_q66(F,x,true);
            different+=z!=v;
            bad[z]=true;
        }
        if (exhaustive_identity || (x % (F.size/64) == 0) || x < 16) {
            assert(v==defining_value(F,x,n));
            ++s;
        }
        U t=F.trace[x], expected=(F.e%2)?0:F.frob(t,1);
        assert(F.trace[v]==expected);
    }
    U image=0;
    for (U x=0;x<F.size;++x) {
        image+=seen[x];
        if(q66) badimage+=bad[x];
    }
    int d=std::gcd(2*a+1,F.e);
    U expected=F.size/4;
    if (F.e%2==0) expected+=(3*expected)/(1U << (d-1));
    assert(expected==image);
    if (q66) assert(image==F.size && different>0);
    if (q66 && F.e==4) assert(badimage<F.size);
    std::cout << "e=" << F.e << ", a=" << a
              << ", modulus=" << F.modulus << ": image " << image << '/' << F.size
              << ", literal defining-sum checks " << s;
    if (q66) std::cout << ", deleted-duplicate image " << badimage;
    std::cout << " PASS\n";
}
int main() {
    for (auto p : std::array<std::array<U,3>,4>{{
        {4,285,501}, {6,4179,8137}, {8,65581,131053}, {10,1048585,2097145}}}) {
        int e=int(p[0]);
        for (int i=1;i<=2;++i) check(Field(e,p[i]),e/2-1,true,e<=6);
    }
    // General-family controls: repeated q-adic positions, odd e, both
    // obstructions d=3 and d=5, plus a beyond e included literally.
    check(Field(2,19),0,false,true);
    check(Field(3,67),1,false,true);
    check(Field(4,285),3,false,true);
    check(Field(4,501),7,false,true);
    check(Field(6,4179),1,false,true);
    check(Field(10,1048585),2,false,false);
    std::cout << "all exact field and literal-definition checks PASS\n";
}
