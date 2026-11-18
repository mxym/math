"""Independent finite stress tests; elementary Pascal recurrences, no imports from draft."""
def need(ok,info):
    if not ok: raise RuntimeError(str(info))
def v(x):
    if not x: raise ValueError('zero')
    return (x & -x).bit_length()-1

def negacyclic():
    # Multiply by 1+x directly on two rings, without binomial coefficient,
    # normalized U, B, aligned-cut formulas or a valuation induction.
    out=0
    for p in range(1,9):
        P=1<<p;e=P//2
        H=[1]+[0]*(e-1); V=H[:]; C=[1]+[0]*(P-1)
        for step in range(1,11*P):
            H=[H[0]+H[-1]]+[H[j]+H[j-1] for j in range(1,e)]
            V=[V[0]-V[-1]]+[V[j]+V[j-1] for j in range(1,e)]
            C=[C[0]+C[-1]]+[C[j]+C[j-1] for j in range(1,P)]
            if (step+1)%P: continue
            T=(step+1)//e
            for free in range(0,e,2):
                indices=[r for r in range(0,e,2) if r&free==r]
                h=sum(H[r] for r in indices); s=sum(V[r] for r in indices)
                c=sum(C[r] for r in indices); f=free.bit_count()
                need(2*c==h+s,(p,T,free,'split'))
                need(v(c)==T-2+f,(p,T,free,'unsigned'))
                if p>=2:
                    need(v(s)==T-1+f,(p,T,free,'signed'))
                    need(v(h)>v(s),(p,T,free,'strict'))
                out+=1
    return out

def original():
    # Stream EVERY j in the Pascal row. Unlike an odd-factorial lookup of
    # selected binomials, maintain its unit part through successive ratios.
    # Evaluate sigma on each j via the factorial digit-sum formula for C(j,k).
    out=0; rows=0; high=0
    for s in range(4):
        L=1<<s
        for a in ([2,3,4] if s<3 else [2]):
            for i in ([2*L+s,2*L+s+1] if s<3 else [2*L+s]):
                for r in (0,1):
                    n=(1<<a)*((1<<i)-1)+r
                    cases=[]
                    for m in range(1,L+1,2):
                        ell=m.bit_length()-1
                        z=1+r+((2*((1<<(s-ell))-m.bit_count()+ell)) if ell==0 else (1<<(s-ell))-m.bit_count()+ell)
                        k=(1<<a)*((1<<(i-s))*m-1)
                        cases.append([m,k,k.bit_count(),z,0])
                    bits=max(e[3] for e in cases)+1; mod=1<<bits;mask=mod-1
                    inv={j:pow(j,-1,mod) for j in range(1,mod,2)};unit=1; t=0
                    for j in range(n+1):
                        if t<bits:
                            b=(unit<<t)&mask; jones=j.bit_count()
                            for c in cases:
                                m,k,kones,z,sw=c
                                if j>=k and kones+(j-k).bit_count()==jones:
                                    c[4]=(sw+b)&mask
                        if j<n:
                            num=n-j; den=j+1
                            vn=v(num); vd=v(den); t+=vn-vd
                            unit=(unit*(num>>vn)*inv[(den>>vd)&mask])&mask
                    for m,k,w,z,sw in cases:
                        S=(pow(2,n,mod)-2*sw)&mask
                        need(S!=0 and v(S)==z,(n,k,z,S));out+=1
                    rows+=1;high=max(high,n)
    return rows,out,high

if __name__=='__main__':
    print("ring cases:",negacyclic(),flush=True)
    print("full streamed original rows, cases, maximum n:",original(),flush=True)
