"""Exact small permutation/ordinal identities; final Airy comparison is numerical."""
from itertools import permutations
from math import exp,log,gamma,ceil

def eq(a,b):
    if a!=b:raise RuntimeError((a,b))
def counts(w,d):
    out=[(0,)*d]
    for c in w:
        v=list(out[-1]);v[c]+=1;out.append(tuple(v))
    return out
def enc(p):
    u=[]
    for i in range(len(p)):
        u.append(max((u[k]+1 for k in range(i) if p[k]>p[i]),default=0))
    v=tuple(c for _,c in sorted(zip(p,u)))
    return tuple(u),v
def mot(n,q):
    a=[1]
    for k in range(n):
        a=[q**h*((a[h-1] if h else 0)+((1+(h>0))*a[h] if h<=k else 0)
                  +(a[h+1] if h<k else 0)) for h in range(k+2)]
    return a[0]
P=I=C=0
for n in range(1,8):
    z=0
    for p in permutations(range(n)):
        u,v=enc(p);d=max(u)+1
        if d>4:continue
        P+=1;x=counts(u,d);y=counts(v,d)
        D=[tuple(i-j for i,j in zip(a,b)) for a,b in zip(x,y)]
        inv=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        ft=sum(abs(p[i]-i) for i in range(n))
        eq(ft,sum(abs(h) for row in D for h in row))
        if ft>2*inv:raise ValueError("footrule bound")
        lt=[]
        for t,j in enumerate(u):
            tt=p[t]
            eq(j,v[tt]);eq(x[t+1][j],y[tt+1][j])
            terms=tuple(x[t+1][i]-y[tt+1][i] for i in range(j))
            if terms and min(terms)<=0:raise ValueError("missing northwest witness")
            lt.append(sum(terms))
        eq(sum(lt),inv)
        if d<=2:z+=3**inv
        # Verify all local scores using only local words and incoming D.
        for a in range(n):
            for b in range(a+1,n+1):
                xx=counts(u[a:b],d);yy=counts(v[a:b],d)
                for t in range(a,b):
                    j=u[t];ord0=D[a][j]+xx[t-a+1][j]
                    hits=[h for h in range(b-a) if v[a+h]==j and yy[h+1][j]==ord0]
                    eq(hits,[p[t]-a] if a<=p[t]<b else [])
                    if hits:
                        tt=hits[0];I+=1
                        eq(sum(D[a][i]+xx[t-a+1][i]-yy[tt+1][i] for i in range(j)),lt[t])
        u2,v2=v[::-1],u[::-1];xx=counts(u2,d);yy=counts(v2,d)
        eq(D[::-1],[tuple(i-j for i,j in zip(a,b)) for a,b in zip(xx,yy)]);C+=1
    eq(z,mot(n,3))
print("canonical permutations of width at most 4 through n=7:",P)
print("internal matched event/block scores:",I,"; reverse-swap whole paths:",C)
print("exact d=2 area-transfer polynomial evaluations at 3 through n=7: PASS")

# Ai(z) power series y''=zy about zero; first root bracket is used only as a diagnostic.
def ai(z):
    a=[1/(3**(2/3)*gamma(2/3)),-1/(3**(1/3)*gamma(1/3)),0.]
    for k in range(1,70):a.append(a[k-1]/((k+2)*(k+1)))
    return sum(v*z**i for i,v in enumerate(a))
lo,hi=-2.34,-2.33
if not ai(lo)<0<ai(hi):raise ValueError("Airy diagnostic")
for _ in range(45):
    mi=(lo+hi)/2
    if ai(mi)>0:hi=mi
    else:lo=mi
print("d=2 continuum lambda (Airy): %.8f"%(-lo/4**(1/3)))
# Symmetric exact transfer, height-truncated only for this diagnostic; Sturm bisection, float.
def upper_eigen(n):
    B=n**(1/3);L=ceil(16*B);q=exp(-1/n)
    dia=[(1+(h>0))*q**h/4 for h in range(L)]
    off2=[q**(2*h+1)/16 for h in range(L-1)]
    lo,hi=0.,1.
    for _ in range(45):
        mi=(lo+hi)/2;s=mi-dia[0];pos=s>0
        for k,e in enumerate(off2):
            if abs(s)<1e-300:s=1e-300
            s=mi-dia[k+1]-e/s;pos+=(s>0)
        if pos==L:hi=mi
        else:lo=mi
    return -log(hi)*B*B
for n in (512,4096,32768,262144):
    print("d=2, n=%d, rescaled log eigenvalue (truncated): %.8f"%(n,upper_eigen(n)))
print("PASS")
