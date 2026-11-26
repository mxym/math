# Two exclusions for Ochem–Zelinsky Question 10

**Yongxian Zhang.** AI-assisted proof development and internal verification; no claim that Question 10 is resolved.

Set \(F(z)=z^2+z+1\). [Ochem–Zelinsky, Question 10](https://arxiv.org/html/2607.19746v1#S5) asks whether primes \(x,y,p,r\) and exponents \(a>b>0\) can satisfy \(F(x)=p^ar,\ F(y)=p^br\). Necessarily \(p\ne3\), since \(v_3(F(z))\le1\), and then \(p\equiv1\bmod3\) by the order-three property. In particular \(p\ge7\). Also \(r\) is odd.

## Even exponent gaps

Suppose \(a-b=2d\), and let \(P=p^d,\ u=2x+1,\ v=2y+1\). Then \(u^2-P^2v^2=3(P^2-1)>0\). The positive integers \(A=u-Pv,\ B=u+Pv\) satisfy \(AB=3(P^2-1)\), and \(A^2\equiv-3\bmod P\). Thus \(A^2\ge P-3\), and
\[
 v^2=(B-A)^2/(4P^2)<9P^2/(4(P-3))\le63P/16
\]
because \(P\ge7\). If \(b\ge d\), on the other hand, \(v^2=4p^br-3\ge12P-3\), contradiction. Therefore \(d>b\), or equivalently \(a>3b\). In particular gap two is impossible. Since now \(P\ge49\), the same upper bound gives
\[
 p^br = (v^2+3)/4
 < \left(\frac{9\cdot49}{16(49-3)}+\frac{3}{4\cdot49}\right)P
 <5P/8.
\]
Thus in the even-gap sector also \(r<(5/8)p^{d-b}\).

## Gap one for nine possible repeated primes

For \(a-b=1\), write \(K=3(p-1)\). Then \(u^2-pv^2=K\). Let \(\epsilon=A+B\sqrt p>1\) be any positive integral solution of \(A^2-pB^2=1\). Multiplying by a power of the unit reduces the positive number \(u+v\sqrt p\) into \([\sqrt K,\epsilon\sqrt K)\), preserving integral coordinates. The reduced coordinates \(u_0,v_0\) satisfy \(0\le v_0<B\sqrt K\) and \(u_0>0\), and they are odd because \(A,B\) have opposite parities. Thus enumerate their finite possibilities by trial square tests. Repeated multiplication by \(\epsilon\) modulo \(12p\) is a permutation, so whole residue cycles can be checked.

If \(r\ne3\), both \(x,y>3\) (since \(F(2)=7\) and \(F(3)=13\) cannot equal the product of two primes), and both are \(2\bmod3\). Then \(u=v=11\bmod12\). Also \(v^2+3\equiv0\bmod p\). The code below finds zero modular survivors for the nine indicated primes. For \(p=7\) in particular, the three odd Pell seeds are \((5,1),(9,3),(19,7)\) with \(\epsilon=8+3\sqrt7\). The first remains opposite modulo 3 and the second remains zero modulo 3. For the third, both coordinates are 2 modulo 3 only after odd iterates, when their residues modulo 4 are different. This gives a simple hand proof for \(p=7\).

For \(r=3\), the exponent of \(p\) in either equation is at most two by the exclusion of \(F(z)=3w^j\), \(j\ge3\), cited in [Ochem–Zelinsky §4, proof of Lemma 8](https://arxiv.org/html/2607.19746v1#S4) as [Bugeaud–Mihăilescu, Theorem 2](https://doi.org/10.7146/math.scand.a-15038). It follows that \((a,b)=(2,1)\); the corresponding two discriminants \(12p^2-3,12p-3\) are not both squares for any of the nine primes.

```python
from math import isqrt

units = [(7,8,3,3), (13,649,180,6), (19,170,39,4),
         (37,73,12,2), (43,3482,531,6), (79,80,9,2),
         (223,224,15,2), (439,440,21,0), (499,4490,201,0)]

def square(n):
    return isqrt(n)**2 == n

for p,A,B,expected in units:
    assert A*A-p*B*B==1
    K, M = 3*(p-1), 12*p
    seeds=0
    for v in range(1,isqrt(B*B*K-1)+1,2):
        u=isqrt(p*v*v+K)
        if u*u!=p*v*v+K or not u%2:
            continue
        seeds+=1
        seed=(u%M,v%M)
        x,y=seed
        while True:
            assert not (x%12==y%12==11 and (y*y+3)%p==0)
            x,y=(A*x+p*B*y)%M,(B*x+A*y)%M
            if (x,y)==seed:
                break
    assert seeds==expected
    assert not (square(12*p*p-3) and square(12*p-3))
```

These exclusions leave odd gaps in general and even gaps with \(a>3b\) open.
