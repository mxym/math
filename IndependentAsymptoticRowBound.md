# Independent derivation of the asymptotic equal-offset row bound

This note records the nonauthor audit's independent derivation of the only row-size input needed for the prime-separation theorem. It does not use the earlier table of signed error constants or the finite enumeration.

**Lemma.** There is an absolute \(U_0\) such that every solution of \(\binom nk=\binom{n-d}{k+d}\) with integers \(d\ge2\), \(k\ge1\), \(n\ge k+2d\), and \(u=n-k\ge U_0\), has \(d>\sqrt u\).

**Proof.** Put \(z=u-d+1/2\), \(x=n-(d-1)/2\), \(y=k+(d+1)/2\), and \(E=z^2-xy\). Thus \(x-y=z-1/2\). Let \(C_m(t)=\prod_j(t+j)\), where \(j\) ranges in unit steps from \(-(m-1)/2\) to \((m-1)/2\), and let \(J_m\) be the positive members of this range. Factorial cancellation gives \(C_{2d}(z)=C_d(x)C_d(y)\), with all factors positive. Pairing opposite \(j\)'s gives \(C_d(x)C_d(y)\le(xy)^d\); also \(C_{2d}(z)\ge(z-d)^{2d}\). Hence \(xy\ge(z-d)^2\). For \(z\ge8d\), if \(y\le z/2\) then \(x<3z/2\) and \(xy<3z^2/4\), whereas \((z-d)^2\ge49z^2/64\). Therefore \(y>z/2\) and \(x>z\).

Write \(w=E/z^2\), \(S_m=\sum_{j\in J_m}j^2=m(m^2-1)/24\), and \(T_m=\sum_{j\in J_m}j^4=m(m^2-1)(3m^2-7)/480\). With \(L_m(t)=-\sum_{j\in J_m}\log(1-j^2/t^2)\) the product identity reads \(d[-\log(1-w)]=L_{2d}(z)-L_d(x)-L_d(y)\). Every log argument \(j^2/t^2\) is \(\le d^2/z^2\le1/64\); the first-order bound for \(-\log(1-v)\) and \(\sum_{j\in J_m}j^2=O(d^3)\) imply \(-\log(1-w)=O(d^2/z^2)\), whence \(E=O(d^2)\). More explicitly, \(-\log(1-v)\le(4/3)v\) on this range and \(x^{-2}+y^{-2}<5/z^2\) give \(|\log(1-w)|\le(13/18)d^2/z^2\); hence \(|w|<1/2\). All constants below are absolute for \(z\ge8d\).

Define \(A=z^2(x^{-2}+y^{-2})\), \(B=z^4(x^{-4}+y^{-4})\), and \(C=z^2(A-3+z^{-1})\). Since \(x^2+y^2=3z^2-z+1/4-2E\), we have
\[
 A=\frac{3-z^{-1}+(1/4-2E)/z^2}{(1-w)^2},\qquad
 B=A^2-2(1-w)^{-2}.
\]
Expanding \((1-w)^{-2}=1+2w+O(w^2)\) gives \(C=4E+O(1+d^2/z+d^4/z^2)\) and \(B=7+O(z^{-1}+d^2/z^2)\). In particular \(C=O(d^2)\) and \(B=O(1)\).

Expand \(L_m(t)\) through \(S_m/t^2+T_m/(2t^4)\). Its error is \(O(d^7/z^6)\) by \(t\ge z/2\) and \(\sum j^6=O(d^7)\). Likewise \(-\log(1-w)=w+w^2/2+O(|w|^3)\). Multiplying the exact log identity by \(z^2/d\) and collecting terms gives, with \(E_*=(S_{2d}-3S_d)/d=(5d^2+1)/24\),
\[
 E-E_*=\frac{d^2-1}{24z}
 +\frac{1}{z^2}\left[\frac{T_{2d}-T_d B}{2d}-\frac{S_d C}{d}-\frac{E^2}{2}\right]
 +O(d^6/z^4).
\]
The bracket is \(O(d^4)\), so \(E-E_*=(d^2-1)/(24z)+O(d^4/z^2)\). In particular with \(\xi=d^{-2}+z^{-1}+d^2/z^2\) we have \(E/d^2=5/24+O(\xi)\), \(C/d^2=5/6+O(\xi)\) and \(B=7+O(\xi)\). Dividing the bracket by \(d^4\), its constant term is
\[
 \frac1{10}-\frac7{320}-\frac1{24}\frac56-\frac12\left(\frac5{24}\right)^2
                       =\frac{25}{1152}.
\]
The original remainder, after division by \(d^4/z^2\), is \(O(d^2/z^2)\). This gives the uniform expansion
\[
 E-E_*=\frac{d^2-1}{24z}
        +\frac{d^4}{z^2}\left[\frac{25}{1152}
                              +O(d^{-2}+z^{-1}+d^2/z^2)\right].
\tag{*}
\]

The quantity \(E\) belongs to \(\tfrac14\mathbb Z\): \(z\) is half-integral; for odd \(d\), \(x,y\) are integral and \(E\in\tfrac14+\mathbb Z\); for even \(d\), \(x,y,z\) are half-integral and \(E\in\tfrac12\mathbb Z\). On the common quarter lattice, the distance from \(E_*\) to the first lattice point strictly above is respectively \(5/24,1/4,1/8,1/12\) for \(d\equiv0,\pm1,\pm2,3\pmod6\), by reducing \(24E_*=5d^2+1\) modulo 6. Thus \(0<E-E_*<1/12\) is impossible.

If the lemma failed there would be solutions with \(u\to\infty\) and \(u\ge d^2\). If \(d\) is bounded on a subsequence, fix \(d\) there. Then \(z\to\infty\), and \(E-E_*=(d^2-1)/(24z)+O_d(z^{-2})\) is positive and tends to zero, a contradiction. Otherwise pass to \(d\to\infty\), when \(z\ge d^2-d+1/2\); in particular \(z\ge8d\) eventually and the bracket error in (*) is uniformly \(O(d^{-2})\). Put \(r=d^2/z\), so \(0<r\le1+O(d^{-1})\). Both terms in (*) are strictly positive for large \(d\), even when \(r\to0\). Their sum is at most \(1/24+25/1152+o(1)=73/1152+o(1)<1/12\). The lattice contradiction completes the proof.

The lemma supplies exactly the \(d>\sqrt u\) input in §2 of [the prime-separation theorem](FactorSingmasterPrimeSeparation.md). It is not an explicit bound on \(U_0\), nor a replacement for the stronger finite-shift computational statement.
