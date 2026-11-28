# Sharp cubic separation of three binomial coincidences under real interpolation

Define the gamma interpolation
\[
 {\cal B}(n,k)=\frac{\Gamma(n+1)}
 {\Gamma(k+1)\Gamma(n-k+1)}.
\]
Consider three distinct equal entries in the lower half, based at $(n,k)$ with $0<k\le n/2$, and at $(n-a_i,k+b_i)$ for $i=1,2$. We require positive **integer shifts** $a_i,b_i$ and write $s_i=a_i+b_i$, $s_1<M:=s_2$. The base coordinates $n,k$ can be real. In particular the real model includes every triple of ordinary Pascal entries after ordering the entries by decreasing $n$ and increasing $k$.

**Theorem.** All such real triples satisfy $n<9M^3$. The sharp asymptotic constant is
\[
 \limsup_{\substack{M\to\infty\\\text{real triples as above}}}
             \frac{n}{M^3}=\frac1{2\log 2}.
\tag{1}
\]
This is sharpness for real base coordinates, not the existence of near-extremal integer triples. For ordinary Pascal entries a much stronger asymptotic separation follows from [Matomäki–Radziwiłł–Shao–Tao–Teräväinen, Theorem 1.3](https://arxiv.org/abs/2106.03335): for every $0<\epsilon<1/3$ and sufficiently large $n$,
\[
 M\ \ge\ \frac{n\log n}{2\exp((\log n)^{2/3+\epsilon})}.
\tag{2}
\]
Thus real geometric sharpness does not extrapolate to the integer conjecture.

[Jenkins, Proposition 1](https://arxiv.org/abs/1411.4111) localizes the slope of one collision using successive binomial ratios. Below the corresponding slope estimate holds without assuming $k>a_i$. The additional ingredients for (1) are a sharp inverse slope derivative, a uniform centered intercept, and separation of two rational slopes by a nonzero determinant. The integer corollary is deduced explicitly from the cited interior multiplicity theorem and a single-collision product estimate; it does not improve the global multiplicity theorem.

## 1. Two distinct rational slope parameters

Use $z=n-k,\ y=k$, so each move is $(z,y)\mapsto(z-s,y+b)$ with $s=a+b$. Put $t=b/s$, and define $\alpha(t)\in(0,1)$ by
\[
 (1+\alpha)^{1-t}\alpha^t=1 .
\]
At an equality, gamma recurrence gives the exact product identity
\[
 \prod_{j=0}^{s-1}(z-j)
   =\prod_{j=0}^{a-1}(z+y-j)\prod_{j=1}^{b}(y+j).
\tag{3}
\]
In the range $z\ge s,\ y\ge0$, compare each factor to its extreme value in each group. The right side is at least $(z+y-a+1)^a(y+1)^b$; since the left side is at most $z^s$, this gives $y\le\alpha(t)z+a-1$ (if $y<a-1$, this is automatic). The left side is at least $(z-s+1)^s$, while the right side is at most $(z+y)^a(y+b)^b$. Here $b\le s-1$, so the latter product is at most $(z-s+1+y+s-1)^a(y+s-1)^b$. Dividing by $(z-s+1)^s$ gives the other bound:
\[
 -(1+\alpha(t))(s-1)\ \le\ y-\alpha(t)z\ \le\ a-1 .
\tag{4}
\]

The inverse of $\alpha$ on $(0,1)$ is $r(x)=\log(1+x)/\log(1+1/x)$. It satisfies
\[
 0<r'(x)\le 1/\log 2,\qquad r'(1)=1/\log 2.
\tag{5}
\]
For verification write $g=\log(1+x)$, $h=-\log x$, $L=g+h$. The numerator of $r'$ over denominator $L^2$ is $g/x+h/(1+x)$. We have $g/x\le L$ because $xh\ge x(1-x)\ge (1-x)g$. Also $h\le2(L-\log 2)$ by comparing the integrands $1/u$ and $2/(u(1+u))$ on $[x,1]$. The function $(1+x)L$ is decreasing since its derivative is $L-1/x<0$, so $(1+x)L\ge2\log 2$. Therefore $h/(1+x)\le L(L-\log 2)/\log 2$, proving (5). The inverse extends differentiably from the left at $t=1$ with $\alpha'(1)=\log 2$; on the whole open interval $\alpha'(t)\ge\log 2$ and $\alpha(t)\ge t\log 2$.

For the ordered triple one has $t_2>t_1$. Indeed the logarithm of ${\cal B}(z+y,y)$ along $(z-u,y+t_1u)$ is strictly concave for $0\le u\le M$. Its second derivative is
\[
 (1-t_1)^2\psi_1(z+y-(1-t_1)u+1)
 -\psi_1(z-u+1)-t_1^2\psi_1(y+t_1u+1)<0,
\]
since the trigamma function is positive and decreasing (its series is $\sum_{j\ge0}(x+j)^{-2}$). Equality at $u=0,s_1$ implies a strictly smaller value at $u=M$. At fixed $z-M>0$, the log binomial is strictly increasing in $y$, as follows from the positive trigamma and the difference of two digamma values. Thus $t_2\le t_1$ is impossible. If $z=M$, the third entry has $z-M=0$ and cannot be in the positive lower half assumed here.

Write $\alpha_i=\alpha(t_i)$ and $\Delta=\alpha_2-\alpha_1$. The determinant $b_2s_1-b_1M$ is a positive integer. By (5),
\[
 \Delta\ge (\log 2)/(s_1M).
\tag{6}
\]
The upper squeeze in (4) for shift 1 and the lower squeeze for shift 2 imply
$z\Delta\le(1+\alpha_2)(M-1)+a_1-1<3M$. Since $n\le2z$ and $\log 2>2/3$, this proves $n<9M^3$.

## 2. The centered intercept and the sharp constant

For uniformity over any $a,b\ge1$ with $s\le M$, suppose $z\ge c M^3$ for a fixed $c>0$ and $M\to\infty$. Then on the corresponding branch of (3),
\[
 y=\alpha(t)z-\frac{\alpha(t)+t}{2}\,s
         +O_c(1+M^2/z).
\tag{7}
\]
To verify it, put $W=z-s/2$, $Y=y+(b+1)/2$, $T=Y/W$, and use
$C_j(v)=\prod_{\nu=-(j-1)/2}^{(j-1)/2}(v+\nu)$ with step one. Equation (3) becomes $C_s(W+1/2)=C_a(W+Y)C_b(Y)$. From (4), $T=\alpha(t)+O(M/z)$; by (5), $\alpha(t)\ge (b/s)\log 2$. Consequently $T\ge\alpha(t)/2$ for all sufficiently large $M$, and the paired centered factors in the three products have ratios $\nu/(W+1/2)$, $\nu/(W+Y)$ or $\nu/Y$ uniformly $O(M/z)$ (for the last, use $b/T=O(s)$). In the centered logarithmic average the linear terms cancel in opposite pairs, leaving $O(M^2/z^2)$. After dividing by $s$ and canceling $\log W$ the identity gives
\[
 (1-t)\log(1+T)+t\log T
    = \log(1+1/(2W))+O(M^2/z^2).
\]
The derivative in $T$ on the segment to $\alpha(t)$ is bounded below by a positive absolute constant, since $0<T<2$ for large $M$. The left side is zero at $\alpha(t)$, so $T=\alpha(t)+O(1/z+M^2/z^2)$. Converting back to $y$ gives (7).

Use (7) for both shifts. On any sequence with $z\ge cM^3$,
\[
 z\Delta=\frac{(\alpha_2+t_2)M-(\alpha_1+t_1)s_1}{2}+O_c(1).
\]
The numerator is at most $2(M-s_1)+O(M\Delta)$: $\alpha_2+t_2\le2$, and $t_2-t_1\le\Delta/\log 2$. Absorb the last term on the left and use (6):
\[
 z\le \frac{s_1M(M-s_1)}{\log 2}+O_c(M^2)
      \le \frac{M^3}{4\log 2}+O_c(M^2).
\]
Hence $n/M^3\le1/(2\log 2)+o(1)$ for every subsequence bounded away from zero; other subsequences do not increase the limsup.

For sharpness take $s_1=s$, $M=2s+1$, and $(a_1,b_1)=(1,s-1)$, $(a_2,b_2)=(2,M-2)$. The determinant is exactly 1, both $t_i\to1$, and $\Delta\sim(\log 2)/(sM)$. For fixed shift and $z>s_i$, the right side of (3) is strictly increasing from its value at $y=0$ to infinity, and the left side exceeds the value at $y=0$: their ratio there is $\prod_{j=a_i}^{s_i-1}(z-j)/b_i!>1$. Thus there is a unique nonnegative continuous solution $y_i(z)$ for $z>M$. In fact $y_i(z)<z$ by comparing at $y=z$ in (3). The centered asymptotic gives, for $z=u M^3$ with fixed $u>0$,
\[
 \frac{y_2(z)-y_1(z)}{M}\ \longrightarrow\ 2u\log 2-\frac12.
\]
Choose fixed positive $u$ on either side of $1/(4\log2)$ and apply the intermediate value theorem between these two points. Any resulting intersection in this bracket has $z/M^3\to1/(4\log 2)$ by the uniform estimate (7). There $y/z\to1$, so $n/M^3\to1/(2\log 2)$. The lower-half restriction still holds at each of the three entries: $1-\alpha_1\sim(\log2)/s$, so $z-y\gg M^2$ by (7), while the shifts change this difference by at most $2M$. Also $y>0$ for sufficiently large $M$. This completes (1).

## 3. Integer triples and the edge of Pascal's triangle

For integers $0<k\le n/2$, the binomial entry is strictly increasing in $n$ at fixed $k$ and strictly increasing in $k$ along the lower half of a row. Thus in a triple of integer equalities all $n$ are distinct; in decreasing row order all $k$ strictly increase. This gives exactly the positive integer shifts and $M$ used above.

For fixed $\epsilon$ as in (2), put $Y_n=\exp((\log n)^{2/3+\epsilon})$. The published interior theorem cited above implies that for sufficiently large $n$ at least one entry in the triple has column index below its interior threshold; its row is at most $n$, and $y=k$ is the smallest column in the triple, so $y\le Y_n$. The common binomial value tends to infinity with $n$ since $\binom nk\ge n$ in this range. We have $z\sim n$; if $M>z/8$ the desired bound follows immediately for large $n$.

Otherwise use either shift in (3) and divide off the first $a$ factors on each side. Taking logarithms gives the exact equality
\[
 \sum_{j=0}^{a-1}\log\bigl(1+y/(z-j)\bigr)
    = \sum_{i=0}^{b-1}\log\bigl((z-a-i)/(y+i+1)\bigr).
\]
The left side is at most $8M y/(7z)$. The right side is at least
$b\log(7z/[8(y+b)])$, since $a+b\le M\le z/8$. As a function of $b$ on $[1,M]$ this bound is increasing: for large $n$, $y\le z/8$, so its derivative is at least $\log(7/2)-1>0$. At $b=1$ its value is $(1-o(1))\log n$, uniformly for $y\le Y_n$. Rearranging gives $M\ge (7/8-o(1))n\log n/y$, which implies (2).

**Exact controls.** `python3 -O verify_singmaster_three_coincidence_spacing.py` confirms the signs at two rational endpoints of a real crossing bracket for six finite parameter values, and checks the separation bound on every coincidence triple whose three rows are at most 200. The controls do not substitute for the uniform asymptotic argument and do not assert any new lattice triples.
