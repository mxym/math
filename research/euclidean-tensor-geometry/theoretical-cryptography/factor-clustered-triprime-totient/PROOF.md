# Proof

## 1. Symmetric data

Let \(N=xyz\), where \(2<x<y<z\) are primes, and let
\(T=\varphi(N)=(x-1)(y-1)(z-1)\). If
\(e_1=x+y+z\) and \(e_2=xy+xz+yz\), then
\[
T=N-e_2+e_1-1. \tag{1}
\]
An integer candidate \(S\) for \(e_1\) therefore fixes
\[
E_2=S+N-1-T,\qquad
P_S(X)=X^3-SX^2+E_2X-N. \tag{2}
\]
For \(S=e_1\), this is \((X-x)(X-y)(X-z)\). Factoring a fixed-degree
polynomial in \(\mathbb Z[X]\) is deterministic polynomial time in the
coefficient bit length, so it remains to bound the candidate count.

## 2. Two algebraic endpoints

For \(t>1\), define
\[
F(t)=(t-1)^2\left({N\over t^2}-1\right),\quad
G(t)=2t+{N\over t^2},\quad u=N^{1/3}. \tag{3}
\]
Differentiation gives
\[
F'(t)=2(t-1)\left({N\over t^3}-1\right),\quad
G'(t)=2\left(1-{N\over t^3}\right),\quad
{dG\over dF}=-{1\over t-1}. \tag{4}
\]
Thus \(F\) increases on \((1,u)\) and decreases on
\((u,\sqrt N)\).

For any pair \(a,b\), put
\[
r=\sqrt{ab},\quad c={N\over r^2},\quad
d=(\sqrt a-\sqrt b)^2=a+b-2r. \tag{5}
\]
If \(abc=N\), direct expansion gives
\[
T=F(r)-(c-1)d,\qquad e_1=G(r)+d. \tag{6}
\]
Applying (6) to either adjacent prime pair shows \(T<F(u)\). Hence
\(F(t)=T\) has unique roots
\[
s_-\in(1,u),\qquad s_+\in(u,\sqrt N). \tag{7}
\]

## 3. The two largest primes

Take \(a=y,b=z,c=x\), with
\(r_+=\sqrt{yz}\) and \(d_+=(\sqrt z-\sqrt y)^2\).
Then \(s_+\ge r_+\). Also
\[
F(z)-T=-{(z-1)(z-x)(z-y)\over z}\le0, \tag{8}
\]
so monotonicity gives \(s_+\le z\).

Apply the mean value theorem to \(G\) as a function of \(F\) between
\(r_+\) and \(s_+\). For some \(\xi_+\in[r_+,s_+]\),
\[
e_1-G(s_+)
=d_+{\xi_+-x\over \xi_+-1}. \tag{9}
\]
The ratio is nonnegative and increasing in \(\xi_+\). Since
\(\xi_+\le z\),
\[
0\le e_1-G(s_+)
\le(\sqrt z-\sqrt y)^2{z-x\over z-1}=R_+. \tag{10}
\]

## 4. The two smallest primes

Take \(a=x,b=y,c=z\), with
\(r_-=\sqrt{xy}\) and \(d_-=(\sqrt y-\sqrt x)^2\).
Then \(s_-\le r_-\). Moreover
\[
F(x)-T=-{(x-1)(y-x)(z-x)\over x}\le0, \tag{11}
\]
so \(s_-\ge x\).

For some \(\xi_-\in[s_-,r_-]\), the same calculation gives
\[
G(s_-)-e_1=d_-{z-\xi_-\over \xi_--1}. \tag{12}
\]
The ratio is nonnegative and decreasing in \(\xi_-\). Since
\(\xi_-\ge x\),
\[
0\le G(s_-)-e_1
\le(\sqrt y-\sqrt x)^2{z-x\over x-1}=R_-. \tag{13}
\]

## 5. Enumeration and bit complexity

The roots \(s_\pm\) are defined by the fixed-degree polynomial
\[
(t-1)^2(N-t^2)-Tt^2. \tag{14}
\]
Fixed-degree real-root isolation and algebraic arithmetic compute
\(G(s_\pm)\) to absolute error below \(1/4\) in
\(\operatorname{poly}(\log N)\) time. Standard root-separation bounds
apply because (14) has fixed degree and \(O(\log N)\)-bit coefficients.

Enumerate integers upward from one less than the approximate
\(G(s_+)\), and downward from one more than the approximate \(G(s_-)\);
dovetail the streams. Approximation adds only \(O(1)\) trials. Equations
(10) and (13) put the true \(e_1\) in one stream after
\(O(1+\min(R_-,R_+))\) trials. For each trial, factor (2) and check
three distinct positive primes, their product \(N\), and totient \(T\).
The algorithm never needs the gaps as input.

## 6. Comparable-factor corollary

If \(x,y,z\in[u/C,Cu]\), then
\[
(\sqrt b-\sqrt a)^2={(b-a)^2\over(\sqrt a+\sqrt b)^2}.
\]
All denominators in \(R_\pm\) are \(\Theta_C(u^2)\). With
\(H=z-x\) and \(\ell=\min(y-x,z-y)\),
\[
D=O_C(\ell^2H/u^2)=O_C(\ell^2H/N^{2/3}). \tag{15}
\]
The stated special cases follow.


## 7. A nontrivial shell of promised inputs

Let \(X\) tend to infinity. The prime number theorem gives
\(\Theta(X/\log X)\) primes in each fixed positive-length subinterval of
\([X,2X]\). Partition \([1.15X,1.20X]\) into
\(J=O(\sqrt X)\) intervals of length at most \(\sqrt X\). If the cells
contain \(n_j\) primes and \(P=\sum n_j=\Theta(X/\log X)\), then
\[
 \sum_j {n_j\choose2}
 \ge {1\over2}\left({P^2\over J}-P\right)
 =\Omega(X^{3/2}/\log^2X). \tag{16}
\]
Choose the two larger primes from one cell and the smaller prime from
\([X,1.05X]\). This yields
\(\Omega(X^{5/2}/\log^3X)\) distinct squarefree triprimes, all in
\([X^3,2X^3]\). Their full spread is \(\Theta(X)\), while one adjacent
gap is at most \(\sqrt X\). Equation (15) gives \(D=O(1)\).

For these constant-ratio triples,
\(\alpha_i=\log p_i/\log N=1/3+O(1/\log X)\); for large \(X\) the three
sufficient inequalities in Morain--Renault--Smith Theorem 1.2 are all
strictly false. This only shows that the present promise supplies a
separate sufficient route. It does not assert that their algorithms
fail on any particular input.

## 8. Scope


The result assumes that \(N\) is the squarefree product of exactly three
distinct primes and that the single value \(T=\varphi(N)\) is supplied.
It does not cover repeated prime powers, a Carmichael-value oracle,
arbitrary numbers of factors, or unassisted factoring.
