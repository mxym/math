# A pointwise localization test for the central Goldbach operator

This is an unconditional fixed-target diagnostic, not uniform positivity. Use the rescaled central kernel and signed measure in [the companion central spectrum quantization note](CentralSpectrumQuantization.md). The only arithmetic input is its elementary pointwise upper-bound sieve for the total variation on each short interval.

Put \(a=1/3,\ b=2/3,\ L=b-a\). For a large even \(N\), set \(S=S(N)>0\), \(\eta=\eta_N=N^{-1/2}\log^3 N\), and recall
\[
d\sigma(t)=\sqrt{t(1-t)}
\left(S\,dt-\frac1N\sum_{\substack{n/N\in[a,b]\\(n,N)=1}}\Lambda(n)\Lambda(N-n)\delta_{n/N}\right).
\]
The real symmetric kernel on \(L^2([a,b])\) is
\[
K(u,v)=\rho_N(u)\rho_N(v)\mathbf1_{\{u+v\ge1\}}\sigma([1-v,u]).
\]
Here the last interval is used only when \(u+v\ge1\); either convention on the null equality line yields the same operator \(T_N\). Its weight is uniformly bounded above and below by positive constants: \(\rho_N(u)=\sqrt{2\pi W_N(\log(Nu))}\,u^{-3/2}\), \(W_N(r)=e^{-2r/\log N}+e^{-r/4}\), and \(0\le \log(Nu)\le\log N\) on the interval for large \(N\) gives \(W_N\ge e^{-2}\). The local sieve estimate (including singleton intervals) is
\[
|\sigma|(I)\le C_0 S (|I|+\eta)
\tag{1}
\]
for every closed central interval \(I\), with one absolute \(C_0\ge1\). The proof is the upper sieve in the companion note, using \(S\gg1\) to absorb the arithmetic remainder into \(S\eta\).

Define \(D_N=\sup_{a\le s\le t\le b}|\sigma([s,t])|\). There are absolute \(c,C>0\) such that
\[
c\,\frac{(D_N-CS\eta)_+^2}{S}\le\|T_N\|_{\rm op}\le C D_N.
\tag{2}
\]
For every centered interval \([s,1-s]\) with \(a\le s\le1/2\), set \(d=\sigma([s,1-s])\) (positive means a deficit of weighted prime-pair mass). There is a corresponding positive-spectrum estimate
\[
\lambda_+(T_N)\ge c\,\frac{(d-CS\eta)_+^2}{S}.
\tag{3}
\]
Here \(\lambda_+(T)=\max(0,\sup_{\|f\|_2=1}\langle f,Tf\rangle)\). Equation (2) for arbitrary intervals does **not** assert a bound for \(\lambda_+\) rather than the full operator norm.

## Proof

The upper bound in (2) follows from \(|K(u,v)|\le\|\rho_N\|_\infty^2 D_N\) and the central interval length \(L\), by Schur or the Hilbert–Schmidt norm.

For the lower bounds, let \(I=[s,t]\) have nonzero signed mass of magnitude \(d=|\sigma(I)|\) and assume \(d\ge 16 C_0 S\eta\). Put
\[
r=\frac{d}{16 C_0 S},\qquad
U=[t-r,t+r]\cap[a,b],\qquad V=[1-s-r,1-s+r]\cap[a,b].
\]
By (1), \(t-s\ge d/(C_0S)-\eta=16r-\eta\ge15r\); hence \(r\le L/15\). The intersections \(U,V\) each have length at least \(r\) even when their centers are exactly at the boundary. For \(u\in U,\ v\in V\), one has
\[
u+v\ge1+t-s-2r>1,
\]
so the actual interval in the kernel is always defined. Its symmetric difference from \([s,t]\) lies in the union of two closed intervals of lengths at most \(r\), one between \(s\) and \(1-v\), the other between \(t\) and \(u\). This statement includes endpoints whose atomic membership changed; using the full closed intervals in (1) is the reason jumps at atoms cause no problem. Thus
\[
|\sigma([1-v,u])-\sigma([s,t])|
\le2 C_0 S(r+\eta)\le d/4.
\]
Consequently the kernel throughout \(U\times V\) has the same sign as \(\sigma([s,t])\) and magnitude \(\ge \tfrac34 d\,(\inf\rho_N)^2\). Let \(f=\mathbf1_V/\sqrt{|V|}\) and \(g=\mathbf1_U/\sqrt{|U|}\). Then
\[
|\langle g,T_N f\rangle|\ge\tfrac34 d\,(\inf\rho_N)^2\sqrt{|U|\,|V|}
\ge c\,d^2/S.
\]
For arbitrary \(I\) this is a bilinear test, and bounds only \(\|T_N\|_{\rm op}\). Taking a sequence of intervals with masses approaching \(D_N\) gives the lower bound in (2), taking \(C\) no smaller than \(16 C_0\); no attainment of the supremum is required. For (3), apply the same proof with \(t=1-s\) and positive mass \(d\). The rectangle is now a square with \(U=V\), because its two original kernel coordinates are \(u_0=t=1-s=v_0\). Thus \(f=g\), and the lower bound on the integral has positive sign. If the displayed threshold is not met, the resulting right-hand side is zero and the asserted positive-part bound is automatic.

The test converts a large signed deficit on a centered summand window into a genuine fixed-target positive spectral obstruction. It does not certify that such deficits occur for the true primes, nor rule them out. Arbitrary signed interval discrepancy yields a complete two-sided modulus only for the full operator norm as shown in (2), and endpoint atoms below the upper-sieve error are intentionally outside its lower-bound resolution.
