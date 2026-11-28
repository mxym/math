# Exact high-rate PGM–Delsarte converse for quantum random access codes

## 1. The relaxation and the result

For integers \(n\ge6,\ 0\le j,r\le n\), put
\[
 \kappa_r(j)=\frac{1}{\binom{n}{j}}
    \sum_{\ell=0}^{j}(-1)^\ell \binom{r}{\ell}\binom{n-r}{j-\ell}.
 \tag{1}
\]
Out-of-range binomial coefficients are zero. This is the mean product of a uniform \(j\)-subset drawn without replacement from \(n\) signs of which \(r\) are negative. Given \(c\), let \(D(n,c)\) be the minimum of \(\sum_{j=0}^n j q_j\) subject to
\[
 q_j\ge0,\quad \sum_j q_j=1,\quad q_0\le c,\quad
 \sum_{j=0}^n q_j\kappa_r(j)\ge0\quad(0\le r\le n).
 \tag{2}
\]
This is the Tan–Jafar full-string PGM relaxation with diagonal cap \(c\). For binary \((n,m)\) codes, \(c=2^{m-n}\), and the equivalent ordinary Delsarte problem is minimum average distance for a formal distribution of a code of size \(1/c\), not necessarily an actual such code. The usual Delsarte version requires equality at \(q_0=c\); a feasible \(q\) with smaller diagonal can be mixed with the point mass at distance zero to reach equality, decreasing its distortion and preserving every Krawtchouk inequality.

**Theorem.** Let \(1/(n+1)\le c\le 1/2\) if \(n\) is odd, and \(1/n\le c\le1/2\) if \(n\) is even. For each integer \(s\in\{2,\ldots,n\}\) with \(s\equiv n\pmod2\), set
\[
 x=s/n,\qquad y=\frac{s^2-n}{n(n-1)},\qquad
 f_c(x)=\frac{c+(1-c)y}{x+y},\qquad
 u=\min_s f_c(s/n).
 \tag{3}
\]
Then
\[
 D(n,c)=2(1-c)-u ,
 \quad (q_0,q_1,q_2)=(c,u,1-c-u),\quad q_j=0\ (j\ge3)
 \tag{4}
\]
is an optimizer. To evaluate \(u\), form
\[
 x_*=\frac{c+\sqrt{c-(1-c)/n}}{1-c}.
 \tag{5}
\]
Clip \(x_*\) to the interval of allowable \(s/n\) and compare at most the two grid neighbors bracketing it. This includes real caps, not just powers of two. In particular it gives the quantum converse
\[
 P^{Q,\mathrm{avg},\mathrm{opt}}_{n,n-k}
 \le \tfrac12\left(1+\sqrt{1-\frac{2D(n,2^{-k})}{n}}\right)
 \qquad(k\ge3,\ n\ge2^k-1).
 \tag{6}
\]
The expression on the right is exactly the bound delivered by (2), not a claim that a quantum code attains it. The scalar fraction/critical point has a close antecedent in Yu–Tan's different tail-mass objective; see SOURCES.md. The new certificate below is the all-distance affine majorant proving exactness for the mean-distance objective.

## 2. A pointwise dual inequality

Fix \(r=(n+s)/2\) where \(2\le s\le n\) has the correct parity. For brevity write \(b_j=\kappa_r(j)\), and \(x,y\) as in (3). Thus \(b_0=1,\ b_1=-x,\ b_2=y\), and
\[
 b_3=\frac{s(3n-2-s^2)}{n(n-1)(n-2)}. \tag{7}
\]
The sign-product interpretation gives \(|b_j|\le1\) and the reflection \(|b_{n-j}|=|b_j|\), by taking subset complements. It also gives
\[
 (n-j)b_{j+1}=-s b_j-j b_{j-1}\qquad(1\le j<n).
 \tag{8}
\]
Indeed, for a uniform \(j\)-subset \(B\) of the sign list, multiply its entire sign product by the sum of signs over the complement. This is \((n-j)b_{j+1}\) in expectation. The sum over all \(n\) signs is \(-s\), and each inside sign times the product removes one factor, giving \(j b_{j-1}\) for the inside part. Equation (7) also follows by using (8) at \(j=2\).

The key inequality is
\[
 b_j\le L_j:=(j-2)x+(j-1)y\qquad(1\le j\le n).
 \tag{9}
\]
At \(j=1,2\) there is equality. The line is increasing, since
\[
 x+y=\frac{(s-1)(n+s)}{n(n-1)}>0.
\]
For \(s\ge3\), we first prove \(\max\{|b_2|,|b_3|\}\le L_3=x+2y\). If \(y\ge0\), \(|b_2|\le L_3\) and \(|b_3|\le x\): the latter follows from \(|3n-2-s^2|\le(n-1)(n-2)\) for \(n\ge6,\ s\le n\). If \(y<0\), then \(x+3y\ge0\), as its numerator with denominator \(n(n-1)\) is \((s-3)n+3s^2-s\). This gives \(|b_2|\le L_3\). In this case \(n>s^2\), so \(b_3>0\), and with the same denominator \(b_3\) has numerator \(s(3n-2-s^2)/(n-2)\le3s\). The numerator of \(L_3\) is \((s-2)n+2s^2-s\ge n\ge3s\), giving the remaining bound.

Put \(J=(n-s)/2\). For \(3\le j\le J\), the sum of the absolute recurrence weights in (8) is \((s+j)/(n-j)\le1\). The base \(b_2,b_3\) thus bounds \(|b_j|\) by \(L_3\) up to \(J+1\) if that interval is nonempty. For every \(j\ge J+2\), use
\[
 L_{J+2}=1+\frac{(s-3)(n^2-s^2)}{2n(n-1)}\ge1.
\]
This covers all \(j\ge3\), including \(J\le1\).

If \(s=2\), \(n\) is even. Here \(b_3=L_3=6/[n(n-1)]\), and \(L_j=((j-3)n+2j)/[n(n-1)]\). The same recurrence, starting at \(b_2,b_3\), controls the absolute values at indices from 2 to \(n/2\), since \(s+j\le n-j\) for all recurrence steps up to \(j=n/2-1\). By reflection this controls every \(j\) from 2 to \(n-2\) by \(\max(n-4,6)/[n(n-1)]\), which is at most \(L_4=(n+8)/[n(n-1)]\). Use the exact value at \(j=3\), and the latter bound for \(4\le j\le n-2\). At \(j=n-1\) use \(|b_{n-1}|=2/n\le L_{n-1}\), and at \(j=n\) use \(|b_n|=1=L_n\). This completes (9).

Extend \(L_j\) to \(j=0\) by its formula \(L_0=-2x-y\), and lift its value there to 1. For any feasible \(q\), (9) and the \(r\)-th inequality in (2) give
\[
 0\le\sum_j q_j b_j
 \le -2x-y+(x+y)\sum_j j q_j + (1+2x+y)q_0.
 \tag{10}
\]
The coefficient of \(q_0\) is positive: \(1+2x+y=1+x+(x+y)>0\). With \(q_0\le c\) this is
\[
 \sum_j j q_j\ge 2(1-c)-f_c(x).
 \tag{11}
\]
One can choose whichever row gives the largest lower bound.

## 3. Matching primal and grid minimizer

For a general row \(r\), let \(s=2r-n\), now possibly negative, and define \(x,y\) by (3). The above cap assumption ensures \(c+(1-c)y\ge0\) for every row. Indeed the minimum \(y\) on the grid is \(-1/(n-1)\) for even \(n\) and \(-1/n\) for odd \(n\). In a row with \(x+y\le0\), this nonnegativity suffices for
\[
 \sum_j q_j\kappa_r(j)=c+(1-c)y-u(x+y)\ge0.
\]
The rows with \(x+y>0\) are exactly \(s>1\), by the factored expression for \(x+y\); in them the inequality holds by the definition of \(u\). All fractions used in the minimum are nonnegative, and the row \(s=n\) gives \(u\le1/2\le1-c\). Thus the vector in (4) is feasible and saturates (11) in a minimizing row. This proves (4), including the case of tied minimizing rows.

For completeness, on \(x>1/n\) the fraction in (3) is
\[
 f_c(x)=\frac{(1-c)n x^2+cn-1}{(x+1)(nx-1)}.
\]
Its derivative has the sign of \((1-c)n x^2-2cnx-(cn-1)\). At \(x=1/n\) this polynomial is \((n+1)(1-c(n+1))/n\le0\). The larger root is (5) and the smaller root is at or below \(1/n\). Thus \(f_c\) is decreasing up to \(x_*\) and increasing afterwards on the relevant interval, allowing the degenerate case where \(x_*\) is at the endpoint and the whole interval is on one side. The two grid neighbors suffice.

## 4. Connecting to quantum codes

We reproduce the standard reduction here to identify precisely the metric and cap. A QRAC encodes each \(x\in\{0,1\}^n\) as a density operator \(\rho_x\) on a space of dimension at most \(2^m\). For each coordinate it has a POVM predicting that bit. \(P\) denotes the success probability averaged over independent uniform input and coordinate. Let \(\bar\rho=2^{-n}\sum_x\rho_x\), and consider the full-string pretty good measurement \(E_y=2^{-n}\bar\rho^{-1/2}\rho_y\bar\rho^{-1/2}\), using inverses on its support. This is a POVM there. Let \(q_j=\Pr(d_{\rm H}(X,Y)=j)\) from this measurement.

The diagonal probability is at most \(2^{-n}\sum_y\operatorname{Tr} E_y\le2^{m-n}\), since \(\rho_y\preceq I\). The transition matrix \(T_{xy}=\operatorname{Tr}(\rho_x E_y)\) is positive semidefinite: it is \(2^{-n}\) times the matrix of Hilbert–Schmidt inner products of the Hermitian operators \(\bar\rho^{-1/4}\rho_x\bar\rho^{-1/4}\). For each parity function \(s_A(x)=(-1)^{\sum_{i\in A}x_i}\), this gives \(\mathbb E[s_A(X)s_A(Y)]\ge0\). Averaging over \(r\)-subsets \(A\) is the \(r\)-th inequality in (2), by counting the intersection of \(A\) with the \(j\) differences; equivalently a random \(j\)-subset intersects fixed \(A\) in the same hypergeometric law. Thus the PGM distortion is at least \(D(n,c)\).

We also need the upper bound on that same distortion. Summing \(E_y\) over all outcomes with fixed bit \(b\) at coordinate \(i\) gives the one-bit PGM for the two conditional density operators \(\rho_{i,0},\rho_{i,1}\), with equal priors and common average \(\bar\rho\). Write \(A_i=(\rho_{i,0}-\rho_{i,1})/2\), so the optimal bias for a direct bit measurement is \(\|A_i\|_1\) (use the sign observable). The PGM bias at this coordinate is \(\operatorname{Tr}(A_i\bar\rho^{-1/2}A_i\bar\rho^{-1/2})\). This is at least \(\|A_i\|_1^2\): pair \(\bar\rho^{-1/4}A_i\bar\rho^{-1/4}\) with \(\bar\rho^{1/4}\operatorname{sgn}(A_i)\bar\rho^{1/4}\) in Hilbert–Schmidt Cauchy–Schwarz. With \(S=\operatorname{sgn}(A_i)\), the second squared norm is \(\operatorname{Tr}(\bar\rho^{1/2}S\bar\rho^{1/2}S)\le\|\bar\rho^{1/2}\|_2\|S\bar\rho^{1/2}S\|_2\le1\), where \(\|\cdot\|_2\) is the Hilbert–Schmidt norm. Singular averages are harmless because the states are supported on \(\operatorname{supp}\bar\rho\). Each original coordinate bias \(2p_i-1\) has absolute value at most \(\|A_i\|_1\). Averaging their squares and using Jensen gives
\[
 D(n,c)\le\mathbb E[d_{\rm H}(X,Y)]
 \le \frac n2\bigl(1-(2P-1)^2\bigr).
 \tag{12}
\]
This implies (6), and uses only uniform average success. This reduction is due to Lin–de Wolf and Tan–Jafar; our result evaluates its relaxation, not its operational tightness.

## 5. Consequences and boundaries

**The quantum high-rate leading constant.** Let \(k\ge3\), \(c=2^{-k}\), and \(n\ge2^k-1\). The cap is admissible: at odd \(n\) this is immediate, and even \(n\ge 2^k-1\) implies \(n\ge2^k\). Put \(a=\sqrt c\). We can choose an allowable \(s\) with \(a\le s/n<a+2/n\le2a\), since \(an\ge (1-c)/a>1\) and \(2/n\le2c/(1-c)\le a\) in this range. Then \(x+y\ge a-1/(n-1)\ge a/2\), using \(1/(n-1)\le c/(1-2c)\le 4c/3\). Meanwhile \(c+(1-c)y\le c+\frac{n}{n-1} 4c<6c\). Consequently \(u\le12\sqrt c\), giving \(D(n,c)=2-O(\sqrt c)\) along any such sequence with \(k\to\infty\). Equation (6) and \(1-\sqrt{1-t}\ge t/2\) yield \(n(1-P^{Q,\mathrm{avg},\mathrm{opt}})\ge D(n,c)/2\).

The matching positive construction is classical. At length \(N=2^k-1\), take the binary linear Hamming code with parity-check columns consisting of all nonzero \(k\)-bit vectors, so its rank is \(k\). For each input prefix correct the zero syndrome by doing nothing and every other syndrome by flipping its unique indicated coordinate. Encode the recovered codeword by \(N-k\) bits and copy the other \(n-N\) bits verbatim. The decoder reconstructs the indicated bit of that full classical representative, so the number of wrong bits is 0 on syndrome zero and 1 otherwise. The syndrome is uniform under uniform input, giving \(P^{C,\mathrm{avg},\mathrm{opt}}\ge 1-(1-c)/n\). It is exactly this value classically: for average success stochastic encoders and decoders can be made deterministic, by taking a maximizing deterministic best response for one and then for the other. Each of at most \(2^{n-k}\) messages denotes one complete decoded string. At least a \(1-c\) fraction of inputs differ from their decoded string, hence the mean Hamming error is at least \(1-c\). Embedding classical messages as orthogonal quantum states proves
\[
 \frac{D(n,c)}2\ \le n(1-P^{Q,\mathrm{avg},\mathrm{opt}}_{n,n-k})\ \le 1-c.
 \tag{13}
\]
Thus for every sequence \(k\to\infty,\ n\ge2^k-1\), the optimum quantum average bit error is \((1+o(1))/n\). This does not assert a worst-case bit success guarantee for the deterministic covering construction.

**Fixed redundancy and a limitation of this relaxation.** At fixed \(k\ge3\), (5) tends to \(a/(1-a)\) with \(a=2^{-k/2}\). Evaluating at neighboring grid points in (3) gives \(u\to2a(1-a)\) and \(D(n,c)\to2(1-a)\). At \(k=3\) the relaxation falls strictly below the \(3/2\) distortion needed to establish the square-root bound by (12), for every \(n\ge7\). In fact \(f_{1/8}(x)>1/4\) is equivalent to \(1-2x+5y>0\), whose numerator with denominator \(n(n-1)\) is
\[
 5s^2-2(n-1)s+n(n-6).
\]
Its discriminant is \(4(-4n^2+28n+1)<0\) for \(n\ge8\), and for \(n=7\) both real roots lie below the first admissible \(s=3\). The strict gap for (2) is a limitation of those LP inequalities only, not a counterexample QRAC at redundancy three. The separate exact small case \((n,m)=(6,3)\) is already in the Tan–Jafar long version.

When \(k\ge4,\ n\ge2^k-1\), the same known Hamming construction (and padding) actually lies above the square-root formula: write \(b=1-c\); then \(1-2b/n>0\) and
\[
 (1-2b/n)^2-(1-k/n)=(k-4b)/n+4b^2/n^2>0.
\]
This is a scope comparison with that older conjecture, not the source of the new converse. The Hamming-length boundary cases and the known \(n-m=1,2\) exact optima are not recast as new results here.
