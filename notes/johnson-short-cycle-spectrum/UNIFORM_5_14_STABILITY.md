# Dimension-uniform quantitative stability of the sharp Johnson 5/14 law

**Research supplement, 8 October 2026.** The [universal sharp theorem](ALL_RANK_SHARP_FIVE_FOURTEENTHS.md) proves, for every degree \(n\ge6\), that the best single-atom to total-variation coefficient under uniform image marginals on every subset rank (equivalently, on the single middle rank) equals \(5/14\). This note proves a **dimension-independent quantitative rigidity theorem for every near-extremizer**. It identifies a universal rational noncontact gap \(1/250\), converts the atom/TV deficit into a bound on probability mass outside four explicitly identified conjugacy classes, controls the masses of those classes by an exactly invertible \(2\times2\) moment system, and controls the conjugation average of the entire signed perturbation. All assertions apply to arbitrary noncentral laws; only the last, symmetrized conclusion passes to the conjugation average.

The finite lemma has a publicly replayable *optimizer-free* integer certificate and an independent exact rational scalar checker. No numerical-optimization output or historical novelty assertion is used.

## 1. Main stability statement

Let \(G=S_n\), \(n\ge6\), let \(u\) be uniform on \(G\), and let \(\nu\) be any probability law with the uniform subset-image marginals of the middle-rank action on \(\lfloor n/2\rfloor\)-sets. By the injective inclusion-matrix theorem in the [sharp paper](ALL_RANK_SHARP_FIVE_FOURTEENTHS.md#5-one-middle-subset-rank-suffices), this is equivalent to uniform marginals at every subset rank, **without assuming centrality**.

Let \(v=\nu-u\) and \(\delta=\|v\|_{\mathrm{TV}}>0\). Assume its identity-atom defect has the **positive orientation**, \(v(e)\ge0\), and put

\[
\eta=\frac5{14}-\frac{v(e)}{\delta}\in[0,5/14].
\tag{1}
\]

Write \(v_+,v_-\) for the positive and negative Jordan parts of \(v\), each of mass \(\delta\). Denote the following disjoint conjugacy classes by

\[
I=\{e\},\quad K=\{4\,1^{n-4}\},\quad
T=\{2\,1^{n-2}\},\quad E=\{3^2\,1^{n-6}\}.
\]

Put \(H=I\cup K\), \(L=T\cup E\), and define the *normalized off-contact leakage*

\[
R=\frac{v_+(G\setminus H)+v_-(G\setminus L)}{\delta}.
\tag{2}
\]

Finally let \(P=(5/14)U_I+(9/14)U_K\) and
\(Q=(6/7)U_T+(1/7)U_E\) be the exact attaining central laws, where \(U_C\) denotes uniform probability on a conjugacy class. Let \(\mathcal A v=|G|^{-1}\sum_{\sigma\in G}(\sigma v\sigma^{-1})_*\) be the conjugation average of the signed measure \(v\).

**Theorem 1 (universal quantitative sharp-support stability).** For **every \(n\ge6\)** and every \(\nu\) as above,

\[
\boxed{R\le250\,\eta.}
\tag{3}
\]

The positive identity mass and negative transposition mass are rigid with **explicit dimension-free errors**:

\[
\boxed{
\begin{aligned}
\left|\frac{v_+(I)}{\delta}-\frac5{14}\right|
&\le\frac{531}{70}R
\le\frac{132750}{70}\eta,\\[3pt]
\left|\frac{v_-(T)}{\delta}-\frac67\right|
&\le\frac{451}{35}R
\le\frac{112750}{35}\eta.
\end{aligned}}
\tag{4}
\]

In addition, the conjugation average of the *whole* signed perturbation is close to the uniquely sharp central direction:

\[
\boxed{
\left\|\mathcal A v-\delta(P-Q)\right\|_{\mathrm{TV}}
\le\frac{1503}{70}R\,\delta
\le\frac{375750}{70}\eta\,\delta.}
\tag{5}
\]

The total-variation norm in (5) is the half-\(\ell^1\) norm of a mass-zero signed measure, and the constants hold uniformly in \(n\). In particular, if \(\eta=0\), then \(R=0\), the four class masses are *exactly* those of \(P,Q\), and \(\mathcal A v=\delta(P-Q)\). This recovers the equality-support theorem but also controls every near-extremizer quantitatively.

For any prescribed atom \(\sigma\), first left-translate \(\nu\) by \(\sigma^{-1}\); the result applies with the same constants. A negative atom deviation is reduced to the opposite Jordan orientation by replacing \(v\) by \(-v\) at the level of the signed perturbation. The theorem does **not** claim that individual *noncentral* densities inside \(K,T,E\) become uniform without averaging.

## 2. A uniform strict rational gap for every noncontact permutation

We use the independent **small-denominator five-point dual** from the [sharp theorem, Section 11](ALL_RANK_SHARP_FIVE_FOURTEENTHS.md#11-a-second-smaller-denominator-rational-dual-proof). Define

\[
(q_1,\ldots,q_5)=\left(\tfrac12,\tfrac13,\tfrac14,\tfrac15,\tfrac16\right),
\quad D=30625,
\quad
(\beta_i)=(4036494,-10841250,13334928,-8850625,2344953).
\]

For each \(g\in S_n\), let \(m_\ell(g)\) denote the number of cycles of length \(\ell\), and put

\[
U_q(g)=\prod_{\ell\ge1}(q^\ell+(1-q)^\ell)^{m_\ell(g)},\qquad
\Phi(g)=\sum_{i=1}^5\frac{\beta_i}{D}\,(1-U_{q_i}(g)).
\tag{6}
\]

It is an admissible orbit-averaged dual because \(U_q\) is a rational linear combination of invariant-subset counts; all such counts have the same expectation under \(\nu\) and \(u\).

The sharp proof establishes \(\Phi(e)=0\) and \(9/14\le\Phi(g)\le1\) for all \(g\ne e\), with precise contacts: \(\Phi=1\) **only** for a single 4-cycle, and \(\Phi=9/14\) **only** for a single 2-cycle or two disjoint 3-cycles, with any number of fixed points.

**Lemma 2 (uniform certified noncontact gap).** These strict, *quantitative* inequalities hold for **every finite degree**:

\[
\begin{aligned}
g\notin I\cup K
&\Longrightarrow h(g)\le1-\frac1{250},\\
g\notin T\cup E
&\Longrightarrow h(g)\ge\frac9{14}+\frac1{250},
\end{aligned}
\qquad h(g)=\mathbf1_{\{g=e\}}+\Phi(g).
\tag{7}
\]

*Proof.* As fixed points contribute factor one to every \(U_q\), it is enough to classify the nontrivial cycle partition \(\lambda\) of the number \(M\) of moved points.

For \(2\le M\le43\), define the exact integer numerator and denominator of \(\Phi(\lambda)\) as in the sharp paper: let \(S=60\), \(q_i=r_i/s_i\), and

\[
\begin{aligned}
N_i(\lambda)&=\prod_{\ell\in\lambda}
(r_i^\ell+(s_i-r_i)^\ell),\\
A(\lambda)&=\sum_i\beta_i
\left(S^M-N_i(\lambda)(S/s_i)^M\right),\\
B(\lambda)&=D S^M.
\end{aligned}
\tag{8}
\]

Then \(\Phi(\lambda)=A(\lambda)/B(\lambda)\), with both integers and \(B(\lambda)>0\). The separate [stability gap checker](check_allrank_stability_gap.py) independently exhausts **all 63,260** nonincreasing partitions \(\lambda\) of sizes \(2,\ldots,43\) whose parts are at least two. Besides rechecking the sharp bound, it enforces the two *stronger exact integer inequalities*:

\[
\lambda\notin\{(2),(3,3)\}
\Longrightarrow
14\cdot250\,A(\lambda)
\ge(9\cdot250+14)B(\lambda),
\tag{9}
\]

\[
\lambda\ne(4)
\Longrightarrow
250A(\lambda)\le249B(\lambda).
\tag{10}
\]

There are no floating-point tolerances, solver outputs, or untested partitions in this range; every comparison is a literal integer inequality. The publicly pinned replay passes all of them.

For \(M\ge44\), the analytical power-mean estimate in the sharp theorem shows, using the single checked rational tail bound,

\[
\frac{33}{50}<\Phi(g)<\frac{47}{50}.
\tag{11}
\]

Both endpoints are **strictly** more than \(1/250\) from the corresponding contact values, since

\[
\frac{33}{50}-\frac9{14}=\frac3{175}>\frac1{250},
\qquad 1-\frac{47}{50}=\frac3{50}>\frac1{250}.
\]

At the identity, \(h(e)=1\), the unique upper contact in \(I\); all nonidentity contacts are handled as stated. Thus (7) holds for every group element at every degree. QED.

## 3. Exact atom-deficit decomposition

Because \(v\) annihilates \(U_{q_i}\), \(\Phi\), and constants, one has \(\int h\,dv=v(e)\). The total masses of \(v_+\) and \(v_-\) both equal \(\delta\), so

\[
\begin{aligned}
\frac5{14}\delta-v(e)
&=\delta-\int h\,dv_+
+\int h\,dv_- -\frac9{14}\delta\\
&=\int_G(1-h)\,dv_+
+\int_G(h-\tfrac9{14})\,dv_-.
\end{aligned}
\tag{12}
\]

Both integrands are nonnegative by the sharp dual theorem. By the uniform strict inequalities (7), the right-hand side is at least

\[
\frac1{250}
\left(v_+(G\setminus H)+v_-(G\setminus L)\right).
\]

Divide by \(\delta>0\), use (1)--(2), and obtain \(R\le250\eta\), proving (3). Notice this is an *exact defect identity*, not a compactness or continuity argument. QED.

## 4. An invertible two-moment system controls the four class masses

Put

\[
x=\frac{v_+(I)}{\delta},\qquad
y=\frac{v_-(T)}{\delta},\qquad
p=\frac{v_+(G\setminus H)}{\delta},\qquad
q=\frac{v_-(G\setminus L)}{\delta}.
\]

Thus \(p+q=R\), \(v_+(K)/\delta=1-p-x\), and \(v_-(E)/\delta=1-q-y\). For a fixed evaluation parameter \(\theta\in(0,1)\), define \(u_C=U_\theta(g)\) at any \(g\) in class \(C\). Since each \(U_\theta\in[0,1]\), the moment equation \(\int U_\theta\,dv=0\) rearranges to

\[
(1-u_K)x+(u_E-u_T)y=u_E-u_K+\varepsilon_\theta,
\qquad|\varepsilon_\theta|\le p+q=R.
\tag{13}
\]

Indeed, the error is the sum over normalized off-contact positive mass of \((u_K-U_\theta)\), plus the sum over normalized off-contact negative mass of \((U_\theta-u_E)\), each integrand in \([-1,1]\). This argument is valid for noncentral laws.

Set \(s=\theta(1-\theta)\). Direct expansion of (6) gives

\[
u_I=1,\quad u_T=1-2s,\quad
u_K=1-4s+2s^2,\quad
u_E=(1-3s)^2.
\tag{14}
\]

At \(\theta=1/2\) and \(1/6\), the two equations (13) have the exact common coefficient matrix

\[
A=\begin{pmatrix}
  7/8&-7/16\\
  335/648&-55/144
\end{pmatrix},
\qquad
\det A=-35/324\ne0.
\tag{15}
\]

The exact attaining classes from the sharp theorem solve (13) with zero error at \(x_0=5/14\), \(y_0=6/7\). Subtracting this exact solution therefore yields

\[
A\binom{x-x_0}{y-y_0}
=\binom{\varepsilon_{1/2}}{\varepsilon_{1/6}},
\quad |\varepsilon_{1/2}|,|\varepsilon_{1/6}|\le R.
\]

The two absolute row sums of \(A^{-1}\) are **exactly** \(531/70\) and \(451/35\), respectively. Hence

\[
|x-x_0|\le\frac{531}{70}R,\qquad
|y-y_0|\le\frac{451}{35}R.
\tag{16}
\]

All four entries of \(A\), its determinant, and its inverse absolute row sums are independently checked by [the scalar certificate](check_allrank_stability_scalars.py) using only Fraction arithmetic. Combining (16) with (3) proves (4). QED.

## 5. Total-variation stability after conjugation averaging

Let \(\mathcal A\) denote averaging a signed measure over conjugation in \(S_n\). It is a positive mass-preserving contraction in total variation and maps any probability measure supported in a single conjugacy class to its uniform class law. Write the normalized Jordan pieces as

\[
\begin{aligned}
\mathcal A(v_+/\delta)
&=xU_I+(1-p-x)U_K+\mu_+,\\
\mathcal A(v_-/\delta)
&=yU_T+(1-q-y)U_E+\mu_-,
\end{aligned}
\tag{17}
\]

where \(\mu_\pm\) are nonnegative central measures of total masses \(p\) and \(q\). We do not assume their supports are disjoint from \(H,L\); they are simply the off-*appropriate*-contact contributions.

Subtract \(P-Q\) and regroup exactly:

\[
\begin{aligned}
\mathcal A(v/\delta)-(P-Q)
={}&(x-5/14)(U_I-U_K)
 +(6/7-y)(U_T-U_E)\\
&+(\mu_+-pU_K)+(qU_E-\mu_-).
\end{aligned}
\tag{18}
\]

Every parenthesized difference has total signed mass zero. The total-variation norm of a difference of two probability laws is at most 1, and that of a difference of two nonnegative measures of common mass \(a\) is at most \(a\). The triangle inequality therefore gives

\[
\left\|\mathcal A(v/\delta)-(P-Q)\right\|_{\rm TV}
\le|x-5/14|+|y-6/7|+p+q
\le\left(\frac{531}{70}+\frac{451}{35}+1\right)R
=\frac{1503}{70}R.
\tag{19}
\]

Multiply by \(\delta\) and apply (3) to obtain (5). QED.

For **central** \(\nu\), one has \(\mathcal A v=v\), so the conclusion controls the original signed law itself. For an arbitrary noncentral \(\nu\), (3)--(4) control its off-contact leakage and class totals, while (5) controls only its conjugation average; these are intentionally distinguished.

## 6. Reproduction, audit boundary, and further questions

The dimension-uniform noncontact gap is a computer-assisted *finite exact assertion*, supplied by an exhaustive 63,260-case integer checker and an independent elementary analytic bound for all remaining cycle shapes. The two-moment inverse is checked separately using Fraction arithmetic. To replay directly from the repository root:

~~~sh
python3 notes/johnson-short-cycle-spectrum/check_allrank_stability_gap.py
python3 notes/johnson-short-cycle-spectrum/check_allrank_stability_scalars.py
~~~

The first script accepts only literal integer inputs and checks every partition through 43 moved vertices, its unique contact shapes, and the exact rational tail for all moved counts at least 44. The second script independently verifies the moment matrix, determinant, and row-sum constants. Both have been independently fetched from immutable public Git commits and replayed successfully on the authorized VPS even when its default scratch filesystem was full, using read-only streaming execution.

The **mathematical deductions** (12)--(19) are displayed in full and do not depend on floating-point optimization. Source hashes and recorded outputs are in [VERIFICATION.md](VERIFICATION.md). No assertion is made that \(1/250\) or the stated Lipschitz constants are optimal; improving them, obtaining a conceptual no-enumeration proof of the strict dual separation, and classifying all noncentral exact extremizers remain separate problems. There is no external referee or priority claim.
