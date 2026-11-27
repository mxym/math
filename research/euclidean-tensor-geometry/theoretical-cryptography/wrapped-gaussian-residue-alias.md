# Exact alias exponents in a wrapped Gaussian residue simulation

## Model and relevance

In the statistical step of [Lyubashevsky–Peikert–Regev, Lemmas 4.7–4.8](https://sites.cc.gatech.edu/fac/cpeikert/pubs/ideal-lwe.pdf) and [Peikert–Regev–Stephens-Davidowitz, Lemma 6.8](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf), a labeled discrete Gaussian and an ordinary Gaussian are combined, with the output ultimately read on a torus. A correct unwrapped estimate remains an upper bound after reduction modulo the output lattice, but need not describe the actual statistical loss. This note solves that **standalone centered noise comparison** at simultaneously large Gaussian scales for fixed lattices and matrices. No secret, cryptanalytic procedure, real parameter set, or new computational hardness reduction is considered.

Let \(L_0\subset L\subset\mathbb R^d\) be full lattices of finite index, \(\Gamma\) a full output lattice, \(A,B\succ0\) real symmetric matrices, \(M:\mathbb R^d\to\mathbb R^d\) a fixed real linear map. Let \(G_K\) denote the continuous Gaussian of density proportional to \(e^{-\pi x^\mathsf T K^{-1}x}\), so its covariance is \(K/(2\pi)\). For scale \(\lambda>0\) choose \(X_\lambda\) on \(L\) with weights proportional to \(e^{-\pi x^\mathsf T A^{-1}x/\lambda}\), and \(G_{\lambda B}\) independently. We compare laws on
\[
\mathcal G=(L/L_0)\times(\mathbb R^d/\Gamma):
\qquad
P_\lambda=\mathcal L\bigl(Z=X_\lambda\bmod L_0,\ (MX_\lambda+G_{\lambda B})\bmod\Gamma\bigr),
\]
\[
Q_\lambda=U_{L/L_0}\otimes(G_{\lambda S}\bmod\Gamma),
\qquad S=MAM^\mathsf T+B.
\]
All copies in a batch below are independently generated, with no shared random choice of covariance. All densities and \(L^p\) norms on \(\mathcal G\) use probability Haar measure. We write \(\|v\|_A^2=v^\mathsf T A v\) and use Euclidean dual lattices.

## 1. Exact signed-frequency formula, with positive discrepancies

The characters of \(\mathcal G\) are
\[
\chi_{\bar k,z}(\ell,y)=\exp(2\pi\mathrm i(z\cdot y-k\cdot\ell)),
\quad \bar k\in L_0^*/L^*,\ z\in\Gamma^*.
\]
Use coefficients with the conjugate of this character. Poisson summation on the centered \(L\) Gaussian and the characteristic function of \(G_{\lambda B}\) give
\[
\widehat P_\lambda(\bar k,z)
=\frac{\sum_{k'\in k+L^*}e^{-\pi\lambda E(k',z)}}{D_\lambda},\qquad
E(k,z)=\|k-M^\mathsf Tz\|_A^2+\|z\|_B^2,\qquad
D_\lambda=\sum_{w\in L^*}e^{-\pi\lambda\|w\|_A^2}.
\tag{1}
\]
For example the conjugate character first produces the Gaussian transform at \(M^\mathsf Tz-k\); dual shifts \(w\in L^*\) give the stated coset in the numerator. The ideal law has \(\widehat Q_\lambda(\bar k,z)=\mathbf 1_{\bar k=0}e^{-\pi\lambda\|z\|_S^2}\). Both expansions are absolutely summable for each fixed \(\lambda>0\), since the map
\((k,z)\mapsto(A^{1/2}(k-M^\mathsf Tz),B^{1/2}z)\) is invertible, with a lattice image.

For a nonzero label character \(\bar k\), (1) is already exactly the discrepancy. For \(\bar k=0\), putting \(u=M^\mathsf Tz\), the subtraction removes the \(k'=0\) summand and pairs \(k'\) with \(-k'\) in the rest. The pair contribution is zero if \(\langle k',Au\rangle=0\), and for the representative having positive inner product it equals
\[
e^{-\pi\lambda E(k',z)}
\bigl(1-e^{-2\pi\lambda\langle k',Au\rangle}\bigr)^2/D_\lambda.
\tag{2}
\]
Indeed the two Gaussian exponents of the pair are \(c-d,c+d\) with \(c=\|k'\|_A^2+\|z\|_S^2\) and \(d=2\langle k',Au\rangle\), and the reference subtracts \(2e^{-\pi\lambda c}\). Thus every Fourier coefficient of \(P_\lambda-Q_\lambda\) is real and nonnegative, and is zero at the trivial character. In particular the supremum of its absolute Haar-density discrepancy is exactly the sum of the nonconstant coefficients: all characters align at the group origin. This nonnegativity uses centered \(X_\lambda\); arbitrary shifted inputs can introduce phases and are not covered by the sharp statements below.

## 2. The exact total-variation exponent and constant

Call \((k,z)\in L_0^*\times\Gamma^*\) **admissible** if either \(k\notin L^*\), or \(k\in L^*\) and \(\langle k,A M^\mathsf Tz\rangle>0\). Let
\[
e_*=\min_{\mathrm{admissible}\ (k,z)} E(k,z).
\tag{3}
\]
If the set is empty, (1)–(2) show \(P_\lambda=Q_\lambda\) exactly. Otherwise \(e_*>0\), the minimum is attained at finitely many points, and the next distinct energy has a positive gap by discreteness of the lattice image. Define the real Fourier polynomial
\[
F=\sum_{\substack{(k,z)\ \mathrm{admissible}\\E(k,z)=e_*}}\chi_{\bar k,z}.
\tag{4}
\]
Repeated characters are counted with their multiplicity; the sum is nonzero, since none is trivial and none cancels. There exists \(\eta>0\), depending only on the fixed data, such that
\[
\|p_\lambda-q_\lambda-e^{-\pi\lambda e_*}F\|_\infty
=O(e^{-\pi\lambda(e_*+\eta)}).
\tag{5}
\]
For the terms off the leading shell this follows by factoring out their minimum energy and bounding the remaining lattice Gaussian at a fixed positive scale. For the finitely many leading terms (2), each positive inner product provides a strictly positive correction exponent, and \(D_\lambda=1+O(e^{-\pi\lambda\min_{w\in L^*\setminus0}\|w\|_A^2})\). These facts prove (5), even when positive inner products far from the leading shell do not have a uniform lower bound.

Consequently the exact first-order statistical error is
\[
d_{\rm TV}(P_\lambda,Q_\lambda)
=\tfrac12\|F\|_1 e^{-\pi\lambda e_*}
+O(e^{-\pi\lambda(e_*+\eta)}).
\tag{6}
\]
There is no generic statement that the unwrapped posterior width alone determines \(e_*\): the admissibility and joint energies depend on the output dual lattice. Formula (6) is an asymptotic at fixed \(A,B,M,L,L_0,\Gamma\), not a dimension-uniform estimate for arbitrary growing rings.

## 3. When the unwrapped exponent survives wrapping

Assume in this section that \(M\) is invertible, and set
\[
C=(A^{-1}+M^\mathsf T B^{-1}M)^{-1}
=A-AM^\mathsf T S^{-1}MA,\qquad e_C=\min_{k\in L_0^*\setminus0}\|k\|_C^2.
\]
In the unwrapped experiment, completing the square yields likelihood ratio \(h_{\lambda C,L_0}(AM^\mathsf TS^{-1}Y-Z)/D_\lambda\), where \(h_{K,\Lambda}\) is the wrapped \(G_K\) density relative to Haar on \(\mathbb R^d/\Lambda\). This follows by summing the joint Gaussian over a fixed residue class; the covolumes cancel because the reference residue is uniform. Under the reference the phase density is \(h_{\lambda(A-C),L}\), pulled back to the finer-period torus \(\mathbb R^d/L_0\), because averaging over \(L/L_0\) kills all frequencies outside \(L^*\). Since \(A-C\succ0\), this is \(1+O(e^{-\pi\lambda\eta_0})\) uniformly for some \(\eta_0>0\). Moreover \(\min_{w\in L^*\setminus0}\|w\|_A^2>e_C\), because \(C\prec A\) and \(L^*\subset L_0^*\). The first shell of \(h_{\lambda C,L_0}-1\) therefore gives an exact positive leading TV constant times \(e^{-\pi\lambda e_C}\) in the unwrapped model.

The joint wrapped energy has the identity
\[
E(k,z)=\|k\|_C^2+\|z-S^{-1}MA k\|_S^2 .
\tag{7}
\]
This gives a **necessary and sufficient resonance condition** for wrapping not to improve the exponent:
\[
\boxed{\quad e_*=e_C
\quad\Longleftrightarrow\quad
S^{-1}MA k\in\Gamma^*
\ \text{for some shortest nonzero }k\text{ for }C\text{ on }L_0^*.\quad}
\tag{8}
\]
Indeed any admissible \(k\) is nonzero; equality in (7) requires both conditions. Conversely for such a \(k\), choosing \(z=S^{-1}MA k\) gives a nonzero \(z\) and positive \(\langle k,A M^\mathsf Tz\rangle\), so the pair qualifies even when \(k\in L^*\). If no resonance is possible, \(e_*>e_C\). More quantitatively, if \(e_{C,2}\) is the next squared \(C\)-length and \(K_C\) the finite first shell, then
\[
e_*\ge\min\left(e_{C,2},\,e_C+\min_{k\in K_C}\operatorname{dist}_S(S^{-1}MA k,\Gamma^*)^2\right).
\]
This is a lower bound on the decaying exponent, not a blanket claim that every output wrapping helps by a common positive margin. For a resonant toy example take \(L_0=\Gamma=\mathbb Z\), \(L=q^{-1}\mathbb Z\), \(A=4\), \(B=1\), \(M=1/2\). Then \(C=2\) and the first-shell \(k=1\) has \(S^{-1}MAk=1\in\Gamma^*\), so wrapping does not improve the exponent (regardless of the finite index \(q\)).

## 4. Closed form for compatible ideal multiplication

Assume \(M\) invertible and \(M L_0\subseteq\Gamma\), equivalently \(M^\mathsf T\Gamma^*\subseteq L_0^*\). Let
\[
a=\min_{k\in L_0^*\setminus L^*}\|k\|_A^2\quad(\min\varnothing=+\infty),\qquad
b=\min_{z\in\Gamma^*\setminus0}\|z\|_B^2.
\]
Then
\[
e_*=\min(a,b)>e_C .
\tag{9}
\]
For \(z=0\) the only admissible case is the nonzero label, giving \(a\). For \(z\ne0\), \(E(k,z)\ge b\). Pick a shortest \(z\) for \(B\) and \(k=M^\mathsf T z\); this is admissible and realizes \(b\). Strictness compared with \(e_C\) follows because \(C\prec A\), and because at the indicated shortest output vector the second term in (7) is strictly positive: \(z-S^{-1}MA M^\mathsf T z=S^{-1}Bz\ne0\). Thus \(e_C<a,b\).

At \(a<b\) the leading \(F\) is just the label-shell polynomial; at \(b<a\) it is the output-shell polynomial evaluated at \(y-M\ell\). The latter substitution is well-defined by the same compatibility. At equality the two polynomials add, and their arguments \(\ell\) and \(y-M\ell\) are independent under product Haar. This also identifies the leading constant in the ties, not just the exponent. Equivalently in this case the actual wrapped value conditional on the label is exactly \(M\ell+G_{\lambda B}\bmod\Gamma\), because changing the latent point inside its label leaves its wrapped image unchanged. Formula (9) identifies the statistical error relative to the **ideal** independent comparison, not relative to a model that copies this conditional shift.

For example, let \(I,J\) be fractional ideals in a number field with its real Euclidean canonical embedding, and take \(L_0=\sigma(I)\), \(L=q^{-1}L_0\) for integer \(q\ge2\), \(\Gamma=\sigma(J)\). Use multiplication by a fixed nonzero \(\mu\) with \(\mu I\subseteq J\). Then \(L^*=qL_0^*\), and any shortest nonzero \(A\)-vector in \(L_0^*\) lies outside \(q L_0^*\), by dividing by \(q\) otherwise. So the two terms in (9) are the usual shortest squared dual lengths in \(A\) and \(B\); the exponent is independent of \(q\) in this compatible model, although the leading polynomial need not be. This is a valid ideal-ring specialization without replacing the canonical lattice by coefficient coordinates or assuming every multiplier from a reduction has the inclusion.

A separate one-dimensional illustration of **incompatibility** takes \(L_0=\Gamma=\mathbb Z\), \(L=q^{-1}\mathbb Z\) for fixed \(q\ge2\), \(A=a\), \(B=b\), \(M=m=r/d>0\) in reduced positive integers. For \(z>0\) any positive integer \(k\) is admissible, while \(k=0\) never is and negative \(k\) cannot improve on its reflection. Because \((r,d)\) is feasible with energy \(b d^2\), no \(z>d\) improves it, so
\[
e_*=\min\left(a,\ \min_{1\le z\le d}\bigl[bz^2+a\operatorname{dist}(rz/d,\mathbb Z_{\ge1})^2\bigr]\right).
\]
The competing straight lines in \(b/a\) describe exact shape changes of the leading shell in this toy model. In the integer case \(d=1\) the wrapped exponent is \(\min(a,b)\) while the unwrapped exponent is \(ab/(b+m^2a)\), strictly less. This illustrates that plain data processing of an unwrapped error bound can lose exponential accuracy.

## 5. Independent repetition budget

Suppose \(e_*\) is finite. Write \(s_\lambda=e^{-\pi\lambda e_*}\) and \(v=\|F\|_2^2>0\). The ideal Haar density \(q_\lambda\) tends uniformly and exponentially to one by its Gaussian Fourier series, so its likelihood ratio obeys
\[
h_\lambda=dP_\lambda/dQ_\lambda-1=s_\lambda(F+o(1))
\]
uniformly; in particular \(\mathbb E_{Q_\lambda} h_\lambda=0\), and \(\mathbb E h_\lambda^2\sim s_\lambda^2 v\). For \(N=N(\lambda)\) independent copies, if \(N s_\lambda^2 v\to t\in(0,\infty)\), the log-likelihood under \(Q_\lambda^{\otimes N}\) converges to \(\mathcal N(-t/2,t)\) (normal parameters mean and variance). The centered linear sum obeys the elementary triangular-array central limit theorem because all summands are \(O(s_\lambda)\); the sum of their squares tends to \(t\) in probability by its variance bound \(O(Ns_\lambda^4)\), and the Taylor remainders are \(O(Ns_\lambda^3)=o(1)\). Since \((1-e^x)_+\) is bounded and continuous, normal integration gives
\[
d_{\rm TV}(P_\lambda^{\otimes N},Q_\lambda^{\otimes N})
\longrightarrow 2\Phi(\sqrt t/2)-1 .
\]
Here \(\Phi\) is the standard normal CDF. If \(N s_\lambda^2\to0\) the TV goes to zero by the product \(\chi^2\) formula. If \(N s_\lambda^2\to\infty\), the affinity of one copy is \(1-s_\lambda^2v/8+o(s_\lambda^2)\) by the Taylor expansion of \(\sqrt{1+h_\lambda}\). Its \(N\)-fold product goes to zero, so TV goes to one. These are properties of comparisons of mutually independent simulations. They make no claim for an oracle with dependent samples or a common latent random parameter.

## Scope and replay

[Peikert, *An Efficient and Parallel Gaussian Sampler for Lattices*, Theorem 3.1](https://eprint.iacr.org/2010/088.pdf) and the cited LPR/PRS reductions use the standard mixed Gaussian completion and smoothing analysis. The [unwrapped joint-residue note](joint-residue-gaussian-smoothing.md) gives a sharper comparison in a product geometry, but has no output torus. The specific contribution here is the wrapped graph shell with cancellation (2), the exact resonance characterization (8), and the compatible ideal simplification (9). These estimates neither invalidate the unwrapped upper bound nor assert changes to a general Ring-LWE hardness theorem.

Run **node verify-wrapped-gaussian-residue-alias.js**. The verifier checks the character-selection identities, completion and compatible exponents on generated toy fixtures, and relative leading behavior by direct low-dimensional noise sums. The formulas, torus comparison, and asymptotic statements are analytic.
