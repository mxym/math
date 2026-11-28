# A joint ideal-by-ideal information converse for Ring-LWE search observations

A bound using only total noise entropy need not control whether all
coordinates of a hidden module element remain statistically identifiable.
We prove an all-samples information converse that retains the **joint
fluctuations of every ideal direction**. The coefficient rows can even be
selected adaptively. A four-element synthetic ring has two critical
constraints whose fluctuations are oppositely signed, forcing success
to tend to zero at a sample count at which either constraint separately
would only bound it by one half.

This is a necessary sample bound, not a computational hardness proof or
a method to recover the hidden element. It gives no classical
polynomial-time algorithm or implication for a concrete scheme.
[Lyubashevsky–Peikert–Regev, Definitions 3.1–3.5 and Theorem 4.1](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf)
formulate search for every hidden element and permitted error law in a
number-field torus. Theorem 4.1 reduces ideal discrete Gaussian sampling
to search for the bounded elliptical family, in quantum polynomial time
under the stated lower bound on the modulus-width product. The
separate search-to-decision Theorem 5.1 assumes the cyclotomic split
case and its specified decision prior. Their §3.1 already explains
statistical impossibility if the wrapped error becomes indistinguishable
from all of Haar.
[Peikert–Regev–Stephens-Davidowitz, Theorem 6.2](https://web.eecs.umich.edu/~cpeikert/pubs/rlwe-anyring.pdf)
give a quantum reduction directly to average-case **decision** for the
specified distribution, without algebraic restrictions on ring or modulus.
Neither theorem is a classical polynomial-time search algorithm.
Our model includes a fixed-error-law instance of the LPR observation
experiment, with a uniform hidden element for the lower bound, but does
not assume that the synthetic examples meet hardness-reduction
parameters.

For discrete no-feedback group codes, the use of a subgroup genie
followed by hypothesis testing is classical. In particular
[Pang–Pradhan–Mahdavifar, Theorem 3 and Appendix D](https://arxiv.org/html/2406.13243v1)
take a minimum of subgroup-wise hypothesis-testing bounds, and
[Como–Fagnani](https://dspace.mit.edu/entities/publication/32a7647f-3902-4e5d-b492-71fe7d75cd53)
study subgroup constraints at capacity for symmetric group channels.
We retain the joint event in an additive model, also with adaptive
coefficients and torus-valued outputs. The contrast with the
[module hashing spectrum](module-information-spectrum.md) is that
here the random input to the joint information densities is the
**noise**, and the direction \(J\) is a remaining hidden submodule,
not an output quotient to be made uniform.

## 1. A simultaneous converse, including adaptive coefficients

Let \(R\) be a finite unital ring, \(M\) a finite left \(R\)-module,
and \(\iota:M\hookrightarrow G\) an injective additive embedding in a
compact metrizable abelian group. The finite model has \(G=M\).
The dual number-field torus model uses
\(R=O_K/qO_K,\ M=O_K^\vee/qO_K^\vee,\ G=K_{\mathbb R}/O_K^\vee\),
and \(\iota(s)=s/q\bmod O_K^\vee\).
For \(S=(S_1,\ldots,S_n)\) uniform on \(M^n\), observe \(m\) samples
\[
            B_i=\iota\!\left(\sum_{j=1}^n A_{ij}S_j\right)+E_i,
                 \qquad E_i\stackrel{\mathrm{iid}}{\sim}\mu .
\]
Rows \(A_i\in R^n\) are public. They may be fixed, independent random
rows, or chosen using previous observations and independent randomness,
before the new \(E_i\) is drawn. The hidden element and innovations
are independent of the independent randomness. Include the entire
public history and relevant random seed in the transcript. The
ordinary scalar Ring-LWE case is \(n=1\); the fixed-\(R,M\), growing-\(n\)
limit below is a distinct module observation experiment.

For a subgroup \(H\le M\) write \(\mu_H=\mu*U_{\iota(H)}\), where
\(U_{\iota(H)}\) is the uniform probability on the indicated finite
group. Let
\[
       \ell_H(e)=\log\frac{d\mu}{d\mu_H}(e),\qquad
       d_H=\mathbb E_\mu \ell_H(E)=D(\mu\|\mu_H).
\]
Always \(\mu_H\ge\mu/|H|\), so the derivative exists and
\(\ell_H\le\log|H|\) at \(\mu\)-almost every point. Submodule sums
and intersections below are those of \(M\).
For each nonzero submodule \(J\), define the image subgroup
\(H_i(J)=\sum_j A_{ij}J\subseteq J\) of the \(i\)-th row. Let
\(\mathcal J\) be any finite collection of nonzero submodules.

**One-shot bound.** For every \(\gamma>0\), any guessing rule has
success probability at most
\[
 \Pr\!\left[
  \sum_{i=1}^m \ell_{H_i(J)}(E_i)>n\log|J|-\gamma
                   \text{ for every }J\in\mathcal J
       \right]+|\mathcal J|e^{-\gamma}.                              \tag{1}
\]
There is also the coefficient-independent form
\[
 \Pr\!\left[
  \sum_{i=1}^m \ell_J(E_i)>n\log|J|-\gamma
                   \text{ for every }J\in\mathcal J
       \right]+|\mathcal J|e^{-\gamma}.                              \tag{2}
\]
Neither right side necessarily dominates the other pointwise; (1)
uses the actual row images. With nonadaptive rows both versions hold
conditional on the fixed public matrix. The same statements apply
when the guessing rule is even given the true error law \(\mu\).
A uniform-prior obstruction also rules out a worst-case success guarantee
of the same size, since such a guarantee would hold on average.

For the proof, fix \(J\) and a reference law on the whole experiment:
keep the prior and the row policy, and at each step replace the error
by \(\mu_{H_i(J)}\), or by \(\mu_J\) for (2). In the reference, given
\(S\bmod J^n\), the transcript is independent of the uniform residual
part of \(S\). Indeed a difference between hidden elements with the
same quotient changes the signal in row \(i\) by an element of
\(\iota(H_i(J))\); the reference innovation is invariant under this
subgroup. This verifies the independence inductively even for a row
chosen from the earlier transcript. The reference success probability
is therefore at most \(|J|^{-n}\), whether or not the quotient was given
to the rule. The joint true-to-reference likelihood, on hidden
element and full transcript, is the product of the successive
\(d\mu/d\mu_{H_i(J)}\) evaluated at the underlying true residuals.
This follows from the chain rule of Radon–Nikodym derivatives,
since the conditional coefficient policy is unchanged. On the event
where its log is at most \(n\log|J|-\gamma\), the true probability of
success is at most \(e^{-\gamma}\). Use the union bound for these
intersections of success and small likelihood, retaining the common
joint event on all the remaining inequalities. This proves (1) and
(2). No pointwise bound on the estimator or time limit is involved.

A simpler consequence for each \(J\) is
\[
              \Pr[\mathrm{success}]
                   \le |J|^{-n}+\sqrt{m\,d_J/2}.                      \tag{3}
\]
The relative entropy of the true joint experiment to the full-\(J\)
reference is exactly \(m d_J\); apply Pinsker to the success event.
If \(d_J=0\) then no number of observations removes that reference
ambiguity. For (1), the corresponding relative entropy is
\(\sum_i \mathbb E d_{H_i(J)}\le m d_J\), since
\(d_H\le d_J\) for \(H\subseteq J\).
The latter monotonicity also follows from the entropy formula below.
In finite additive raw observations \(\mu\) may nevertheless be
globally far from uniform even if a particular \(d_J\) is tiny.

## 2. The active-submodule window

Fix \(R,M,G,\mu\) in this section. For a coset \(E+\iota(J)\),
the conditional law of \(E\) is a probability on a finite fiber of
size \(|J|\); write \(H(E\mid E+\iota(J))\) for the expected entropy
of this law. Then
\[
              d_J=\log|J|- H(E\mid E+\iota(J)).
 \tag{4}
\]
In fact \(\mu_J\) has the same quotient law as \(\mu\), with uniform
conditional fiber laws. This gives, on each fiber, \(\ell_J(E)\)
as \(\log|J|\) plus the log of the conditional point probability.
It gives finite moments of every fixed order even if \(\mu\)
is singular on \(G\), since \(\sum_w p_w|\log p_w|^k\) is bounded
uniformly over laws on at most \(|J|\) points.
In particular \(d_H\le d_J\) for \(H\subseteq J\):
\(d_J-d_H\) is the expected relative entropy of the finer \(H\)-coset
labels, given a \(J\)-coset, to their uniform \(|J|/|H|\) law.

Assume all \(d_J>0\) for nonzero submodules; otherwise (3) applies
directly. Put
\[
 r_*=\max_{J\ne0}\frac{\log|J|}{d_J},\qquad
 \mathcal A=\{J\ne0:r_*d_J=\log|J|\}.
\]
If \(m/n\) stays a fixed amount below \(r_*\), (2) implies success
tends to zero: for a maximizing \(J\) the mean misses the threshold
by order \(n\), while the variance is \(O(n)\). At
\(m=n r_*+b\sqrt n+o(\sqrt n)\), let \(Z\) be the
centered Gaussian vector with covariance
\(\operatorname{Cov}_\mu(\ell_J(E),\ell_K(E))_{J,K\in\mathcal A}\).
When each active marginal variance is nonzero, (2) gives
\[
     \limsup_{n\to\infty}\Pr[\mathrm{success}]
            \le \Pr[\sqrt{r_*}Z_J+b d_J>0\ \text{for all }J\in\mathcal A].
 \tag{5}
\]
There is no independence assertion about \(Z\). Indeed use any
\(\gamma\to\infty\) with \(\gamma=o(\sqrt n)\), discard inactive
constraints by the law of large numbers (or simply omit them),
and apply the joint CLT. Positive marginal variances make the
boundary of the indicated orthant-null event have zero Gaussian
probability, even for singular joint covariance. The same proof
works if an active marginal is identically constant and
\(b d_J\ne0\), with its deterministic sign. No matching
achievability or \(b=0\) deterministic boundary statement is made.

There is an algebraic constraint on the active vector. Write
\(U=E+\iota(J)\), \(V=E+\iota(K)\), \(W=E+\iota(J+K)\).
The pair \((U,V)\) identifies \(E+\iota(J\cap K)\), and \(W\) is
a function of either. Conditional on \(W\) all relevant fiber
laws are finite. By (4) and the modularity of log subgroup size,
\[
        d_J+d_K-d_{J\cap K}-d_{J+K}
                       = I(U:V\mid W)\ge0.                           \tag{6}
\]
With \(d_0=0\), the active family enlarged by zero is thus closed
under meets and joins: \(r_*d_J-\log|J|\) is nonnegative and
submodular. When \(J,K\) are active, equality in (6) means that
\(U,V\) are independent given \(W\), and gives the pointwise relation
\(\ell_J(E)+\ell_K(E)=\ell_{J\cap K}(E)+\ell_{J+K}(E)\).
For the latter, conditioned on \(W=w\) express each \(\ell\) through
the conditional probabilities in the same finite fiber. Subtracting
the two sides cancels the common hidden-point probability and leaves
\(\log[p(U,V\mid w)/(p(U\mid w)p(V\mid w))]\), which vanishes.
Thus the Gaussian in (5) can have genuine linear dependencies,
not just correlated coordinates.

## 3. Two failures of a total-entropy or separate-bound argument

Take the synthetic ring \(R=M=\mathbb F_2[u]/(u^2)\). The only
nonzero submodules are \(J=(u)\) and \(M\). Let the additive error be
\(X+Yu\): \(X\) is Bernoulli with parameter \(p\in(2/3,1)\);
given \(X=0\), \(Y=0\); given \(X=1\), \(Y\) is fair. Let
\(p\) be the unique root in \((2/3,1)\) of
\(h(p)=p\log2\) for binary entropy \(h\) in nats. Existence and
uniqueness follow from strict decrease of \(h(p)-p\log2\) on
\([2/3,1]\), positivity at \(2/3\) and negativity at \(1\).
Here \(H(Y\mid X)=H(X)\), so \(d_M=2d_J=2(1-p)\log2>0\) and
both submodules are active. On \(X=0,1\) the likelihood values are
\[
  \ell_J:\quad \log2,\ 0,\qquad
  \ell_M:\quad \log(4(1-p)),\ \log(2p).
\]
Since \(p>2/3\), the two centered quantities are perfectly negatively
correlated and both have positive variance. At \(b=0\) the right side
of (5) is zero, whereas using either Gaussian marginal alone gives
\(1/2\). The negative covariance is between two **nested** constraints;
it is not a consequence of having independent CRT coordinates.

A different example separates total entropy from one-direction sample
cost even with full support. In the finite abstract ring
\(R=M=\mathbb F_2[u]/(u^d)\), choose independent coefficients in the
\(u\)-adic basis, all lower coefficients Bernoulli \(1/4\), and
the last coefficient Bernoulli \(1/2+2^{-d}\), for \(d\ge2\).
Use a single hidden module element (\(n=1\)). The full entropy
deficit is \(\Theta(d)\), but for the top ideal \(J=(u^{d-1})\),
\[
             d_J=\log2-h(1/2+2^{-d})=\Theta(4^{-d}).
\]
Thus (3) shows that even an unbounded guessing rule needs
\(\Omega(4^d)\) observations to reach success \(2/3\), with the
same lower bound against adaptive coefficient policies.
Every additive Fourier coefficient of the error is nonzero,
so this is not an exact translation-period ambiguity. This is an
engineered noise law for which the model is statistically almost
uninformative in a direction, not a result for a conventional
Ring-LWE error family.

## 4. Reading the directional deficit for wrapped Gaussian noise

For a fixed full lattice \(L\subset\mathbb R^D\) let
\(G=\mathbb R^D/L\) and take a centered spherical Gaussian of
width \(s\) wrapped on \(G\). Normalize Haar to probability.
Its density \(p\) has Fourier coefficients
\(e^{-\pi s^2\|\xi\|^2}\) on \(L^*\).
Averaging along \(\iota(J)\) retains only characters that are
trivial on \(\iota(J)\). Write \(P_Jp\) for that average.
If \(\|p-1\|_\infty\le\epsilon<1\), the exact bounds are
\[
 \frac{1}{2(1+\epsilon)}
       \sum_{\xi\in L^*:\ \xi\ \text{nontrivial on }\iota(J)}
                e^{-2\pi s^2\|\xi\|^2}
 \ \le\ d_J\ \le\
 \frac{1}{2(1-\epsilon)}
       \sum_{\xi\in L^*:\ \xi\ \text{nontrivial on }\iota(J)}
                e^{-2\pi s^2\|\xi\|^2}.                              \tag{7}
\]
Indeed \(d_J=\int(p\log(p/P_Jp)-p+P_Jp)\,d\mathrm{Haar}\).
The scalar Taylor remainder in the first argument has second
derivative \(1/x\) between \(1/(1+\epsilon)\) and
\(1/(1-\epsilon)\), and Parseval evaluates
\(\|p-P_Jp\|_2^2\). The same reasoning applies to any Gaussian
covariance by replacing the squared norm by its quadratic form.
For a fixed nonzero \(J\) and \(s\to\infty\), only the shortest
nontrivial-on-\(J\) dual shell contributes to the leading rate.
This is a directional refinement of washing out the entire wrapped
density. Also, for every nondegenerate wrapped Gaussian at finite
width all Fourier coefficients are strictly positive and hence there
is no nontrivial exact translation stabilizer: characters separate
points. The exponentially weak-direction issue in (3) is different
from exact indistinguishability and from computational hardness.

These formulas use the specified wrapped law (or condition on a
fixed shared error parameter); they do not identify the law of a
compound experiment with an unknown jointly resampled covariance.
Neither (1) nor (7) gives a way to solve general Ring-LWE in
classical polynomial time or a statement about concrete parameters.

The companion verifier uses only finite generated residue distributions.
It checks likelihood and reference invariance under adaptive rows, finite
fiber and submodularity identities, and the Fourier projection identity.
It does not implement a guessing rule or assess any cryptographic sample.
