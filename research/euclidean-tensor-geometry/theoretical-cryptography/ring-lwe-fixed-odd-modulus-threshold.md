# A statistical search threshold for dyadic tori at a fixed odd modulus

We determine the information-theoretic search transition for a
specified continuous Ring-LWE experiment with genuinely uniform
independent public coefficients. The optimum is over arbitrary
decisions and does not come with a computational bound or a
solver. The modulus is fixed and the proof uses exact product
spherical noise, so it is not a complexity classification of
general Ring-LWE, a test of deployed parameters, or a
cryptanalytic procedure.

## 1. Model and result

Fix an odd integer \(q\ge3\) and let \(d\to\infty\) run over
powers of two. Put \(R_d=(\mathbb Z/q)[x]/(x^d+1)\).
Identify the additive group of \(R_d\) with the coefficient
grid \((\mathbb Z/q)^d\), embedded in \(\mathbb T^d\) by
\(u\mapsto u/q\bmod\mathbb Z^d\).
For hidden rank \(n\ge1\), a uniform \(S\in R_d^n\), and
\(m\ge1\) rows \(A_i\) iid uniform on \(R_d^n\), the observed
responses are
\[
 B_i=(A_i S)/q+E_i \pmod{\mathbb Z^d}.
\]
Here \(E_i\) are iid with product Haar density \(p_b=f_b^{\otimes d}\),
where
\[
 f_b(t)=\sum_{k\in\mathbb Z}b^{k^2}e^{2\pi i k t},\quad 0<b<1 .
\]
The noise is independent of \(A,S\) and known as a law. The
scalar case \(n=1\) is the dual continuous spherical dyadic
Ring-LWE model: in the orthogonal power-basis coordinates the
codifferent is \((1/d)\mathbb Z[x]/(x^d+1)\), and a canonical
width \(s\) gives \(b=e^{-\pi d s^2}\).
Let \(P_{\rm opt}(A)\) denote the best possible uniform-prior
probability of exactly identifying the entire hidden element
conditional on the public matrix, with no time restriction.

For each divisor \(\ell>1\) of \(q\) put
\[
 g_{\ell,b}(t)=f_{b^{\ell^2}}(\ell t),\qquad
 L_{\ell,b}(t)=\log\frac{f_b(t)}{g_{\ell,b}(t)},\qquad
 C_\ell(b)=\mathbb E_{f_b}L_{\ell,b},\qquad
 c_*(b)=\min_{\substack{\ell\mid q\\ \ell>1}}\frac{C_\ell(b)}{\log\ell}.
 \tag{1}
\]
The notation \(\mathbb E_{f_b}\) means that the argument is a
circle variable with density \(f_b\).

**Theorem.**

1. For \(b_d\to b_*\in(0,1)\), the threshold for the
   rate \(n/m\) is exactly \(c_*(b_*)\): if the rates stay a
   positive distance below this value, \(P_{\rm opt}(A)\to1\);
   if they stay a positive distance above, \(P_{\rm opt}(A)\to0\).
   Convergence throughout is in \(L^1\) over \(A\).
2. More precisely, suppose each
   \[
       t_{\ell,d}=\frac{dm\,C_\ell(b_d)-dn\log\ell}{\sqrt{dm}}
          \longrightarrow t_\ell\in[-\infty,\infty].
       \tag{2}
   \]
   If any \(t_\ell=-\infty\), the limit is 0. Otherwise it is the
   joint Gaussian probability
   \[
      \Pr\{Z_\ell+t_\ell>0:
                    \ell\mid q,\ \ell>1,\ |t_\ell|<\infty\},
      \quad
      \operatorname{Cov}(Z_\ell,Z_{\ell'})
      =\operatorname{Cov}_{f_{b_*}}(L_{\ell,b_*},L_{\ell',b_*}).
      \tag{3}
   \]
   The event is certain if the index set is empty. In particular
   for prime \(q\) the only candidate is \(\ell=q\), at every
   \(b_*\). The joint expression does not assume its coordinates
   independent. We do not claim that multiple divisors actually tie.
3. If \(b_d\to0\), write
   \(V_q(b)=\operatorname{Var}_{f_b}(L_{q,b})\). Whenever
   \[
       \frac{dm C_q(b_d)-dn\log q}{\sqrt{dm\,V_q(b_d)}}\to z\in\mathbb R,
       \tag{4}
   \]
   one has \(P_{\rm opt}(A)\to\Phi(z)\) in \(L^1\).
   Here \(C_q(b)\sim b^2\) and \(V_q(b)\sim2b^2\);
   the exact centering in (4) does not require \(n\) bounded.

There are no restrictions on how \(n,m\) grow other than the
displayed regimes. The condition of fixed \(q\) is essential in
the proof of ideal stabilization, and even modulus is excluded.

## 2. A common finite-sample sandwich

We use the following additive observation formulation. Let \(R\)
be a finite ring, \(M\) a finite left module embedded in a compact
abelian group, and the error have a strictly positive continuous Haar density
\(p\). Denote averages over a submodule \(J\) in this group by
\(P_Jp\). For actual residual noises \(E_i\) set
\[
       T_J=\sum_{i\le m}\log(p(E_i)/(P_Jp)(E_i)).
\]
Let \(\mathcal J\) be the set of nonzero submodules of \(M\),
including \(M\) itself. For each \(\gamma>0\) the optimal conditional
success \(P_{\rm opt}(A)\) obeys for every fixed matrix \(A\)
\[
 P_{\rm opt}(A)\le
     \Pr\{T_J>n\log|J|-\gamma\ \forall J\in\mathcal J\}
                       +|\mathcal J|e^{-\gamma}.             \tag{5}
\]
For independent uniform rows the average also obeys
\[
 \mathbb E_A P_{\rm opt}(A)\ge
     \Pr\{T_J>n\log|J|+\gamma\ \forall J\in\mathcal J\}
                       -|\mathcal J|e^{-\gamma}.             \tag{6}
\]
The probabilities on the right sides are over the *same shared
noise sample* in each of the directions.

For (5), replace the noise by \(P_Jp\) for a fixed direction \(J\).
In the reference model, within each coset of \(J^n\) the
transcript law is identical for every hidden element. The
success probability is at most \(|J|^{-n}\). The likelihood
ratio from reference to actual law, including the hidden
index, has actual log \(T_J\). Thus actual success with
\(T_J\le n\log|J|-\gamma\) costs at most \(e^{-\gamma}\).
Union over the bad directions gives (5); this is the static
case of the [simultaneous ideal converse](ring-lwe-search-ideal-converse.md).

For (6), use a posterior collision bound, not a complexity
bound or a proposed decoder. Conditional on the observation,
the maximum posterior mass is at least the sum of squared
posterior masses. Therefore the optimal success is at least
the expected posterior mass of the true hidden element.
Under a uniform prior, conditional on the true \(S=s\) and
error \(E\), the reciprocal of its posterior mass is \(1+W\),
where \(W\) is the sum of the other hypotheses' likelihood
ratios relative to the truth. For a fixed difference
\(v\in M^n\setminus\{0\}\), the shifts \(A_i v\) are uniform
in \(J(v)=\sum_j Rv_j\), iid across rows, because this
additive homomorphism from \(R^n\) has equal fibers.
Consequently the conditional expectation of its ratio over
\(A\) is \(\exp(-T_{J(v)})\).
There are at most \(|J|^n\) differences with \(J(v)=J\).
On the joint high-information event of (6) we thus have
\(\mathbb E_A W\le|\mathcal J|e^{-\gamma}\).
Use \(1/(1+W)\ge1-W\) there and nonnegativity off the event.
This proves (6). No statement about searching the posterior
in polynomial time is involved.

## 3. Exact fixed-base stabilization

The number of ideals of \(R_d\) is eventually constant, and all
of them are additive products in a suitable fixed-size block
decomposition of the coefficient coordinates. The proof uses
\(q\) fixed. For every odd prime \(p\mid q\), the factors of
\(x^d+1\) mod \(p\) are separable and all irreducible factors have
degree \(\operatorname{ord}_{2d}(p)\), because every root has
order \(2d\). If \(d=2^k\), then for sufficiently large \(k\) this
degree is \(2^{k+2-v_2(p^2-1)}\). In fact the order modulo
\(2^{k+1}\) is a power of two, and for \(t\ge1\)
\[
       v_2(p^{2^t}-1)=v_2(p^2-1)+t-1.
\]
Successive squaring proves the valuation formula, since
\(p^{2^t}+1\equiv2\bmod 8\) for \(t\ge1\).

Choose a fixed dyadic \(d_0\) in this stable regime for every
\(p\mid q\), and put \(k_0=d/d_0\).
Under substitution \(z=x^{k_0}\), each irreducible factor
\(F(z)\) of \(z^{d_0}+1\) modulo \(p\) gives one irreducible
factor \(F(x^{k_0})\) of \(x^d+1\). Indeed all roots of the latter
have order \(2d\), and every irreducible factor would have
degree \(\operatorname{ord}_{2d}(p)=k_0\operatorname{ord}_{2d_0}(p)\),
which is already its entire degree. For each \(p^e\Vert q\),
use the pairwise coprime monic Hensel factorization modulo
\(p^e\) at level \(d_0\); substitution produces a coprime
monic factorization modulo \(p^e\) at level \(d\), since the
product is the polynomial and the reductions are those
just identified.

The component of either ring at each lifted factor is free
over \(\mathbb Z/p^e\) and reduces to a field modulo \(p\).
Every nonzero element is \(p^j\) times a unit for some
\(0\le j<e\): choose the common coefficient valuation \(j\)
and divide by it, and invert the residue-nonzero factor
using the nilpotence of \(p\). Thus all ideals of this component
are the powers \(p^j\), including \(j=e\) for zero.
Substitution embeds \(R_{d_0}\) in \(R_d\), and matches the
component projections, as seen by substituting the lifted
factors (or their associated Chinese-remainder idempotents).
Extension of ideals preserves exactly the tuple of these
component exponents, hence induces a bijection from ideals
at \(d_0\) onto ideals at \(d\).

In the coefficient decomposition
\[
      u(x)=\sum_{j=0}^{k_0-1}x^j u_j(x^{k_0}),\qquad u_j\in R_{d_0},
\]
\(R_d\) is free of rank \(k_0\) over \(R_{d_0}\).
An ideal extended from \(J_0\subseteq R_{d_0}\) is exactly
the set with each \(u_j\in J_0\), and \(|J|=|J_0|^{k_0}\).
The coefficient blocks here simply permute the \(d\) coordinates.
Uniform averaging over \(J\) consequently factorizes, and the
joint vector of \(T_J\)'s in (5)–(6) is an iid sum of \(m k_0\)
identical block information vectors:
\[
     \bigl(l_{J_0,b}(U)\bigr)_{J_0\ne0},\quad
     l_{J_0,b}=\log(f_b^{\otimes d_0}/P_{J_0}f_b^{\otimes d_0}),
     \quad U\sim f_b^{\otimes d_0}.
     \tag{7}
\]
In particular \(|\mathcal J|\) is bounded independently of \(d\).

## 4. The actual capacity bottlenecks

The ideal information in a block has an elementary
strict lower bound. Take any additive subgroup
\(J_0\le(\mathbb Z/q)^{d_0}\), a uniform \(X\in J_0\),
and \(Y=X/q+E\) in that block, with independent
\(f_b\)-noise. Then
\[
 \mathbb E l_{J_0,b}(E)=I(X;Y)
      \ \ge\ \sum_{i=1}^{d_0} I(X_i;Y_i\mid X_{<i})
      \ =\ \sum_{i=1}^{d_0} C_{\ell_i}(b),
 \tag{8}
\]
where \(\ell_i\) is the cardinality of the conditional input
group in coordinate \(i\), and \(C_1(b)=0\).
The first equality uses that translation preserves the conditional
noise entropy and the output density is the subgroup average.
Given \(X_{<i}\), the coordinate \(X_i\) is uniform on one translate
of the same subgroup of \(\mathbb Z/q\), of order \(\ell_i\):
the group of differences is the kernel of the map of consecutive
coordinate projections. Thus its entropy increments are
\(\log\ell_i\), \(\prod_i\ell_i=|J_0|\), and translating a coset
does not change the scalar mutual information \(C_{\ell_i}\).
The individual group average has density \(g_{\ell_i,b}\) up
to that translation, by Fourier orthogonality.
Finally \(Y_i\) and \(Y_{<i}\) are independent given \(X_{<i}\).
The difference between the first two expressions in (8)
is \(\sum_i I(Y_i;X_{<i}\mid Y_{<i})\), by the entropy chain
rule for the product conditional channel.

Equality in the inequality (8) holds only for a product subgroup.
In fact, the prefix observation law is everywhere positive for
any given allowed \(X_{<i}\). So if the conditional mutual
information vanishes, the conditional law of \(Y_i\) given
\(X_{<i}\) must be the same at every possible \(X_{<i}\).
Convolving with \(f_b\) is injective on input probability measures
on the circle, because all its Fourier coefficients are nonzero.
Hence the conditional law of \(X_i\) is independent of \(X_{<i}\).
For equality in the sum this holds at every coordinate, giving
a product uniform support. The converse for product supports
follows immediately.

For an ideal \(J_0\), multiplication by \(x\) is a signed cyclic
coordinate permutation. Thus if an ideal is a product subgroup,
all its coordinate subgroups are the same (each subgroup is
closed under negation), and it has the form \((q/\ell)R_{d_0}\)
for some \(\ell\mid q\). Dividing (8) by
\(\sum_i\log\ell_i=\log|J_0|\) for nonzero ideals gives
the minimum \(c_*(b)\) in (1), because the full product ideals
\((q/\ell)R_{d_0}\) attain \(C_\ell(b)/\log\ell\).
Every nonproduct ideal has strictly larger normalized
information at any fixed \(b\). There are finitely many such
ideal types at the base, so they have a positive gap from
\(c_*(b_*)\), uniform for \(b\) near \(b_*\), by continuity.
The precise candidates for the minimum are therefore the
full product ideals associated with scalar divisors, not
arbitrary correlated ideals.

## 5. Fluctuations and squeezing the optimum

For \(b\) near \(b_*\in(0,1)\), the block densities and their
averages have a uniform positive lower bound and finite upper bound
in the fixed dimension \(d_0\), by continuity and positivity of
\(f_b\). Hence their information vectors are uniformly bounded.
All covariance entries are continuous in \(b\), and any nonzero
direction has positive variance: if \(l_{J_0,b}\) were constant,
the normalized densities would be equal, which would say
\(f_b^{\otimes d_0}\) was invariant under a nonzero shift.
Its coordinate Fourier coefficients in degree one already
preclude such a shift.

If (2) includes a negative-infinite limit, (5) for that product
ideal and a bounded-variance fluctuation normalized by
\(\sqrt{dm}\) give a limit of zero. Otherwise, if at least one
\(t_\ell\) is finite then \(n/m\to c_*(b_*)\): the finite entry
forces the limit \(C_\ell(b_*)/\log\ell\), and the absence of any
negative-infinite entry forces this to be the minimum.
If all entries go to positive infinity, eventually
\(n/m\le c_*(b_d)\). In either situation the nonproduct directions
are uniformly strictly above the rate by the gap just proved,
and their offsets divided by \(\sqrt{m k_0}\) go to positive
infinity in (7). They can be discarded by a variance bound.
The remaining, product directions have exactly the joint
information vector of \(dm\) independent scalar copies of
\((L_{\ell,b})_\ell\). The bounded-vector triangular-array CLT
gives the joint Gaussian in (3), with positive marginal
variances even if the covariance matrix is singular. Thus
shifting thresholds by \(\gamma=(m k_0)^{1/4}\) cannot change
the limiting joint probability; active boundary events have
measure zero, and \(|\mathcal J|e^{-\gamma}\to0\).
This proves that the upper bound for every \(A\) and the
averaged lower bound have the same limit. If \(U_d\) is the
deterministic upper bound, the inequality
\(\mathbb E|P_{\rm opt}(A)-u|\le
  U_d-\mathbb E P_{\rm opt}(A)+|U_d-u|\)
for that common limit \(u\) gives the asserted \(L^1\) result.
The first-order claims similarly follow by applying bounded
variances directly when the rate has a fixed gap.

For \(b\to0\), in a fixed block the uniform expansion is
\(f_b^{\otimes d_0}=1+2b\sum_i\cos(2\pi u_i)+O(b^2)\).
A shortest Fourier mode corresponds to a signed power of the
root of unity, a unit, and cannot annihilate a nonzero
ideal. One can see this directly: if a coordinate character
were trivial on an ideal, the signed cyclic coordinate action
would make all coordinate characters trivial on it.
Thus for every nonzero base ideal
\(P_{J_0}f_b^{\otimes d_0}=1+O(b^2)\). Since the density is
normalized, \(D(P_{J_0}f_b^{\otimes d_0}\|1)=O(b^4)\),
and
\[
 \mathbb E l_{J_0,b}
   =D(f_b^{\otimes d_0}\|1)-D(P_{J_0}f_b^{\otimes d_0}\|1)
   =d_0 b^2(1+O(b)),\qquad
 \|l_{J_0,b}\|_\infty=O(b).
\]
The divergence identity is from invariance of its averaged
density, and the scalar entropy expansion follows from
\(f_b=1+2b\cos(2\pi u)+O(b^4)\).
For the full product direction specifically,
\(C_q(b)\sim b^2\) and \(V_q(b)\sim2b^2\) by the same expansion
of its scalar likelihood. Condition (4) entails
\(dm\,b^2\sim dn\log q\to\infty\).
Every proper ideal has
\(\log|J_0|<d_0\log q\) by a fixed positive amount, so its
expected sum in (7) exceeds its threshold by at least a
constant times \(dn\) for large \(d\).
Its variance is \(O(dm\,b^2)=O(dn)\) from the uniform fixed
block bound. Thus only the full product direction remains.
The scalar independent likelihood sum satisfies the CLT since
one centered summand is \(O(b)\) compared with total
standard deviation asymptotic to \(\sqrt{2dm}\,b\).
Apply (5)–(6) with \(\gamma=(dn)^{1/4}\) and the same
\(L^1\) squeeze to prove (4).

## 6. Relation to previous work

[LPR, §2.5 and Definitions 3.1–3.2](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf)
give the cyclotomic residue-degree description and the search
observation model. The continuous experiment here is a
prescribed spherical error case and a fixed-modulus limit,
not a proof or refutation of the hardness of the error
families in their reductions. This includes observations at
**all** public coefficients, not only fixed unit coefficients.

[Pang–Pradhan–Mahdavifar, Theorems 1–3 in the 2024 manuscript](https://arxiv.org/pdf/2406.13243v1)
give one-shot group coding bounds with subgroup terms, a
clear precedent for the general random-coding and
subgroup-converse ideas in Section 2. The additional steps
here are the matching common-noise event for the specified
module ensemble, the exact stabilized dyadic ideal
decomposition, strict elimination of nonproduct ideals, and
the resulting fixed-modulus first- and second-order
statistical formulas for typical public matrices.
The scalar channel capacity as a difference of entropy
flatness quantities is standard; compare [Luzzi–Ling–Bloch,
Appendix B, Equation (43)](https://arxiv.org/abs/2206.10443).
This is complementary to the large-modulus-uniform
[one-error alignment note](ring-lwe-dyadic-ideal-information-alignment.md);
the fixed-modulus argument here does not need its separate
Fourier orbit estimate.
The companion checker uses only arithmetic in synthetic small
quotient rings and a finite-set subgroup projection identity.
It does not recover hidden values or replace the proof.
