# Sharp continuity on a prescribed block-marginal fibre

We determine the exact trace-distance modulus of mutual information
for a prescribed marginal when both states are block diagonal on
that side. The result includes arbitrary fixed priors of
classical–quantum ensembles, with no commutativity assumption on
their conditioning states. It also allows quantum coherence and
entanglement *within* the blocks.

Let \(A=\bigoplus_{i=1}^m A_i\), \(d_i=\dim A_i\), \(b=\dim B\), and write
\(\pi_i=I_{A_i}/d_i\). Fix block weights \(p_i>0\) with \(\sum_i p_i=1\).
Zero-weight blocks may simply be deleted on a common-marginal
fibre. All logarithms are natural. Put \(r_i=\min(d_i,b)\) and
\(K_i=d_i r_i\). Expand \(p\) into the probability vector
\[
                  P=\bigoplus_i (p_i/K_i)^{[K_i]},
\]
where the superscript in brackets means repeated entries, not
exponentiation. Denote by \(F_P(\delta)\) the Hamming-distortion
equivocation \(H(P)-R_P(\delta)\), where \(R_P\) is the classical
rate-distortion function of a source with law \(P\).

**Theorem.** For any two block-diagonal states \(\rho_{AB},\sigma_{AB}\)
with common \(A\)-marginal and block weights \(p_i\),
\[
       |I(A:B)_\rho-I(A:B)_\sigma|\ \le\ F_P(\delta),
       \qquad T(\rho,\sigma)\le\delta,\quad
       T=\tfrac12\|\rho-\sigma\|_1.
\]
If \(b\ge\sum_i d_i\), this is the exact maximum for every
\(\delta\in[0,1]\) on the prescribed fibre
\(\rho_A=\sigma_A=\bigoplus_i p_i\pi_i\), among block-diagonal pairs.
Here \(K_i=d_i^2\). In particular:
* All \(d_i=1\) gives the exact modulus for arbitrary prior \(p\)
  of classical–quantum ensembles when \(b\) is at least its support
  size. Optimizing over noncommuting output ensembles cannot exceed
  the classical Hamming-equivocation curve.
* One block gives the familiar isotropic curve on a maximally mixed
  fibre. Choosing the blocks as the eigenspaces of a prescribed
  marginal gives an exact result for the states commuting with that
  marginal tensored with \(I_B\) (with the indicated dimension condition).

An operator comparison from Berta et al.'s
[sharp conditional-entropy proof](https://arxiv.org/html/2607.24687v2#S1),
also used for the [dimension-only common-marginal
modulus in this repository](https://github.com/mxym/math/tree/main/research/fixed-marginal-mutual-information-20261118),
is adapted here to different block weights. The key reference is
allowed to be subnormalized. This is distinct from
[Alhejji–Smith](https://arxiv.org/abs/1909.00787) and
[Wilde](https://arxiv.org/abs/1909.01755), which give uniform
dimension-only classical and quantum/classical continuity bounds,
and from the dimension-only separable bound in
[Berta et al., Proposition 2.1](https://arxiv.org/html/2607.24687v2#S2).
We use the classical fixed-prior Fano curve of
[Sakai, Theorems 1 and 3, unique decoding](https://doi.org/10.3390/e22030288)
as the expression for the modulus; the classical curve itself is
not new. The theorem makes no claim about coherence across distinct
blocks or general unrestricted fixed density matrices.

## 1. Formula for the expanded-prior curve

If \(P\) has just one positive entry, take \(F_P=0\). Otherwise
\(F_P(0)=0\) and \(F_P(\delta)=H(P)\) at
\(\delta\ge\delta_{\rm sat}=1-\max_i(p_i/K_i)\).
For \(0<\delta<\delta_{\rm sat}\) let \(c>0\) solve
\[
                    \sum_i\min(p_i,K_i c)-c=\delta .       \tag{1}
\]
This has a unique solution in the increasing portion before the
constant part of the piecewise-linear left side: in expanded
coordinates its slope is the number of entries above \(c\) minus
one, starting positive and reaching zero when only a maximal
entry can exceed \(c\). Set
\[
 \mu_i=\min(p_i,K_i c),\qquad L=\frac{1-\delta}{c}>1 .
\]
Then \(F_P(\delta)\) is the entropy of the vector \(w\) of the
\(P\)-coordinates clipped at \(c\), with one copy of \(c\) replaced
by \(1-\delta\). In particular
\[
           F_P(\delta)=
            -\sum_i p_i\log(\mu_i/K_i)-(1-\delta)\log L .    \tag{2}
\]
Indeed an unclipped coordinate is unchanged in \(w\), while on
all clipped coordinates the logarithm in the sum is \(\log c\).
The modified entry has probability \(1-\delta\), giving (2).
For example, with \(d=(1,2)\), \(p=(1/20,19/20)\) and \(b\ge3\),
the rare virtual entry is no longer clipped after distance \(1/5\). At distance \(1/4\)
the vector \(w\) is \((3/4,1/15,1/15,1/15,1/20)\), not the
dimension-only equal-error vector.

For an elementary check of the classical interpretation, tag a
decoded symbol \(j\). Take the vector of clipped weights and
multiply its \(j\)th weight by \(L\). Its sum is at most 1 by (1).
The relative-entropy inequality against this subprobability
vector gives an upper bound on each posterior's entropy; averaging
over decoded symbols yields (2) whenever the decoding success is
at least \(1-\delta\). For equality, use an ensemble over clipped
coordinates with \(P_j>c\); on coordinate \(j\) take the normalized
posterior with its \(j\)th weight \(1-\delta\).
The ensemble probabilities \((P_j-c)/(1-\delta-c)\) give prior \(P\)
and error \(\delta\). Above the saturation error, a constant
decoder at a most probable coordinate attains equivocation \(H(P)\).

## 2. The operator bound at fixed block weights

For any positive matrix \(Y\) on \(A_i\otimes B\),
\[
                   Y\le r_i I_{A_i}\otimes\operatorname{Tr}_{A_i}Y .
\]
For a rank-one matrix, expand its vector in Schmidt form and use
Cauchy–Schwarz with at most \(r_i\) terms in a quadratic form;
the resulting diagonal sum is bounded by the product on the right.
Summing the rank-one inequalities proves the claim.
Thus the block \(\sigma_i\) of the anchor state, of trace \(p_i\),
satisfies
\[
                      \sigma_i\le K_i\pi_i\otimes\sigma_B .
\]
For the proof only block weights need agree. Mix both states
towards the strictly positive product
\((\bigoplus_i p_i\pi_i)\otimes I_B/b\) to take all logarithms on full
support, without affecting those weights. Equality of the two
marginals is preserved, and in the prescribed uniformly mixed
blocks it preserves the exact marginal as well. Trace distance
decreases and finite-dimensional entropy continuity gives the limit.

For \(0<\delta<\delta_{\rm sat}\) form the block reference operators
\[
 W_i=\mu_i\pi_i\otimes\sigma_B,\qquad
 \tau_i=W_i+(L-1)\frac{\mu_i}{K_i}\,\sigma_i,\qquad
 W=\bigoplus_i W_i,\quad \tau=\bigoplus_i\tau_i.
\]
Then
\[
 W\le\tau\le LW,\qquad
 \tau_i\ge L(\mu_i/K_i)\sigma_i,\qquad
 \tau_B\le\left(\sum_i\mu_i+(L-1)c\right)\sigma_B=\sigma_B .   \tag{3}
\]
The first two comparisons follow from the domination of each \(\sigma_i\).
For the last, use \(\mu_i/K_i\le c\) and sum the partial traces.
The reference \(\tau\) need not have trace one.

Define \(G=\log W-\log\tau\), so \(-\log L\,I\le G\le0\) by
operator monotonicity, even when the blocks do not commute.
With \(\Delta=\rho-\sigma\) and equal block weights,
\(\operatorname{Tr}(\Delta\log W)=\operatorname{Tr}(\Delta_B\log\sigma_B)\),
because the scalar term on block \(i\) is \(\log(\mu_i/d_i)\).
Expanding relative entropies gives the identity
\[
 \begin{split}
 H(A|B)_\rho-H(A|B)_\sigma
   ={}&\operatorname{Tr}(\Delta G)+D(\sigma\Vert\tau)
       -D(\rho\Vert\tau)+D(\rho_B\Vert\sigma_B).
 \end{split}
\]
Data processing and (3) imply
\(D(\rho\Vert\tau)\ge D(\rho_B\Vert\tau_B)\ge
D(\rho_B\Vert\sigma_B)\). Data processing also holds for this
subnormalized second operator: divide by its trace and subtract
the same logarithmic scalar on both sides.
The Jordan parts of \(\Delta\) each have trace \(T\le\delta\), so
\(\operatorname{Tr}(\Delta G)\le\delta\log L\).
The per-block lower bound in (3) gives
\[
 D(\sigma\Vert\tau)\le-\log L-\sum_i p_i\log(\mu_i/K_i).
\]
We get precisely (2). Exchanging the states gives the absolute
bound on conditional entropy, and cancellation of the shared
\(H(A)\) gives the claimed mutual information bound.

At large \(\delta\) a simpler range bound suffices. Recording the
block label as a classical register gives
\(H(A|B)_\omega=H(i|B)_\omega+
\sum_i p_i H(A_i|B)_{\omega_i/p_i}\).
The first term is nonnegative for a classical register; by
Araki–Lieb each term in the sum is at least \(-\log r_i\).
The upper bound is \(H(A)\le H(p)+\sum_i p_i\log d_i\).
The range width is consequently at most \(H(P)\).
At \(\delta=0\) the states coincide.

The same calculation gives a directional bound even without equal
block weights, in a convenient shifted functional.
For a block-diagonal \(\omega\) with weights \(s_i\), set
\(J(\omega)=H(A|B)_\omega+\sum_i s_i\log r_i\).
Then \(J(\rho)-J(\sigma)\le F_P(\delta)\) when \(\rho\) has
positive block weights \(p_i\), with no condition on the block weights
of \(\sigma\).
Indeed if the latter are \(q_i\), the entropy identity has an additional
term \(-\sum_i(p_i-q_i)\log(\mu_i/d_i)\), and the
last anchor bound has \(q_i\) instead of \(p_i\).
Their combined change versus (2) is exactly
\(\sum_i(q_i-p_i)\log r_i\), which cancels in \(J\).
At saturation \(0\le J(\omega)\le H(\bigoplus_i(s_i/K_i)^{[K_i]})\)
from the same range calculation. In the classical–quantum case
\(r_i=1\), this is a prior-dependent one-sided equivocation bound.

## 3. Extremizers when the conditioning space is large enough

Assume \(b\ge\sum_i d_i\), so \(K_i=d_i^2\).
Choose orthogonal subspaces \(B_i\) with \(\dim B_i=d_i\).
Let \(\phi_i\) be a maximally entangled rank-one projector on
\(A_i\otimes B_i\), and set \(\sigma=\bigoplus_i p_i\phi_i\).
Then \(\sigma_A=\bigoplus_i p_i\pi_i\) and
\(H(A|B)_\sigma=-\sum_i p_i\log d_i\).

For the interior range of \(\delta\), put
\(\ell=1-\delta-c>0\) and \(t_j=(p_j-\mu_j)/\ell\).
These numbers are nonnegative and sum to one. For each \(j\)
with \(t_j>0\), define the normalized output block \(\rho^{(j)}\)
supported on \(A\otimes B_j\):
* On \(A_j\otimes B_j\), assign weight \(1-\delta\) to \(\phi_j\)
  and weight \(c\) to each of the other \(d_j^2-1\) vectors of
  a maximally entangled orthonormal basis.
* For \(i\ne j\), take the product of the maximally mixed states
  on \(A_i,B_j\), with weight \(\mu_i\).

The \(j\)th total weight is \(u_{jj}=1-\delta+(d_j^2-1)c=\mu_j+\ell\),
since \(t_j>0\) implies \(\mu_j=d_j^2c\).
The other totals are \(u_{ij}=\mu_i\). Their sum is one by (1).
The \(B_j\)-marginal of \(\rho^{(j)}\) is maximally mixed.
Set \(\rho=\sum_j t_j\rho^{(j)}\) on these mutually orthogonal
conditioning subspaces. Its \(i\)th \(A\)-weight is
\(\mu_i+\ell t_i=p_i\), and within the \(i\)th block its marginal
is maximally mixed as required.

On the distinguished projectors \(\phi_j\), the respective weights
are \(t_j(1-\delta)\) and \(p_j\). For an active \(j\),
\(p_j-t_j(1-\delta)=\mu_j-ct_j\ge0\), since
\(\mu_j=d_j^2c\) and \(t_j\le1\). For inactive \(j\) it is
nonnegative as well. All other weight of \(\rho\) is off the support
of \(\sigma\), and that total is \(\delta\).
Hence the trace distance is exactly \(\delta\).

Finally, in \(\rho^{(j)}\) the spectra in the \(i\ne j\) blocks
have \(\mu_i\) equally spread over \(d_i d_j\) entries, whereas
the formal Fano vector \(w\) spreads it over \(d_i^2\).
Its entropy therefore differs from \(H(w)\) by
\(\sum_{i\ne j}\mu_i(\log d_j-\log d_i)\).
Subtracting \(H(B_j)=\log d_j\) gives
\[
 H(A|B)_{\rho^{(j)}}=
            H(w)-\sum_i u_{ij}\log d_i.
\]
Averaging over the orthogonal \(B_j\) blocks and subtracting
the value of \(\sigma\) gives \(H(w)\), proving sharpness.

At saturation choose \(j\) maximizing \(p_j/d_j^2\).
Take \(\rho=(\bigoplus_i p_i\pi_i)\otimes\pi_{B_j}\) and the
same \(\sigma\). Their common spectral weight on \(\phi_j\)
is \(p_j/d_j^2\), their only overlap, and hence the distance is
\(\delta_{\rm sat}\). Their conditional-entropy difference is
\(H(p)+2\sum_i p_i\log d_i=H(P)\).
This pair is allowed for every larger distance budget.
In the case \(d_i=1\) for all \(i\), every displayed extremizer
is a classical joint probability table embedded in orthogonal
conditioning labels.

The companion [exact verifier](verify_factor_block_marginal_continuity.py)
checks normalization, marginals, distances and the entropy identities
for rational inputs. It also checks the PSD comparisons on
noncommuting rational anchor blocks. The general result follows
from the proof, not from the finite set of rational tests.
