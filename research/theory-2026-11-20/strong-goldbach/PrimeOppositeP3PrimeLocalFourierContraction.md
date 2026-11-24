# Prime-local Fourier contraction on full-size signed dual P3 modes

Written research note, 2026-11-24. This is a genuine extra oscillatory saving on some full-size off-diagonal blocks of the independent-frequency completion. It does not beat the ordinary affine exponent ceiling. It isolates why treating the third local factor by the triangle inequality, even while exploiting both prime-local Fourier operators exactly, is insufficient.

Use the notation of [the signed two-frequency completion](PrimeOppositeP3SignedTwoFrequencyCompletion.md): true prime \(q_i\asymp Q\), squarefree \(s\asymp S\) coprime to the actual \(N\), \(R\) in the \(r\) variable, and exact \(H=\sqrt N\). Let
\[
 A_0=RQS/H,\qquad B_0=SQ^2/R.
\]
Assume \(A_0,B_0\ge1\) and \(A_0\le QN^{-c}\) for a fixed \(c>0\), as is true in the genuinely full-size application below. The existing same-\(q\) and zero-mode bounds may be retained. Then the signed, \(q_1\ne q_2\) completed energy satisfies the independent additional bound
\[
 \left|\text{signed completed off-diagonal energy}\right|
 \ll N^{o(1)}\,QH\,\left(1+\frac{B_0}{Q}\right).
 \tag{1}
\]
This may be used in minimum with the existing absolute \(Q^3S^{3/2}N^{o(1)}\) bound. It works uniformly for all true \(q\)-weights \(|b_{q,s}|\le1\) from the originating estimate.

## Exact operators and weights

Fix \(s,q_1,q_2\) with the two primes distinct. The completion modulus \(m=sq_1q_2\) has dual \(\ell\) length \(m/R\asymp B_0\). In the exact CRT factorization the \(q_i\) Kloosterman factors are of the form
\[
 \mathrm{Kl}_{q_1}(c_1h_1,d_1\ell),\qquad
 \mathrm{Kl}_{q_2}(c_2h_2,d_2\ell),
\]
where the four displayed constants are units at their own local primes and depend on \(N,s,q_1,q_2\), not on \(h_i,\ell\). In particular the factor at \(q_1\) is independent of \(h_2\), and conversely. The \(s\)-local factor has the form
\[
 \mathrm{Kl}_s(a_1h_1+a_2h_2,b\ell)
 =\sum_{x\bmod s}^{*}
     e_s(bx\ell)\,e_s(a_1\bar x h_1)\,e_s(a_2\bar x h_2),
 \tag{2}
\]
where the original \(N\) is retained in \(a_1,a_2\). Thus for any one fixed \(x\) all three phases split, with individually bounded factors in \(h_1,h_2,\ell\). There is no replacement of actual residues by equidistributed model residues.

The nonseparable analytic coefficient also separates with the correct full dual cutoff. In the originating signed formula write \(\lambda=m/R\) and scale its completed weight as
\[
 \frac Rm\widehat G_{12,s}(\ell R/m)
 =\frac{1}{A_0^2\lambda}\,
  \mathcal W(h_1/A_0,h_2/A_0,\ell/\lambda).
\]
For fixed \(s,q_1,q_2\), the function \(\mathcal W\) is Schwartz with every fixed Schwartz seminorm bounded by a power of \(L\), uniformly. Indeed it is the \(v\)-integral of the compact smooth \(\psi(v)\), the two scaled \(\widehat W\)-factors from true Poisson, smooth powers of \(v\), and the phase \(e(-v\ell/\lambda)\). The two \(\widehat W\)-arguments are fixed-comparable multiples of \(h_i/A_0\) on this support. Differentiate in the three normalized variables inside the compact integral; differentiating in the third only inserts powers of \(v\). Integration by parts in \(v\) then gives arbitrary decay in the third variable, while arbitrary decay in the first two is preserved by choosing higher Schwartz orders for \(\widehat W\). Smooth factors may depend on \(N\) through the permitted logarithmic derivative bounds.

For use below, partition each normalized coordinate into its central interval of length \(O(1)\) and the signed dyadic outer intervals of lengths \(O(2^j)\). On one such three-dimensional box, the mixed partial derivatives (with each variable differentiated at most once) give upper rectangular Stieltjes variation \(\ll_J L^{O_J(1)}2^{-J(j_1+j_2+j_3)}\) for any fixed \(J\). This follows by adding all boundary variations and integrating each mixed derivative along its corresponding side; polynomial factors from side lengths are absorbed by choosing higher Schwartz order. Three successive Abel summations therefore reduce the weighted sum to the supremum of rectangular sums cut inside these same boxes, times this variation and \(1/(A_0^2\lambda)\). This retains the physical \(\ell\)-scale \(\lambda\) even though the weight originally involved a \(v\)-integral; no replacement by a long \(\ell\)-sum is made. Negative frequencies are split by sign as needed. Arbitrarily high tails in \(h_i\) may be dropped, using the fixed margin \(A_0\ll QN^{-c}\); alternatively the remainder of the same box argument handles their residue repetition via the extra factors below.

## Fourier estimate

For any unit \(c,d\) modulo an actual prime \(q\), the matrix indexed by \(h,\ell\bmod q\) with entries
\[
 K_{h,\ell}=\mathrm{Kl}_{q}(ch,d\ell)
   =\sum_{u\bmod q}^{*} e_q(ch\,\bar u+d\ell u)
\]
has \(\ell^2\) operator norm at most \(q\). It is the product of two unnormalized finite additive Fourier matrices (both norm \(\sqrt q\)) and the partial inverse permutation on the unit residues (operator norm \(1\)). No Weil estimate is needed for this spectral norm, and projections to arbitrary subsets cannot increase it. For arbitrary integer intervals \(J_h,J_\ell\) of lengths \(A,B\), bounded input \(a_h\), summing repetitions modulo \(q\) by Cauchy and counting the repeated output residues gives
\[
 \sum_{\ell\in J_\ell}\left|\sum_{h\in J_h}a_h\mathrm{Kl}_q(ch,d\ell)\right|^2
 \ll q^2 A(1+A/q)(1+B/q).
 \tag{3}
\]
This remains valid for clipped intervals and in the presence of the additional unit-modulus phases in (2).

For each fixed \(x\) in (2), apply (3) to both \(q_i\) factors, and then use Cauchy in the common \(\ell\) on the product of the two output vectors. On central/full-size boxes the two \(h_i\)-lengths are \(O(A_0)\), dual length is \(O(\lambda)\). The resulting bound is
\[
 O\bigl(Q^2 A_0(1+\lambda/Q)\bigr)
\]
for the unnormalized triple rectangular sum. On a dyadic outer box the same bound acquires at most a fixed polynomial in the doubling factors, including any \(1+A/q\) from (3). The rapid variation bound above absorbs it in the convergent outer-box sum. For all \(x\) use the triangle inequality, costing at most \(S\), producing the weighted bound
\[
 N^{o(1)}\,\frac{Q^2S}{A_0\lambda}\,(1+\lambda/Q)
\]
for each true \(s,q_1,q_2\). Sum over \(O(SQ^2)\) such triples, with \(|b_{q_i,s}|\le1\). Since \(\lambda\asymp B_0\) and \(A_0 B_0=S^2Q^3/H\), this proves (1). No unsigned majorization across \(h_1,h_2,\ell\) has been used in (3): the saving comes from the truly oscillatory local matrices in the full-size region.

## What is new, and the exact ceiling

When \(B_0\le Q\) in exponent units, (1) beats the old block energy \(Q^3S^{3/2}\) by a power exactly when \(2t+1.5v>.5\), where \(Q=N^t,S=N^v,R=N^u\). For example take
\[
 (t,v,u)=(.200,.068,.272).
\]
These exponents sit in the actual middle setup; all scales are polynomial, \(A_0=N^{.040}\ll Q\), \(B_0=N^{.196}\ll Q\), and \(S<Q\). They also lie in the proposed .06-cutoff improvement's target half-plane \(u+3t+1.8v=.9944<1\) and outside the affine region \(u+v+t=.54>.5\). The old completed bound has exponent .702, whereas (1) has exponent .700, a genuine power on active full-size modes. The squarefree \(s\) variable can have the displayed exponent with largest factor below \(N^{.06}\), e.g. with two true sieve prime factors in small fixed exponent windows near .034. Thus it is not an artifact of a forbidden single large factor.

However, even in the most favorable case \(B_0\le Q\), Cauchy in the physical \((r,s)\) variables now gives the off-diagonal error \((RSQH)^{1/2}N^{o(1)}\), which is \(o(\sqrt N)\) by a power only when \(u+v+t<.5\), exactly the ordinary affine range. In the numerical example it gives exponent .520, not below .5. Residue wrapping \(B_0>Q\) only increases this bound. Hence this exact pair of full prime-local Fourier contractions with the \(s\)-local \(x\)-sum taken absolutely gives an actual gain but cannot by itself certify a beyond-affine block. To gain analytically one must save additionally across \(x\) or across the true \(q_1,q_2\) averages, or obtain an improved prime-local restricted operator on the structured short vectors. This is not a no-go against such joint cancellations, and no P3 bound is claimed.