# Odd populations: invariant odd-cycle mass and rare solvability

Glitzner and Manlove, *Perspectives on Unsolvability in the Roommates Problem*, arXiv:2505.06717v3, Conjectures 1 and 3, respectively propose odds of solvability of order 1/n (a specific equivalent) and a mean odd-cycle mass of order √(n/log n), for odd n and independent uniform complete strict rankings (IC). Solvability here requires a stable matching with precisely one unmatched person, who ranks everyone above being alone and participates in blocking-pair tests. It is **not** the event that arbitrarily deleting somebody leaves a solvable induced submarket. Write Pₙ for solvability probability and X for invariant odd-cycle mass, including a possible singleton.

**Theorem.** For n tending to infinity through odd integers, X/√n has the same Rayleigh times arcsine limit, in law and all positive integer moments, as for even n in PROOF.md, unconditionally and conditionally on nonsolvability. Moreover,
  Pₙ ~ C n^{3/4} exp(−√n),
  C = e^{1/4}/(2√π) ∫₀^∞ t^{−3/2}(1−exp(−t−2t²)) dt.
The positive, finite integral is a constant. These conclusions contradict the proposed orders for odd n. We give the parity details and prove the precision required for the exponentially small probability. Subscripts N in the proof refer to an even residual population only where so specified.

## 1. Odd-cycle mass

In the absence of a singleton the number m of vertices on cycles ≥3 now is odd (the remaining population has even size). The residual population after removing all odd cycles is always even, so the instancewise signed identity in §1 of PROOF.md still applies. YS Lemmas 3.1–3.3 use n+m even, Dirichlet parameters 1 or 2 and a matching on the n−m others. No step needs n,m separately even: the Gaussian integral is 1/(n+m−1)!! and the concentration proof and the closed-form Dirichlet moments use n,m,n−m only (there are (n−m)/2 matching edges). Likewise the symmetry proof of (2) in PROOF.md and the matching-only profile in YS Prop. 4.2 apply with this parity; the matching-edge sum and its second moment still count (n−m)/2 edges. The multiplier
  A(n,m)=(n)_m(n−m−1)!!/(n+m−1)!!
now starts at A(n,1)=1, with A(n,m+2)/A(n,m)=(n−m)/(n+m+1). In particular it is bounded by C exp(−c m²/n): at m=2k+1 the factors have the form 1−(4j+3)/(n+2j+2), 0≤j<k. Summing their logarithms at m/√n→x gives the same limit exp(−x²/2). The signed coefficient asymptotic (4) was for all integer m; the shifted mesh 2/√n gives exactly (5). For the singleton bound the residual N=n−1 is now even, and the same multiplier is ≤1 starting at m=0 instead of m=1. Hence its probability is at most Cn² exp(−c√n). This (coarse) estimate suffices here. Pittel, *On random stable partitions*, Corollary 4.3, already established an even-population estimate of this type; our use for odd populations changes the residual parity.

Solvability forces a singleton, so Pₙ→0. On solvable instances X=1 (not zero); for all r≥1, E[X^r | nonsolvable]=(E[X^r]−Pₙ)/(1−Pₙ). This leaves the scaled moments and weak limit unchanged.

## 2. Signed expression for odd solvability

Set N=n−1 even. By Mertens (2015), eq. (19), or by fixing the invariant singleton f in the signed identity, one has
  Pₙ = n ∑_{π all even on N labels}(−1)^{L(π)} ∫ K_π(x)∏_{i=1}^N(1−x_i) dx,            (A)
where K_π is the usual stability kernel on N individuals in PROOF.md §2, integrated over the unit cube. Indeed, for a stable extension with f all other people rank their successor above f, and f ranks everyone above itself. Given the successor scores, this contributes exactly the factors displayed. On a solvable instance the unique invariant singleton qualifies and the compatible all-even signed sum is one, by the same symmetric truncation/completion argument with O={f}; on every other instance there is no qualifying permutation. Thus (A) marks a single instance, not its number of near-perfect matchings.

Let m=2k, J=1/(N+m−1)!!, let S=∑x_i, q=∑x_i² and h=∑_{ij∈B₀}x_ix_j. Under the reference measure μ with density J^{-1} e^{−S²/2}∏_A x_i on the positive orthant, S²∼χ²_{N+m}. YS Lemma 3.1 bounds the integrands K_π and the matching-only kernel W of their §4 by C J times this density, on the cube. We normalize the new weight by setting V=exp(√N)∏_i(1−x_i). It is not bounded uniformly on the cube. The following estimates account for this.

**Radial calculation.** Uniformly in m, E_μ exp(2(√N−S))=O(1). Uniformly for m≤√N log N,
  E_μ exp(√N−S)= exp(1/4−m/(2√N)) + O(log³ N/√N).               (B)
To see this, set ρ=√(N+m−1), the mode of the chi density. Writing s=ρ+t, its log-density relative to the mode is g(t)=(N+m−1)log(1+t/ρ)−ρt−t²/2 on t>−ρ. As g(0)=g'(0)=0 and g''≤−1, it is ≤−t²/2. For |t|≤log N the expansion gives g(t)=−t²+O(log³ N/√N) uniformly in m. The normalizing integral in t is bounded below by a constant by integration over |t|≤1. The Gaussian tail after the shift e^{-bt}, b=0,1,2, outside |t|≤log N is smaller than every inverse power of N. Thus E exp(−b(S−ρ))=exp(b²/4)(1+O(log³ N/√N)). Since √N−ρ≤O(N^{-1/2}) for all m, this proves the bound for b=2. In the smaller m range √N−ρ=−m/(2√N)+O((1+log² N)/√N), which gives (B).

## 3. The normalized common kernel

Let G be the symmetric event in YS (3.1), with x_i≤a=2 log² N/√N there and μ(G^c)≤exp(−c log² N). Since 0≤V≤exp(√N−S), Cauchy–Schwarz and (B)'s square-integrability bound make the V-weighted tail outside G superpolynomially small. The normalized stability integrals are bounded by C J for every m. Restoring the m long edges to W on G as in PROOF.md §2, the integrated constant and linear terms are common to all H because VW1_G is still symmetric on the m long vertices. Denote their integral by b'_{N,m}=∫_G VW(1+m x_v x_w) dx for any distinct v,w∈A (drop that term at m=0). For m≤√N log N,
  |∫ V K_π−b'_{N,m}|/J ≤ C(m² log⁸ N/N²+e^{-c log² N}).           (C)
The remainder bound holds since ∫VW≤CJ; outside G use the original canceled kernel and the preceding tail bound.

We need a uniform common-profile error **o(N^{-1/4})**, not merely o(1). On G, YS (4.5) gives
  log[W e^{S²/2}/∏_A x_i]= q/2+h−q²/4+O(log⁸ N/N).
Since ∑ log(1−x_i)=−S−q/2+O(aq), q≤aS=O(log² N), one obtains after multiplying by V, relative to the density Jμ,
  exp(√N−S) · exp(h−q²/4+O(log⁸ N/N+log⁴ N/√N)).
Including the linear term changes this by a relative O(ma²)=O(log⁵ N/√N). All deterministic errors here are o(N^{-1/4}). They can be integrated in absolute value at that order because h≤q/2 implies h−q²/4≤1/4 and E exp(√N−S)=O(1).

It remains to replace h−q²/4 by −1/2. YS Lemma 3.3, (4.5)–(4.6) give Eq=2+O((m+1)/N), Eh=1/2+O((m+1)/N), and both variances O(1/N). On G, |h−q²/4+1/2|≤|h−1/2|+C log² N |q−2|. The exponential difference is bounded by a constant times this quantity because both exponents are upper bounded. Cauchy–Schwarz with the radial second moment bounds its weighted mean by O((1+log² N)(N^{-1/2}+(m+1)/N))=o(N^{-1/4}). Restoring the missing tail and invoking (B) proves uniformly
  b'_{N,2k}/J = e^{−1/4}e^{−k/√N} + o(N^{-1/4}).                  (D)
The fixed-point factor is responsible for both changes from the even-solvability common profile. Simply multiplying the known even solvability probability by n exp(−√n) would miss the change in the cancellation window.

## 4. Scalar cancellation and its constant

For clarity write d_k=[z^k]e^{z/2}√(1−z) and v_k=[z^k]e^{−z/2}/√(1−z), respectively the signed and unsigned all-even long permutation counts divided by (2k)!. The coefficient and multiplier bounds of YS Lemma 5.1 are: d₀=1, d₁=0, d_k<0 (k≥2), ∑d_k=0, ∑|d_k|=2, |d_k|~ e^{1/2}k^{−3/2}/(2√π), |d_k|≤C(k+1)^{−3/2}, and 0≤v_k≤C(k+1)^{−1/2}. Also A_{N,k}=(N)_{2k}(N−2k−1)!! J≤exp(−k²/(4N)). Beyond 2k>√N log N the normalized unsigned kernel bound kills the tail faster than any power. Summing (C) against v_k A costs O(N^{-3/4}log⁸ N)+o(N^{-1/4}) because ∑ k^{3/2}e^{-k²/(4N)}=O(N^{5/4}). Only after grouping signs do we integrate (D) against d_k A; its error is o(N^{-1/4}) since ∑|d_k|≤2. We conclude
  e^{√N}Pₙ/n = e^{−1/4}∑_{k≥0} d_k A_{N,k}e^{−k/√N} + o(N^{−1/4}),
extending A by zero above N/2.

By the cancellation sum and signs, the scalar sum equals ∑_{k≥2}|d_k|(1−A_{N,k}e^{-k/√N}). At k/√N→t>0 its parenthesized factor tends to 1−e^{-2t²−t}. Uniformly it is at most min(1,2k²/N+k/√N), by the product bound for 1−A in YS Lemma 5.1. Thus N^{1/4} times the sum tends to e^{1/2}/(2√π) times the displayed integral in the theorem: truncate t to [δ,L] for Riemann sums; the small-t portion is O(√δ+δ^{3/2}) by the last bound and the large-t portion O(L^{-1/2}) by summing k^{-3/2}. This yields the constant stated above. Finally nN^{-1/4}~n^{3/4} and exp(−√N)~exp(−√n).
