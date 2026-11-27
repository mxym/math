# Exact discrepancy when independent discrete Gaussians are added

Convolving lattice discrete Gaussians is often an excellent approximation to a wider discrete Gaussian, but it is not an exact identity. For a fixed number of equal-width summands, we compute the leading error from the shortest shell of the dual lattice and give the resulting sharp product total-variation threshold. A finite quotient can preserve the discrepancy exactly or suppress its leading term: for two summands we compute the exact new threshold at every fixed odd modulus as well.

This is a theorem about synthetic, standalone noise laws. It neither assumes that the errors are revealed in Ring-LWE nor gives an analysis of a deployed system. [Genise–Micciancio–Peikert–Walter, Theorem 4.6 and Corollaries 4.7–4.9](https://web.eecs.umich.edu/~cpeikert/pubs/gaussians.pdf) provide broad convolution approximation principles. [Kairouz–Liu–Steinke, Theorem 11](https://proceedings.mlr.press/v139/kairouz21a/kairouz21a-supp.pdf) give an exponential upper bound for two scalar discrete Gaussians. Their scalar completion-of-squares formula already shows the parity dependence for two equal-width summands. We use the standard Gaussian decomposition and Poisson summation, not a new general convolution theorem; the focus is the matching leading constants, sufficient residue statistic, and quotient-dependent product profile.

## On the full lattice

Let Λ be a fixed full-rank Euclidean lattice, and D_(Λ,s) denote the centered probability law on Λ with mass proportional to exp(−π‖x‖²/s²). The parameter s is not the ordinary scalar standard deviation. Fix n≥2, and write P_s for the sum of n IID draws from D_(Λ,s) and Q_s=D_(Λ,√n s) for the reference. Let λ be the length of a shortest nonzero vector of the dual lattice Λ*, let V be the set of dual vectors of length λ (including both signs), and let K=|V|. Set
```
ε_s = exp[−πs² (n−1)λ²/n],     B_n = 2K if n=2, or n²K if n≥3.
```
The exact likelihood ratio dP_s/dQ_s depends only on x modulo nΛ and is not constant for any finite s>0. As s→∞,
```
χ²(P_s,Q_s) ∼ B_n ε_s² .
```
For N independent outputs and N ε_s²→τ∈[0,∞], the total-variation limit is
```
TV(P_s^N,Q_s^N) → 2 Φ(√(B_n τ)/2) − 1 ,
```
with value 1 at τ=∞. Here Φ is the standard normal cumulative distribution function. The likelihood description also means that replacing every output by its residue modulo any integer q divisible by n preserves all these distances **exactly at finite s and N**.

To prove this, let W={(z₁,…,z_n):Σ z_i=0} in the n-fold ambient Euclidean space and let M=Λ^n∩W. For x∈Λ, each tuple summing to x has its norm squared split into ‖x‖²/n plus the squared norm of its deviation from (x/n,…,x/n). The deviations form the lattice coset M+t_x with t_x the orthogonal projection of (x,0,…,0) to W. Consequently
```
dP_s/dQ_s(x) = φ_s(x) / E_(Q_s) φ_s(X),
φ_s(x) = Σ_(y∈M*) exp(−πs²‖y‖²) exp(2πi⟨y₁,x⟩).
```
The second formula is Poisson summation on W for the coset, after suppressing a common constant. The dual lattice here is the orthogonal projection of (Λ*)^n to W: a vector y∈W is dual to M exactly if y_i−y_n∈Λ* for all i, by testing vectors with v and −v in two slots. This condition gives a lift (y_i−y_n)_i, whose projection is y. In particular n y₁ lies in Λ*, proving the exact periodicity. Nonconstancy follows because the coefficient of at least one nontrivial character is a sum of positive terms. In more detail a vector obtained by projecting (v,0,…,0) for a shortest dual v has a nontrivial character; its first component is (n−1)v/n and v is not in nΛ*.

For y=proj_W(z), z∈(Λ*)^n, one has
```
‖y‖²=(1/n) Σ_(i<j) ‖z_i−z_j‖² .
```
If y≠0 at least n−1 unordered pairs have unequal entries. Equality in this count is attained only by a singleton and a complementary class (for n=2 the singleton designation is ambiguous). Each unequal pair contributes at least λ². Equality for the norm therefore occurs exactly by projecting a tuple with a single exceptional entry v∈V after subtracting the common entry. Every such projection contributes the character x↦exp(−2πi⟨v,x⟩/n), regardless of the exceptional position, since the two possible first coordinates differ by v. For n≥3 the nK projections described are distinct; for n=2 each is counted twice. Therefore uniformly on Λ
```
φ_s(x)=1+ε_s F(x)+o(ε_s),
F(x)=a_n Σ_(v∈V) exp(−2πi⟨v,x⟩/n),    a_2=1, a_n=n (n≥3).
```
The error above is uniform by the positive gap to the next shell of the fixed dual lattice M* and a convergent Gaussian lattice series: bound the tail at s≥s₀ using its smallest remaining squared norm and summability at s₀. The reference distribution becomes uniform modulo nΛ by Poisson summation on the fixed sublattice nΛ. Thus E_(Q_s)F→0. The variance under that limiting uniform distribution is B_n: if n≥3 the characters from distinct v are distinct because their differences have length at most 2λ<nλ; when n=2 only the pair {v,−v} shares a character, since equality in the Euclidean triangle bound is otherwise impossible. Orthogonality of characters gives the constants. In particular the centered likelihood difference is uniformly O(ε_s) and has variance ∼B_n ε_s². As a single-output statement TV is also asymptotic to ε_s E|F(U)|/2, with U uniform on Λ/nΛ.

For product TV with 0<τ<∞, under Q_s^N the independent centered likelihood differences have maximal bound O(ε_s) and total variance tending to B_n τ. Their sum converges to a normal, their squared sum concentrates, and the cubic log-likelihood remainder tends to zero. The log likelihood tends to N(−B_nτ/2,B_nτ), and TV is the expectation of the bounded continuous positive part (1−exp(log likelihood))_+, giving the displayed limit. At τ=0 the product chi-square tends to zero. At τ=∞ the product affinity tends to zero since the single-output squared Hellinger distance is ∼B_n ε_s²/8, by Taylor expansion with uniform likelihood bound. Finally whenever n|q the likelihood is measurable in the residue modulo qΛ, so each divergence and every product TV considered here is unchanged by the quotient. This is stronger than just saying that the leading term survives.

For fixed q with n∤q the leading term disappears: modulo lcm(n,q)Λ the reference tends to uniform. Averaging each shortest-shell character over a residue fiber modulo q projects it to the common quotient modulo gcd(n,q)Λ. The projection is zero unless v∈(n/gcd(n,q))Λ*, impossible for a shortest nonzero vector. Thus in that case the quotient χ² is o(ε_s²); this observation alone does not identify the new leading rate for general n.

## Two summands and a fixed odd quotient

Now n=2 and q≥3 is any fixed odd integer (not necessarily prime). Let P_{s,q},Q_{s,q} denote the two laws reduced modulo qΛ. Then
```
χ²(P_{s,q},Q_{s,q}) ∼ 4K exp[−πs²λ²(1+q⁻²)] .
```
If N exp[−πs²λ²(1+q⁻²)]→τ then their product TV tends to 2Φ(√(4Kτ)/2)−1, again with value 1 at τ=∞. For Λ=Z the constant is 8 and λ=1. An even quotient, by contrast, gives exactly the full-lattice error with leading constant 4 for Λ=Z.

For n=2 the earlier dual theta sum simplifies to
```
φ_s(x)= Σ_(v∈Λ*) exp(−πs²‖v‖²/2) exp(πi⟨v,x⟩).
```
Projecting the likelihood to residues means taking its conditional expectation under Q_s. The terms with v∈2Λ* are constant as functions of x and cancel in the likelihood difference. For any other v, apply Poisson summation on qΛ to compute its conditional character average at r modulo qΛ:
```
E_(Q_s)[exp(πi⟨v,X⟩) | X mod qΛ=r]
 = [Σ_(w∈Λ*) exp(−2πs²‖w/q−v/2‖²) exp(2πi⟨w,r⟩/q)]
   /[Σ_(w∈Λ*) exp(−2πs²‖w/q‖²) exp(2πi⟨w,r⟩/q)] .
```
The denominator tends to one uniformly, as does E_(Q_s)φ_s. In the numerator multiply this term by exp(−πs²‖v‖²/2) and put t=2w−qv. Since q is odd, t≡v mod 2Λ*, and in a nontrivial parity class both v and t are nonzero. The smallest possible exponent after extracting πs² is `λ²(1+q⁻²)/2`, attained only when v and t are both shortest. Moreover t=±v in that parity class, by the same length and equality argument used on the full lattice. All other terms in the resulting two-lattice sum have a positive gap and are uniformly smaller (the positive quadratic form in (v,t) gives a convergent lattice series). The corresponding w are (q±1)v/2. As v ranges over shortest vectors with both signs, these yield the leading real function
```
F_q(r)= 2 Σ_(v∈V) exp(2πi⟨[(q+1)/2] v,r⟩/q).
```
The unconditional parity averages of the nontrivial classes, multiplied by their original coefficients, are O(exp(−πs²λ²)) in total by the same formula with quotient q=1. They are lower order when q≥3. Hence the projected likelihood difference is β_s F_q(r)+o(β_s) uniformly, where β_s=exp[−πs²λ²(1+q⁻²)/2]. The multiplier (q+1)/2 is a unit mod q, so distinct shortest vectors give distinct nontrivial characters modulo qΛ (2λ<qλ). Since Q_{s,q} tends to uniform, the variance of the leading function is 4K. Apply the same bounded product-likelihood argument to finish.

For the power-of-two coefficient-orthogonal cyclotomic lattice, this theorem applies to spherical discrete noise (with the codifferent or other fixed scale handled by the actual dual minimum). It does not describe a varying number of summands, lattices growing with s, or a growing modulus in the odd-quotient formula. [The verifier](verify-discrete-gaussian-convolution-residues.js) checks the shortest-shell counts and Fourier multipliers exactly in integer toy examples and gives deterministic numerical illustrations of the scalar full, odd- and even-quotient constants.
