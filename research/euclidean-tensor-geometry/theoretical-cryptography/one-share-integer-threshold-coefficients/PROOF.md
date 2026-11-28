# Arithmetic bounds for one atomic integer share at exact threshold

## 1. Model and statement

Fix integers n≥3 and 2≤t<n and one public setup. Let M be a nonzero additive subgroup of Z^D for a finite D, with its displayed integer coefficient embedding. A sharing is a tuple (s,x_1,…,x_n) in M^(n+1). Dealer generation may be nonlinear, may mix the D coordinates, and may have any joint randomness. We assume only the following form of correctness: each t-set T has a fixed public vector λ_T of integers, zero off T, such that s=Σ_i λ_T,i x_i for every sharing considered. Larger sets may use a t-subset. Write B=max_T,i |λ_T,i|. This is a coefficient **magnitude**, not a number of bits or a share size. The secret and each atomic share are measured in the **same fixed ambient module and coefficient embedding**. The coefficient of the target s is exactly 1; reconstructing c·s followed by division is not a permitted normalization. Replacing the secret alphabet by a sublattice is an explicit change of the set of protected secrets, not a rescaling of the common embedding.

Here is the extra algebraic condition, stated independently of any security experiment. In Q^(n+1) let e_i be the standard basis, with e_0 representing the secret. Form the subspace W spanned by the public relations e_0−Σ_i λ_T,i e_i and set E=Q^(n+1)/W, with v_i the class of e_i. Require

> (AR) For every |U|≤t−1, v_0 is not in the rational span of {v_i:i∈U}.

Equivalently the published relations must not imply a rational scalar identity for the secret supported on one of these smaller sets. This is an explicit structural assumption, not part of the syntax of integer reconstruction. Two natural sufficient conditions are:

* For two distinct allowed secrets there is, for every U as above, at least one local view in the support of both conditional laws. If AR failed the same view would imply the same secret, a contradiction. In particular any pairwise statistical privacy guarantee with TV strictly less than one for such two secrets suffices. The observation works for cross-coordinate dealer maps because the implied scalar identity holds in Q^D on the entire tuple.
* In the SEC scalar-matrix genre, write the formal shares as x_i=g_i s+H_i r, assume the authorized identities hold on the formal independent input coordinates, and impose g_U∈Col_Q(H_U) (in particular g_U∈Col_Z(H_U)). Every linear consequence supported on U would provide rational a with a^T H_U=0 and a^T g_U=1, impossible under the stated column condition. No modular, computational or distributional security equivalence is asserted.

Put k=n−t. With AR, the following necessary coefficient bounds hold:
    
    B ≥ max(t, k+1),
    k ≤ max_(1≤a,b≤B) #{d>0 : d divides ab, d≤B−a, ab/d≤B−b}
      ≤ max_(1≤N≤B²) τ(N),                                      (1)

where τ is the number of positive divisors. In particular as k→∞, using natural logs,

    log B ≥ (1/(2 log 2) − o(1)) log k log log k.               (2)

This rules out polynomial coefficient magnitude in k, and hence in n whenever k≥n^c for a fixed c>0. It does not rule out polynomial bit length.

For a fixed AR reconstruction table put

    L = lcm { |λ_T,i| : |T|=t, i∈T }.

Two secrets whose conditional share laws overlap at every t−1 view must differ by an element of L M. Conversely, for the same table every finite set of allowed secrets in L M admits finite-support sharings with exact reconstruction and arbitrarily small pairwise TV error on all t−1 views. A coset meeting the integral solution set is handled by translating a fixed integral solution. Moreover

    lcm(1,…,t) divides L.                                      (3)

Thus under the overlap hypothesis any distinct protected secrets in the coefficient embedding have infinity-distance at least lcm(1,…,t) in the common embedding. If all allowed secrets satisfy ||s||∞≤β_sec, this forces the **secret amplitude bound** β_sec≥lcm(1,…,t)/2; it is not a bound on the reconstruction magnitude B. For t=n−1 the construction below simultaneously attains the universal magnitude and spacing bounds: B=t and L=lcm(1,…,t).

## 2. The quotient and the t+1 local certificate

Every coefficient λ_T,i with i∈T is nonzero, since omitting a zero coefficient would contradict AR. Every t-set of v_i is linearly independent: a dependence would let us remove one vector without reducing its span, again contradicting AR. Fix a t-set T_0. Its span contains v_0. For i outside T_0 choose any fixed (t−1)-subset J of T_0; the reconstruction equation for J+i with nonzero coefficient at i places v_i in span(v_0,{v_j:j∈J})⊆span(v_{T_0}). Thus dim E=t, and every t-set of shares is a basis.

Choose R⊆[n] of size t+1. For i∈R let r_i∈Z^R be the vector for T=R\{i}, extended by zero at i. Its only zero is at i. Each r_i reconstructs v_0. Their affine hull has dimension exactly one. Indeed, at least two r_i differ. If its direction space had dimension ≥2, a coordinate projection onto some two coordinates would have rank two (a nonzero 2×2 minor in a matrix of a direction basis). The affine hull would then contain a rational vector zero on these two coordinates. As an affine combination of r_i it would still reconstruct v_0, now on at most t−1 coordinates. This contradicts AR.

Choose an integer primitive direction d for this line by dividing the difference of two distinct r_i by the gcd of its coordinates. Then r_i=r_*+a_i d with all a_i integers: by Bézout some integer linear functional takes d to 1, so any rational multiple a_i d in Z^R has integral multiplier. The a_i are distinct. Each d_j≠0, since coordinate j is zero at r_j and not at any other r_i. The zero at r_j gives the exact identity

    (r_i)_j = d_j (a_i−a_j).

Taking extreme parameters gives an entry of magnitude at least t, proving B≥t. For every prime power p^e≤t, two of the t+1 parameters have equal residue modulo p^e. Their difference is nonzero, so some nonzero table entry is a multiple of p^e. Taking all such prime powers proves (3). For reference, lcm(1,…,t)≥2^t/(t+1) without a prime estimate: the valuation of binom(t,j) at p is a sum of terms each zero or one, at most floor(log_p t) nonzero terms by the factorial formula. Thus each binomial coefficient divides this lcm; the largest is at least 2^t/(t+1).

## 3. Two-dimensional reduction and divisor bound

Fix J of size t−2 (J is empty when t=2), and work in E/span(v_J). Its dimension is two. Denote the classes of v_0 and v_i, i outside J, by w_0 and w_i. Here w_0≠0, every pair w_i,w_j is independent (J+i+j is a basis), and no w_i is parallel to w_0 by AR. Fix a basis (w_0,u) and write w_i=β_i(z_i w_0+u). The β_i are nonzero rational numbers and the slopes z_i∈Q are all distinct. Projecting the public identity for J+i+j and solving two scalar equations gives its coefficient at i as

    λ_{J+i+j,i} = 1/(β_i (z_i−z_j)).

There are m=k+2 slopes. Let i_−,i_+ be the minimum and maximum, and let Δ=z_{i_+}−z_{i_−}>0. Let a,b be the absolute values of the two coefficients on these endpoints in the reconstruction for J+i_−+i_+. They are positive integers ≤B. For any interior point i, set z=(z_i−z_{i_−})/Δ in (0,1). The absolute coefficient on i_− in the pair reconstruction for J+i_−+i is A=a/z; the one on i_+ for J+i+i_+ is D=b/(1−z). Hence A,D are integers bounded by B, with A>a and D>b, and

    (A−a)(D−b)=ab.

Distinct z give distinct positive divisors A−a of ab, with the cutoffs in (1). Applying this to all m−2 interior slopes proves (1). Also the m−1 distinct absolute coefficients on i_−, one for each other slope, are positive integers ≤B. This proves B≥k+1.

For (2), fix δ∈(0,1), use Y=(log B)^(1−δ), and consider N≤B². For large B, n_p=v_p(N) satisfies Σ_{p>Y} n_p≤2 log B/((1−δ) log log B). The contribution of these primes to log τ(N) is at most log 2 times this sum, since e+1≤2^e. The primes ≤Y contribute O(Y log log B), since there are at most Y of them and each n_p≤2 log B/log 2. This is o(log B/log log B) at each fixed δ>0. Letting δ→0 gives the uniform upper bound (2 log 2+o(1)) log B/log log B for log τ(N). Now log B≥log(k+1) by the previous paragraph, so (1) gives (2) by multiplying by log log B and using log log B≥log log k for large k.

## 4. Exact secret-spacing criterion for one table

For necessity, fix distinct secrets s,s′ and a t-set T, j∈T. Let U=T\{j}. A shared view in the two supports gives two full outcomes with the same shares on U. Subtracting the reconstruction identity yields s−s′∈|λ_T,j| M. In any Z-module, aM∩bM=abM for relatively prime positive a,b: write x=ay=bz and combine x=(ua+vb)x=ab(uz+vy) with ua+vb=1. Apply this to distinct maximal prime powers in L; the divisibilities by the entries imply s−s′∈L M. Using the integer coefficient embedding gives the asserted infinity-distance and bound.

For sufficiency first consider scalar shares (M=Z). Let U be any t−1 set. The vectors v_0 and v_i for i∈U form a basis of E. There is a unique rational functional f_U on E with f_U(v_0)=1 and f_U(v_U)=0. Let (1,h^U) be its values on all generators. This is a solution of the allowed relations with secret 1, h^U_U=0, and

    h^U_i=1/λ_{U+i,i} for i outside U.

In the normalized lattice of all integral scalar solutions of the public equations, let I_U be the set of secret values of solutions vanishing on U. Every such solution is a scalar multiple of (1,h^U): the values on v_0,v_U determine the functional. Hence

    I_U = L_U Z,    L_U = lcm_{i outside U} |λ_{U+i,i}|,
    ⋂_U I_U = L Z.

This describes L as the generator of an intersection of **dual solution-image ideals**. It is not the primal intersection of the row span of an unauthorized set with the target line; that rational intersection is zero by AR. The integral analogue of a primitive unit-target annihilator, used by integer span programs, is stronger: it would force L_U=1. The basic ideals and normalization are classical; the content here is their exact value in terms of one-share threshold reconstructors and the universal bound (3).

Consequently L h^U is integral. Fix U_0 and for secret s∈L Z use the particular solution x^0(s)=s h^{U_0}. All (0,x) integral solutions form a lattice K in Z^n (an additive subgroup with a finite integer basis). For a bounded finite secret set, sample each basis coefficient independently uniformly on {0,…,H−1} where H is a power of two; add this random element of K to x^0(s). For secrets s,s′ and U, the vector (s−s′)(h^U−h^{U_0}) is in K and cancels the particular-solution difference on U. If its basis coordinates are a_1,…,a_r then the TV distance of the two uniform boxes before projecting onto the view is

    1−∏_j (1−min(1, |a_j|/H)) ≤ (Σ_j |a_j|)/H.

Indeed the box intersection is a product of the coordinate intersections, and all atoms in each box have the same mass. Applying the projection to views cannot increase TV. Take H large versus the maximum finite numerator over all pairs and U; smaller views follow by marginalization. The same proof works for general M by using any integer basis of M and running independent copies for the coordinates in that basis. Equivalently, the integral homogeneous solution group inside M^n is itself a free abelian group of finite rank, and the cancelling vectors already belong to it. If translating to a different coset, add a fixed integral solution for its base secret to every tuple.

This is a finite-support construction for the conventional fixed-view, pairwise statistical criterion. It does not establish hard-core or continual local-leakage resilience. For a general public table the construction is existential. All admissible equations on exactly t coordinates have unique coefficients in E; if several forms are advertised, AR is imposed on all of their relations and uniqueness follows because the t vectors are independent. The necessity applies to every displayed equation, without assuming its nonzero entries have gcd 1. The explicit family below avoids dependence on enumerating all t-sets.

## 5. Explicit moment-table construction

Write player labels as 0,…,n−1 in this section (distinct from the formal secret index of §1). Let k=n−t as before. Work first over Z. Require of the share tuple x the k lower-moment equations and secret map

    Σ_j j^a x_j = 0  for 0≤a<k,
    Σ_j j^k x_j = s,                                          (4)

with 0^0=1. For a t-set T let O be its omitted k-set. The polynomial P_O(X)=∏_{u∈O}(X−u) is monic of degree k and zero at all omitted labels. Therefore (4) gives the exact integer reconstruction

    s=Σ_{j∈T} P_O(j) x_j.

The maximum magnitude of any entry is (n−1)!/(t−1)! (in particular ≤(n−1)^k). At each j the number of distances |j−u|≥d to other labels is (j−d+1)_++(n−j−d)_+≤n−d for d≥1, so the k largest distances are no larger, term by term, than those at endpoint 0. The endpoint attains the product by choosing the k largest.

Let L_* be the lcm of these entries. For each prime p the number of nonzero distances from j divisible by p^e is floor(j/p^e)+floor((n−1−j)/p^e)≤floor((n−1)/p^e), with equality at the endpoint for all e. To maximize the valuation of a product of k distinct chosen distances (distinct labels), select the k with greatest valuations. The maximal sum of valuations for a fixed j is the sum over e of the smaller of k and the count just computed. Thus exactly

    v_p(L_*) = Σ_{e≥1} min(k, floor((n−1)/p^e)).               (5)

This gives an algorithm using primes ≤n−1 and implies L_* divides (n−1)!.

For any U of size t−1, O′=[n]\U has k+1 labels. Write h^{O′} for the vector zero off O′ with entries 1/∏_{u∈O′\{j}}(j−u) at j∈O′. These are the leading coefficients of the degree-k Lagrange basis on O′. Interpolation of X^a for 0≤a≤k proves that h^{O′} has lower moments zero and kth moment one. It witnesses AR for the displayed table because each putative reconstruction on U would hold on this rational solution with zero view and nonzero secret. Multiplying h^{O′} by L_* gives an integer vector, since each denominator is an actual nonzero entry for the omitted k-set O′\{j}. Set μ^{O′}=L_*h^{O′}; every entry has magnitude ≤L_*.

For explicit bounded sampling let A≥1 be an integer; take secrets s=L_*c, |c|≤A. Fix one (k+1)-set O_0 and take x^0(s)=c μ^{O_0}. A basis for the integral homogeneous kernel of all k+1 moments has t−1 vectors u_ℓ (0≤ℓ≤t−2), the coefficient vectors of X^ℓ(X−1)^(k+1), in degrees 0,…,n−1. Each vector annihilates the moments because a finite difference of order k+1 of a polynomial of degree at most k is zero. Their leading positions have coefficient ±1. Successively subtract integral multiples to clear the first t−1 coordinates of any integral kernel vector. A remainder supported on the last k+1 coordinates is zero by the Vandermonde equations; this proves that these vectors are an integer basis.

Sample t−1 uniform independent coefficients on {0,…,H−1} with H a power of two, and add their combination of the u_ℓ to x^0(s). Every share has magnitude at most

    A L_* + (H−1) 2^(k+1),

because in any fixed position the magnitudes across the shifted binomial rows sum to at most 2^(k+1). The dealer uses exactly (t−1) log₂ H fair coin tosses. Given any two secrets and U maximal unauthorized, use the cancelling vector (c−c′)(μ^{[n]\U}−μ^{O_0}). Its infinity norm is at most 4A L_*. The basis coordinate at ℓ is the X^ℓ coefficient of division of the corresponding vector polynomial by (X−1)^(k+1), hence has magnitude bounded by

    4A L_* Σ_{j=0}^ℓ binom(k+j,k)
        ≤ 4A L_* binom(n−1,k+1).

This uses the power-series expansion of (1−X)^(-k−1) and ℓ≤t−2. Thus for any 0<ε≤1 it suffices to take H a power of two with

    H ≥ 4A L_* (t−1) binom(n−1,k+1) / ε.

The box argument gives pairwise view TV≤ε and monotonicity covers every smaller U. The explicit arithmetic uses polynomial bit complexity in n, log A and log(1/ε), with each such parameter supplied in the usual integer or precision representation. To share a bounded vector in Z^D, repeat independently in each coordinate with ε/D; the shared object per party is still one element of the fixed common module, the public scalar reconstruction coefficients are unchanged, and the union coupling gives TV≤ε. This uses D times as many scalar coins and the bound on each share coefficient is unchanged after using the enlarged H.

When k=1 (t=n−1), (5) gives L_*=lcm(1,…,t), and the coefficients are j−u, of maximum magnitude t. The same family therefore achieves both exact lower boundaries together, with a finite interval of multiples of L_*, not an arbitrary unscaled secret interval. Privacy can be made arbitrarily close to perfect, not claimed exact. Neither positive nor negative results in this note treat two or more atomic shares per party, an arbitrary coordinate-mixing reconstruction map, or the endpoints t=1,n.
