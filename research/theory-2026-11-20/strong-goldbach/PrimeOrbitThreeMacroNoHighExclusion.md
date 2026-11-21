# Three macroscopic labels in a near-smooth six-prime terminal orbit cannot all be intermediate

**Theorem.** Fix a finite F and an odd prime p. Let N→∞ be even, (N,p)=1, log(N/N_F)=o(log N). Suppose a six-prime, strongly connected, closed all-composite factor orbit containing p has exactly three positive logarithmic weights on a weight-convergent subsequence. Then at least one of the three positive weights is **one**. This does not exclude a weight-one label or all such orbits. It extends this no-high exclusion to near-smooth centers without expanding N as a fixed-alphabet product in a logarithm involving two moving small primes.

Use S={p,q,r} for the weight-zero labels; q,r→∞ as in the [multiple-seed theorem](PrimeOrbitMultiSeedMinimal.md). Each label is a unit modulo N. The complete exponent matrix A has zero diagonal, row sums at least two, and nullity(I−A)=2 by the [six-label moving-seed rank theorem](PrimeOrbitMovingSeed.md) and multiple-seed bounds. Write w_j=lim log x_j/log N, W=diag(w), and on a further subsequence P_ij=lim A_ij log x_j/log N. Every row of P is stochastic, with zero diagonal, and rank(P−W)≤4 by taking limits in (A−I)diag(log x_j/log N). Positive-weight columns have bounded integer multiplicities fixed on a subsequence, hence a macro appears on an actual arc exactly if it carries positive mass there. These reductions do not presume bounded exponents at the small primes.

Suppose all three positive weights are strictly below one. All six inputs are O(N^(1−η)) for some fixed η>0, and all complements are asymptotic to N. The three stochastic small rows have disjoint supports because gcd(N−s,N−t) divides the nonzero subpower difference t−s. No small row has p-mass: if v_p(N−s)log p≥c log N along a subsequence, apply the p-adic Subspace Theorem to the primitive pair (N,s) at infinity and at F∪{p}, using coordinates except for X−Y,Y at p. The product is at most (N/N_F)s p^(−v_p(N−s))=N^(−c+o(1)), impossible for the distinct unbounded ratios N/s. If s=p the exponent is zero already. This is precisely the [near-smooth q-row argument](PrimeOrbitFourMacroNearSmoothIntermediate.md), valid for *any* subpower input and with no assertion about q- or r-powers.

## Excluding a small singleton macro block

If some small row at s is supported just on one macro J, then N−s=v J^d with fixed positive integer d, v=N^o(1), and w_J=1/d. No other macro occurs in that actual row. For any small t, gcd(N−J,N−t) divides F(t) for F(Z)=v Z^d−Z+s, since N−J divides F(N). Each F(t)>0 and is subpower. Thus P_J is disjoint from every small row, and belongs to row(P−W) because e_J=P_s is there. The four nonnegative disjoint-support rows consisting of P_J and the three small rows are independent, hence form a basis of row(P−W). For every macro X its X-coordinate in (P−W)_X is strictly negative, and all other coordinates are nonnegative. In this basis X can only lie in a singleton block: a negative coefficient on a block with two nonzero coordinates would make both coordinates negative. Each of the three macro coordinate vectors is therefore one of the four stochastic basis rows.

If only two macros are directly singleton-parented by small rows, the fourth basis row must be P_J=e_H for the third macro H. Let X be the other directly small-parented macro. The same polynomial argument makes P_X disjoint from all three small rows, and it too belongs to the four-row span since e_X does. Necessarily P_X=P_J=e_H. Each of J,X thus has the same fixed exponent 1/w_H at H, so their complement gcd has logarithmic weight one, contradicting divisibility by |J−X|=O(N^(1−η)). Fewer than two direct parents cannot supply three distinct macro singleton blocks.

Otherwise all three macros R_i have respective distinct direct small parents s_i, with N−s_i=v_i R_i^{d_i}, v_i subpower. Each P_{R_i} is disjoint from all small rows; thus no macro targets any macro, even by an actual single occurrence. All macro complements factor on S. Eliminate the macro coordinates from Af=f to obtain the three-by-three first-return exponent matrix K on S; it is irreducible with all row sums ≥2 and nullity(I−K)=2. So K−I is rank one and equals ab^T for positive integer vectors a,b with gcd_i a_i=1. Indeed irreducibility precludes zero rows or columns of K−I; its rank-one off-diagonal entries are therefore strictly positive, giving positive factors since the size is three. Taking a primitive integer generator of its column direction makes the other factor integral. Write Z=∏s_j^{b_j}>1. The exact first-return monomials give

    s_i Z^{a_i}=v_i(N−R_i)^{d_i}.

Reducing modulo N yields Z^{a_i}≡(−1)^(d_i+1); primitivity gives Z²≡1 mod N and thus Z≥sqrt(N+1). Comparing real logarithms gives a_i log Z=d_i log N+o(log N), so a_i are bounded and can be fixed. Their ratios are exactly those of d_i and hence a_i=d_i/g for g=gcd_i d_i. At the s_i valuation, the left side of the displayed equation is 1 modulo a_i, whereas the right side is zero modulo d_i since s_i∤v_i. Thus a_i=1 for every i and all d_i have the same value d. Now v_i/s_i=Z/(N−R_i)^d. These positive subpower rationals are pairwise within a relative O(N^(−η)) since d is fixed; clearing their subpower denominators forces equality. But each reduced denominator is its own distinct prime s_i. This excludes the singleton-macro case.

## The only remaining stochastic pattern

Quotient the row space by the span of the three disjoint small rows; the quotient has dimension at most one. Call a macro unused if it is absent from all small rows. Its coordinate functional descends to the quotient and takes a negative value on its own adjusted row (P−W)_X. Two unused macros would give nonzero coordinate functionals of opposite signs on this one-dimensional quotient: on either macro's own row its coordinate is negative and the other's nonnegative, and the other's nonzero functional cannot vanish on this nonzero quotient vector. Every outside macro row has both coordinates nonnegative, hence both zero. Since no small row targets them, those two macros could not be reached from outside in the actual directed graph. This contradicts strong connectivity.

Within a common small-row block with two macro coordinates B,C, the functional taking a vector y to y_B/P_{sB}−y_C/P_{sC} descends to the quotient and is strictly negative on (P−W)_B and strictly positive on (P−W)_C. In particular those two nonzero quotient vectors have opposite orientations. Three macros in a single block are impossible because that would make three nonzero vectors on a line pairwise opposite. If there is one unused macro, then no two *other* macros can share a block: their opposite quotient orientations are incompatible with both having nonnegative coordinate at the unused macro (a nonzero functional on that line). The two covered macros would therefore need two different blocks, each accompanied by a small-column entry since no singleton macro is allowed. Only q,r are available. The third small row then has no column left, impossible.

Thus all three macros are covered; one per block would need three accompanying small entries, but only q,r are available. The macro counts in the three blocks must be 0,1,2. Their exact form, denoting the small inputs by I,J,K, is

    P_I supported on {t},     P_J on {s,A},     P_K on {B,C},

with {s,t}={q,r} and A,B,C the three macros. In particular I≠t. An additional unused coordinate is the p column: all small rows vanish there and the B,C adjusted rows give opposite nonzero quotient vectors on which the p-coordinate is nonnegative. Hence that functional vanishes on the entire quotient and there is no p-mass anywhere. This last fact is not an assumption on the actual p-exponents.

## A fixed exact eigenspace, despite two moving small primes

Let R be the fixed three-column exponent chart at A,B,C and E the corresponding three identity columns. The columns of F_3=R−E are independent: for F_3 x=0 the J row forces x_A=0 and the K row gives b x_B+c x_C=0 for actual fixed exponents b,c>0. The B row gives x_B=R_BC x_C since x_A=0 and there is no loop. This forces x_B=x_C=0. Thus the fixed rational left kernel H of F_3 has dimension three and contains e_I^T as row I uses no macro. For h∈H, h(A−I_6) has support only on S. These images form a one-dimensional space since the full left 1-eigenspace has dimension two. As e_I is in H and its image has −1 at coordinate I, for each fixed integral h∈H we have

    h(A−I_6)=λ_h(e_I^T A−e_I^T)

with λ_h an integer (evaluate at I). Moreover λ_h is bounded uniformly on this sequence for each h: at t≠I the denominator A_It is asymptotic to log N/log t since P_It=1, while |[h(A−I_6)]_t|=O_h(log N/log t). Fix λ_h on an integral basis of H along a subsequence. The full left 1-eigenspace is then a *fixed* rational plane.

Every nonzero member of this plane has both signs by positive Perron orthogonality, and each sign support contains a cycle by following a same-sign predecessor in hA=h; looplessness implies at least four supported indices. For any macro killed by a fixed nonzero integral h on this plane, square the identity ∏((N−x)/x)^{h_x}=1 and expand modulo N² at units to get

    2∑ h_x/x ≡ 0 (mod N).

Clearing denominators with the product of all supported prime labels makes the numerator nonzero for large N: some growing macro belongs to the support because there are only three small indices, and modulo that macro the cleared numerator is nonzero (h is fixed). If the sum of the weights of the remaining two macros were <1, this nonzero integer would have magnitude <N, impossible. Killing each macro in turn proves every pair of macro weights sums to at least one. This reasoning also precludes any eigenrow simultaneously killing two macros, in the present no-high case.

In the small K row the mass identity is b w_B+c w_C=1, and therefore b=c=1 and w_B+w_C=1. In particular there is the exact factorization N−K=v B C for a positive integer v=N^o(1). Choose a fixed nonzero integral eigenrow h with h_A=0; necessarily h_B h_C≠0.

## Using the actual pair factorization in the inverse congruence

All six labels are units modulo N. From vBC=N−K one has 1/B≡−v C/K and 1/C≡−v B/K. In the inverse congruence above, clear the small denominators by D=pqr and K. This gives divisibility by N of the integer

    2D [ K∑_{x∈S} h_x/x − v(h_B C+h_C B) ].

Its absolute value is O(N^(max(w_B,w_C)+o(1)))=o(N), because D,K,v are subpower and the weights are fixed strictly below one. Thus the bracket vanishes exactly. It implies h_B C+h_C B=O(N^o(1)) and consequently B/C approaches the fixed positive rational ρ=−h_B/h_C with power-saving accuracy (since C is macroscopic). The weights of B and C are equal, hence both 1/2.

Also K∑_{x∈S}h_x/x is an integer. For every small prime x≠K, reduction after multiplication by D gives x|h_x by coprimality. If K=p this kills both q,r eventually, impossible with h_A=0 and support size at least four. Otherwise one of q,r equals K and the other is killed, leaving h supported on exactly p,K,B,C with h_K≠0.

Finally the exact multiplicative eigenrow identity, after logs divided by log N, yields h_p+h_K+(h_B+h_C)/2=0, since B,C have weight 1/2 and all complements have weight one. Squaring that identity and using (N−x)/N=1+O(N^(−η)), the positive ratios B/C=ρ(1+O(N^(−η'))) and BC=(N−K)/v, gives

    v^(h_B+h_C)=p^(2h_p) K^(2h_K) ρ^(h_B−h_C) (1+O(N^(−η'')))

with some fixed η''>0. This algebra holds for signed powers too: B^(2h_B) C^(2h_C)=(BC)^(h_B+h_C)(B/C)^(h_B−h_C), and 2∑h_x=h_B+h_C cancels the powers of N. The two rationals have logarithmic height o(log N), because every power is fixed and p,ρ are fixed, K,v subpower. A nonzero relative difference cannot be this small by clearing the subpower denominators and numerators. Hence equality is exact. But the moving prime K is eventually coprime to the fixed pρ and to v since v divides N−K and (N,K)=1. The K valuation of this equality contradicts h_K≠0. This finishes the no-high case.

## Context and scope

The prime-factor-orbit construction is related to [Bożek, arXiv:1909.09900](https://arxiv.org/abs/1909.09900), and the publicly indexed abstract of [Kelanemer, SSRN 7274460](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) describes an overlapping terminal exponent-matrix framework and broader claims. The latter full text was not retrievable for comparison, so this note makes no priority claim and does not rely on that preprint. In combination with the [macroscopic lower bound](PrimeOrbitMacroscopicRank.md) and the [four](PrimeOrbitFourMacroNearSmoothExclusion.md)- and [five](PrimeOrbitFiveMacroExclusion.md)-macroscopic exclusions, this leaves exactly three positive limiting weights, at least one equal to one, in the specified fixed-seed, six-label, near-smooth terminal setting. It does not eliminate those remaining patterns or prove Goldbach.
