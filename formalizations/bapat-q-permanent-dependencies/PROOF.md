# What the endpoint and perturbation package proves

The complete order-200 counterexample is stated and proved in
`notes/bapat-q-permanent-counterexample/proof.md`. This formal package
certifies the universal endpoint identities in its Section 2 and the
positive-definite perturbation and explicit interval chain of Section 5.
It does not itself certify Sections 3–4. The separate complete complex
formalization now supplies their Gram/Fischer correspondence, recurrence
semantics and integer certificate for an existential perturbation; these
must be connected to this explicit wrapper by an actual correspondence proof.

For any complex matrix A, let Pq(A) be the actual inversion-weighted
permutation polynomial and N=n(n−1)/2. Its derivative at one is the sum
of each permutation product weighted by its actual inversion count.
For distinct rows i,j and columns k,l, restriction of permutations with
those prescribed images is an explicit bijection to bijections between
the complementary row and column sets. Their products split into the
two prescribed entries and the complementary product. This proves the
actual deleted-minor permanent identity, including an empty complement.

Counting an inverted pair gives

    P′1(A) = Σ(i<j,k<l) Ai,l Aj,k per(A^{ij,kl}).

Expanding the ordinary permanent in each of the N row pairs gives the
two terms Ai,k Aj,l and Ai,l Aj,k. Their subtraction proves

    2 P′1(A) = N per(A) − Σ(i<j,k<l) det A[{i,j},{k,l}] per(A^{ij,kl}).

The determinants and complementary permanents here are actual matrix
objects. No counting, determinant or derivative identity is assumed.
At n=0,1 the sums are empty. The n=2 complementary permanent is one.

Conjugating a permutation product of a Hermitian matrix gives the product
for the inverse permutation. The actual inversion count is invariant under
inversion. Pairing the terms therefore proves that Pq(A) is real for real q.

For finite products of m complex entries bounded in norm by r, with each
entry changed by at most t, the product changes by at most m t r^(m−1).
Induction uses the identity

    ai ∏a − bi ∏b = (ai−bi)∏a + bi(∏a−∏b).

The empty and singleton products are handled separately; no division by
the radius is used. If |Aij|≤R, R≥0, and B=A+tI with 0≤t≤1, the entries
of B are at most R+1 in norm. Summing this product estimate, with the
proved inv(σ)≤N and |Sn|=n!, gives

    |P′1(B)−P′1(A)| ≤ N n! n t (R+1)^(n−1).

Put Γ=N n! n(R+1)^(n−1). If Γ≥1 and Re P′1(A)≤−1/2, set ε=1/(4Γ).
Then 0<ε≤1, and Re P′1(A+εI)≤−1/4. For an actual Gram matrix A=VV*,
its quadratic form is nonnegative; adding εI gives a strictly positive
quadratic form on every nonzero vector. Negative endpoint derivative
also ensures non-diagonality: every nonidentity permutation product of
a diagonal matrix is zero, and its identity permutation has zero inversions.

For q in [0,1], induction gives |q^m−1|≤m(1−q). Apply this to each
derivative monomial. Exponents zero and one contribute no derivative
variation; natural truncated subtraction keeps these cases valid. If
the entries of B are bounded by r, summation gives

    |Re P′q(B)−Re P′1(B)| ≤ K(1−q),   K=N(N−1)n! r^n.

If K≥1, choose h=1/(8K) and q0=1−h. Then 0<q0<1, and the derivative
is at most −1/8 throughout [q0,1]. The proved real mean-value theorem
yields Re Pq0(B)−Re P1(B)≥h/8>0. Hence the actual real-axis polynomial
is not monotone on [-1,1]. For n≥3 and R≥0 the required Γ and K bounds
follow from elementary dimension and factorial inequalities. At n=200,
R=1600 these are exactly the parameters of the archived finite note.

`negative_gram_counterexample_transfer` is the full transfer statement:
it constructs the positive-definite non-diagonal matrix and a violating
parameter from an actual Gram matrix with the stated entry bound and
negative endpoint. It does not assert the existence of its input. To obtain
the specified rational parameters, the parallel Gram/Fischer and integer-
certificate proof must be connected to this wrapper inside Lean. The negative
endpoint is not assumed in that parallel complete counterexample theorem.
