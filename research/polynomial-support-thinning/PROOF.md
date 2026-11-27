# Polynomial support thinning on anchored product grids

## 1. Setup and exact theorem

Let F be any field, A_i ⊂ F distinct-point sets with q_i=|A_i|≥2, a_i∈A_i distinguished anchors, and G=∏_(i=1)^n A_i. Let f be nonzero as a function G→F. Use its unique reduced polynomial representative, with degree at most q_i−1 in variable i, and let d be its total degree. Existence and uniqueness follow by tensor-product interpolation; reducing modulo the monic coordinate vanishing polynomials never increases total degree. Write S={x:f(x)≠0}.

For θ=(θ_1,…,θ_n)∈[0,1]^n let P_θ be the product law whose i-th factor is (1−θ_i)δ_(a_i)+θ_i Unif(A_i), and write μ(θ)=P_θ[S]. If 0<θ'_i≤θ_i≤1 for all i, put r_i=θ'_i/θ_i, list the factors in nondecreasing order, and put D_0=min(d,n). Then
```
   μ(θ') ≥ μ(θ) ∏_(j=1)^D_0 r_(j).                       (1)
```
The empty product is 1. Let A={i:r_i<1} and m=|A|. Equality in (1) is characterized as follows:
- If d≥m, equality holds exactly when f vanishes on each of the anchor faces x_i=a_i with i∈A, equivalently its reduced representative has the factor ∏_(i∈A)(X_i−a_i). For m=0 the condition is vacuous.
- If d<m, equality holds exactly when f is a nonzero constant times ∏_(i∈K)(X_i−a_i) for a d-element K⊂A whose product of factors r_i is minimal. This includes d=0 and allows all ties for K.

The bound is sharp for every allowed degree, every grid and every positive parameter pair. If d≤n, choose the product of d best coordinates' anchor factors. If d>n, choose f=∏_(i=1)^n (X_i−a_i)^(e_i), with 1≤e_i≤q_i−1 and Σe_i=d; the possible total degrees are all integers from n to Σ(q_i−1), and its support avoids all anchor faces. For d>n the exponent count remains D_0=n: repeated coordinate powers do not introduce additional thinning factors.

If some θ'_i=0 but all θ_i>0, (1) extends by continuity. For d>0 the right side is 0; equality holds exactly when f vanishes identically on the face fixing every zero-final-parameter coordinate to its anchor. For d=0 it is equality always. When θ_i=0 at both endpoints, first restrict to those coordinates' common anchor face; if the restriction is zero then both probabilities are zero, otherwise use the restricted grid and its reduced degree. One-point coordinate grids can be treated by the same restriction. These conventions do not use undefined ratios.

## 2. An ordered-grid support lemma

Put D=Σ_i(q_i−1). Order the elements of each A_i arbitrarily, say a_(i,0),…,a_(i,q_i−1), temporarily with no restriction on where the anchor lies. Encode a point by its ranks u=(u_i), and write |u|=Σ_i u_i. For any f and support S as above, the uniform support average satisfies
```
   (D−d)/2 ≤ E_(x∈S)[sum of coordinate ranks of x] ≤ (D+d)/2.    (2)
```
This extends [Potapov, Theorem 3] from binary grids; the proof uses his matching idea but with Newton products and interpolation weights.

Define L_i(T)=∏_(b∈A_i)(T−b) and w(x)=∏_i L_i'(x_i)^(-1). For every polynomial H of total degree <D,
```
   Σ_(x∈G) w(x) H(x) = 0  in F.                               (3)
```
In one coordinate, Lagrange interpolation of T^k for 0≤k≤q_i−1 gives Σ_(b∈A_i) b^k/L_i'(b)=0 for k<q_i−1 by its top coefficient. For any monomial of total degree <D some coordinate has exponent <q_i−1; the product sum therefore vanishes, even if other coordinates have higher exponents. This proves (3) for any characteristic.

For each rank vector u define N_u(X)=∏_i∏_(j<u_i)(X_i−a_(i,j)). Its value at rank vector v vanishes unless u≤v componentwise; N_u(u) is nonzero. On the rank vectors of S, the matrix M=(N_u(v))_(u,v∈S) is triangular in a linear extension of that order, with nonzero diagonal. Its weighted Gram matrix B=M diag(w(v)f(v)) M^T is nonsingular because every diagonal weight is nonzero. A nonzero term in the determinant therefore gives a permutation π of S with B_(u,π(u))≠0 for each u. But
```
   B_(u,v) = Σ_(x∈G) w(x) f(x) N_u(x) N_v(x).
```
Equation (3) implies |u|+|v|≥D−d whenever B_(u,v)≠0. Sum over u and v=π(u) to get the lower bound. Reversing each coordinate order transforms |u| into D−|u| and gives the upper bound.

Now put the anchor first in every coordinate, and uniformly permute the other q_i−1 ranks. An anchor always has rank 0, and every nonanchor has expected rank q_i/2. Taking the expectation of the upper bound in (2) gives
```
   Σ_i [1 − q_i P_(x∈S)(x_i=a_i)] ≤ d.                         (4)
```
For every coordinate subset T the same sum restricted to i∈T is at most min(d,|T|). Indeed fix all outside values and apply (4) to each nonempty fiber of S, where the restriction has degree at most d. Average using the conditional fiber sizes in the uniform law on S; empty fibers contribute zero. Each term is at most 1, giving the further |T| cap. Thus for arbitrary weights λ_i≥0, summation by layers of λ (or summation by parts after sorting) yields
```
   Σ_i λ_i [1 − q_i P_(x∈S)(x_i=a_i)]
      ≤ Λ_d(λ) := sum of the min(d,n) largest weights.             (5)
```
To see the identity, integrate the subset bound over T_t={i:λ_i≥t}, t>0. The integral on the right is ∫ min(d,|T_t|)dt=Λ_d(λ). Individual terms on the left may be negative; the identity uses finite linearity, not nonnegativity of those terms.

## 3. Thinning and the log-derivative

Sample an active set J by independent indicators with probabilities θ_i. Fix inactive coordinates to their anchors and sample the active ones uniformly and independently, giving precisely P_θ. Let M(J) be the nonvanishing probability in that uniform restriction. For i∈J, M(J\{i}) is the nonvanishing probability when its i-th coordinate is the anchor. Since the uniform probability of that anchor is 1/q_i, for M(J)>0,
```
   M(J) − M(J\{i}) = M(J)[1 − q_i P(x_i=a_i | f(x)≠0,J)].
```
When M(J)=0 both quantities are 0. Apply (5) to every nonempty restriction, with the same d upper bound; the weighted sum on that restriction is at most Λ_d(λ) M(J). (The largest weights over J alone can only give a smaller bound.)

Differentiating the multiaffine expectation μ(θ)=E_J M(J) gives
```
   θ_i ∂_i μ(θ) = E_J[1_(i∈J)(M(J) − M(J\{i}))].
```
Indeed, condition on the independent set of all other active coordinates; the contribution is an affine interpolation between their M-value and that of the set with i added. This identity also holds at θ_i=1 by polynomial evaluation. Summing with weights λ_i gives
```
   Σ_i λ_i θ_i ∂_i μ(θ) ≤ Λ_d(λ) μ(θ).                         (6)
```
Now λ_i=−ln r_i and along 0≤s≤1 put θ_i(s)=θ_i e^(−sλ_i). The original distribution has full grid support at every s; hence μ(θ(s))>0. By the chain rule the derivative of ln μ(θ(s)) is at least −Λ_d(λ). Integrating gives (1), since e^(−Λ_d(λ)) is the product in that bound.

## 4. All positive-parameter equality cases

If d≥m, Λ_d(λ)=Σ_i λ_i. For i∈A, letting μ_0 be the nonvanishing probability when x_i is set to its anchor and the other coordinates keep their laws, the exact identity θ_i ∂_i μ = μ−μ_0 holds by the affine interpolation in θ_i. Each μ_0 is nonnegative. The gap in (6) is then Σ_(i∈A) λ_i μ_0. Equality of the integral occurs exactly if it vanishes throughout the interval, equivalently these anchor faces have no support (all other-coordinate distributions have full support). By uniqueness of the reduced polynomial, vanishing identically on x_i=a_i gives the factor X_i−a_i. In the coordinate-shifted reduced monomial basis, this vanishing is precisely absence of every term with exponent of i zero. Hence all factors are present jointly. The converse also follows from the same derivative identity.

Now suppose d<m. Condition on every inactive coordinate value. The law on inactive coordinates does not change. Their probabilities are all positive, and (1) applies on each active fiber with its own reduced degree d_z≤d. If the whole comparison is an equality, every nonzero fiber must itself have equality at the global bound. Since every active λ is positive and d<m, a nonzero fiber of degree d_z<d would have a strictly better lower bound (Λ_(d_z)<Λ_d), impossible. Thus every nonzero fiber has degree d and equality with all λ positive. The case d=0 is simply a nonzero constant; below assume d>0.

On a nonzero fiber with every coordinate active, F(s)=μ(θ(s)) is a finite linear combination of real exponentials and is positive. Equation (6) shows e^(Λ_d s)F(s) is nondecreasing on [0,1]; equality at the endpoints makes it constant there. Finite linear combinations of exponentials are real-analytic, so F(s)=F(0)e^(−Λ_d s) for all s≥0. Alternatively, apply a Vandermonde determinant to the derivatives at an interior point once exponents are collected. Each point x in the support has probability asymptotic to a positive coefficient times e^(−s λ(K_x)), where K_x={i:x_i≠a_i} and λ(K)=Σ_(i∈K)λ_i. Finite summation of nonnegative terms shows the smallest λ(K_x) over support points is exactly Λ_d. If |K_x|<d then λ(K_x)<Λ_d, so f vanishes at every such point.

Use the monomial basis in X_i−a_i. Restriction to any set of fewer than d nonanchor coordinates yields the zero function, and hence the zero reduced polynomial on that restricted grid. All monomials using fewer than d coordinates are therefore absent. Total degree d leaves only squarefree terms c_K∏_(i∈K)(X_i−a_i) with |K|=d. A nonzero such term is the only surviving one at any point with nonanchor set exactly K, so its weight λ(K) is ≥Λ_d, and by definition must equal Λ_d.

For every such nonzero term let E_K be the event that none of its coordinates are anchors. At time s its probability is c'_K e^(−Λ_d s), with c'_K=∏_(i∈K)θ_i(0)(1−1/q_i)>0. If exactly one E_K holds, f is nonzero, and if none holds, f is zero. If distinct E_K and E_L both hold, their joint probability is O(e^(−λ(K∪L)s)) with λ(K∪L)>Λ_d. Therefore the limit of e^(Λ_d s)F(s) is Σ_K c'_K. But at s=0 full support gives strictly positive overlap between any two distinct E_K, implying μ(θ(0))≤P(∪_K E_K)<Σ_K c'_K when there is more than one term. That contradicts constancy. Each nonzero fiber is thus exactly one allowed monomial with a nonzero scalar factor.

Finally, each of those monomials already has full total degree d in active variables. Its coefficient upon fixing inactive values is identical to its coefficient in f, since any additional inactive power exceeds d. A nonzero fiber hence fixes one common term and nonzero coefficient for every fiber. The fibers must all be this same monomial, with no zero fibers, and interpolation shows f equals it on the whole grid. Conversely the probability for any allowed monomial is exactly ∏_(i∈K) θ_i(1−1/q_i), so (1) is an equality. This proves the classification.

## 5. Binary specialization, equality in Potapov's support inequality, and plateaued functions

For G={0,1}^n with anchor 0, θ_i=2p_i where p_i is the Bernoulli success probability. With a common p>0 and p'=pq, the conclusion is
```
   μ_f(pq) ≥ q^d μ_f(p)    for 0<p≤1/2 and 0≤q≤1.
```
This is Potapov's Proposition 10 throughout its stated parameter range and extends it to q>1/2. Taking p=1/2 gives μ_f(u)≥u^d|S|/2^(n−d) for all 0≤u≤1/2, extending Corollary 2's u≤1/4 range. The endpoint p=0 of the Proposition follows directly: for d>0 its right side is no larger than μ_f(0); for d=0 the function is constant. More generally binary coordinates with biases above 1/2 can be flipped whenever the comparison moves further toward their more likely bit; after flipping each changed coordinate the ratio is for the less likely bit.

Independently, the lower equality in (2) for binary input with the usual order 0<1 holds exactly when S is the coordinate (n−d)-cube through zero, with all other coordinates fixed to zero. The upper equality follows by flipping all inputs, so the complementary fixed coordinates are all one. Here is a direct proof, including the constant case. Put k=n−d and let π be the binary Gram matching. A nonzero B_(u,v) means Σ_x f(x) x^(u∨v)=1 (mod 2); since this degree is ≤d+|u∨v|, (3) implies |u∨v|≥k. At equality every matched pair has |u|+|v|=k, hence disjoint support and |u∨v|=k. All points of S have weight ≤k, so the odd sum for each matched pair implies u∨v itself belongs to S (the only possible support point above it). Every weight-k point can only match the zero vector, so by injectivity of π there is exactly one such point w. This forces S⊂{x:x≤w}. The indicator f is the product of all (1+X_i) for i outside the support of w, times its nonzero restriction to the free coordinates. The total degree is (n−k) plus the degree of that restriction because the factors use disjoint variables and do not cancel. Since d=n−k the restriction is the constant 1. Conversely each stated cube has that degree and average weight k/2.

Finally, let a Boolean plateaued function have uniform spectral mass on its Walsh support S_f of cardinality 2^h, where h≥0. Its Fourier entropy H=h, its total influence I is the mean Hamming weight on S_f, and Potapov Proposition 4 gives degree(1_(S_f))≤n−h/2. Potapov Theorem 2 then gives I≥h/4. If h>0 and equality held, both these inequalities would be equalities. The binary equality characterization makes S_f a coordinate cube of dimension exactly h/2, which instead has 2^(h/2) points. Contradiction. Thus H<4I when h>0, although the known examples of Li–Tang approach 4. When h=0 the function is affine and H=0; I=0 precisely for constants. No claim about nonplateaued functions or an improved universal constant is made.

## References

See SOURCES.md for the versions, precise prior results, and targeted duplicate checks.
