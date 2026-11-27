# Exact triple collisions and a bounded pair Gram matrix

## 1. Setting and theorem

Let \(\mathcal X\) be finite, \(m\ge2\), and \(F\) a finite random
function \(f:\mathcal X\to[m]\) drawn independently of a normalized
finite-dimensional cq state
\(\rho_{XE}=\sum_x |x\rangle\langle x|\otimes R_x\), \(R_x\succeq0\).
The law of \(F\) may be weighted; the explicit laws below are rational
and can equally be sampled using uniform finite seed multisets.
Write \(\rho_E=\sum_xR_x\) and
\[
 \Delta_F(\rho)=\frac12\mathbb E_f\sum_{z=1}^m
       \left\|\sum_{x:f(x)=z}R_x-\frac1m\rho_E\right\|_1.
\]
Regula–Cheng call \(F\) \(k^*\)-universal if for every \(j\) distinct
inputs, \(2\le j\le k\), its all-equal output probability is
\(m^{1-j}\). Strong \(k\)-wise independence means the outputs on each
set of at most \(k\) distinct inputs are mutually independent and
uniform. The strong condition implies the starred condition, but
not conversely.

Put \(p=1/m\), \(v=p(1-p)\), take \(z\) uniformly and independently of
\(f\), and set \(B_x=1_{\{f(x)=z\}}-p\). Index by unordered two-element
sets \(e=\{x,y\}\subset\mathcal X\), and let
\[
 \eta_e=B_xB_y/v,\qquad K_{e,e'}=\mathbb E_{f,z}\eta_e\eta_{e'}.
\]
All probabilistic moments in the proof of the converse below are taken
over this joint law of \((f,z)\), not over a conditional seed law at
some fixed bin. Define the finite-dimensional benchmark
\[
 \Pi=\max\left\{\sum_x\operatorname{tr}(R_x M_x):
 M_x=M_x^*,\ \|M_x\|_\infty\le1,\ \sum_x M_x^2\preceq(4p)^{-1}I
 \right\}.
\]
For positive \(R_x\), passing from Hermitian \(M_x\) to its positive
part increases the objective and preserves both constraints. Thus
\(\Pi\) is Regula–Cheng's \(\pi^\triangle_{m/4}(X|E)_\rho\)
(Equation (85), equivalent cq form (124)).

**Theorem 1.** If \(F\) is \(3^*\)-universal and \(K\preceq C I\)
for \(C\ge1\), then for every such cq state,
\[
 \frac{\Pi}{\max\{3,\sqrt{2+4C}\}}
      \ \le\ \Delta_F(\rho)\ \le\ \Pi.
\]
The upper bound is Regula–Cheng's Equation (86) for \(2^*\)-universal
hashing; the proof below derives the asserted lower bound.

**Direct collision formula.** For distinct input indices, the
probability that their indicators all equal one is \(p\) times the
probability of all hash outputs being equal. Therefore all collections
of at most three indicators are iid Bernoulli \(p\): joint probabilities
including zeros follow by expanding products of \(1-1_{\{f(x)=z\}}\).
In particular \(K_{e,e}=1\), \(K_{e,e'}=0\) for incident distinct pairs,
and for disjoint pairs with union \(T\),
\[
 K_{e,e'}=p\big(\Pr_f[f\text{ is constant on }T]-p^3\big)/v^2.
\]
For the last identity, all moments of orders below four already have
the independent value. Thus \(K=I\) is equivalent to \(4^*\)-universality
when \(3^*\)-universality holds (also with vacuous quartets).
An empty pair matrix satisfies the condition automatically.

## 2. The noncommutative fourth-moment bound

Fix any feasible Hermitian collection \(M_x\). Write \(Q=\sum M_x^2\)
and \(X=\sum_x B_x M_x\). Then \(B_x^2=v+(1-2p)B_x\), so
\[
 X^2=vQ+(1-2p)\sum_x B_xM_x^2
       +v\sum_{e=\{x,y\}}\eta_e A_e,
 \qquad A_e=M_xM_y+M_yM_x .
\]
The three displayed groups of scalar coefficients are pairwise
orthogonal in \(L^2\): for a linear coefficient with an overlapping
pair, use \(B_x^2=v+(1-2p)B_x\); for disjoint indices use triple
independence. Consequently all mixed terms vanish when squaring
\(X^2\) and taking the expectation, in their original multiplication
order. In particular
\[
 \mathbb E X^4=v^2Q^2+(1-2p)^2v\sum_x M_x^4
                    +v^2\mathbb E\left(\sum_e\eta_e A_e\right)^{\!2}.
\]
For any vector \(u\), the quadratic form of the last expectation is
\(\sum_{e,e'}K_{e,e'}\langle A_eu,A_{e'}u\rangle\), bounded by
\(C\sum_e\|A_eu\|^2\), since \(K\preceq C I\) also acts on
complex vector-valued coefficients. This gives the operator
inequality with \(C\sum_e A_e^2\). The elementary inequality
\((P+P^*)^*(P+P^*)\preceq2(P^*P+PP^*)\) for \(P=M_xM_y\) gives
\[
 \sum_e A_e^2\preceq2\sum_xM_x (Q-M_x^2)M_x
       \preceq2\|Q\|_\infty Q.
\]
Using \(Q^2\preceq\|Q\|_\infty Q\), \(M_x^4\preceq M_x^2\),
and \(\|Q\|_\infty\le1/(4p)\) now yields
\[
 \mathbb E X^4 \preceq v\,D\,Q,
 \qquad D=(1-2p)^2+\tfrac14(1+2C)(1-p).                 \tag{1}
\]
No commutation between different \(M_x\) was used.

## 3. Clipping and the converse

Use the clipping (functional calculus) argument of Regula–Cheng
Lemmas 13–14, replacing exact fourth moments by (1).
Set \(g(t)=\max(-c,\min(c,t))\), \(h(t)=t-g(t)\), where \(c>0\);
then \(\|g(X)\|_\infty\le c\) and \(|h(t)|\le t^2/(4c)\)
because \((|t|-2c)^2\ge0\).
Define \(H_x=\mathbb E B_xh(X)\) and \(L_x=2H_x/v\).

To control each individual norm, use
\(-|B_x|\,|h(X)|\preceq B_xh(X)\preceq |B_x|\,|h(X)|\).
The identity \(|B_x|=2v+(1-2p)B_x\) and the first three moments
show that \(\mathbb E |B_x| B_i B_j=0\) for \(i\ne j\).
For \(i=j\ne x\) this expectation is \(2v^2\), and for \(i=j=x\)
it is \(2v^2+v(1-2p)^2\). These follow directly from
\(B_i^2=v+(1-2p)B_i\) and
\(\mathbb E B_xB_i=v 1_{\{x=i\}}\). Hence
\[
 \|H_x\|_\infty\le \frac{v}{4c}
  \left((1-2p)^2 + 2v\|Q\|_\infty\right)
 \le \frac{v}{4c}\big((1-2p)^2+(1-p)/2\big).
\]
Thus \(\|L_x\|_\infty\le1\) when \(c\ge3(1-p)/4\), since
\((1-2p)^2\le1-p\) for \(0<p\le1/2\).

Next the \(B_x/\sqrt v\) are orthonormal. Apply the ordinary Bessel
inequality to the vector-valued random variable \(h(X)u\) for an
arbitrary vector \(u\) to obtain
\(\sum_x H_x^2\preceq v\mathbb E h(X)^2\).
Combined with (1), this implies
\[
 \sum_x L_x^2\preceq
  \frac{1}{4vc^2}\,\mathbb E X^4\preceq \frac{D}{4c^2}Q .
\]
So the \(L_x\) are feasible if also \(c\ge\sqrt D/2\).
Both requirements hold with \(c=(1-p)\max\{3,\sqrt{2+4C}\}/4\).
Indeed for \(t=(1-p)^{-1}\in[1,2]\),
\[
 D/(1-p)^2=(2-t)^2+\tfrac14(1+2C)t
  \le\max\{(5+2C)/4,(2+4C)/4\}
\]
by convexity and the endpoint values.
For \(C\le 3/2\) both entries are at most \(9/4\); for \(C\ge3/2\)
the second is the larger.

Choose \(M_x\) maximizing \(\Pi\) (the feasible set is compact).
Trace norm duality with \(g(X)/c\) and
\(\mathbb E B_x X=v M_x\) give
\[
 \begin{aligned}
 \Delta_F(\rho)
 &=\tfrac m2\mathbb E\left\|\sum_xB_x R_x\right\|_1\\
 &\ge\frac{m}{2c}\sum_x\operatorname{tr}\left[
       R_x\mathbb E B_x(X-h(X))\right]\\
 &=\frac{mv}{2c}\left(\Pi-\tfrac12\sum_x\operatorname{tr}(R_xL_x)\right)
 \ge\frac{1-p}{4c}\Pi.
 \end{aligned}
\]
The last inequality uses feasibility of the entire collection \(L_x\).
This proves Theorem 1. In particular, if \(C\) stays bounded, the same
two-sided one-shot comparison holds uniformly across input sizes.
More generally, along an i.i.d. sequence with \(\log C=o(d)\) for
blocklength \(d\), the factor is subexponential. Comparison with a
fully independent family in Theorem 1 transfers that family's
exact reliability exponent (e.g. Cheng–Gao–Li–Qiu Theorem 24) to
these ensembles at the same output sizes. There is no condition on
the commutativity of the side-information states.

## 4. Strict relaxations and witnesses

Suppose the family is \(3^*\)-universal and its four-input all-equal
collision probabilities are at most \(p^3\), not necessarily equal.
Then \(K=I-A\) for a real symmetric entrywise nonnegative matrix \(A\).
Since \(K\succeq0\), \(\lambda_{\max}(A)\le1\).
For each real \(u\), \(|u^\top A u|\le |u|^\top A |u|\), so
\(\|A\|_\infty\le1\) in the spectral norm. Therefore \(K\preceq2I\)
and the converse coefficient is at least \(1/\sqrt{10}\).
This is an upper bound only on fourth-order collisions; the pair and
triple constraints in the theorem remain equalities.

For either an excess or a deficit witness over **any** \(m\ge2\),
partition the input set into four-element blocks and up to three
leftover inputs; take at least one block. In each block independently
draw the outputs uniformly from
\(a_1+a_2-a_3-a_4=s\) in \(\mathbb Z/m\mathbb Z\).
Use independent uniform outputs on leftovers. Since any three
outputs determine the remaining output uniquely, this family is
strongly three-wise independent. A full block is all equal with
probability \(p^2\) if \(s=0\), zero if \(s=1\). All other quartets
are independent. The Gram matrix in the direct collision formula
is the identity plus, in each block, off-diagonal entries on the
three complementary pair-pair matches. The correlation on such a
match is \(a=p/(1-p)\) for \(s=0\) and
\(a=-p^2/(1-p)^2\) for \(s=1\).
Its spectrum is in \([1-|a|,1+|a|]\), with upper edge attained
when at least one block is present. Both choices give \(C\le2\)
and fail \(4^*\)-universality; the \(s=0\) example even violates
the ordinary fourth collision upper bound. The examples are proofs
about finite hash laws; they are not claims about seed efficiency.

## 5. Flat-source extrema at exact order three

Let \(N=mb\), with \(b\ge1\) integral, and let the source be uniform on
all \(N\) inputs, with trivial side information. Denote by \(d_3(N,m)\)
the infimum of mean TV over \(3^*\)-universal families; it is also the
infimum over strongly three-wise independent families, taking that
condition only up to the number of inputs. Define \(w=1-2/m\).

**Theorem 2.** In this setting,
\[
 \frac{m-1}{2N}\left(1-\frac{w}{2b+1}\right)
   \ \le\ d_3(N,m)\ \le\
 \frac{m-1}{2N}\left(1-\frac{w}{N}\right).                    \tag{2}
\]
The left bound is attained when \(m=2\) or \(m\ge2b+1\).
For \(m=3,4\) at all \(b\) the exact value is
\[
 d_3(N,m)=\frac{m-1}{2N}\left(1-\frac{w}{3b}\right).             \tag{3}
\]
The binary extremizing law is due to Pass and Spektor, in their
study of upper moments of order \(p\ge2\). It also attains the binary
TV optimum here: for the sum \(S\) of the \(N\) binary signs,
\(|S|\ge S^2/N\) and pairwise independence gives \(\mathbb E S^2=N\);
TV is \(|S|/(2N)\). The lower certificate in (2) is also the scalar
three-moment stop-loss bound of Courtois and Denuit; what is at issue
here is realizing moments simultaneously in all bins of each function
and the further multibin exact cases. See [SOURCES.md](SOURCES.md).

### Moment identities and symmetrization

For a fixed function let \(c_j\) denote its bin counts, set
\(d_j=c_j-b\), and use
\(V=\sum_j d_j^2, W=\sum_j d_j^3, L=\sum_j(d_j)_+\).
Since \(\sum_jd_j=0\), its TV distance is \(L/N\).
The two- and three-input all-equal constraints give
\[
 \mathbb E\sum_j(c_j)_2=(N)_2/m,\qquad
 \mathbb E\sum_j(c_j)_3=(N)_3/m^2,
\]
where \((a)_t=a(a-1)\cdots(a-t+1)\).
Expanding around \(b\) gives, respectively,
\(\mathbb EV=V_0:=N(1-1/m)=b(m-1)\) and
\(\mathbb EW=wV_0\): the expansion of the third moment
is \(N(b-1)(b-2)+(3b-3)V+W\).
These identities also hold for \(N=2\), with vacuous third
factorial constraint and \(W=0\).

Conversely, sample any distribution on integer bin profiles
summing to \(N\), then uniformly permute input positions and output
labels. If the two centered moment identities hold, each pair
or triple has the right all-equal probability. For a triple,
the probability of precisely a prescribed pair agreeing is the
two-input probability minus the all-equal probability; the
all-distinct probability is then determined, too. Output-label
symmetry is uniform over assignments having each equality pattern,
so the distribution of every triple of outputs is exactly the
independent uniform one. The same reasoning handles one or two
outputs and patterns impossible at small \(m\). This proves the
equivalence of the two infima and allows explicit profile mixtures.

### Lower bound and exact cases

For every positive integer \(d\),
\(d(2b+1-d)\le b(b+1)\). For \(a=-d\in[0,b]\),
\(a+a^2/(2b+1)\le b+b^2/(2b+1)\).
Apply the first inequality to positive deviations and the
second to negative ones, and use that the positive and negative
total masses both equal \(L\). This gives
\[
 V-\frac{W}{2b+1}\le
 \left(\frac{b(b+1)}{2b+1}+b+\frac{b^2}{2b+1}\right)L=2bL.
\]
Expectations yield the lower bound in (2).

For an upper construction, use the balanced (zero deviation)
profile; the symmetric profile with \(\lfloor m/2\rfloor\) pairs
\((b,-b)\) and any leftover zero, of variance \(V_s\);
and the constant-output profile \(((m-1)b,-b,\ldots,-b)\).
The symmetric profile has \(W=0\), \(L/V_s=1/(2b)\), and \(V_s\ge V_0\).
The constant-output profile has variance \(NV_0\), cubic/variance
ratio \(Nw\), and \(L/N=1-1/m\). Give the constant profile
probability \(1/N^2\); give the symmetric profile probability
\((1-1/N)V_0/V_s\); assign the remainder to the balanced profile.
The weights are nonnegative, sum to one, and give
\(\mathbb EV=V_0\), \(\mathbb EW=wV_0\).
The resulting \(\mathbb E(L/N)\) is precisely the upper bound in (2).
For \(m=2\) the bounds agree; equivalently one can collapse
the two nonzero profile probabilities to \(1/N\).

When \(m\ge2b+1\), there is another profile formed by taking
\(\lfloor m/(2b+1)\rfloor\) blocks of \(b\) positive entries \(b+1\)
and \(b+1\) negative entries \(-b\), filling the rest with zeros.
Here \(W/V=1\), and the pointwise lower-bound inequality is
an equality, as for the symmetric profile. This profile's
\(V\) is \(\lfloor m/(2b+1)\rfloor (2b+1)b(b+1)\ge V_0\):
the filled number of positions is at least \(m/2\), and \(b+1\ge2\).
Use this profile's variance contribution \(wV_0\), and use
the symmetric profile's variance contribution \((1-w)V_0\).
Dividing each contribution by its profile variance gives the two
probabilities, whose sum is at most one. Fill the remainder with
the balanced profile. This matches both moments and attains
the lower bound in (2).

For \(m=3,4\), the stronger pointwise inequality
\(W-3bV+6b^2L\ge0\) holds. To see this, divide deviations by \(b\).
For positive normalized deviation \(y\) put
\(P(y)=y(y-1)(y-2)\); for negative magnitude \(a\in[0,1]\)
put \(J(a)=a(1-a)(4+a)\). The normalized target is
\(\sum P(y)+\sum J(a)\), using the same total mass on each sign.
If there are two or more positives, there are at most two
negatives, so the total positive mass \(l\le2\).
Since \(P(u)+P(v)-P(u+v)=3uv(2-u-v)\ge0\) for
\(u+v\le2\), merge the positives to reduce to a single
positive of value \(l\). The case of no positives is zero.
For one positive, the only interval to check is \(1\le l\le2\),
since \(J\ge0\) and \(P\ge0\) otherwise.
The concave function \(J\) has smallest sum at fixed total \(l\)
when all negative magnitudes except at most one are zeros or ones:
transferring between two interior magnitudes to a boundary does
not increase the sum. Thus the sum is at least \(J(l-1)\).
Now \(P(1+r)+J(r)=3r(1-r)\ge0\).
Taking expectations proves the (3) lower bound.
For equality, replace the additional block profile above by
one \((2b,-b,-b)\) block with zeros elsewhere. Its variance \(6b^2\ge V_0\);
its \(W/V=b\); it has equality pointwise, as does the symmetric profile.
Use variance contributions \(wV_0/b\) and \((1-w/b)V_0\),
respectively, and the same balanced completion. This proves (3).

## 6. Independence threshold and sharp dependence on the Gram norm

For a uniform \(N\)-point source with \(m\le N\),
Cauchy–Schwarz in the scalar benchmark gives
\(\Pi=\frac12\sqrt{m/N}\), attained by constant
\(M_x=\frac12\sqrt{m/N}\). Theorem 2 instead gives
\(d_3(N,m)\asymp m/N\) uniformly in \(N=mb\), \(m\ge2\),
with the leading coefficient in (2) when \(b\to\infty\).
In particular take a uniform independent bit source with
\(N=2^d\), \(m=2^{r_d}\), and \(r_d/d\to R\in(0,1)\).
The best error at strong order three has base-two exponent \(1-R\),
whereas at strong order four the exponent is \((1-R)/2\),
by Theorem 1 at \(C=1\). Therefore within the strong \(k\)-wise
hierarchy, four is the minimum order giving this universal
one-shot lower bound up to an absolute constant, or the
associated exact i.i.d. reliability exponent uniformly over
the ensembles. This statement does not imply \(4^*\) itself is
necessary, nor does it address the optimal error with no
specified family constraint.

One can also use the standard binary affine family:
\(f(x)=Ax+c\) with uniform independent \(A\in\mathbb F_2^{r\times d}\),
\(c\in\mathbb F_2^r\), \(1\le r\le d\), \(N=2^d\), \(m=2^r\).
The augmented rows \((1,x_i)\) of up to three distinct
input points are linearly independent, because an affine relation
must have even cardinality and cannot have weight two.
Thus each output coordinate has independent evaluation at
three points, and the rows of \((A,c)\) are independent.
For a flat input, each seed yields the uniform law on
an affine subspace of size \(2^{\operatorname{rank}A}\);
its TV is \(1-2^{\operatorname{rank}A-r}\).
The rank distribution can also be written explicitly:
\[
 \Pr(\operatorname{rank} A=j)=
 2^{-rd}\prod_{i=0}^{j-1}
      \frac{(2^d-2^i)(2^r-2^i)}{2^j-2^i}\quad(0\le j\le r).
\]
Indeed choose an ordered independent basis for the rank-\(j\)
image and a rank-\(j\) map to its \(j\) coordinates, then divide
by the number of ordered bases of a \(j\)-space. In particular,
\(\Pr(\operatorname{rank} A=r)=\prod_{i=0}^{r-1}(1-2^{i-d})\),
so \(2^{r-1-d}\le\Pr(\operatorname{rank} A<r)<2^{r-d}\),
by bounding \(1-\prod(1-a_i)\) below by the largest \(a_i\)
and above by their sum. On the defect event the distance is in
\([1/2,1\)). This alone establishes the positive-rate separation
for the affine family.

For this family, four distinct augmented inputs are dependent
exactly when their sum is zero, when the four evaluations
are uniform subject to their single affine relation. Such a
quartet's all-equal probability is \(p^2\); an independent
quartet's is \(p^3\). The Gram matrix therefore groups pairs by
their common nonzero input difference. Such a class has \(N/2\)
disjoint pairs, with all off-diagonal correlations \(1/(m-1)\);
other entries vanish. Consequently
\[
 C_{\rm aff}=\lambda_{\max}(K)
       =1+\frac{N/2-1}{m-1}.
\]
For \(m=2\), the only deficient matrix is the zero row; hence
\(\Delta_F=1/(2N)\), \(C_{\rm aff}=N/2\), and exactly
\(\Delta_F/\Pi=1/(2\sqrt{C_{\rm aff}})\).
As \(N\to\infty\) along powers of two, this rules out improving
the \(C^{-1/2}\) order uniformly over finite cq sources and
\(3^*\)-universal families. The converse in Theorem 1
asymptotically has this same coefficient along this sequence.
