# Affine and symmetric endpoints of joint approximate nondeterministic degree

## 1. Definitions

Let \(f:\{0,1\}^n\to\{0,1\}\). A \(b\)-witness of error \(\epsilon_b\in[0,1)\) is a real polynomial \(p_b\) such that \(|p_b(x)|\ge1\) whenever \(f(x)=b\) and \(|p_b(x)|\le\epsilon_b\) whenever \(f(x)\ne b\). Write \(d_b\) for the minimum possible degree and set
\[
 \delta_b=1-\epsilon_b,\qquad
 L_b=1+\left\lfloor\frac{2\epsilon_b}{1-\epsilon_b}\right\rfloor .
\]
Thus \(d_1=N_{\epsilon_1}(f)\) and \(d_0=N_{\epsilon_0}(\bar f)\) in Pednekar–Podder's notation. A coordinate is relevant if flipping it changes \(f\) somewhere. We may restrict irrelevant coordinates to constants without changing the function of the remaining bits, the number \(m\) of relevant bits, or its decision-tree complexity \(D(f)\). Witness degrees cannot increase when doing so. A nonconstant function has \(d_0,d_1\ge1\), and \(D(f)\le m\). Constant functions have \(m=D=0\).

## 2. Both witnesses affine: exact maximum

**Theorem 1.** For each error pair \((\epsilon_0,\epsilon_1)\), among all functions with \(d_0,d_1\le1\), the largest \(m\) and the largest \(D(f)\) both equal \(L_0+L_1\).

Suppose \(p_b\) is affine on the relevant coordinates. Every relevant coordinate \(i\) occurs on an edge where the label changes. By the reverse triangle inequality, the magnitude of the coefficient of \(x_i\) in \(p_b\) is at least \(\delta_b>0\). Orient the bit in its increasing direction for \(p_b\). Along any chain of single unused bit flips increasing \(p_b\), the successive values increase by at least \(\delta_b\). Therefore the chain includes at most \(L_b\) vertices of label \(1-b\), because they all lie in the value interval \([-\epsilon_b,\epsilon_b]\). This counts both endpoints of a closed interval, including when \(2\epsilon_b/\delta_b\) is an integer.

Orient every bit so that \(p_1\) increases on flipping \(0\) to \(1\). Let \(A\) be the coordinate set on which \(p_0\) also increases, and \(B\) the set on which it decreases. If one of the sets is empty, a single full chain is monotone in the two witnesses (possibly after reversing direction for \(p_0\)). Its \(m+1\) vertices include at most \(L_1\) zeros and \(L_0\) ones.

Otherwise, in the \(A\)-cube and \(B\)-cube choose arbitrary saturated chains from the all-zero vertex to the all-one vertex. In their product consider the perimeter: the four paths obtained by fixing one chain at one of its endpoints while going along the other chain. This perimeter has exactly \(2m\) distinct vertices, since just the four corners are shared across the four sides. The two paths from \((0_A,0_B)\) to \((1_A,1_B)\) through the two opposite corners are both increasing for \(p_1\). Their union covers the perimeter, which thus contains at most \(2L_1\) zeros. The two paths from \((0_A,1_B)\) to \((1_A,0_B)\) through the other two corners are both increasing for \(p_0\), and give at most \(2L_0\) ones on the same perimeter. Therefore \(m\le L_0+L_1\).

For attainment put \(s=L_0+L_1-1\); use a pivot bit \(z\), \(s\) other bits, and their weight \(w\). Define \(f=1\) iff
\[
 (z=0\ \text{and}\ w<L_0)\quad\text{or}\quad(z=1\ \text{and}\ w\ge L_1).
\]
Then \(f=0\) iff \(w+L_0z\) lies in the length-\(L_1\) integer interval \([L_0,L_0+L_1-1]\), and \(f=1\) iff \(w-L_1z\) lies in the length-\(L_0\) integer interval \([0,L_0-1]\). For each interval use the corresponding affine form minus its midpoint, times \(2/(L_b+1)\). On the interval the absolute value is at most \((L_b-1)/(L_b+1)\le\epsilon_b\), and on exterior integers it is at least \(1\). This gives both witnesses. Unequal errors generally require different cutoffs on the two pivot branches.

Here is a deterministic-query adversary for this function. Assume no repeated queries. Until the pivot is queried or the last nonpivot query is reached, distribute nonpivot replies within the capacities \(L_0-1\) ones and \(L_1-1\) zeros, whose sum is \(s-1\). If the pivot is queried before the last nonpivot bit, answer \(z=0\) and keep the same count capacities on those bits. While at least one nonpivot bit remains, both sides of the cutoff \(w=L_0\) are possible: the weight can be at most \(L_0-1\) or at least \(L_0\), using the unread bits, because neither capacity has been exceeded. This argument also forbids terminating before the pivot while some nonpivot bit is unread, by considering the possible branch \(z=0\). If the last nonpivot bit is queried before the pivot, the earlier counts are exactly \(L_0-1\) ones and \(L_1-1\) zeros. Answer with bit \(0\) if \(L_0\le L_1\) and \(1\) otherwise. At the resulting weight the two values of the pivot give different labels, so it too must be queried. In every case the adversary forces all \(s+1\) queries. Since \(D(f)\le m\le s+1\), the sharpness claim follows.

At equal errors less than \(1/3\), \(L_0=L_1=1\). For two relevant coordinates each label can occupy at most two points: each small slab is an antichain in its oriented 2-cube. With both points of each color and both bits relevant this is precisely XOR or XNOR. Constants and one-bit functions cover the other cases.

## 3. One affine witness and the exact opposite endpoint

We use the projection-AND number \(\operatorname{PAND}(g)\) as in Kothari et al. Definition 13: the largest \(k\) for which disjoint nonempty bit blocks, each toggled by a fresh variable from a base input, give the function equal to one only at all-zero fresh variables. A coordinate subcube is sufficient for the applications below. A restriction or such a projection cannot increase witness degree, since coordinates become constants or single fresh bits (possibly negated), and multilinear reduction never raises degree.

**Endpoint lemma.** If \(\operatorname{PAND}(g)=k\) and \(g\) has a 1-witness of degree \(d\) and error \(\epsilon\), then \(k\le(1+2/(1-\epsilon))d^2\), and at \(\epsilon=0\) the stronger \(k\le d\) holds.

For \(k\ge1\), the projected witness can be averaged over the layers of fresh variables. A monomial on \(j\) distinct bits has average \(\binom tj/\binom kj\) at weight \(t\). Thus the average extends to a univariate polynomial \(P(t)\) of degree at most \(d\). Divide by the nonzero value at 0 so that \(P(0)=1\); then \(|P(j)|\le\epsilon\) for the integers \(1\le j\le k\). For \(\epsilon=0\) the \(k\) distinct roots give \(k\le d\). Otherwise put \(M=\max_{[0,k]}|P|\). Markov's inequality after rescaling gives \(\max_{[0,k]}|P'|\le2d^2 M/k\). Because every point is at distance at most \(1/2\) from an integer in the interval, \(M\le1+d^2 M/k\). For \(k>d^2\) this implies \(1-\epsilon\le|P(0)-P(1)|\le2d^2/(k-d^2)\), proving the bound. For \(k\le d^2\) it already holds, including \(k=0\).

**Theorem 2.** If \(f\) is nonconstant and \(d_1\le1\), then
\[
 m\le 2\operatorname{PAND}(\bar f)+L_1-1.
\]
Consequently \(D(f)\le m\le 2(1+2/(1-\epsilon_0))d_0^2+L_1-1\). If \(\epsilon_0=0\), the exact maximum of both \(m\) and \(D(f)\) under \(d_0\le d\) is \(2d+L_1-1\), for every integer \(d\ge1\).

To prove the bound, orient bits so that \(p_1\) is increasing in each relevant coordinate with coefficient at least \(\delta_1\), as in Theorem 1. Its small slab is precisely the zero set of \(f\). Choose a minimal slab vertex \(u\) in the coordinatewise order, and a maximal slab vertex \(v\ge u\), possible by finiteness. Write \(|u|=r\), \(|v|=t\). Their polynomial values lie at distance at most \(2\epsilon_1\), but differ by at least \((t-r)\delta_1\), giving \(t-r\le L_1-1\). At \(u\), any nonempty deletion of a 1-coordinate leaves the slab by minimality. This gives a point-isolating restriction for \(\bar f\) with \(r\) available coordinates. At \(v\), similarly use arbitrary additions among the \(m-t\) zeros. Thus \(\operatorname{PAND}(\bar f)\ge\max(r,m-t)\ge(m-L_1+1)/2\). Apply the endpoint lemma.

For sharpness in the exact case, use \(m=2d+L_1-1\) bits and set \(f=0\) iff their weight is in \([d,d+L_1-1]\). Center and scale this length-\(L_1\) interval as in Theorem 1 to get \(p_1\). For each slab point \(y\), there are at least \(d\) ones and \(d\) zeros in \(y\). Choose \(d\) disjoint pairs of coordinate positions, one of each type in each pair. The product of their \(d\) bit differences is nonzero at \(y\) and has support inside the slab: a nonzero evaluation requires one 1 and one 0 in every pair. A linear combination of these products is nonzero on the entire slab. Indeed, the span contains an element nonzero at each slab point individually, so the union of finitely many proper coordinate hyperplanes cannot cover that span over the reals. Such a combination is the exact 0-witness of degree at most \(d\). The function is nonconstant symmetric. For any nonconstant symmetric function on \(m\) bits, choose a transition between weights \(j\) and \(j+1\). In any query order reply to the first \(m-1\) queries with \(j\) ones and \(m-1-j\) zeros in a fixed sequence. The two final completions differ in output, hence no earlier termination is possible and the tree must query all \(m\) bits. This gives \(D(f)=m\), and confirms every bit is relevant.

For each fixed \(\epsilon_0>0\) the quadratic order in \(d_0\) in Theorem 2 cannot be improved, even if \(\epsilon_1=0\). Use \(f=\mathrm{OR}_m\) with witness \(p_1=w\), where \(w\) is the input weight. For \(m\ge2\) the standard degree-\(d\) Chebyshev witness for the 0-label is
\[
 p_0(w)=
 \frac{T_d((m+1-2w)/(m-1))}
           {T_d((m+1)/(m-1))}.
\]
It equals 1 at zero, and has absolute value at most \(1/T_d((m+1)/(m-1))\) at the other weights. The identity
\(\operatorname{arcosh}((m+1)/(m-1))=2\operatorname{artanh}(1/\sqrt m)\ge2/\sqrt m\)
follows from the double-angle formula and \(\operatorname{artanh}(t)\ge t\). Therefore every \(m\) with \(2\le m\le (2d/\operatorname{arcosh}(1/\epsilon_0))^2\) gives the stipulated error. This is a standard single-endpoint approximation; we use it to show sharp order, not a new Chebyshev estimate.

## 4. Symmetric functions: cubic joint bound

**Theorem 3.** Let a nonconstant symmetric \(f\) depend on \(n\) bits, and use the degrees \(d_b\) above. For each \(b\) put \(C_b=1+2/(1-\epsilon_b)\). Then
\[
 D(f)=n \ \le\ (2\min(d_0,d_1)+1)
                 \max(C_0d_0^2,C_1d_1^2)-1 .
\]
In particular \(D(f)=O_{\epsilon_0,\epsilon_1}(\min(d_0,d_1)\max(d_0,d_1)^2)\).

Consider the label sequence at successive Hamming weights \(0,\dots,n\). If a run \([\ell,h]\) of length \(r=h-\ell+1\) has label \(b\) and \(\ell>0\), fix \(\ell-1\) bits to 1, \(n-h\) bits to 0, and leave \(r\) free. All-zero free bits give the opposite label (weight \(\ell-1\)); every other completion gives label \(b\) (weight in the run). If \(\ell=0\), the run ends before \(n\); fix the rest of the bits to 0, leave \(r=h+1\) free, and complement those bits to obtain opposite label only at the all-zero free input. Therefore \(r\le\operatorname{PAND}(1_{f=1-b})\le C_{1-b}d_{1-b}^2\).

The two witnesses bound the number of transitions, using Pednekar–Podder's Lemma 9 argument separately for each label. Square and multilinearly reduce \(p_b\), then average on each weight. As in the endpoint lemma this defines a real univariate polynomial of degree at most \(2d_b\) taking values at least 1 on its own label and at most \(\epsilon_b^2\) on the other. Subtract any number strictly between these thresholds. Each transition supplies a root in its own disjoint open interval between consecutive integers. Thus there are at most \(2\min(d_0,d_1)\) transitions. The number of runs is one larger. Summing their length bounds gives the result, since they partition \(n+1\) weights. The identity \(D(f)=n\) follows from the transition adversary already given above. No claim is made that the cubic exponent is optimal for symmetric functions.

## 5. Different conjectures and a literal counterexample

Kothari et al. v3 Conjecture 3 asks for the exponent pair \((2,2)\) on deterministic complexity with equal constant errors. Theorems 2 and 3 establish it for the one-affine and symmetric subclasses respectively: for nonconstant functions, \(d_b\ge1\). Their v3 Theorem 12 already proves exponent pair \((3,3)\) on all total Boolean functions, implying the weaker polynomial approximate-degree statement in Pednekar–Podder v1 Conjecture 3. We do not claim the unrestricted \((2,2)\) question.

Pednekar–Podder v1 Conjecture 2 instead prints a literal constant-one bound on approximate degree by \(\max(d_0,d_1)\). This bound is false, even at arbitrarily small positive witness error. For parity on two bits the exact witnesses \(p_1=x_1-x_2\) and \(p_0=x_1+x_2-1\) have magnitude 1 on their own labels and vanish on the other. For any two-sided error less than \(1/2\), parity on \(n\) bits has approximate degree \(n\): with \(F=(-1)^f\) and a real approximant \(Q\) to \(f\), the polynomial \(1-2Q\) has strictly positive correlation with \(F\), but degree below \(n\) would be orthogonal to that full parity character. For every \(n\) split the parity into two parities on \(\lfloor n/2\rfloor\) and \(\lceil n/2\rceil\) bits, with sign characters \(A,B\); \((A-B)/2\) and \((A+B)/2\) are the two exact witnesses of degree at most \(\lceil n/2\rceil\). The matching lower bound at every error \(\epsilon_b<1\) follows from the highest coefficient of \(p_b^2\): its two parity-class means differ strictly, so it cannot have degree below \(n\) after reduction. Thus even-dimensional parity requires a factor 2 in any uniform multiplicative comparison. The exact rational-degree parity example is known, not a novelty claim.
