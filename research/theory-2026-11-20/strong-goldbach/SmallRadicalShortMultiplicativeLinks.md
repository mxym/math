# Short true multiplicative links cannot match two slopes between fixed-target cliques

Research note, 2026-11-24. This uses the actual completely multiplicative Liouville sign on all links. It is an arithmetic obstruction to direct short-unit and short factor-swapping arguments, not a counterexample about \(\lambda\), nor a conclusion about the full graph of multiplicative dependencies.

## 1. Actual setup and the short ratio relation

Let \(P\) be large even with \(\operatorname{rad}(P)\le(\log P)^B\), put \(L=\log P\), \(I=[uP,vP]\), \(0<u<v<1\) fixed, \(y=e^{L^\delta}\) for \(0<\delta<.1\), \(z=e^{L^{.24}}\), \(H=L^{3/5}\), and \(D=P^{1/2}e^{-H}\). The actual source rows are
\[
n=p k\in I,\quad p\in\mathcal P\subset\{P^\sigma<p\le D:\ p\text{ prime}\},\quad
P^-(k)>z,\quad m=P-pk,\quad P^-(m)>y ,
\]
with fixed \(0<\sigma<1/4\). A clique label is the actual \(k\) and an \(m\)-vertex is its real reflection at an eligible slope \(p\). The statement applies either to all such labeled cliques or to [the disjoint width-positive families](SmallRadicalCoprimeCliqueObstruction.md). If different full cliques overlap, a repeated physical vertex has ratio \(1\) and may still be regarded as a labeled edge where appropriate; we distinguish it from a nontrivial ratio.

Fix \(1\le T\le e^H/2\). In particular \(T\ll P^\sigma\) and \(T^2D^2<P\). For an ordered link from \(k\) to \(k'\) with actual slopes \(p,p'\) use a reduced rational ratio
\[
m'=\frac{a}{b}m,\qquad1\le a,b\le T,\quad(a,b)=1.
\tag{1}
\]
The physical interval for both \(m,m'\) forces \(a\asymp_J b\). Because \(a\mid m'\), \(b\mid m\), they are \(y\)-rough and target units. If \(a/b\ne1\), neither \(a\) nor \(b\) can equal \(1\) for large \(P\): otherwise the central ratio bound forces the other to be bounded, contrary to all its prime factors being \(>y\). Thus both exceed \(y\). These are true complete-multiplicativity relations:
\[
\lambda(m')=\lambda(a)\lambda(b)\lambda(m).
\tag{2}
\]
Indeed \(m=b r,m'=a r\) for an actual common cofactor \(r\). A single-prime for single-prime transfer has sign \(+1\), not \(-1\). In particular **no** such link of height \(T<y^2\) flips sign, since both nonunit \(a,b\) are then prime.

## 2. No parallel short links between two distinct cliques

The actual link equation is
\[
a p k-b p' k'=(a-b)P.
\tag{3}
\]
Every permitted \(k,k'\) is a unit modulo \(P\). If \(k=k'\), (3) forces \(k\mid a-b\). Since \(k\ge uP/D\gg T\), this forces \(a=b=1\) and then \(p=p'\). Likewise any short link with \(p=p'\) forces \(p\mid a-b\), since \(p\) is a target unit; because \(p>T\), again it is the identical row. More generally \(\gcd(k,k')\mid a-b\); if it exceeds \(T\) there is no nontrivial link.

Now suppose there are two short links in the **same orientation** from \(k\) to \(k'\), with possibly completely different ratios \(a_i/b_i\) and slopes \(p_i,p_i'\), \(i=1,2\). Reduce (3) modulo \(P\) for each link; eliminate the common unit \(k\) or \(k'\) to obtain
\[
P\ \mid\ a_1 b_2 p_1 p_2'-a_2 b_1 p_2 p_1' .
\]
Each product here is positive and at most \(T^2D^2<P\), so the integer difference is zero, not just small modulo a fraction of \(P\). All prime factors of the short factors \(a_i,b_i\) are at most \(T\), whereas each actual slope prime exceeds \(T\). Unique factorization gives equality of the slope prime multisets \(\{p_1,p_2'\}=\{p_2,p_1'\}\), including multiplicities. If \(p_1=p_2\) then \(p'_1=p'_2\); the physical endpoints agree and their reduced ratio is unique, so this was only one link. If \(p_1\ne p_2\), the multiset equality instead forces \(p'_1=p_1\) and \(p'_2=p_2\). By the single-slope obstruction following (3), both links would be identical rows, hence \(k'=k\).

Therefore between **any two distinct \(k\)-labels, all short ratios together yield at most one actual link** at this height. This is stronger than one link per prescribed ratio. It also permits an identity edge from an overlap of full cliques, but then there is no second, even nonidentity, short edge. Within one clique there is no nontrivial short link at all. In particular one cannot transfer an internal distinct-vertex pair to a second clique by applying two separate short scalar edits to its coordinates, regardless of the parities of the short units.

## 3. Global direct-link bill compared with the true intra-clique normalization

For a fixed nontrivial reduced \(a/b\), (3) cannot have \(p=p'\). For distinct true primes \(p,p'>T\), \(\gcd(ap,bp')=1\), since \((a,b)=1\). Therefore for fixed \(p,p'\), \(k\) lies in the one progression
\[
k\equiv (a-b)P(ap)^{-1}\pmod{b p'}.
\]
The true \(I/p\) interval has length \(O_J(P/p)\). As \(bp p'\le TD^2<P\), the endpoint floor is absorbed by \(O_J(P/(p b p'))\); each such \(k\) determines \(k'\) uniquely. Dropping the remaining rough masks and congruences only gives an upper bound. Sum over the genuine slope primes using \(\sum_{p\in\mathcal P}1/p=O_\sigma(1)\). Thus
\[
\#\{\text{actual labeled links of ratio }a/b\}\ll P/b,
\qquad
\sum_{\text{these links}}k\ll (P^2/b)\sum_{p,p'\in\mathcal P}\frac1{p^2p'}
\ll P^{2-\sigma}/b .
\tag{4}
\]
The same bound with \(k'\) in place of \(k\) holds by reversing and using \(a\asymp_J b\). The label multiplicity in the full collection is included in the actual \(p,p'\) loops.

Over all short ratios \(1\le a,b\le T\), the unrestricted reciprocal sum \(\sum 1/b\) is \(O(T\log(2T))\), so all direct links together have number \(O(PT\log(2T))\) and starting \(k\)-weighted total \(O(P^{2-\sigma}T\log(2T))\). Also with the natural double reciprocal link weight,
\[
\sum_{\text{actual nontrivial short links}}\frac1{ab}
\ll P\sum_{b>y}\frac1{b^2}\sum_{a\asymp_J b}\frac1a
\ll P/y.
\tag{5}
\]
Here \(a\asymp_J b\) and the exclusion of \(a=1\) or \(b=1\) are essential; the inner sum is \(O_J(1)\) even over all integers. Without these reciprocal weights, no \(O(P/y)\) assertion is made.

For comparison, the genuine unsigned \(k\)-weighted intra-clique off-diagonal of the full slope range has total \(\asymp P^2\kappa_z V_y(P)^2/L\), as [proved using prime BV](SmallRadicalWeightedCoprimeDispersion.md) with each rough \(k\) fixed. The weighted direct link count in (4) summed over ratios is polynomially smaller, since \(T=P^{o(1)}\). The disjoint width-positive clique window also gives the same intra-clique weighted order. For an unweighted comparison in that previous window \(p\in[P^{.40},P^{.45}]\), retain \(k\) in a fixed-factor interval at scale \(P^{.55}\) within its full physical \(k\)-range, with no prime from the slope window dividing \(k\). There are \(\asymp P^{.55}\kappa_z\) such rough \(k\)'s by the integer rough count and the exact single-divisor subtraction already checked for this window. Each has true prime-slope mass \(\asymp P^{.45}V_y/L\), with all physical interval weights comparable. Thus genuine unequal internal pairs already have total \(\gg P^{1.45}\kappa_z V_y^2/L^2\) in that fixed-factor slice. The old **unweighted single-box** shared-gcd bound is \(O(X^2Y/y)=O(P^{1.45}/y)\) at \(X\asymp P^{.45},Y\asymp P^{.55}\), so it is negligible there too. This is polynomially larger than the count of all direct short links just obtained. This comparison is about **direct** links, not their transitive closure, which can still connect large components.

## 4. Short signed cycles on clique labels and their limitation

There is also a precise partial consistency statement about combining direct links. Consider a directed cycle of \(\ell\) clique labels with a short rational link on each edge. Let \(p_i\) be the actual outgoing slope at \(k_i\), and \(q_i\) the actual incoming slope there. They may be **different** physical vertices of that same clique; the product of edge ratios does not telescope for that reason. Use the notation \(a_i/b_i\) for the \(i\)-th directed multiplier and suppose all slopes in this cycle are at most \(X_*\), with
\[
(T X_*)^\ell<P.
\tag{6}
\]
Multiplying the true link congruences (3) mod \(P\) around the cycle and canceling the \(k_i\)'s gives
\[
\Big(\prod_i a_i p_i\Big)\equiv
\Big(\prod_i b_i q_i\Big)\pmod P.
\]
Both positive products are \(<P\), hence equal as integers. Unique factorization again separates the true slope primes \(>T\) from the short factors, giving \(\prod_i a_i=\prod_i b_i\) exactly. Thus the **actual edge-sign product** around such a clique cycle, calculated with \(\lambda(a_i)\lambda(b_i)\) from (2), equals \(+1\). This result is not automatic telescoping on \(m\)-vertices. In particular these cycles do not give an inconsistency to assigning a constant sign to each clique that obeys their edge relations.

For example take the genuine angular band \(p\in[P^{.26},P^{.30}]\) and the corresponding interior \(k\)-range with \(I/k\) contained in that band. Demand \(R_z(k)=1\) and no band prime dividing \(k\), making true cliques disjoint by the same unique-slope argument as before. This retains a fixed positive fraction of the rough harmonic \(k\)-mass: on each fixed-factor \(k\)-interval the union upper for divisibility by real band primes subtracts at most a relative \(\sum_{p\text{ in band}}1/p=\log(.30/.26)+o(1)<1\); the quotient rough count is uniform at genuine polynomial scale. The genuine prime-slope count with \(k\) fixed follows from ordinary maximal prime BV as before, so this remains a fixed positive fraction of the full \(k\)-weighted unsigned moment. In this entire real band \(T^3P^{.90}<P\), hence no triangle of short links produces an opposite-sign cycle. At larger slopes or on longer cycles, (6) can fail, and the modular equality alone does not justify the integer equality or this sign assertion.

## 5. A non-coordinatewise pair-product case covered by the rigidity

One can rule out a true pair-product transfer without assuming initially that the individual ratios are short. Let \(m_1,m_2\) be distinct genuine coprime vertices in one clique, and \(m'_1,m'_2\) distinct genuine coprime vertices in another labeled clique, and suppose
\[
b m'_1m'_2=a m_1m_2,\qquad (a,b)=1,\quad a,b\le T_0,\quad T_0T_1\le T .
\]
Assume one actual \(m_i\), say \(m_1\), has a genuine prime \(R>P/T_1\). For large \(P\), \(R>T_0\), so \(R\) is not canceled by the short ratio; \(R\) occurs in exactly one of the two target vertices by their coprimality. Reorder the targets so that \(R\mid m'_1\). Then both \(m_1/R\) and \(m'_1/R\) are at most \(T_1\). Hence after reducing the first coordinate ratio \(m'_1/m_1\) its height is at most \(T_1\), while the second ratio, obtained by dividing \(a/b\) by the first, has height at most \(T_0T_1\le T\). The two-link rigidity now rules out transport to a distinct clique. Within the same clique both short links must be identities, so the physical pair is unchanged up to order and \(a/b=1\). In particular no sign-changing pair-product transfer of this type exists even when only one vertex has the near-full prime. For general pairs without such a large common prime, a short total product ratio may require redistribution through long factors; no conclusion is reached there.

These statements constrain fixed-\(P\) transfers that use actual complete multiplicativity with short arithmetic edits, and give a dense domain where specified short cycles are sign-consistent. They do not establish smallness of the actual signed coprime moment, and do not exclude useful constraints from long multiplicative relations, arbitrary pair-product collisions, or the entire multi-step closure of the short-link graph.