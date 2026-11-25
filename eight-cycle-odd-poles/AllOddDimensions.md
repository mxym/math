# Exact alternating eight-cycle rank for every odd dimension

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

In the [Gesmundo–Landsberg–Walter](https://arxiv.org/abs/1801.09106) complex periodic single-shared-tensor model with equal physical and bond dimension q, the maximum alternating eight-cycle flattening rank is **q⁴** for q≡1 (mod 4) and **q⁴−1** for q≡3 (mod 4). This is a complete odd-dimensional rank theorem, not a general claim for even q. The q≡3 case is the [unmarked-poles theorem](README.md). The proof below closes the other case.

For q = 2r+1 with r even, use the marked single-site spoke deformation and notation from [the unmarked-poles proof](README.md). Let k be the marked inverse class, j one unpaired unmarked class, and partition the remaining r−2 classes into N=(r−2)/2 disjoint pairs (u,v). We prove full rank for all such q≥5; q=1 trivial. Prior q≡3 mod4 is treated separately.

## 1. Quadratic term and marked cubic locality

The previous first elimination has S1=0 including on the marked residual E_k. The second-order K0 block H2 is a direct sum by inverse-class multisets even with the marker. For each residual E_i, its quadratic dressing is supported only on itself and K_{i,a}, with data local to those classes. As before S2[E_i,E_j]=0 if i≠j. The effective quadratic residual W2 is zero on unmarked pairs. Its marked entry W2_{k,j} uses only H2_{k,j} and the corresponding two couplings; it depends only on k,j. In particular it is regular where disjoint unmarked pair blocks have their poles. If this marked quadratic rational function is not identically zero, the answer already follows: expand the full skew Pfaffian along k, use the coefficient of t^{3r/2−1}, and localize at the selected unmarked poles. The coefficient using last edge k-j is the only summand with the entire product of selected poles, because every marked quadratic entry is regular there and an unmarked cubic entry can have a selected pole only on its own pair. The marked entry can be chosen nonzero by freely varying k and j on their regular open neighborhoods (allow the marker to vary near its old finite certificate). Thus it suffices in what follows to suppose the marked quadratic rational function is identically zero. This dichotomy does not rely on modular proof of that identity.

For cubic W3, let A(k,j) be the k-j entry with only the two classes k,j, and let B(k,j,a) be the difference on adding exactly one extra class a. Then over the full model
W3_{k,j}=A(k,j)+sum_{a outside k,j}B(k,j,a).
Indeed the cubic is the S3 pairing of the quadratic dressings. With three marked loops and no old perturbation, the outside-k endpoint counts must coincide, so the only possible matching endpoints are K_{k,j} on the left and E_j or K_{j,k} on the right; all intermediate counts outside k are fixed. With one marked loop and two old perturbations, consider left E_k or K_{k,a} and right E_j or K_{j,b}. An endpoint involving an extra outside {k,j} forces at least two changes outside k, and both endpoints cannot involve distinct extra classes (four changes would be needed even without the counts of j). Thus if an extra appears in the endpoint it is the only one and the old budget at that class or j is exhausted. An extra occurring only in intermediate Schur blocks needs two old perturbations to introduce and remove it, so endpoint counts outside k agree; once again only K_{k,j} on the left with E_j or K_{j,k} on the right is possible. A closed walk with an invisible leaf class but no individual label of that class is impossible here because every excursion starts with a labeled outgoing spoke. This proves the additive decomposition, assigning each summand with a unique extra to that class. The only non-base denominators for W3_{k,j} are the leading H2 blocks incident to k or to j. A leading pair block not incident to k appears at most once.

## 2. Simple poles in characteristic zero

Near a smooth simple Pfaffian root P=0 of H2_{u,v}, the mixed block has corank exactly two; otherwise all size-four Pfaffian cofactors vanish and no derivative of P can be nonzero. Its inverse has a simple pole, with skew residue R of rank two. The only possible double pole in W3_{u,v} uses that same inverse on both sides of the cubic pairing. Write b_u,b_v for the corresponding two quadratic coupling columns; the coefficient of the double pole is, up to sign, (R b_u)^T C(R b_v), with C the cubic skew block. But W2_{u,v}=0 identically gives b_u^T R b_v=0 by taking the quadratic expression's residue. On the two-dimensional image of R the induced form is nondegenerate, so R b_u and R b_v are dependent, and the displayed double coefficient vanishes by skew-symmetry. Therefore every selected unmarked entry has at most a simple pole. Its nonzero modular residue from the old certificate now lifts to a genuine simple pole in Q_p after Hensel; after the characteristic-zero double cancellation, the lifted normalized numerator is p-integral at P=0 (division by the simple monic local root factor preserves integrality). Marked entries can have a selected pole only when the selected pair contains their other endpoint, and then at most simply because only that endpoint's dressing uses the inverse. The unmarked nonmatching entries have no selected poles by the prior locality proof.

## 3. Full product coefficient and local identity

In the cubic Pfaffian, to obtain the full product of simple poles, either all chosen unmarked pair edges are used, leaving k-j, or exactly one pair (u,v) is replaced by k-u and j-v, or by k-v and j-u. No two replacements are possible because the marked vertex is used only once. Order the residual variables as the consecutive ordered pairs and then k,j; relative signs for a replacement are exactly those of the local four-by-four Pfaffian on u,v,k,j. Divide the normalized product residue by the product of the selected pair residues. The resulting rational function on the product pole locus is
A(k,j) + sum_{(u,v)} [ Z(u,v;k,j) − A(k,j) ],
where Z is the residue of the local four-class cubic Pfaffian divided by the residue of W3_{u,v}. Indeed its baseline W3_{k,j} contribution is additive over the extras; each replacement term is local to these four classes because unmarked W3_{j,v} involves just j,v,k, and the extra terms of W3_{k,u} other than v do not use the chosen H2_{u,v} pole. This expression is regular in a product of the local p-adic neighborhoods where the featured within-class and pairs incident to k or j are units and the selected residues are units; it can be evaluated even at coincident copies before perturbing to make the unrelated cross-pair denominators nonzero.

Use p=65521 and the previous local u,v,k arrays with the scale in class u varied. Let the new free j array (c,u,d,e) be (17651,17353,17755,19478) at its positive label and (9972,8255,9931,6661) at its negative label, with no further marked leaves. Use q9 for u,v,k,j and q5 for k,j alone. At x0=12833 the q9 exact modular calculation gives residues W3_{u,v}=21978, W3_{u,k}=25728, W3_{v,k}=46003 and regular values W3_{u,j}=35343, W3_{v,j}=18137, W3_{k,j}=58561. Thus
Z=(21978·58561 −25728·18137 +35343·46003)/21978 = 21540 mod p.
The q5 computation gives A(k,j)=21540 mod p, exactly equal to Z. Hence if every selected pair uses the same modular local data, then A+N(Z−A) reduces to 21540 for every N. Lift the pole by Hensel for each pair; the simple-residue identities in characteristic zero allow computation of their reduction by the modular calculation. Vary the selected lifts independently near these data to make the nonmatching H2 blocks and ambient base complements invertible, using the same dominant p-adic class projections as the first theorem. The normalized product residue stays a unit modulo p; there is no condition that copies have identical coordinates over Q_p. Therefore the cubic Pfaffian is a nonzero rational function over Q_p, hence over C. The prior all-other-sector construction was verified at marker=0 and remains generically nonzero, so the entire flattening has full rank at some complex parameter point.

## 4. Exact certificate notes

The q9 matrix arithmetic enumerates sparse traces through order 3, takes the first Schur complement, and interpolates S2,S3 in the old u-class common scale x. Degree at most two holds exactly: three old perturbations are forbidden by even endpoint parity, and the marker scale is independent of x. Sympy rational arithmetic over F_65521(x) then computes all cubic entries from S3 and the S2 dressings. In residual E ordering, the omitted row representative (0,0,a,-a) pairs with the omitted sign-relabelled column representative (0,0,-a,a). The orbit coefficient has length 4 in all E rows, giving a common skew normalization. Thus the computed rational matrix in each modular evaluation is skew, which should be checked by entry sums (FracElement equality direct negation can differ by a unit representation). q5 exact value follows by the same calculation without the scaled classes.


## Reproduction

In a scratch directory with the three companion scripts and Python packages NumPy and SymPy, run:

```sh
for x in 0 1 2 3; do
  OPENBLAS_NUM_THREADS=1 python3 c8q9.py 4 "$x" 1 0 || exit
done
OPENBLAS_NUM_THREADS=1 python3 c8q9.py 2 0 1 0
python3 c8q9res.py 1 0
python3 c8q5val.py
```

The modular certificate asserts exact residues 21978 and 16895, hence corrected factor 21540, and independently computes the same two-class value. Its intermediate pickle files are local products of `c8q9.py` and are not distributed. Do not replace them with untrusted files. The uniform result uses the characteristic-zero proof above, not interpolation of ranks across dimensions.
