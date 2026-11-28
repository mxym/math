# Exactly three strict Gaussian basis-improvement families with three odd conductor primes

**Scope.** This is a statement about explicit integral bases of a cyclotomic integer lattice and the operator norm of its Gaussian coordinate map. It does not concern any deployed system, lattice decoding, or the full algebraic conditions of a Ring-LWE reduction.

Let \(m\) be a normalized cyclotomic conductor, so \(m\not\equiv2\bmod4\), and put \(\widehat m=m\) for odd \(m\), \(m/2\) for even \(m\). Use the canonical inner product counting both embeddings in every complex pair. A **shortest-root basis** means an integral basis all of whose vectors are shortest nonzero vectors. In these fields they are precisely signed roots of unity, as recalled below. A powerful tensor basis has squared operator norm \(\widehat m\) when there are three odd conductor primes.

**Theorem.** If \(m\) has exactly three distinct odd prime factors \(p<q<r\), there exists an integral basis with squared operator norm strictly less than \(\widehat m\) if and only if
\[
              (p,q,r)\in\{(3,5,7),(3,5,11),(3,5,13)\}.
\]
The odd prime exponents and the possible power of two in \(m\) are arbitrary. The witnesses in the three exceptional families consist of shortest vectors, and give squared norm less than \(c_r\widehat m\) for the listed rational constants \(c_r<1\); no claim is made that those bounds are optimal. Every other triple has minimum squared operator norm exactly \(\widehat m\) **over all integral bases**, not only shortest-root bases. The proof in fact excludes any strictly improving linearly independent \(d\)-tuple of lattice vectors in every other normalized block.

## 1. Normalize to projected tensor coordinate vectors

For an odd prime \(s\), let \(P_s=I-J/s\) project onto the zero-sum hyperplane and write \(u_i^{(s)}=P_s e_i\), \(i=0,\ldots,s-1\). In squarefree \(m=pqr\), after scaling by \(\widehat m^{-1/2}\), the roots have the Gram of
\[
               v_{ijk}=u_i^{(p)}\otimes u_j^{(q)}\otimes u_k^{(r)} .
                                                               \tag{1}
\]
Indeed a prime-factor trace gives \(s-1\) at coincident labels and \(-1\) at distinct labels, the traces multiply across the coprime factors, and division by \(m\) gives the projected Gram. The powerful basis consists of omitting the last label in each coordinate; the remaining \(u_i^{(s)}\)'s span their projected lattice integrally because the full relation is \(\sum_i u_i^{(s)}=0\). Its normalized squared operator norm is 1: each factor's Gram is \(I_{s-1}-J/s\), whose largest eigenvalue is 1. The powerful tensor basis identifies the full ring of integers, not merely a proper finite-index submodule.

Here is a convenient shortest-vector argument that does not require a new short-vector computation. For any lattice \(L\) with squared minimum \(\lambda\), a vector of \(L\otimes(P_s\mathbb Z^s)\) can be written \(\sum_i w_i\otimes u_i^{(s)}\), \(w_i\in L\), unique up to a common addition. Its squared norm is \(s^{-1}\sum_{i<j}\|w_i-w_j\|^2\). A nonconstant list has at least \(s-1\) unequal pairs, each costing at least \(\lambda\). Equality for \(s\ge3\) requires one exceptional entry and a common value on the other \(s-1\), with their difference shortest in \(L\). Induction from \(L=\mathbb Z\) therefore gives exactly the signed products (1) as shortest vectors, with squared length \(d/N\) for \(d=(p-1)(q-1)(r-1)\) and \(N=pqr\).

For a prime power \(s^a\), group each root \(\zeta_{s^a}^j\zeta_s^i\) by \(j\bmod s^{a-1}\); the Ramanujan trace is zero between different groups, and within a group after scaling by \((s^a)^{-1/2}\) is \(P_s\). Thus the normalized lattice is an orthogonal sum of copies of the projected \(s\)-lattice and every root is in just one copy. An even conductor's power-of-two factor has a scaled orthonormal root basis, with squared scaling \(2^{a_0-1}\) if its factor is \(2^{a_0}\). Tensoring these prime-power decompositions gives a block sum of identical (1) lattices after normalization by \(\widehat m^{-1/2}\). A shortest-root integral basis of the full ring is a union of shortest-root integral bases of the blocks: all shortest vectors are supported in one block and generation in each block then follows. Consequently the classification reduces to a single squarefree normalized block.

## 2. The size obstruction and the packing view

Let \(P=P_p\otimes P_q\otimes P_r\), and \(H=\operatorname{im}P\). The full \(N\) vectors (1) are the projections of the coordinate orthonormal basis. Thus their frame operator on \(H\) is \(I_H\). If a subset \(S\) of \(d\) labels is a basis, the squared operator norm of its column map is the largest eigenvalue of its frame operator
\[
                    F_S=I_H-F_{S^c},\qquad
 F_{S^c}=\sum_{a\notin S}v_a v_a^\mathsf T .
\]
It is always at most 1 and **strictly** less than 1 exactly when the omitted labels span \(H\). If \(d>N/2\), there are fewer than \(d\) omitted labels, hence none can do so. The inequality \(d/N\le1/2\) leaves precisely the three triples in the theorem: if \(p\ge5\) or if \(p=3,q\ge7\) the least possible product \(\prod(1-1/p_i)\) already exceeds \(1/2\); if \(p=3,q=5\), it reduces to \(r\le16\).

The rank obstruction is exactly the real frame basis-packing threshold, not just a counting heuristic. For any rank-\(d\) Parseval frame on \(N\) columns of identical squared length \(\delta=d/N\), the dimension of \(\ker F_{T^c}\) is \(d-\operatorname{rank}(T^c)\); each such direction is an eigenvector of \(F_T\) with eigenvalue 1. Thus
\(d-\operatorname{rank}(T^c)\le\operatorname{tr}F_T=\delta|T|\).
The [Edmonds–Fulkerson base-packing criterion](https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn3p147_A1b.pdf), Theorem 2, implies that there are exactly up to \(\lfloor1/\delta\rfloor\) disjoint real frame bases. The opposite inequality follows by cardinality. That does **not** guarantee an integral basis of a particular lattice generated by the frame; the determinant-one check in the exceptional cases is essential.

## 3. The three exact positive certificates

Use the flat label \(((5i+j)r+k)\) for \(0\le i<3,0\le j<5,0\le k<r\). A hex mask lists a subset by having bit \(\ell\) equal to 1 exactly at its flat label \(\ell\), with least significant bit indexed 0. The following table and accompanying integer-only verifier certify existence:

| Largest prime \(r\) | Rank \(d\) | Hex mask | Rational \(c_r\) |
|---:|---:|---|---:|
| 7 | 48 | `0xcbb0fcd90e22b270cc393904b2` | \(183/200\) |
| 11 | 80 | `0x1faa2f302f7680000fdf5fa5175f7b7043100201fd` | \(193/200\) |
| 13 | 96 | `0xffeed28a084141e9209e9fb15bffc761c604826f58ab2c87` | \(49/50\) |

For clarity the two computations in the certificate are specified here.

* **Integral generation.** In the powerful basis each factor-label vector is the corresponding standard coordinate if the label is below the last, and the all-\(-1\) vector if it is last. Form the integer matrix whose columns are the tensor products of these vectors for the selected mask, in lexicographic order. Its determinant in every row of the table has absolute value 1. This is the necessary exact check; a nonzero determinant or full modular rank alone is insufficient.
* **Operator norm.** The integer matrix \(G\) with entries
\[
  G_{(i,j,k),(i',j',k')}=
        (3\mathbf1_{i=i'}-1)(5\mathbf1_{j=j'}-1)
                                      (r\mathbf1_{k=k'}-1)
\]
is \(N\) times the normalized Gram. For \(c_r=a/b\) from the table, the symmetric matrix \(aN I-bG\) is positive definite. The verifier checks this by fraction-free elimination with positive leading principal minors, using only integers. Hence the normalized squared norm is strictly less than \(c_r\). The verifier also reports the complementary ranks modulo 2 as a diagnostic. Where full, that gives a separate test for a strict gap, but neither a proof of determinant one nor of the listed numerical bound.

The masks can be transferred to every block of a higher prime-power conductor. A strictly contracting shortest-root basis also remains strictly contracting after tensoring with the powerful basis of any additional coprime odd prime-power factor, since that factor has normalized operator norm 1. Thus the three families provide broader examples beyond the exact three-odd-prime classification, without implying a complete classification for larger numbers of primes.

## 4. Proving the converse for arbitrary lattice columns

The counting obstruction in §2 alone does not exclude longer columns. The additional step is an obstruction in the ambient coordinate frame: after controlling which short columns can overlap, their **integer coefficient Gram** has no eigenvalue below 1. We give the short-column and overlap details.

### 4.1 A short-column list for the only small bottom factors

Use a *normalized* block, so every column of a putative basis of norm \(\le1\) has squared norm \(\le1\). In a tensor with \(P_s\mathbb Z^s\), subtracting the slice at a uniformly chosen anchor gives average sum of squared slices exactly twice the squared tensor norm, by the pairwise formula of §1. If \(k\) entries of an anchored representation are nonzero, the tensor norm is also at least \((1-k/s)\) times their sum of squared slice norms, by Cauchy–Schwarz on their sum. We use this below with the usual squared lengths. In \(P_p\mathbb Z^p\), the shortest squared length is \((p-1)/p\). Any other nonzero vector has squared length at least 2 if \(p=3\), or at least \(2(p-2)/p\) if \(p\ge5\): an integer representative with two entries differing by at least 2 contributes at least \(2p\) to the sum of squared differences, and otherwise it reduces to a \(0,1\) vector.

First suppose \(q\ge11\). The bottom squared minimum is \(\lambda=(1-1/p)(1-1/q)\ge20/33\), and \(r\ge13\). There is an anchor with at most three nonzero entries. The two- and three-entry lower bounds \(2(1-2/r)\lambda\), \(3(1-3/r)\lambda\) are both \(>1\); only one top slice survives. Its bottom squared norm is at most \(r/(r-1)\le13/12\). Anchoring in the \(q\) factor next gives at most three nonzero \(P_p\)-entries, but the two- and three-entry bounds are already at least \(12/11\) and \(16/11\), respectively. Thus this too is a single slice. A nonshort \(P_p\)-factor has squared length at least \(6/5\), whose product with \(1-1/q\) is at least \(12/11>13/12\). All columns are therefore shortest roots, and §2 applies.

For the remaining cases we only need to exclude strict improvement when the triple is not one of the three listed. These cases are \((3,5,r)\) with \(r\ge17\), and \((3,7,r)\), \((5,7,r)\) with \(r\ge11\). A bottom *root* below means \(u_a^{(p)}\otimes u_b^{(q)}\), with an optional whole-vector sign. The allowed columns in these three cases are:
- **S:** a single root at one top label.
- **M:** two roots at the same top label, with plus signs. If \(p=3\), the two share their \(p\)-label and have distinct \(q\)-labels. For \((p,q)=(5,7)\), they share their \(q\)-label and have distinct \(p\)-labels.
- **L:** two roots at the same top label, with opposite signs and with both bottom labels different. This is allowed only in the two \(p=3\) cases.
- **X:** one bottom root at each of two distinct top labels, with relative sign chosen so their bottom inner product is positive. This is allowed only in the two \(p=3\) cases.

Here is verification that the list is exhaustive. For \((3,5)\), the bottom squared norms have denominator 15; the pure top-slice cutoff \(r/(r-1)\le17/16<16/15\) leaves bottom squared norms at most 1. Anchor in its five slices of \(P_3\), getting at most three nonzero entries; a nonshort entry has squared norm at least 2, and by itself would already give \(8/5>1\) in the tensor. If three shortest entries are present and all equal, reanchor at them and reduce to two. If they are not all equal, the five-entry list (two zeros) has at least eight unequal pairs, giving squared norm at least \(16/15\). Thus at most two shortest entries suffice. The two-entry squared norm is \((16-2a)/15\), where \(a=3\langle w_i,w_j\rangle\) is in \(\{\pm1,\pm2\}\); \(a=2\) gives M, \(a=1\) gives L. Thus the only bottom squared lengths at most 1 are \(8/15,12/15,14/15\).

For \((3,7)\), the bottom cutoff is at most \(11/10\), giving at most three nonzero \(P_3\)-entries after anchoring. Three have lower bound \(8/7>11/10\). A nonshort entry alone gives at least \(12/7\) and cannot coexist with another at the anchored sum bound. Two shortest entries have squared norm \((24-2a)/21\) in the bottom tensor, so again only \(a=2,1\) fit, giving M and L of squared lengths \(20/21,22/21\); the bottom root squared length is \(12/21\). For \((5,7)\) the same anchored sum permits at most two nonzero \(P_5\)-entries and two already give lower bound \(8/7>11/10\). The sole entry has squared length at most \(77/60<2\); the integer difference test then leaves a singleton or a two-subset, giving bottom squared lengths \(24/35,36/35\) (S or M).

At the top level, in the two \(p=3\) cases anchoring permits at most three nonzero bottom entries; three have bound \(3(1-3/r)\lambda>1\) for the stated \(r\). Two entries cannot include a nonshort one: the lower bounds are \((1-2/r)(8/15+12/15)>1\) or \((1-2/r)(12/21+20/21)>1\). For two shortest bottom entries write \(b=pq\langle w_i,w_j\rangle\). The squared norm is
\[
                  \frac{2M_0}{pq}-\frac{2M_0+2b}{pqr},
       \qquad M_0=(p-1)(q-1)\in\{8,12\}.
\]
The norm cap at \(r\ge17\) or \(r\ge11\), respectively, forces \(b>0\) and gives X as stated. In the \((5,7)\) case the anchored sum permits only two or fewer and two have lower bound \(2(1-2/r)(24/35)>1\), so X does not occur.

### 4.2 Overlaps in the ambient root coefficients

Lift each column on this list to its indicated coefficient vector in the \(N=pqr\) coordinate vectors before projection by \(P\). Thus the lifted column has one or two coefficients \(\pm1\), not in general a single coordinate unit vector. The compatibility rule for column pairs is the \(2\times2\) principal minor of \(I-B^\mathsf TB\succeq0\). In units scaled by \(pqr\), if their deficits from unit squared length are \(d_1,d_2\), their inner product has magnitude at most \(\sqrt{d_1d_2}\).

For pure columns S/M/L at the same top label, the following table lists the deficits and lower bounds on the magnitude of their inner product **if their lifted supports overlap**, the latter divided by the factor \(r-1\). Pairs are distinct up to signs. The star denotes one separately treated class.

| Bottom pair | Deficits \((d_S,d_M,d_L)\) | S–M | S–L | M–M | M–L | L–L |
|---|---|---:|---:|---:|---:|---:|
| (3,5) | \((7r+8,\,3r+12,\,r+14)\) | 6 | 7 | star | 4 | 2 |
| (3,7) | \((9r+12,\,r+20,\,22-r)\) | 10 | 11 | 6 | 8 | 4 |
| (5,7) | \((11r+24,\,36-r,\,\text{absent})\) | 18 | absent | 6 | absent | absent |

The resulting lower bound is strictly above \(\sqrt{d_1d_2}\) in every nonstar case in the relevant ranges \(r\ge17\) and \(r\ge11\); a type with negative deficit is already absent. For example the squared-bound difference for S–M in \((3,5)\) is \(15r^2-180r-60>0\) for \(r\ge17\), and L–L reduces to \(2(r-1)>r+14\). All the comparisons can also be checked by expanding their squared differences in \(r-17\) or \(r-11\), respectively; they have positive constant and nonnegative other coefficients.

The table follows just from the bottom products \((p\mathbf1_{a=a'}-1)(q\mathbf1_{b=b'}-1)\). For a shared root orient two columns so that its sign is positive in each. With \(p=3\), S–M and S–L give \(M_0-2\) and \(M_0-1\). For M–L, the two unshared roots have bottom dot at most 1 in these units, because one shares the first label with the shared root and the other does not; the result is at least \(M_0-4\). For L–L, the unshared pair has bottom dot at least \(-(q-1)\), so the result is at least \(M_0-2-(q-1)\). For M–M at one shared root, the bottom dot is \((p-1)(q-4)\) if the two plus roots share the \(p\)-label, or \((q-1)(p-4)\) if they share the \(q\)-label. Type S duplications up to sign, or other identical lifts up to sign, are excluded by independence.

The star case \((3,5)\) allows two overlapping M columns at the same fixed \(p\)- and top labels. However two disjoint two-subsets within this same group would have inner magnitude \(8(r-1)>3r+12\), so all pairs in the group must overlap. Three such M columns, oriented as sums, would have diagonal \(12(r-1)/(15r)\) and pair inner product \(2(r-1)/(15r)\), giving largest eigenvalue \(16(r-1)/(15r)>1\) for \(r\ge17\). Thus there are at most two M columns in each fixed group.

Next consider any overlap involving X. In the \((3,5)\) case \(r\le32\) whenever X is present and its largest possible deficit is \(32-r\le15\). In \((3,7)\), \(r\le16\) and its largest deficit is \(48-3r\le15\). When an X and a pure column share an exact root coordinate, their projected inner product in the scaled units is \(r\) times the unprojected local bottom inner product, minus the inner product between the two bottom sums. The first part has magnitude at least \(r(M_0-2)\); the subtracted part has magnitude at most \(4M_0\) because there are at most four root pairings. Thus the total magnitude is at least 70 in the first case or 62 in the second. The largest possible pure deficits in these respective ranges are at most 232 and 156, so this violates the pair rule in both cases.

For two X's with a shared exact root, if their two supports are identical the sign condition \(b>0\) fixes their relative sign and they coincide up to a whole-column sign. Otherwise at most one exact root is shared. The unprojected local bottom inner product sum is then at least \(M_0/2\) in absolute value: a shared root contributes \(\pm M_0\), and any other top match between two distinct roots can cancel at most \(M_0/2\). The projected scaled inner product is therefore at least \(rM_0/2-4M_0\), at least 36 or 18, respectively, again above the allowed magnitude 15. So X columns cannot overlap any other column's root support.

The only possible connected components of the lifted-column overlap graph are consequently isolated columns and the indicated M-pairs in \((3,5)\). The coefficient matrix \(C\) with these lifts as columns has \(C^\mathsf TC\succeq I_d\): its blocks are \([1]\), \([2]\), and \(\begin{pmatrix}2&\pm1\\\pm1&2\end{pmatrix}\). On the \(d\)-dimensional subspace \(\operatorname{im}C\), the matrix \(CC^\mathsf T\) is therefore at least identity as a quadratic form. In all triples now under consideration \(d>N/2\), so \(\operatorname{im}C\cap H\) contains a nonzero vector. On it,
\(\langle y,PCC^\mathsf TPy\rangle=\langle y,CC^\mathsf Ty\rangle\ge\|y\|^2\).
The projected basis \(PC\) has operator norm at least 1. This is the required converse and also explains why arbitrary choices of longer columns cannot evade the rank count.

For arbitrary conductor exponents in a nonexceptional triple, the normalized minimum squared length of a block is \(d/N>1/2\). A candidate of operator norm \(<1\) has every column supported in a single block, since two nonzero block components would have squared norm \(>1\). A basis then restricts to a basis in each block, where the contradiction has just been proved. In the three exceptional triples, repeat the explicit contracting basis from §3 in every block. This completes the full classification.

## 5. Meaning for coordinate padding and source comparison

In canonical real orthonormal coordinates a spherical continuous Gaussian of width \(s\) sent to integral trace coordinates by a basis matrix \(B\) has width-squared matrix \(s^2B^\mathsf T B\). Independent Gaussian padding can make that covariance spherical exactly when the target width is at least \(s\|B\|_{\rm op}\), by positive semidefiniteness of the missing covariance. Thus these certificates reduce the sufficient (and for the fixed map necessary) Gaussian padding width by an exact factor smaller than \(\sqrt{c_r}\) relative to the powerful basis. This covariance calculation does not require or prove the algebraic compatibility of the full reduction in [Peikert–Pepin, *Algebraically Structured LWE, Revisited*](https://web.eecs.umich.edu/~cpeikert/pubs/structured-lwe.pdf), §5.3 and Corollary 5.5. It asserts neither a new security reduction nor a property of a particular error sampler.

The powerful tensor coordinates and their trace normalization are standard, e.g. [LPR, *A Toolkit for Ring-LWE Cryptography*](https://sites.cc.gatech.edu/fac/cpeikert/pubs/toolkit.pdf), §4. The underlying tight frame and rational matroid are standard as well: [Chien–Flynn–Waldron](https://www.math.auckland.ac.nz/~waldron/Preprints/Rational-frames/1-s2.0-S0024379515001275-main.pdf) and [Martin–Reiner](https://arxiv.org/abs/math/0402206). The prior tensor-stability result in this repository treated larger triples and left small ranges open. The present conclusion is a full strict-improvement classification for three odd primes, using determinant-one and rational Gram certificates at the three positive triples and the ambient coefficient Gram obstruction for the many short-column possibilities in the converse. In the three positive cases no exact minimum over all integral bases is claimed. The finite replay is a verification of the masks and bounds, not a claim that the search used to find them was exhaustive.
