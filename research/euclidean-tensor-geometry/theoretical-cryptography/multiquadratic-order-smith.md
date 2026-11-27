# All additive elementary divisors of a multiquadratic tensor order

Let \(K_i=\mathbb Q(\sqrt{d_i})\), where the squarefree \(d_i\) have independent square classes over \(\mathbb Q\), and \(M=K_1\cdots K_n\). Write
\[
 A=\mathcal O_{K_1}\cdots\mathcal O_{K_n}\subset B=\mathcal O_M .
\]
We determine every additive local Smith exponent of \(A\subset B\), including at the wild prime \(2\) and for arbitrarily many factors. At \(2\) the input is just four types of the original quadratic factors, but ramification indices alone do not distinguish the answers. The general calculation avoids building a global integral basis of \(M\).

**Scope and comparison.** This is about integral lattices inside otherwise isometric tensor products of canonical embedding spaces. [Lyubashevsky–Peikert–Regev, §1.2](https://sites.cc.gatech.edu/fac/cpeikert/pubs/toolkit.pdf) avoids this defect with pairwise coprime conductors in its cyclotomic tensor decomposition. The [earlier tensor-order note](tensor-order-integral-defect.md) computes arbitrary-degree local exponents when at most one factor is wild and gives two wild examples. The multiquadratic setting here treats any number of wild factors. For prior work on the maximal order and indices in multiquadratic fields, see the discussion of Schmal's integral bases in [*Indices of multiquadratic number fields*](https://www.impan.pl/shop/en/publication/transaction/download/product/82480). The invariant computed here comes from comparing the given product order to the maximal order, not just from computing the total index, field discriminant, or the common index of primitive elements. There is no claim about a learning problem or particular cryptosystem.

## 1. Exact formulas

A Smith exponent \(s\) at \(p\) means a diagonal entry \(p^s\) in the additive inclusion after localization and completion. Count \(s=0\) as a coordinate with no defect.

**Odd primes.** If \(k\) of the \(d_i\) are divisible by the odd prime \(p\), take \(\lfloor j/2\rfloor\) with multiplicity \(2^{n-k}\binom{k}{j}\) for \(0\le j\le k\).

**The prime two.** For an odd \(d_i\), call it type U if \(d_i\equiv1,5\bmod8\), and type A if \(d_i\equiv3,7\bmod8\). For even \(d_i\), use the odd part \(d_i/2\): call it type B for residues \(1,5\bmod8\), and type C for residues \(3,7\bmod8\). These three non-U types correspond respectively to local roots \(i,\sqrt2,i\sqrt2\) after the unramified quadratic base change.

Remove all U factors, and repeat the final exponent list \(2^{\#\mathrm{U}}\) times. For the remaining factors do the following.

* If there are none, the list is the single exponent \(0\).
* If only one type of A, B, C occurs, anchor one factor of that type, and start with one of the following pair lists \((P_0,P_1)\):
  \[
  \begin{array}{c|cc}
  \text{anchor type} &P_0&P_1\\\hline
  \mathrm{A}&(0,0)&\text{not used}\\
  \mathrm{B}\text{ or }\mathrm{C}&(0,0)&(0,1)
  \end{array}
  \]
* If two or three types occur, choose two different anchor types. If A occurs, include A and one of B or C; otherwise choose B and C. Use
  \[
  \begin{array}{c|cc}
  \text{anchor types}&P_0&P_1\\\hline
  \mathrm{AB}\text{ or }\mathrm{AC}&(0,0,0,1)&(0,1,1,1)\\
  \mathrm{BC}&(0,0,1,1)&(0,1,1,2).
  \end{array}
  \]
For every subset \(S\) of the remaining non-anchor factors, set \(s=|S|\) and let \(k\) count its type B or C factors. Add to each entry of \(P_{k\bmod2}\) the number \(s+\lfloor k/2\rfloor\). Concatenate the resulting lists. For the single-anchor type A, \(k\) is always zero. Equivalently subsets of the same selected type counts are collected with ordinary binomial multiplicities. This gives \(2^n\) entries after restoring U factors and is independent of the allowed anchor choice.

In particular the additive cokernel is the direct sum of the cyclic groups given by the positive entries, prime by prime. Modulo \(p^e\), for \(e\ge1\), the kernel and cokernel have the same abstract groups with \(p^s\) replaced by \(p^{\min(e,s)}\); this identifies no natural ring decomposition.

## 2. An integral two-branch diagonalization

Let \(V\) be a DVR, \(F\) its fraction field, and \(W\) the integers in a finite separable extension \(E/F\). Suppose \(C_0\subset W\) is a full \(V\)-order in \(E\) and \(t_1,\ldots,t_m\) are nonzero elements of \(C_0\). Put
\[
 C=C_0[X_1,\ldots,X_m]/(X_j^2-t_j^2)_j .
\]
Its generic fiber is a product of \(2^m\) copies of \(E\), by evaluation at \(X_j=\pm t_j\); the normalization is \(W^{2^m}\). The additive inclusion is equivalent by \(V\)-linear basis changes to the direct sum over subsets \(S\subset[m]\) of
\[
 2^{|S|}\Bigl(\prod_{j\in S}t_j\Bigr)C_0\ \longhookrightarrow\ W. \tag{1}
\]
Here \(2\) is the ordinary integer in \(V\); it need not be a unit. In particular no Fourier matrix is inverted at a wild prime.

For one variable, evaluation sends \(f+Xg\) to \((f+tg,f-tg)\). The source substitution \((f,g)\mapsto(f-tg,g)\) is invertible because \(t\in C_0\). On the target, subtraction of the first branch from the second is also an invertible basis operation. The resulting maps are \(f\) in the first component and \(-2tg\) in the second. The same operations are \(C_0\)-linear on any preceding tensor product, with target \(W^{2^j}\). They commute with the remaining \(t\)'s, so induction proves (1). If the \(t\)'s are integral only in the normalization and not in the smaller anchor order, the stated source substitution is not justified; the anchor choices below guarantee the stronger condition.

## 3. Normalization and the anchor orders at two

Use the unramified quadratic extension \(V/\mathbb Z_2\) with fraction field \(F=\mathbb Q_2(\sqrt5)\). It is unramified because \((1+\sqrt5)/2\) has polynomial \(X^2-X-1\) irreducible modulo two. This base change preserves the Smith exponents: each \(2^s\) remains a uniformizer power, and a Smith basis stays invertible. The normalization after base change is the base change of the normalization, since the extension of DVRs is finite étale and base change preserves normality here, or equivalently by the unramified base change of the field factors and their integer rings.

A rational odd unit has square class represented by exactly one of \(1,5,-1,-5\), according to its residue modulo eight. One way to see that all units \(1\bmod8\) are squares in \(\mathbb Q_2\) is to lift an odd root from modulo eight inductively: adding \(2^{k-1}\) to a root modulo \(2^k\) toggles the square in the next bit for \(k\ge3\). The other residue classes cannot be squares of odd integers. Adjoining \(\sqrt5\) thus leaves representatives \(1,-1\) for odd units, and \(2,-2\) for even squarefree inputs. The square-root scalars used for these changes are units. The type U factor is split over \(V\) also integrally: its quadratic integer generator \((1+\sqrt{d_i})/2\) has the two split roots differing by the unit \(\sqrt{d_i}\), so it gives \(V\times V\). For the other types use the basis \(1,\sqrt{d_i}\), whose change to the indicated type generator uses a unit, so the orders are \(V[i]\), \(V[b]\), \(V[c]\) for \(b=\sqrt2,\ c=i\sqrt2\), respectively. Unramified or split factors therefore cause only the stated multiplicity.

With one non-U type the anchor order is already the integer ring of its quadratic field; for example \(b,c\) have Eisenstein polynomials, and \(i-1\) does too. With two different non-U types the field generated is \(F(\zeta_8)\): \(i=\zeta_8^2,\ b=\zeta_8-\zeta_8^3,\ c=\zeta_8+\zeta_8^3\), and any pair of \(i,b,c\) generates the same field. It is of degree four, with \(W=V[\zeta_8]\), because the polynomial \((X+1)^4+1\) of \(\zeta_8-1\) is Eisenstein. The order \(C_0\) of an AB or AC anchor has integral basis \(1,i,b,c\) up to units or permutation, and contains every possible additional type generator. If A is absent and the two anchors are B and C, the basis is \(1,b,c,2i\), which contains the only extra possible generators \(b,c\). Thus in all cases every remaining generator qualifies as \(t_j\in C_0\) for (1).

A product of selected anchor-type elements contains a number \(k\) of \(b,c\) factors. As an element of \(W\) it is \(2^{\lfloor k/2\rfloor} b^{k\bmod2}\) times a unit if \(b\in W\). If the only type is C, use \(c\) instead of \(b\); the same assertion holds using \(c^2=-2\). Multiplication by any unit of \(W\) is invertible on the ambient integer module and therefore does not affect the Smith exponents of this block. The factor \(2^s\) in (1) adds a further \(s\) to all block exponents.

The degree-two Smith lists are immediate: the identity block has two zeros, and multiplication by \(b\) or \(c\) sends the basis \(1,b\) or \(1,c\) to \(b,2\) or \(c,-2\), giving \((0,1)\). For degree four organize the coordinates into the even pair \(1,\zeta_8^2\) and the odd pair \(\zeta_8,\zeta_8^3\). In an AB or AC anchor the even block is the identity, and the odd block has columns \((1,-1)\) and \((1,1)\), with exponents \((0,1)\). Multiplying by \(b\) replaces the even pair by \(2,2i\) and leaves the same odd span, giving \(P_1=(0,1,1,1)\). In a BC anchor the even basis is \(1,2i\), and the odd block is unchanged, yielding \(P_0=(0,0,1,1)\). Multiplying the BC basis by \(b\) gives the even pair \(2,2i\) and the odd pair \(b,2c\), the latter with Smith exponents \((0,2)\) by its unit entry and determinant of valuation two. This gives \(P_1=(0,1,1,2)\). Combining these lists with (1) proves the dyadic formula.

## 4. Odd primes and examples

At odd \(p\), base-change to the unramified quadratic DVR, so all unit square classes of \(\mathbb Q_p\) become squares: the only possible nonsquare class of units is already resolved over the quadratic residue field, by Hensel lifting. The factors with \(p\nmid d_i\) give two integral branches and hence the factor \(2^{n-k}\). For \(k>0\), anchor one of the ramified fields, whose order is \(V[\sqrt p]\) after multiplying its root by a unit. Every remaining ramified generator is the same \(\sqrt p\), up to change by a unit. In (1) the indicated \(2^s\) is a unit, so the block from \(s\) extra roots has exponents \(\lfloor s/2\rfloor,\lceil s/2\rceil\). These are the two values \(\lfloor j/2\rfloor\) for \(j=s\) and \(j=s+1\); counting anchor absent or present gives the multiplicity \(\binom{k}{j}\). If \(k=0\) every block is already the full ring. This proves the formula without invoking the at-most-one-wild computation.

For \((d_1,d_2)=(-1,2),(2,-2),(2,10)\) the dyadic exponents are respectively \((0,0,0,1),(0,0,1,1),(0,0,1,2)\). In all three examples the two factor fields are individually totally ramified at \(2\), so the ramification degrees of the factors alone predict none of the distinctions. For \((-1,2,-10)\), all three types occur and the list is
\[
 (0,0,0,1)\ \cup\ (1,2,2,2).
\]
As an additional check on the total exponent, the tensor discriminant has valuation \(2^{n-1}\sum_i v_p(\mathrm{disc}(K_i))\). The maximal order's discriminant is, by the [abelian conductor-discriminant formula](https://repositorio.unesp.br/server/api/core/bitstreams/e67bdd9b-f254-40b5-a01b-70480ab863fe/content), the product of the discriminants of the nontrivial quadratic subfields. At \(2\), type A contributes valuation two, B and C contribute three, and U zero. Multiplying types adds their square classes in the group of order four after U is collapsed. In the rank-two type case each type occurs \(2^{n-2}\) times among the products of the \(d_i\), giving \(v_2(\mathrm{disc}(B))=8\cdot2^{n-2}\), consistent with the sum of the block exponents above. This discriminant check cannot determine their individual values.

**Replay.** Run `python3 verify-multiquadratic-order-smith.py`. It builds exact branch-evaluation matrices for canonical local models and independently recomputes their Smith valuations over a localization using exact rational operations. It also checks the total index from the discriminants and the modulo-\(p^e\) sizes. This is a proof of local additive structure, not a scheme-level result.
