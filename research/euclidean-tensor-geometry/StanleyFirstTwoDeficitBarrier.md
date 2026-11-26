# A sharp two-deficit barrier outside the narrow band

**Yongxian Zhang.** AI-assisted proof development and internal mathematical checks; no external peer review claimed.

Consider two ordinary trees whose cutoff-two heavy skeleton is a five-vertex path in the same mass order
\[
(m_1,\ldots,m_5)=(6,12,6,6,6).
\]
At each path vertex attach \(u_i\) single leaves and \(v_i\) length-two arms. The two nonroot leaf-count vectors are
\[
L^{A}=(3,7,4,3,4),\qquad L^{B}=(4,7,3,4,3).
\]
Here \(u_i=2L_i-m_i+1\) and \(v_i=m_i-1-L_i\), which are nonnegative in both cases and give the stated masses. All spine edges are heavy and the off-spine branches have at most two vertices. The trees are nonisomorphic: their mass order is not palindromic, so the only possible isomorphism of their heavy skeletons preserving the mass order is the identity, which does not match the leaf vectors. Their rooted-block type multisets coincide, so the top high homogeneous layers of their \(U\)-polynomials also coincide.

Nonetheless all \(U\)-coefficients whose combined low mass (indices \(1,2\)) is at most two coincide. The invariant survives more than just the one- and two-cut part of the unmarked deck.

## Joint coarsening deck

For a component interval of the spine, write \(m,L,r\) for its total mass, number of nonroot leaves, and count of spine vertices, respectively. Consider the abstract coarsening deck with a label \((m,L)\) on each interval: for every cut set of the spine, record the unordered multiset of these labels, retaining multiplicity of cut sets. The two vectors above give the same such deck. To see this, encode a label \((m,L)\) as \(Bm+L\) for an integer \(B>21\) (21 is the total number of nonroot leaves for either tree), so all labels on intervals are encoded injectively. Put
\[
\alpha=(2,1),\qquad\beta=(6B+3,6B+4).
\]
The two sequences of encoded vertex labels are \(\alpha\circ\beta\) and \(\alpha\circ\beta^{\rm rev}\): the near-concatenation joins the last and first labels into \(12B+7\). The [Billera–Thomas–van Willigenburg factor reversal equality](https://arxiv.org/abs/math/0405434) gives identical L-polynomials and therefore identical joint coarsening decks.

## Coincidence through deficit two

For any cut of combined low mass at most three, every skeleton root is in a high component: a low root forces its whole block, at least six vertices, into low components. The high components are therefore the interval components of a spine coarsening, with their mass reduced by the corresponding deficits. Each intact interval mass is divisible by six, so for low mass at most three its deficit is read unambiguously from the residue of the high index.

A single attached leaf contributes \(1+x_1t\) to a normalized rooted cut series, and a length-two arm contributes \(1+x_1t+(x_2+x_1^2)t^2\). For an interval with parameters \(m,L,r\) the total number of arms is \(v=m-r-L\). Thus its degree-one coefficient is \(Lx_1\) and its degree-two coefficient is \(vx_2+(\binom L2+v)x_1^2\). The deficit-two coefficient from two separate marked components is \(L_iL_j x_1^2\). All unmarked contributions, all separate marks, and the \(\binom L2\) parts are read from the common \((m,L)\) deck. For a single marked component the sum of the remaining term \(v=m-r-L\), over all cut sets and marked components with the specified mass signature, is also equal: \(m,L\) contributions are read from that deck, and the sum of \(r\) contributions from the identical oriented mass words. This accounts for every term of total low mass at most two, including ties because the calculation labels the choice of marked interval before aggregating.

## Third deficit distinguishes

The coefficient of \(x_1x_2x_{15}x_{18}\) comes only from the unique \(18+18\) one-cut split, with both detached fragments lying on the side shortened to 15. Its contribution from a side with \(v\) arms and \(L\) nonroot leaves is \(v(L-1)\), since the size-two fragment must detach an entire arm and the singleton must detach elsewhere. In tree \(A\) the two sides have \((L,v)=(10,6),(11,4)\); in tree \(B\) they have \((11,5),(10,5)\). Thus the coefficient is \(6\cdot9+4\cdot10=94\) in \(A\), and \(5\cdot10+5\cdot9=95\) in \(B\). The shared low-deficit deck is not an ordinary CSF collision.

[Independent edge-cut verification](stanley-marked-path-verify.js) agrees on all 75 low-mass-at-most-two monomials and reproduces the differing coefficient.
