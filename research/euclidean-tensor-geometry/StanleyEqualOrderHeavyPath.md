# Equal-order heavy path skeletons: marked cuts

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

**Theorem.** Suppose the heavy skeleton is a path on at least two vertices. If all its blocks at cutoff \(h=2\) have a common order \(s\ge3\), their tree is determined among all trees by its ordinary chromatic symmetric function. More generally, at any cutoff \(h\) and common order \(s\ge h+2\), the invariant determines the equal-order path skeleton decorated by the number of nonroot leaves in each block.

## Part and order data

Use the unsigned cut polynomial \(U\) and the heavy skeleton convention of [the predecessor proof](./StanleyHeavyEdgeCore.md). Its top high homogeneous layer determines the common block order \(s>h\) and number \(q\) of blocks in any rival. Setting \(x_1=\cdots=x_h=0\) forces every block intact: cutting at any nonheavy edge would create a nonempty piece contained in its off-skeleton side of size at most \(h\). After undoing the index scaling by \(s\), this is the ordinary skeleton cut polynomial. For \(q\ge3\) the number of singleton one-edge splits counts its leaves, and two leaves force the skeleton to be a path. For \(q=2\) no skeleton recognition is needed.

Orient the path provisionally. Put \(w_i\) for the block mark weight, \(P_i=\sum_{j=1}^i w_j\) and \(M=P_q\). The suffix count \(Q_i=M-P_{q-i}\) defines \(S_i=(P_i+Q_i)/2\), \(D_i=P_i-Q_i\). Thus \(D_{q-i}=D_i,\ S_{q-i}=M-S_i\), and reversing the word negates every \(D_i\).

## Single and paired marked cuts

If \(s\ge h+2\), mark one detached leaf via deficit \(\delta=1\) and factor \(x_1\); \(w_i\) is the number of leaves of the block other than its root. Every shortened interval of intended length \(i\ge1\) has surviving order \(si-1>h\). If \(s=3,h=2\), specialize \(x_1=0\) and mark one arm detach via deficit \(\delta=2\) and factor \(x_2\). The root polynomial is \(z^3+x_2 z\) for endpoint-rooted blocks \(E\), and \(z^3\) for center-rooted blocks \(C\); put \(w_i=1\) on \(E\), \(0\) on \(C\). A shortened interval of intended length \(i\ge2\) then has order \(3i-2>2\).

An interval of required component order \(si\) or \(si-\delta\) must contain at least \(i\) skeleton roots, since each root contributes at most \(s\) vertices. If the intended large-component lengths sum to \(q\), all counts are exact and no small fragment can contain a root. Each required intact component has no detachment; each once-shortened one has exactly one detached fragment, with possible origins counted by the sum of \(w_i\) in that interval. For the leaf mark this holds because the detached singleton must be a nonroot original leaf; for the arm mark it follows from the two rooted polynomials. Here and below the cut coefficients are computed from the full \(U\) (leaf mark) or from \(U|_{x_1=0}\) (arm mark).

In the leaf-mark case \(M\) is the number of leaves of the whole tree. In the arm-mark case that number is \(2q-M\). These are read from the degree sequence, determined by \(X_T\) by [Martin–Morin–Wagner](https://arxiv.org/abs/math/0609339). For the arm mark, the degree-four vertices are precisely the center-rooted blocks at interior skeleton vertices, so the number of \(E\) endpoints is also known, giving \(S_1,D_1^2\) directly.

For every \(i\le\lfloor q/2\rfloor\) for which both intervals can be shortened (all \(i\ge1\) in the leaf case; all \(i\ge2\) in the arm case), the coefficient of
\[
x_\delta x_{si-\delta}x_{s(q-i)}
\]
is \(P_i+Q_i\). The coefficient of
\[
x_\delta^2 x_{si-\delta}x_{s(q-i)-\delta}
\]
is \(P_i(M-P_i)+Q_i(M-Q_i)\), except when \(i=q-i\), in which case it is half that expression because the one middle cut is counted once. These recover \(S_i\) and \(D_i^2\).

## Three components recover signed products

Take \(a+b+c=q\), with all lengths at least one in the leaf case or two in the arm case. Let \(C_{ab}\) be the coefficient of \(x_\delta^2 x_{sa-\delta}x_{sb-\delta}x_{sc}\), multiplied by two if \(a=b\). Treat the segments labeled \(a,b,c\) as distinct formal objects even when lengths repeat. This coefficient is the sum over all six permutations of the product of the mark counts in the segments labeled \(a,b\). The multiplier accounts exactly for two marked segments with the same signature; unmarked and marked signatures never coincide.

If one segment of length \(u\) is at the left it has count \(S_u+D_u/2\); if at the right, \(S_u-D_u/2\). A middle segment with length-\(u\) left and length-\(v\) right has count \(M-S_u-S_v+(D_v-D_u)/2\). Let \(C_{ab}^{(0)}\) be the known expression with all \(D\)'s set to zero. Pair the orders with their reverse: the terms linear in \(D\) cancel. The three middle choices give
\[
C_{ab}-C_{ab}^{(0)}
=\frac12\bigl(D_aD_c+D_bD_c-D_aD_b-D_a^2-D_b^2\bigr).
\]
Hence \(Z_{ab}=2(C_{ab}-C_{ab}^{(0)})+D_a^2+D_b^2 =D_aD_c+D_bD_c-D_aD_b\), and cycling marks yields
\[
D_aD_b=(Z_{ac}+Z_{bc})/2.
\]
The identity applies unchanged when lengths repeat. All needed single magnitudes and means are determined from the two-part cuts and their reflected indices.

In the leaf case any two distinct indices \(1\le i,j\le\lfloor q/2\rfloor\) have \(i+j\le q-1\), so take the third length \(q-i-j\ge1\). The products and magnitudes determine the vector \(D\) up to simultaneous sign (pick any nonzero coordinate as an anchor). Then \(P_i=S_i+D_i/2\), and successive differences recover every mark weight. At cutoff two this completely determines each rooted block: if it has \(u\) single leaves and \(v\) length-two arms, \(w_i=u+v\) and \(s-1=u+2v\). Simultaneous sign reversal only reverses the spine.

## The order-three boundary

In the arm case all distinct \(2\le i,j\le\lfloor q/2\rfloor\) are covered by three parts except the pair \((q/2-1,q/2)\) for even \(q\). For this adjacent pair, if both entries are nonzero, their signs agree since \(|D_{i+1}-D_i|=|w_{i+1}-w_{q-i}|\le1\). Thus the interior vector is known up to overall sign, and only alignment with \(D_1\) remains.

If either \(D_1=0\) or the interior vector is zero, there is no unresolved ambiguity beyond reversal. Otherwise for \(q\ge7\) choose a nonzero interior \(D_j\) and set \(l=q-1-j\), so \(3\le l\le q-3\) and \(D_{l+1}=D_j\). The squared count sum \(W_l=\sum_{b=0}^{q-l}(P_{b+l}-P_b)^2\) over all connected \(l\)-sets is known from the [preceding giant moment extraction](./StanleyHeavyEdgeCore.md#5-equal-order-star-and-double-star-skeletons),
\([x_{3l-2k}x_2^k x_3^{q-l}]U|_{x_1=0}\) for \(k=1,2\); sum the first moment plus twice the second. Indeed the giant has at least \(l\) roots by size for \(k=1\), and by parity for \(k=2\): fewer roots would give at most \(l-2\), insufficient mass. Then exactly \(l\) roots are forced and every complementary root is intact.

Changing the sign of \(D_1\) alone changes both \(P_1,P_{q-1}\) by \(-D_1\), leaving all other \(P\)'s fixed. Only two terms of \(W_l\) change: the terms whose initial index is 1 and whose final index is \(q-1\), respectively. The net change is \(2D_1D_{l+1}=2D_1D_j\), nonzero, so one orientation is impossible. For \(q\le5\), there are at most two entries and they are adjacent, hence all nonzero signs agree. At \(q=6\), the only residual ambiguity has \(D_2=0\) and \(D_1,D_3\) both nonzero. Orient \(D_3=1\) by reversal; necessarily the words are \(101010\) or \(011001\). The coefficient of \(x_2^3x_3^4\) in \(U|_{x_1=0}\) counts connected all-\(E\) pairs and triples (same lemma), giving 0 and 1 respectively. This completes the order-three case.

**Context.** The leaf-basis approach for [proper \(q\)-caterpillars](https://arxiv.org/abs/2307.02234) requires a uniform pendant path length, unlike the present order-three family with both two singletons and a pendant two-vertex path. And an internal \(E\) block attaches its pendant support to a nonleaf spine vertex, so removing leaves need not leave a path, unlike ordinary caterpillars. This result has unbounded diameter but does not close unrestricted diameter six. Three-component cuts containing two marks genuinely go beyond interval-composition data.

### Why unmarked giant intervals do not suffice

[Acharya–Das–Milenkovic–Orlitsky–Pan](https://people.ece.cornell.edu/acharya/papers/str_rcn_sidma.pdf) give the distinct non-reversed words \(\mathtt{01001101},\mathtt{01101001}\) with the same substring-composition multiset. They even agree on the formal unmarked multigiant polynomial for this path construction: each interval of length \(j\ge2\) of a segmentation is assigned \(y_j\), and every singleton is assigned its own letter variable. This 39-monomial identity follows by taking all \(2^7\) cut sets on each path, or by the recursion \(G_\varnothing=1\), \(G_w=\ell_{w_1}G_{w_{2:}}+\sum_{j=2}^{|w|} y_jG_{w_{j+1:}}\). But the actual order-three cut polynomials after setting \(x_1=0\) differ at \(x_2^2x_8x_{12}\), with coefficients \(3\) and \(2\) respectively (\(1=E\)). The only admissible skeleton lengths here are \(4,4\), where both detachments lie in one component: size 8 needs at least four roots by its even parity, and size 12 similarly needs at least four. The count is the sum of the two side binomial counts at the central cut. Thus the extra cut information separates a standard ambiguity of the unmarked extraction.

