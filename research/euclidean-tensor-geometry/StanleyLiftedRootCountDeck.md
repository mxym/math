# Lifting the mass deck by the number of skeleton roots

**Yongxian Zhang.** AI-assisted proof development and internal mathematical checks; no external peer review claimed.

**Theorem.** Let the cutoff-two heavy skeleton of an ordinary tree be a path on \(q\ge2\) blocks. Each block has mass \(m\), with \(v(m)\) attached two-vertex arms and \(m-1-2v(m)\) attached single leaves. Assume \(v(m)=\alpha m+\beta\) for two fixed rational numbers \(\alpha,\beta\) (with nonnegative integer attachment counts at the occurring masses). Put \(e=1\) if \(\beta\ne -1\), and \(e=2\) otherwise. Suppose all block masses are multiples of a common integer \(g>eq\) and exceed \(\max(eq^2,2+eq)\). Then the ordinary CSF reconstructs the whole tree among all unweighted trees. The masses can have arbitrary width and arbitrary common-modulus residues after dividing by \(g\). The same number \(v_0\) of arms at every block is the case \(\alpha=0,\beta=v_0,e=1\).

## Certificates from the unsigned cut polynomial

Take cutoff \(h=2\). The top high homogeneous layer of the unsigned cut polynomial \(U\) determines the multiset of rooted-tail factors and hence the number \(q\), the block orders and their numbers of arms, for any equal-\(U\) rival. In detail, a block's sole highest indexed variable is \(x_m\) with coefficient one, and its first-deficit term has coefficient \(L x_1\) at \(x_{m-1}\), where \(L=u+v\) is its number of nonroot leaves; these indices are high because \(m>3\). Together \(m-1=u+2v\) and \(L=u+v\) determine \(u,v\). Thus the affine relation applies to the rival on its entire block multiset, without presuming that its skeleton is a path.

Specialize \(x_2=0\). A single leaf contributes \(A(y)=1+y\), and an arm \(B(y)=1+y+y^2\), with \(y=x_1t\) and \(t\) counting deficit. In any connected skeleton component of intact mass \(m\) on \(r\) roots, the total number of arms is \(\alpha m+\beta r\), and the number of attached single leaves is \(m-r-2(\alpha m+\beta r)\). Its normalized rooted series is therefore
\[
F(y)^m H(y)^r,\qquad F=A^{1-2\alpha}B^\alpha,\quad H=A^{-1-2\beta}B^\beta .
\]
Rational powers here mean formal series with constant term one. The series \(H-1\) has valuation \(e\): its first coefficient is \(-1-\beta\); if \(\beta=-1\), then \(H=A/B\) and \(H-1=-y^2/B\).

## Joint root-count reconstruction

Let \((m_1,\ldots,m_k)\) be a prescribed list of positive intact component masses summing to the total tree order, with each \(m_i\) a multiple of \(g\) and at least the least block order (all other mass lists have zero multiplicity). Give each mass position a label, even if some are equal. For each \(k_i\in[0,eq]\), read the coefficient of the high factors \(x_{m_i-k_i}\) times the low factor \(x_1^{\sum_i k_i}\) in \(U|_{x_2=0}\). Multiply that coefficient by
\[
\prod_{(m,k)}\bigl(\#\{i:(m_i,k_i)=(m,k)\}\bigr)! .
\]
This restores the number of labelings of equal high signatures. Indeed, different pairs \((m_i,k_i)\) cannot give equal indices since the masses are multiples of \(g>eq\).

The extracted coefficients come from exactly the assumed intact mass list. First, all intended high factors have index \(>2\) by the minimum size bound, and the total low mass is at most \(eq^2\) since \(k\le q\) in each possible skeleton cut. We only query \(k\le q\), which suffices. No root can appear in a low component: this would put its whole block into low components, contradicting the minimum block size. For an actual intact component mass \(m_i'\) associated to a factor \(x_{m_i-k_i}\), having \(m_i'<m_i\) would imply \(m_i'\le m_i-g<m_i-k_i\), impossible. Actual and intended intact masses each sum to \(N\); hence all agree, including each deficit. This applies to arbitrary rival skeletons, because all roots accounted for means the surviving high components correspond to connected components of the cut skeleton even before recognizing a path.

Labeling the positions as above, the data are exactly the coefficients of the formal sum
\[
\mathcal D_{\mathbf m}(\mathbf y)
=\sum_{\substack{\text{skeleton cuts and}\\\text{labelings of masses }m_i}}
\prod_{i=1}^k F(y_i)^{m_i}H(y_i)^{r_i},
\]
known through degree \(eq\) in each variable. Divide by the known unit \(\prod_i F(y_i)^{m_i}\) at this precision. If \(z_i=H(y_i)-1\), what remains is the substitution in
\[
\sum_{\text{cuts and labelings}}\prod_i(1+z_i)^{r_i}.
\]
Each \(r_i\le q\), so this is a polynomial of degree at most \(q\) in each variable. Substitution is injective on these degree bounds at the given truncation. Indeed, in one variable, the \(z^j\) terms have distinct leading orders \(ej\le eq\) with nonzero leading coefficients. This gives triangular recovery, and its tensor product does so in all variables. Reexpand the recovered polynomial in \(w_i=1+z_i\); the coefficient of \(\prod w_i^{r_i}\) is the exact number of cut/label assignments with those pairs \((m_i,r_i)\). Forgetting labels and dividing by their corresponding multiplicities gives the joint multiset deck of component masses and root counts.

## Lift to the narrow-band mass order

In the joint one-cut deck, an edge separates off a skeleton leaf precisely when one component has \(r=1\). For \(q\ge3\) there are exactly two such splits in the target, so any rival also has a path skeleton. For \(q=2\) this is automatic. Fix an integer \(C>\max m_v\). In the recovered joint deck replace each pair \((m,r)\) by \(m+Cr\). This is exactly the ordinary weighted cut polynomial with vertex weights \(m_v+C\), all in the narrow band \([C,2C-1]\). The narrow-band [Billera–Thomas–van Willigenburg](https://arxiv.org/abs/math/0405434) factor-reversal argument determines their order up to reversal: an inner factor with at least two parts and a nontrivial merge produces an oversized part from the two intact endpoint weights, so two nonsymmetric factors are impossible. Subtract \(C\) to recover the original mass word. Each rooted block is now determined by its mass and the certified affine arm count, proving full tree reconstruction.

This is a different arbitrary-width criterion from the [common-residue theorem](StanleyModularBlockCountPaths.md): no component count is encoded a priori by the mass congruence, and the recovery of that count instead uses low-degree cut coefficients. It does constrain the allowable rooted types, and it does not reconstruct arbitrary width with unrelated ornaments or unrestricted branching cores.
