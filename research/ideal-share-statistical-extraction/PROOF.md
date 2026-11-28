# Statistical privacy and equal alphabets

## 1. Model and result

Let \({\cal M}\) be a set of size \(q\ge2\), \({\cal K}\) a finite dealer key set and \({\cal C}\) a nonempty class of distributions on \({\cal K}\), fixed independently of the secret. A deterministic sharing map assigns shares \(S_j(m,k)\). Any \(t\) shares reconstruct \(m\) exactly for all \(m,k\), with \(2\le t\le n\). For each **one** \(P\in{\cal C}\), \(K\sim P\), all unauthorized subsets \(J\) with \(|J|<t\), and every \(m,m'\), suppose
\[
  {\rm TV}\bigl(S_J(m,K),S_J(m',K)\bigr)\le\varepsilon.              \tag{1}
\]
There is no other dealer randomness. The quantifier in (1) is within the same allowed source at both messages. Here TV is one-half the \(\ell_1\) distance of probability mass functions.

Suppose party \(j\) has a share alphabet of size at most \(q\), embedded in a fixed \(q\)-point set \(\mathcal Y\). For any one fixed message \(m_0\), the same deterministic map \(k\mapsto S_j(m_0,k)\) works for all \(P\in{\cal C}\):
\[
 \sup_{P\in{\cal C}} {\rm TV}\bigl(S_j(m_0,K),U_{\mathcal Y}\bigr)
 \le 2(1-1/q)\varepsilon.                                         \tag{2}
\]
The bound may be capped at \(1-1/q\). For \(q=2^b\) a fixed bijection with bit strings gives a \(b\)-bit extractor. In particular if \(\varepsilon=0\) the full output is exactly uniform, as already follows from the standard ideal-share argument. We show in Section 3 that the constant in (2) is necessary even for the best arbitrary deterministic \(q\)-output extractor, in the stated small-error range.

## 2. Proof of the upper bound

Fix an allowed source \(P\). Introduce an independent uniform message \(M\) and choose a set \(J\) of \(t-1\) parties excluding \(j\). Write \(Z=S_J(M,K)\) and \(Y=S_j(M,K)\). If \(\mu_m\) is the conditional law of \(Z\) given \(M=m\), and \(\bar\mu=q^{-1}\sum_m\mu_m\), then
\[
\begin{split}
 \mathbb E_Z {\rm TV}({\cal L}(M\mid Z),U_{\cal M})
 &= {\rm TV}({\cal L}(M,Z),U_{\cal M}\otimes\bar\mu)\\
 &= q^{-1}\sum_m{\rm TV}(\mu_m,\bar\mu)
 \ \le (1-1/q)\varepsilon.                                      \tag{3}
\end{split}
\]
For the last step average the pairwise bounds (1) with one zero term for \(m'=m\). Conditioning only uses \(Z\) values of positive probability.

For each fixed \(Z=z\), the authorized decoder assigns every possible \(y\) to at most one correct \(m\); fill in unused pairs arbitrarily. With conditional masses \(p_y=\Pr[Y=y\mid z]\), each decoder group \(G_m\subseteq\mathcal Y\) has sum \(p_m=\Pr[M=m\mid z]\). For any nonnegative \(p_y\) and each group (including empty),
\[
 \sum_{y\in G_m}(p_y-1/q)_+\ \le\ \left(\sum_{y\in G_m}p_y-1/q\right)_+.
\]
If the left is nonzero, all of its positive terms together subtract at least \(1/q\); otherwise this is immediate. Summing over \(m\) gives \({\rm TV}({\cal L}(Y\mid z),U_{\mathcal Y})\le{\rm TV}({\cal L}(M\mid z),U_{\cal M})\). Average over \(z\) and use convexity of TV plus (3). Finally, singleton privacy holds since \(t\ge2\). If \(\nu_m\) is the law of \(S_j(m,K)\), the same pairwise averaging shows \({\rm TV}(\nu_{m_0},q^{-1}\sum_m\nu_m)\le(1-1/q)\varepsilon\). Triangle inequality yields (2) uniformly for every \(P\). No privacy hypothesis is applied to the authorized tuple \((Z,Y)\).

## 3. A source class with exact minimax error

Let \(G\) be a finite abelian group of order \(q\) (use \(\mathbb F_2^b\) when the messages are \(b\) bits), and take the dealer set \({\cal K}=G^G\). A key is an entire tuple \(x=(x_m)_{m\in G}\). To share message \(m\), give the first party \(x_m\) and the second party \(x_m+m\). Subtraction gives exact reconstruction for every key. For any \(P\) on the key set, write \(P_m\) for the marginal of \(X_m\) and \(\tau_m P_m\) for its translate by \(m\). Define \({\cal C}_\varepsilon\) to be **one fixed class**: all joint distributions \(P\) for which both families \((P_m)_m\) and \((\tau_m P_m)_m\) have pairwise TV distance at most \(\varepsilon\). This is precisely (1) for the two nontrivial unauthorized coalitions; the empty view is automatic. No independence or flatness of the key coordinates is required. In particular every coupling of uniform marginals is in the class.

A permutation of any one coordinate is a candidate \(q\)-output extractor and can reach error \(2(1-1/q)\varepsilon\). To see this for coordinate \(m_0\), pick \(a\in G\) and take a product law on the key having marginals
\[
 P_m=(1-2\varepsilon)U_G+\varepsilon\,\delta_a+
                \varepsilon\,\delta_{a+m_0-m}                   \tag{4}
\]
for \(0\le\varepsilon\le1/2\). For the first family only the last point varies with \(m\); after translating by \(m\), only the first point varies. Both families have distances at most \(\varepsilon\), so this law is admissible for **all** messages at once. At \(m=m_0\) the two points coincide and the error is the claimed number. Relabeling the output by a permutation leaves the error unchanged.

It remains to exclude every other extractor. This matters because an arbitrary map may look at all coordinates of the key, unlike a fixed share. For a map \(F:G^G\to[q]\), let \(h_a(x)=\mathbf1_{\{F(x)=a\}}\) be each color indicator. Consider a four-corner rectangle obtained by varying two different coordinates of \(x\) over two values each, with every other coordinate fixed. If the alternating corner difference of some \(h_a\) is nonzero, construct two different uniform-marginal couplings as follows. Place mass \(w=1/(4q)\) on each of its four corners. At every coordinate each allocated marginal atom is at most \(1/q\); the remaining required marginal measures \(U_G\) minus the allocated masses are nonnegative and all have mass \(r=1-1/q\). Add \(r\) times the product of these remaining marginals after normalization by \(r\); this completes a coupling with uniform marginals. Now add or subtract the signed measure \(w(\delta_{00}+\delta_{11}-\delta_{01}-\delta_{10})\) on the rectangle. Both resulting laws are nonnegative, have the same uniform marginals, and are in \({\cal C}_\varepsilon\). Their probabilities of the event \(F=a\) differ by at least \(2w\), so on one of them the output's TV from uniform is at least \(w\).

If every mixed corner difference of \(h_a\) is zero, then \(h_a\) is a sum of a constant and single-coordinate functions. Indeed, the change upon changing one coordinate is independent of each other coordinate, by the corresponding rectangle identity. Changing coordinates one at a time from a fixed base point gives the additive representation. A Boolean-valued additive function has at most one nonconstant summand: varying two nonconstant summands gives values \(c,c+d,c+e,c+d+e\) with \(d,e\ne0\); these include at least three distinct real numbers. Thus each nonconstant color indicator depends on a single coordinate. If two such indicators depended on different coordinates, there would be a key on which both took value 1, contrary to disjointness of different colors. They therefore all use the same coordinate. A constant output or a missing color already incurs at least \(1/q\) error under the product of uniform marginals. Otherwise a one-coordinate map from \(q\) symbols onto \(q\) colors must be a permutation.

We have proved the following dichotomy: either \(F\) is a coordinate permutation, or its worst-case error even on uniform-marginal couplings is at least \(1/(4q)\). If \(0\le\varepsilon\le1/[8(q-1)]\), then \(2(1-1/q)\varepsilon\le1/(4q)\). The general upper bound and the two lower cases give the exact minimax equality
\[
  \min_{F:G^G\to[q]}\
  \sup_{P\in{\cal C}_\varepsilon}{\rm TV}({\cal L}_P(F(K)),U_{[q]})
       =2(1-1/q)\varepsilon.                                    \tag{5}
\]
This proves sharpness of the universal constant with \(t=n=2\). It does not assert this exact curve when the error is larger, or sharpness separately for every \(t,n\). For \(q=2\) the result is a one-bit optimum; for \(q>2\) the lower bound is for full \(q\)-symbol output, not for projected shorter output.

## 4. Limits of the comparison

The lower bound is a finite worst-class construction, not an efficiency claim: its key universe has \(q^q\) points and the class is not restricted to flat sources. Thus this example is not a separation with short dealer keys in the long-secret sense of Bosley–Dodis. The upper bound requires the equal-alphabet assumption; absent that hypothesis, producing a distribution with each atom at most \(1/q\) at perfect privacy does not force a full \(q\)-symbol output to be uniform. This is consistent with existing tagged constructions using larger alphabets. With only ordinary subset privacy, no inference is made about local leakage, non-malleability, or any actual implementation.
