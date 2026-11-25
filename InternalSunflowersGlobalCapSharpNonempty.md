# Sharp global-cap nonempty internal sunflower extraction; one injective projection does not suffice

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

For \(H\) a finite simple 3-uniform family, call \(F\subseteq H\) nonempty-internally valid if each nonempty intersection of two distinct triples in \(F\) is the common kernel of an \(m\)-petal sunflower contained in \(F\). If all pair codegrees of \(H\) are at most \(D\), \(1\le D\le m\), the sharp uniform retention proportion for nonempty internal witnessing is
\[
\Theta(m^{-3/2}/D).
\]
The upper examples are tripartite, have injective \(AB\) projection, and every \(A\)-vertex sees fewer than \(m\) distinct \(C\) labels. In particular the previously proposed sufficient \(\Omega(m^{-2})\) nonempty estimate for AB-injective triples is false even within the one-sided low-diversity class and with globally capped pairs: take \(D=m\). This does not disprove the unrestricted \(\Omega(m^{-3})\) full question of [Janzer–Jin–Sudakov–Wu, §6](https://link.springer.com/article/10.1007/s00493-026-00222-1#Sec6), explicitly about internal rather than ambient witnesses.

## Lower bound

Use the conflict graph on triples, joining triples with a repeated pair. It has maximum degree at most \(3(D-1)\), so a greedy coloring gives a linear class of size at least \(|H|/(3D-2)\). Apply the established [linear nonempty extraction theorem](LinearTripleInternalSunflowers.md) to that class to retain an additional \(\Omega(m^{-3/2})\). This is the global-cap lower bound already noted in the workbench's [GlobalPairCap note](InternalSunflowersGlobalPairCap.md). The matching upper bound below lifts the random obstruction from the [two-injective theorem](https://github.com/mxym/math/blob/ed2d8f37c98e60ac70be85ac0275566e11bb4c3b/research/euclidean-tensor-geometry/TwoInjectiveInternalSunflowers.md), using a different private-label allocation that allows repeated AC pairs.

## A sparse projected graph

It suffices to construct examples for all sufficiently large \(m\), uniformly in \(D\), since a larger universal constant covers finitely many small \(m\) (take a singleton host there). Put \(u=m-1\), \(t=\min(D,u)\), \(n=m^8\), \(d=\lfloor m^{3/2}/100\rfloor\), and \(M=\lceil8nd/u\rceil\). Take a random simple bipartite graph \(G\) on \(B,C\), each of size \(n\), with independent probability \(d/n\). With probability \(1-o(1)\), \(nd/2\le e(G)\le2nd\) and the maximum degree is at most \(2d\), by binomial tail bounds and \(d/\log n\to\infty\).

The following property also holds with probability \(1-o(1)\):
\[
e_G(X,Y)\le m(|X|+|Y|)/4\qquad
(X\subseteq B,\ Y\subseteq C,\ |X|,|Y|\le M/m).
\]
For nonempty \(X,Y\) of sizes \(x,y\), the mean is bounded by \((d/n)xy\le dM(x+y)/(2nm)\le m(x+y)/256\) for sufficiently large \(m\); the last inequality follows from \(M=\lceil8nd/u\rceil\) and \(d^2\le m^3/10^4\). The binomial upper-tail bound at \(k=\lceil m(x+y)/4\rceil\) is at most \((e/64)^k\le2^{-m(x+y)/4}\). At most \(n^{x+y}\) pairs of subsets have these sizes, and the sum over positive sizes tends to zero since \(\log_2 n=o(m)\). Empty sets need no bound. Fix a graph satisfying all properties.

## Chunking and assigning private labels

Replace each projected edge \(bc\) by \(t\) distinguished copies, with copy indices \(1,\ldots,t\). For each fixed \(c\) and each copy layer independently, partition its list of \(B\)-neighbors into nonempty chunks of size at most \(t\). Thus a chunk is a bunch of edge occurrences within one color \(c\), using distinct \(B\)-vertices. The number \(N\) of chunks satisfies
\[
N\le \sum_c t\left\lceil \deg_G(c)/t\right\rceil\le e(G)+nt\le 3nd
\]
for sufficiently large \(m\), uniformly in \(D\) since \(t\le m-1\) and \(d\ge m-1\) eventually.

On the chunks construct the simple conflict graph in which they conflict if they have the same \(c\) label or meet the same \(B\)-vertex. For each chunk, the first type contributes at most \(t\lceil\deg_G(c)/t\rceil\le2d+t\). Each of its at most \(t\) \(B\)-vertices lies in at most \(t\deg_G(b)\le2td\) chunks, so the second type contributes at most \(2t^2d\). Greedy coloring needs at most \(2d+t+2t^2d+1\) classes. Break each class into batches of at most \(u\) chunks and assign a new private \(A\)-vertex \(a\) to each batch. The total number is at most \(N/u+2d+t+2t^2d+1\le M\) for sufficiently large \(m\) because the second term is \(O(m^{7/2})=o(nd/u)\).

For every occurrence of an edge \(bc\) in a batch, introduce the triple \((a,b,c)\). Chunks in a batch have different \(C\)-labels and use pairwise disjoint sets of \(B\)-vertices; within a chunk its \(B\)-vertices are distinct. Therefore \(AB\) is injective, each \(AC\) pair has codegree at most \(t\), and each \(BC\) pair of \(G\) has exactly \(t\) distinct \(A\)-completions (two copies could not be in the same batch). The family is simple and has exactly \(te(G)\) edges. Each \(A\)-vertex sees at most \(u=m-1\) distinct \(C\)-labels.

## Bound every valid output

Let \(F\) be nonempty-internally valid. Every host pair has codegree at most \(t<m\), so no pair can repeat in \(F\); otherwise a witness for that pair would require \(m\) distinct triples containing it. Thus \(F\) is linear. No \(A\)-vertex can occur twice, because linearity would create singleton kernel \(\{a\}\), whose \(m\) petals need \(m\) different \(C\)-labels, impossible in the host. Consequently \(s=|F|\le |A|\le M\). In \(B\) and in \(C\) every vertex of degree at least two has degree at least \(m\), again by its singleton kernel. Set \(X,Y\) to be those high vertices in \(B,C\), so \(|X|,|Y|\le s/m\le M/m\). Edges of \(F\) meeting both \(X,Y\) are at most \(e_G(X,Y)\le m(|X|+|Y|)/4\le s/2\), since \(BC\) is injective *in \(F\)*. All other edges meet a vertex of degree one in \(B\cup C\), hence number at most \(2n\). It follows \(s\le4n\). Meanwhile \(te(G)\ge ndt/2=\Omega(nm^{3/2}D)\) uniformly since \(t\ge D/2\). This proves the upper bound. In particular at \(D=m\) the ratio is \(O(m^{-5/2})\), invalidating the stronger sufficient route rather than the original full-scope target.
