# All regular spiders are 0-rotatable

A graceful labeling of an \(m\)-edge tree uses all vertex labels \(0,\ldots,m\), with all edge differences \(1,\ldots,m\). A tree is **0-rotatable** if each individual vertex can be prescribed to receive 0 in some graceful labeling.

**Theorem.** For every \(k,\ell\ge1\), the tree \(T(k,\ell)\) obtained by identifying one endpoint of \(k\) paths of length \(\ell\) is 0-rotatable.

This proves the regular-spider conjecture stated in the introduction of [Rofa, arXiv:2611.29448v1](https://arxiv.org/abs/2611.29448v1), which had established the case \(\ell=4\). It does not prove 0-rotatability of spiders with arbitrary unequal legs, of arbitrary rooted symmetric trees, or the Graceful Tree Conjecture. Regular spiders were already known to be graceful; the result is the ability to prescribe the zero vertex at **any** depth.

The proof first gives a general label lift for copies of a tree joined at a leaf. Two small labelings, whose sizes are independent of the number of copies, give one gracefully labeled exceptional copy preserving prescribed small or large labels, and as many other copies as desired.

## 1. A leaf-rooted bouquet lift

Let \(H\) be a tree with \(m\ge1\) edges, rooted at a leaf \(r\) with neighbor \(s\). Use its bipartition \(U\sqcup V\) with \(r\in U\), and write \(a=|U|-1\) and \(b=|V|\), so \(m=a+b\). Suppose the following two labelings are given:

1. An \(\alpha\)-labeling \(f\) of \(H\) whose low side is \(U\). Thus \(f(U)=[0,a]\) and \(f(V)=[a+1,m]\).
2. A graceful labeling \(g\) of \(H-r\), translated to the interval \([1-b,a]\) of its \(m\) vertex labels, with the single matching condition \(g(s)=f(r)\). Translation does not change its edge differences \(1,\ldots,m-1\).

Let \(H^{[k]}\) be obtained from \(k\) copies of \(H\) by identifying their copies of \(r\), and put \(q=km\). Let \(c=f(r)\). For the common root use \(c\), and on copy 1 keep \(f\) on \(U\), adding \(q-m\) to the labels on \(V\). For each copy \(i=2,\ldots,k\), assign
\[
 F_i(v)=
 \begin{cases}
      g(v)+m(i-1), & v\in U\setminus\{r\},\\
      g(v)+m(k-i+1), & v\in V .
 \end{cases}                                                   \tag{1}
\]

**Vertex bijectivity.** Copy 1 occupies \([0,a]\) and \([q-b+1,q]\). For every fixed \(v\ne r\), as \(i\) runs from \(2\) to \(k\), the shift in (1) runs once through \(m,2m,\ldots,(k-1)m\), in one order or the other. The translated intervals \([1-b,a]+mj\), \(1\le j\le k-1\), are adjacent and disjoint, and their union is exactly \([a+1,q-b]\). The case \(k=1\) has no ordinary copies.

**Edge bijectivity.** On copy 1, every high label was translated by \(q-m\) and every low label preserved, so its edge differences are \(q-m+1,\ldots,q\). The edges incident to \(r\) in the other copies have differences \(m,2m,\ldots,(k-1)m\), by \(g(s)=c\).

For the other edges, orient \(uv\) from \(u\in U\) to \(v\in V\). Its differences on the ordinary copies are
\[
             |mt+e|,\qquad
 t\in\{k-2,k-4,\ldots,2-k\},\quad e=g(v)-g(u).
\]
The \(t\)-set is symmetric, so replacing \(e\) by \(|e|\) does not change the multiset. Each \(d=1,\ldots,m-1\) occurs once as \(|e|\). The values \(|mt+d|\) are distinct: matching signs imply \(t=t'\), \(d=d'\); opposite signs would give \(d+d'=m\) and \(t+t'=-1\), impossible since all \(t\)'s have the same parity. They are positive nonmultiples of \(m\) bounded by \(m(k-2)+(m-1)\). Counting \((k-1)(m-1)\) of them shows they are exactly the nonmultiples of \(m\) below \(q-m\). This completes the graceful labeling.

In particular, the lift preserves the label 0 whenever it occurs in the low side of the exceptional copy. It also sends a base label \(m\) in the high side to \(q\); complementing every label \(x\mapsto q-x\) then gives zero at that vertex. The same map preserves **all** specified low-side labels and shifts **all** specified high-side labels by the same amount, not merely one extreme. Unlike a shift of an entire graceful graph, the reserve is large enough to handle arbitrarily many copies because the normal-copy edge differences are indexed by parity and residue independently.

## 2. Specialization to paths

Take \(H=P_{\ell+1}\) rooted at its starting endpoint, so \(m=\ell\). Even-depth vertices form \(U\), with \(a=\lfloor\ell/2\rfloor\), and odd-depth vertices form \(V\), with \(b=\lceil\ell/2\rceil\).

We use two classical path results:
* Every path has a graceful labeling giving its first endpoint any prescribed label. Equivalently, a graceful permutation of \([0,n-1]\) may start with any element. This is the one-endpoint theorem of Flandrin–Fournier–Germa and Gvozdjak, also covered by [Cattell, *Graceful labellings of paths*](https://doi.org/10.1016/j.disc.2007.03.046); see the precise one-endpoint formulation in [Ollis–Willmott, Lemma 1](https://ajc.maths.uq.edu.au/pdf/51/ajc_v51_p243.pdf). No prescribed **pair** of endpoints is needed.
* By [Cattell's Corollary 1](https://doi.org/10.1016/j.disc.2007.03.046), a path has an \(\alpha\)-labeling giving 0 to any specified vertex, except the middle vertex of \(P_5\). See also the same formulation in [Shan–Zhong, Lemma 2(b)](https://arxiv.org/pdf/2605.14295).

To place 0 at any even depth other than the exception, use the second result to get \(f\) having 0 at that depth. Its low side must be \(U\). To place 0 at an odd depth, use that result at the odd vertex and **complement the path labeling before lifting**. Then \(U\) is the low side and the odd vertex is labeled \(\ell\). After the lift, complement the whole spider to send \(q\) at that vertex to 0.

In either case \(c=f(r)\in[0,a]\). The first result makes \(g\) possible: take a graceful permutation on \([0,\ell-1]\) starting at \(c+b-1\), then subtract \(b-1\) throughout. Its first vertex is \(s\), the neighbor of the common root. Thus the hypotheses of Section 1 hold. Any leg at the prescribed depth can be chosen as the exceptional one.

### The sole exception \(\ell=4\), depth 2

For \(k\ge2\) use [Rofa, Case 2](https://arxiv.org/pdf/2611.29448v1). For a direct comparison, start from the Section 1 lift with path \(f=(2,3,1,4,0)\) and \(g=(2,-1,1,0)\), and keep the root label 2. The first two legs together use labels \(\{0,1,3,4,q-3,q-2,q-1,q\}\) away from the root and all eight differences \(q-7,\ldots,q\): the first leg supplies the top four, and the second supplies \(q-4,q-5,q-6,q-7\). Replace these two leg sequences, not including the root, by
\[
                  (q-2,0,q,1),\qquad(q-1,4,q-3,3).
\]
They use the same eight labels and differences, and now 0 is at depth 2. This is Rofa's two-leg rearrangement. For \(k=1\) the path sequence \((1,4,0,2,3)\) gives differences \(3,4,2,1\) and fixes the middle zero. The path sequence printed for \(k=1\) in Rofa v1 instead repeats difference 3; this replacement repairs that base case without changing the \(k\ge2\) result.

This completes every depth for every \(k,\ell\).

## 3. Exact checks and relation to prior work

For length five the following witness seeds yield all nontrivial depths directly; complement the lifted labeling where the marked seed label is 5. Depths 0 and 1 use the usual alternating-extreme path seed.

| Depth | Exceptional path seed \(f\) | Normal tail seed \(g\) | Marked label before lifting |
|---|---|---|---|
| 2 | \((1,5,0,3,2,4)\) | \((1,0,-2,2,-1)\) | 0 |
| 3 | \((1,3,2,5,0,4)\) | \((1,0,-2,2,-1)\) | 5 |
| 4 | \((1,3,2,5,0,4)\) | \((1,0,-2,2,-1)\) | 0 |
| 5 | \((2,3,1,4,0,5)\) | \((2,-2,1,-1,0)\) | 5 |

The companion [exact checker](verify_factor_graceful_spider_bouquet.py) independently searches for the path seeds for all depths through leg length 16, checks the lift at several even and odd copy counts, and checks the full residue partition over a wider range. It also checks the branched instance \(H=K_{1,4}\) rooted at a leaf, illustrating that the copy lemma does not require \(H\) to be a path. These checks are not a formalization of Cattell's theorem or of the full proof.

[Bahls–Lake–Wertheim](https://msp.org/involve/2010/3-3/involve-v3-n3-p01-p.pdf) prove gracefulness when spider leg lengths differ by at most one, and construct special graceful labelings of equal-leg spiders. [Rofa's earlier work](https://arxiv.org/abs/2312.16235) handles 0-rotatability for regular spiders of leg length at most three and asks about all spiders and more general symmetric trees. The \(k\)-independent seeds and residue partition above lift the specified extreme at any path depth; the conclusion is uniform in the arbitrary equal leg length, and not merely at the central root.
