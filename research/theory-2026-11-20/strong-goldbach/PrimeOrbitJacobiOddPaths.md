# Quadratic reciprocity on odd-multiplicity paths

At an even \(N>2\), use vertices the odd primes \(x<N-1\) coprime to \(N\). A full factor edge \(x\to y\) means \(y\mid N-x\); keep it in the **odd graph** exactly when \(v_y(N-x)\) is odd. This is a loopless graph; omitting factors with even multiplicity does not require them to be small or internal. A genuine endpoint is a vertex \(x\) with \(N-x\) prime. A square complement need not be prime and has no odd edge.

### 1. An all-center parity-cycle theorem in one residue class

Suppose \(N\equiv2\bmod4\). From any unit seed \(p\equiv3\bmod4\), at least one of the following is reachable by odd edges:

1. a genuine prime endpoint;
2. two vertex-disjoint directed simple cycles, with composite complements on all their vertices;
3. a directed simple cycle of even length, with composite complements on its vertices.

In alternatives 2 and 3 the paths to the cycles need not be disjoint. The even cycle need not be closed, have only one odd successor per row, or contain the seed. This does not assert a Goldbach representation at every center.

In fact take any vertex set closed under all odd edges and its adjacency matrix \(A\) over \(\mathbb F_2\), with rows indexed by **inputs**. Let \(\epsilon_x=1\) if \(x\equiv3\bmod4\), else zero, and \((-1)^{\lambda_x}=(N/x)\) (Legendre symbol at the actual prime \(x\)). One has, for \(B=I-A\),
\[
                            B\epsilon=0,\qquad B\lambda=\epsilon .
\]
Indeed \(N-x\equiv x\bmod4\) gives the first identity. Write \((N/x)=((N-x)/x)\), factor \(N-x\), and apply quadratic reciprocity separately to every prime \(y\mid N-x\). Here \(y\ne x\), both are units, and \((x/y)=(N/y)\). The reciprocity sign bit is
\(\epsilon_x\sum_y v_y(N-x)\epsilon_y=\epsilon_x^2=\epsilon_x\bmod2\).
The two identities require only odd-edge closure, not closure under all prime factors.

If \(\epsilon\ne0\), \(\lambda,\epsilon\) give a genuine generalized eigenvector chain of length two at zero for \(B\). Thus \(1\) has algebraic multiplicity at least two for \(A\); the conclusion would not follow merely from the existence of a seed of arbitrary residue. Also every \(3\bmod4\) vertex retains an odd number of \(3\bmod4\) successors, so some cycle through those residues is reachable, without implying it is the even cycle below.

Use the full odd-edge reachable set and stop if any endpoint occurs. If no two simple cycles are disjoint, the determinant permutation expansion on its \(s\) vertices gives
\[
        f(t)=\det(tI-A)=t^s-\sum_{\text{directed simple cycles }C}t^{s-|C|}
                    \quad\text{in }\mathbb F_2[t].
\]
A nonidentity contributing permutation consists of just one cycle with the other vertices fixed. Now \(f(1)=0\) gives an odd number of cycles, and \(f'(1)=0\) then gives an even number of odd-length cycles. There is an even-length one. This argument does not require numerical eigenvalues or a classification of the cycles.

### 2. No sole odd return to a fixed seed in a square class

Fix a squarefree integer \(d\ge1\), a finite set \(F\) of rational primes, \(\eta>0\), and an odd prime \(p\). Let \(N=d z^2\) be even with \(z\) a positive integer, \(p\nmid N\), and \(z_F=\prod_{l\in F}l^{v_l(z)}\ge z^{1/2+\eta}\). For all sufficiently large such centers and **every** prime divisor \(q\mid N-p\), the row \(N-q\) cannot equal \(p v^2\) with \(v>1\). The exception \(v=1\) is precisely the represented pair \(N=p+q\). The first edge may have any positive multiplicity, and we impose no restriction on the other prime factors of \(N-p\) or on the prime factors of \(v\). All centers supported on a fixed finite set are covered by taking the finite set of possible \(d\)'s.

Suppose otherwise. Since \(q\mid N-p\) and \(N=q+p v^2\), the prime \(q\ne p\) divides \(v^2-1\). Both \(q\) and \(v\) are odd, so \(v=mq+\sigma\) for \(m\ge1,\ \sigma\in\{\pm1\}\). In particular \(q\le v+1\ll z,\ v\asymp z\), and \(mq\ll z\). Constants may depend on the fixed \(p,d\). The number \(\sqrt{d/p}\) is irrational because \(p\nmid d\).

* If \(q\le\sqrt z\), then \(|v-\sqrt{d/p}\,z|\ll q/z\). Apply the two-dimensional [\(p\)-adic Subspace Theorem, Theorem 1.1](https://pub.math.leidenuniv.nl/~evertsejh/dio2011-padicsubspace.pdf) to \((v,z)\), with forms \((X-\sqrt{d/p}\,Y,Y)\) at infinity and the coordinate forms at \(F\). Their product is \(O(q/z_F)\ll z^{-\eta}\).
* If \(q>\sqrt z\), then \(m\ll\sqrt z\), and the exact equality \(mq=v-\sigma\) gives
  \[
             (2pmv+1)^2-4p m^2 N=1+4pm\sigma .
  \]
  The positive square roots on the left have sum \(\gg mz\), so
  \[
             |2pmv+1-2\sqrt{pd}\,m z|\ll 1/z .
  \]
  For \((X,Y)=(2pmv+1,mz)\), use \((X-2\sqrt{pd}\,Y,Y)\) at infinity and the coordinate forms at \(F\). The product is \(O(m/z_F)\ll z^{-\eta}\), since the finite-place \(Y\)-product is at most \(1/z_F\).

In either case reducing to the primitive integer vector cannot increase the product: division by the common gcd \(g\) multiplies it by \((g_F/g)^2\le1\). The primitive sup norm is \(O(z^2)\), so a fixed negative height power applies. The finite exceptional rational lines give only finitely many slopes, including if primitive heights stay bounded. But the slopes converge to the respective irrational numbers \(\sqrt{d/p}\) and \(2\sqrt{pd}\). This rules out an infinite sequence. We make no claim when \(d,p\) vary freely or the smooth-part threshold fails.

For an intersection with section 1, suppose also that \(N\equiv2\bmod4,\ p\equiv3\bmod4\). There is an odd successor \(q\equiv3\bmod4\). Its row cannot be square, since \(N-q\equiv3\bmod4\). Thus either a pair is reached, or there is a second odd step \(q\to r\) with \(r\notin\{p,q\}\). Indeed its whole odd support cannot be the single vertex \(p\) by the theorem. A stronger, explicitly **unary** consequence is that the full odd orbit from \(p\) cannot consist of at most three nonendpoint vertices if every row in it has precisely one odd successor. Along a unary path \(\epsilon\) stays one and \(\lambda\) toggles, so its terminal simple cycle has even length, here necessarily two. If \(p\) belongs to the cycle the theorem already rules it out. Otherwise \(p\to a\to b\to a\); write \(N-p=a u^2,\ N-b=a w^2,\ N-a=b v^2\). As above \(w\equiv\pm1\bmod b\) and \(w>1\), hence \(w\ge b-1\). If \(p<b\), then \(u>w\) and
\[
              b-p=a(u^2-w^2)\ge a(2w+1)>b,
\]
impossible. If \(b<p\), there are only finitely many possibilities for \(b\); fix each as seed and apply section 2 to its actual edge to \(a\) followed by \(N-a=b v^2\). No assertion is made here about a three-vertex orbit with branching.

**Checks and scope.** [The control](check_jacobi_odd_paths.py) factors every physical row in a finite range, checks both parity identities without using one to compute the other, and checks the determinant argument independently on every loopless digraph on at most four vertices. At \(N=514\), starting from \(3\), the odd rows are \(3\to7,73;\ 7\to3;\ 73\to\varnothing\): an even cycle need not itself be unary or closed. At \(N=852\), the rows \(852-5=7\cdot11^2\) and \(852-7=5\cdot13^2\) really form a closed odd pair at a represented center (\(13+839=852\)); this is not an unrestricted prohibition. The finite checks illustrate, not prove, the asymptotic theorem.

The full graph is due to [Bożek](https://arxiv.org/abs/1909.09900). The [earlier signed-order route](PrimeOrbitOutwardAllCenters.md) follows contributions of large multiplicative order and allows arbitrary edge valuations; that is different from the Jacobi chain in the odd graph. A targeted search for quadratic-reciprocity colorings of Bożek's graph did not yield a verified duplicate. [Kelanemer's nearby 2026 record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) was inaccessible in full; no priority or completeness claim is intended.