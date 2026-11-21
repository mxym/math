# Small binary dependencies and disjoint odd-factor paths at every center

At an even center \(N>2\) the vertices are the odd unit primes \(x<N-1\). Write \(A_{xy}=v_y(N-x)\bmod2\) over \(\mathbb F_2\) (the full **odd graph**); \(B=I-A\) with input rows. Loops are absent because \(x\nmid N\). A genuine endpoint has \(N-x\) prime. All statements about the parity graph allow arbitrary factors of even multiplicity, including primes not in the chosen set. No bound on the size of the full graph is assumed.

**Parity support theorem.** If \(c^\top B=0\) is a nonzero vector, let \(s\) be its support size and \(M\) the largest supporting label. Size one is impossible. At every sufficiently large center, for \(s\ge3\) one has the absolute bound
\[
              \log\log N\ \ll\ s^4\{\log(2s)+s\log(2M)\}.              \tag{1}
\]
At \(N=d z^2\) with \(d\ge1\) fixed squarefree this holds for **all** \(s\ge2\), with \(\log(2dM)\) instead of \(\log(2M)\). These are bounds for actual binary dependencies; an arbitrary simple cycle with additional odd exits need not give such a vector. A closed unary cycle does.

Put \(L=\log\log N\) and \(Y=c_0 L^{1/5}(\log L)^{4/5}\) for a sufficiently small absolute \(c_0>0\). Consider all input rows with labels at most \(Y\), retaining the columns at **all** vertices. Their left defect is at most one, and if nonzero its only nontrivial dependency is a two-label word \(\{p,q\}\). This pair is mutual in the actual graph, and has the same odd successors outside the pair in its two rows. In each of the following cases the left defect is **zero** throughout for sufficiently large \(N\):

* \(N=d z^2\) with \(d\) fixed (no smoothness assumption);
* \(N\) has a prime-power divisor \(P>8\sqrt{NY}\), with freely varying base.

More precisely, a pair dependency always requires a coprime factorization \(N/2=D_+D_-\) with **both** factors \(\gg\sqrt{N/(p+q)}\). In general the pair alternative cannot be removed: even for a fixed pair \(p=3,q=7\), there are infinitely many centers in the \(2\bmod4\) class at which the pair is genuinely closed in the odd graph with both complementary rows composite.

### Proof of the support and pair bounds

Let \(S\) be the support of \(c\). Componentwise parity of exponents, in the full integer factorizations, gives exactly
\[
                    \prod_{x\in S}(N-x)=b\,u^2,\qquad b=\prod_{x\in S}x       \tag{2}
\]
for a positive integer \(u\). For size one the supporting prime would divide \(N\), impossible. For \(s\ge3\), use \(f(T)=\prod_{x\in S}(T-x)\) in (2), with \(T=N\). It has \(r=s\) distinct simple roots and multiplicative coefficient height \(H(f)\le(1+M)^s\). For square-class centers instead use \(f(T)=\prod_{x\in S}(dT^2-x)\), \(T=z\). This has \(r=2s\) distinct simple roots with \(H(f)\le(d+M)^s\). Both are integer-polynomial problems \(f(T)=b u^2\). [Bérczes–Bugeaud–Győry–Mello–Ostafe–Sha, Theorem 2.1(i), (2.8)](https://arxiv.org/pdf/2310.09704) applies over \(\mathbb Q\) with just the archimedean place: \(r\ge3\), all LeVeque indices equal 2, \(Q_S=|D_K|=1\), \(N_S(b)=b\). The radical polynomial \(f^*\) is \(f\). In particular
\[
 \log h(T)\le 80r^4\log(16r^3)+50r^4\log H(f)+16r^3\log b,
\]
where \(h(T)=\log|T|\) for positive integers \(T>1\). This proves (1), using \(\log b\le s\log M\); for each fixed \(d\), \(\log\log z=\log\log N+O(1)\) eventually. This argument is uniform in the moving roots and their number. In particular a closed unary odd cycle on labels at most \(M\) has length \(\gg (\log\log N/\log(2M))^{1/5}\) apart from an unrestricted-center pair, with the stated square-class variant.

For \(M\le Y\) we have \(s\le\pi(Y)\ll Y/\log Y\), so the right-hand side of (1) is \(O(Y^5/(\log Y)^4)\), less than \(L\) for sufficiently small \(c_0\). In the fixed-square-class case one can first take \(Y>d\), so the same constant works with a threshold depending on \(d\). Every nonzero word in the indicated small-label space is therefore a pair except where all are excluded. For a pair \(\{p,q\}\), the \(p,q\) columns of its row dependency give odd mutual arcs, and every other column gives equality of the two outgoing parities. Two disjoint pair words would sum to weight four, already excluded. Two intersecting pair words would by addition give all three pair words on their three labels. Their largest label would divide \(N-x\) for both smaller labels \(x\), hence divide their positive difference smaller than itself. This is impossible. Thus the defect is at most one.

For such a pair the neglected square factors in (2) matter: \(u^2=(N-p)(N-q)/(pq)\), so \(u^2\equiv1\bmod N\), since \(pq\) is a unit modulo \(N\). Whenever \(D\mid N,\ u\equiv\sigma\bmod D,\ \sigma\in\{1,-1\}\), put \(E=N/D,\ j=(u-\sigma)/D\). Then
\[
 \frac{\sqrt{pq}\,u}{N}=\sqrt{(1-p/N)(1-q/N)},\qquad
 \left|\frac{\sqrt{pq}\,j}{E}-1\right|\le\frac{p+q+\sqrt{pq}}{N}.
\]
The second bound uses \(1-\sqrt{(1-a)(1-b)}\le a+b\) for \(0\le a,b\le1\). As \(p+q<2N\), multiplying by the bounded conjugate factor gives
\[
           1\le |pq\,j^2-E^2|\le 8(p+q)E^2/N.                       \tag{3}
\]
Nonvanishing uses distinct primes \(p,q\) and \(E>0\). Each odd prime power exactly dividing \(N\) has one sign for \(u\). For \(2^a\parallel N\), the two even neighbors \(u-1,u+1\) have gcd 2; thus one sign holds mod \(2^{a-1}\) (also vacuous at \(a=1\)). Allocate the odd prime powers and this reduced 2-part to their signs, giving coprime \(D_+,D_-\) with product \(N/2\). Applying (3) to each bounds the other one below by \(\sqrt{N/(8(p+q))}/2\). An odd prime-power divisor \(P\) of \(N\) can itself be used as \(D\); for a 2-power \(P\ge2\) use \(P/2\). Hence any \(P>8\sqrt{NY}\) precludes the pair.

For the unrestricted sharp distinction, fix any different odd primes \(p,q\). Start \(u=v=1\) in \(q u^2-p v^2=q-p\). Take any nontrivial positive Pell unit \(a+b\sqrt{pq}\) of norm one, passing to an even power that is \(1\bmod 2\) in the integral basis \(1,\sqrt{pq}\) if necessary (equivalently take a power in the finite unit group modulo 2 of the order \(\mathbb Z[\sqrt{pq}]\)). Repeatedly replace
\[
             (u,v)\longmapsto (au+pbv,\;qbu+av).
\]
The equation and oddness are preserved; the two values grow. The distinct even centers \(N=p+q u^2=q+p v^2\) have both \(p,q\) as units: reduction of the conic mod \(p,q\) gives \(u^2=1\bmod p,\ v^2=1\bmod q\). For every positive step both rows are composite, with the other vertex as their **only odd** successor. For \(p=3,q=7,\ (a,b)=(55,12)\), the first composite center is \(57970\) with \(u=91,v=139\). This does not say that these larger centers lack a Goldbach pair elsewhere.

### Consequence: disjoint paths from independent quadratic classes

Let \(G=(\mathbb Z/2N\mathbb Z)^\times/\langle N-1\rangle\) and use its vector quotient \(G/2G\). Take any menu of small unit-prime seeds \(x\le Y\), of class rank \(t\) in this quotient. There are at least \(t-1\) vertex-disjoint odd-edge paths from distinct seeds to distinct targets, each target either a genuine endpoint or a label \(>Y\). In either zero-defect case above there are at least \(t\) such paths. An endpoint seed may supply a length-zero path. Without the zero-defect condition, every wholly small closed odd orbit from a character-nontrivial seed (or any menu generating a nonzero class) contains the **same pair** if it has no endpoint; it cannot be wholly small at all in the zero-defect cases. For \(N\equiv2\bmod4\), the class of each unit seed \(3\bmod4\) is nontrivial by the character mod 4. More generally a character on small residues is always available: at \(v_2(N)=2\) use the character mod 8 with kernel \(1,3\); at \(8\mid N\) use the one with kernel \(1,7\). Only seeds on which the chosen character is nontrivial are covered by that single-character observation.

Indeed give the finite graph a vertex separator \(T\) between the seed set and the set of all endpoints and all vertices \(>Y\); deletions may include seeds or targets. Let \(U\) consist of the vertices reachable from the undeleted seeds after deleting \(T\). It contains no targets, all its labels are small, and every odd successor from \(U\) lies in \(U\cup T\). Every seed belongs there as well, including deleted seeds in \(T\). The matrix
\[
               [\,I-A_{U,U}\ \mid\ -A_{U,T}\,]
\]
has left nullity at most \(\delta\), where \(\delta=1\) in general and \(0\) in the zero-defect cases: any left relation extends by zeros to the full graph because all other columns vanish on these input rows. Thus its right nullity is at most \(|T|+\delta\). For any quadratic character of \(G\) the vector of its sign bits on \(U\cup T\) is in that right kernel: for each odd \(x\),
\[
                    N-x\equiv(N-1)x\bmod 2N,
\]
so \(\chi(N-x)=\chi(x)\). The character restrictions on the seed menu span dimension \(t\), by vector-space duality. Hence \(|T|\ge t-\delta\). The finite directed vertex form of Menger's theorem gives the claimed disjoint paths, allowing the usual splitting of vertices into capacity-one input/output copies. The closed-orbit version is the same left-rank bound on a square matrix: a nonzero right character restriction forces a nonzero left relation supported on it.

Rank need not be large for every \(N\). As a nonvacuous example \(N=10\cdot17^{2a}\) has fixed unit seeds \(11,13\) independent by the characters mod 4 and the Legendre character mod 5 (their sign pairs are \((-,+),(+,-)\)); both characters are trivial on \(N-1\). The two seeds are eventually small, and the theorem gives two vertex-disjoint paths at every sufficiently large such center. Leaving a growing seed range by odd multiplicities is **not** the same as reaching a prime; this is not a proof of binary Goldbach.

[Finite controls](check_small_odd_dependencies.py) verify exact pair signs, genuine Pell rows, a nonvacuous pair at \(852\), and the two-character seed fixture. The graph is [Bożek's factorization graph](https://arxiv.org/abs/1909.09900) with even valuations discarded. Compare the separate [odd Jacobi/cycle obstruction](PrimeOrbitJacobiOddPaths.md) and [full-order escape](PrimeOrbitOutwardAllCenters.md); the latter large-factor matching does not prescribe parity of the output edge. The height input is the cited general superelliptic theorem, not a new bound on ordinary Goldbach exceptional sets.