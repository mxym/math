# An explicit low-radius five-part strip for Borsuk's problem in dimension four

**Theorem.** A diameter-one subset of \(\mathbb R^4\) contained in a ball of squared radius \(15007/50000\) admits a partition into at most five sets of squared diameter at most \(999999/1000000\). No assumption on contact points is needed. Section 4 improves the endpoint to \(30027/100000\) at the same margin. The pieces are obtained from one rotated regular-simplex cone partition.

The [ProofAtlas research map](https://www.proofatlas.ai/collaboration/borsuk-problem-r4/) already records the closed \(3/10\) threshold and a nonexplicit strip above it. The contribution here is an explicit endpoint and margin, proved by localizing the extremal cone configurations and bounding their incidence on a circle. This is a partial result; the general upper bound of six and the unresolved choice between five and six are discussed in [Chalmers](https://arxiv.org/abs/2611.17375) and [Tolmachev](https://arxiv.org/abs/2611.16775).

## 1. Stability of the simplex cone angle

Take unit regular simplex vertices \(v_1,\ldots,v_5\). Assign each point to a maximizing \(\langle x,v_i\rangle\) (ties will be handled at the end). The closed cone for color \(i\) has as its generators the four rays \(-v_j\), \(j\ne i\). In fact, the four functionals \(v_i-v_j\) take value \(5/4\) on their respective generators and vanish on the other three. Write \(G\) for the four-column generator matrix; its Gram matrix is \((5I-\mathbf1\mathbf1^\top)/4\).

A unit direction in the cone is \(Gp/\|Gp\|\) with \(p\ge0\) and \(\sum p_i=1\). For the greatest possible negative inner product with another unit direction in the cone, project \(-Gp\) orthogonally onto the cone, obtaining \(Gr\). Orthogonality to \(Gr\) and the polar-cone inequality for the residual show that the maximum, if positive, is \(\lambda=\|Gr\|/\|Gp\|\). A zero projection admits no negative inner product.

Let \(J\) be the positive support of \(r\), with \(j=|J|\). The projection conditions give \(r_i=c-p_i\) on \(J\), \(p_i\ge c\) off \(J\), and \(c=(1-\sum_{J}p_i)/(5-j)\). Indeed, the residual inner products with the generators are \(\bigl[1+\sum r_i-5(p_i+r_i)\bigr]/4\); they vanish on \(J\) and are nonpositive off it. In particular \(c>0\), so \(1\le j\le3\). Put
\[
P=\sum_{J}p_i,\quad S=1-P,\quad a=P/S,\quad
u=\sum_{J}p_i^2/S^2,\quad v=\sum_{J^c}p_i^2/S^2,\quad z=5u-(1+a)^2 .
\]
The Gram formula gives \(4\|Gp\|^2/S^2=5v+z\) and \(4\|Gr\|^2/S^2=5/(5-j)+z\). The ratio \(\lambda^2\) increases in \(z\) and decreases in \(v\), since \(5v\ge5/(4-j)>5/(5-j)\) and the numerator is positive. Also
\[
v\ge \frac1{4-j},\qquad z\le -1+\left(\frac5{5-j}-2\right)a-a^2,
\]
the latter by \(p_i<c=S/(5-j)\) on \(J\). The denominators in these comparisons are positive: at the original \(z\) this follows already from the positive numerator and \(5/(4-j)>5/(5-j)\).

When \(j=1\), \(z\le-1\), giving \(\lambda^2\le3/8\); when \(j=3\), \(z\le-15/16\), giving \(\lambda^2\le5/13\). For \(j=2\) write \(D=v-1/2\) and \(A=a/3+a^2\). Then
\[
\lambda^2\le\frac{2/3-A}{3/2+5D-A}\le4/9.
\]
In particular the cone angle is at most \(\theta=\arccos(-2/3)\).

Set \(\varepsilon=21/20000\) and \(q_0=4/9-\varepsilon\). If two unit cone vectors have negative inner product with square at least \(q_0\), projecting the negative of either vector onto the cone must give support size \(j=2\). The inequality then gives
\[
(5/9+\varepsilon)A+5q_0D\le(3/2)\varepsilon,
\qquad P\le a<0.0086,\quad D<0.000711.
\]
Let \(p_*\) put mass \(1/2\) on each of the two indices outside \(J\). The squared difference on those two coordinates is \(S^2D+P^2/2\), and the contribution from \(J\) is at most \(P^2\). Thus \(\|p-p_*\|^2\le D+3P^2/2\). Also \(\|Gp_*\|^2=3/8\) and \(\|Gp\|^2\ge[5(1-P)^2/2-1]/4\). The two norms exceed \(0.612\) and \(0.603\), respectively. For nonzero vectors \(b,b'\), the normalized squared chord is \((\|b-b'\|^2-(\|b\|-\|b'\|)^2)/(\|b\|\|b'\|)\). Applying this to \(Gp,Gp_*\), the squared chord is bounded by
\[
\frac{(5/4)(0.000711+(3/2)\,0.0086^2)}{0.603\cdot0.612}
<
(0.0535-0.0535^3/24)^2
\le \bigl(2\sin(0.0535/2)\bigr)^2.
\]
Each direction is therefore within angle \(0.0535\) of a normalized two-ray sum. The inner products of two reference sums are \(1,1/6,-2/3\) according as the associated two-element sets coincide, overlap once, or are disjoint. The original inner product is less than \(-0.66\) and its change under replacement is less than \(2(0.0535)\), so the references are disjoint. Each cone has three such unordered pairs, giving 15 in total.

## 2. A phase-exclusion bound

Let \(H'\) be a closed set of directions of angular diameter at most \(\theta+e\) in a unit sphere of dimension at least one. Consider a fixed ordered reference pair of angle \(\theta\), with \(0<\theta<\pi\). Its Haar-random rotation can be sampled by first choosing a Haar rotation and then composing on the right with an independent uniform rotation in the plane of the pair. Conditional on the first rotation, both vectors traverse a great circle, separated by phase \(\theta\). Let \(E\) consist of phases \(t\) with both the directions at \(t\) and at \(t+\theta\) in \(H'\).

Two phases of circular distance \(d\) in the interval \((e,W)\), where \(W=2\pi-2\theta-e\), cannot both be in \(E\). Order the phases with forward difference \(d\); the cross pair has forward difference \(\theta+d\), strictly between \(\theta+e\) and \(2\pi-(\theta+e)\). If \(2e<W\) and \(0<W\le\pi\), a maximal \(W\)-separated subset of \(E\) has at most \(\lfloor 2\pi/W\rfloor\) members, by the cyclic gaps (the cases of zero or one member are immediate). Each phase lies within \(e\) of a member by maximality and exclusion. Inside each such arc the phases span an interval of length at most \(e\), since they have circular distances at most \(2e<W\), and \(2e<\pi\). Consequently the probability of both reference directions landing in \(H'\) is at most \(\lfloor 2\pi/W\rfloor e/(2\pi)\). No independence between different reference pairs is required for a union bound.

## 3. From an original bad pair to a forbidden phase

Take the closure of the diameter-one set and translate the enclosing ball to the origin. Put \(r=15007/50000,\ T=0.999999,\ h=1-1/2000\). Suppose a pair in one closed cone has squared distance at least \(T\). A nonnegative directional cosine (or a zero point) is impossible, since \(2r<T\). The magnitude of the negative cosine is at least \(T/(2r)-1>0\) and its square exceeds \(q_0\). Each norm exceeds \(h\sqrt r\): otherwise the universal cone bound gives squared distance at most \(r(1+h^2+4h/3)<T\).

Let \(H\) be normalized directions of points of norm at least \(h\sqrt r\). For two such points with norms \(b,b'\) and directional cosine \(c'\),
\[
1\ge (b-b')^2+2bb'(1-c'),\qquad c'\ge 1-\frac1{2rh^2}>-2/3-0.002 .
\]
The derivative magnitude of arccos on \([-2/3-0.002,-2/3]\) is less than \(3/2\). Thus \(H\) has angular diameter at most \(\theta+0.003\). Its closed enlargement \(H'\) by angle \(0.0535\) has diameter at most \(\theta+0.110\). A bad pair forces both directions of one of the rotated reference pairs into \(H'\), by Section 1.

With \(e=0.110\), we have \(W>\pi/2\). Indeed, \(\theta<3\pi/4-0.055\), since
\[
\cos(3\pi/4-0.055)\le -0.7071(1-0.055^2/2-0.055)<-2/3.
\]
Here \(0.7071<1/\sqrt2\), and the sine and cosine bounds follow by elementary Taylor inequalities. Also \(W<\pi\) because \(\theta>\pi/2\). Section 2 implies that the probability of any of the 15 bad reference events is at most \(45e/(2\pi)<1\). Choose a rotation avoiding them all. No cone then has a pair of squared distance at least \(T\); the closed cone intersections are compact, so each nonempty intersection has squared diameter less than \(T\). Break ties arbitrarily and restrict to the original set. \(\square\)

## 4. A tighter packing bound and endpoint \(0.30027\)

The endpoint in the theorem improves to \(r=0.30027=30027/100000\) with the same margin \(T=0.999999\). Two estimates in the proof tighten together.

First let \(\varepsilon=0.002,\ q_0=4/9-\varepsilon,\ a_0=9\varepsilon/[2(1-q_0)],\ D_0=3\varepsilon/(10q_0)\). The stability inequality gives \(a/a_0+D/D_0\le1\). Since \(P=a/(1+a)\), \(3a_0^2/2<D_0\), and \(0\le a/a_0\le1\), we obtain the joint bound
\[
D+3P^2/2\le D_0(1-a/a_0)+(3/2)a_0^2(a/a_0)^2\le D_0.
\]
Also \(P<0.0159\) and \(\|Gp\|>0.596\), by the same norm inequality as in Section 1. The chord bound \(5D_0/(4\cdot0.596\cdot0.612)\) is less than \((0.0684-0.0684^3/24)^2\); each reference error is thus less than \(0.0684\). Disjointness follows again from the reference inner products, \(q_0>0.66^2\), and \(2(0.0684)<1/6+0.66\). Use \(h=0.99908\); the exact inequalities \((T/(2r)-1)^2>q_0\), \(r(1+h^2+4h/3)<T\), and \(1-1/(2rh^2)>-2/3-0.0016\) give the angular diameter of the enlarged set at most \(\theta+0.0024+2(0.0684)=\theta+0.1392\).

Second, the phase bound can use not just the individual spans but also the gaps between their arcs. In Section 2 assume \(W>3e\). For a maximal separated set of \(k\ge2\) phases, the covering arcs of radius \(e\) are disjoint. The sections of \(E\) in these arcs are compact; replace each by its smallest containing closed subarc within that arc, of length at most \(e\). The forward gap between consecutive subarcs is at least \(W-2e>e\) by separation of their centers. If this gap were less than \(W\le\pi\), the two endpoints, both in \(E\), would contradict phase exclusion. Hence the gaps are at least \(W\), and the measure of \(E\) is at most \(\min(ke,2\pi-kW)\). The case \(k=1\) has measure at most \(e\); the empty case contributes zero.

Here \(e=0.1392\), and \(\theta<2.301\), as certified by the alternating Taylor upper bound for \(\cos(2.301)\) through degree 12, which is less than \(-2/3\). Using \(3.14159<\pi<3.14160\) gives \(W>3e\), \(5W>2\pi\), and \(15(2\pi-4W)<2\pi\). If \(k\le3\), use \(45e<2\pi\) instead. Thus the probability per reference pair is strictly below \(1/15\) in every case. The same union bound proves the improved endpoint.
