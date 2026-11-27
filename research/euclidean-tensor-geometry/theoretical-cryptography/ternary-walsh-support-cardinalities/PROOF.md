# Attainable Walsh support sizes of ternary functions across finite dimensions

Fix \(\omega=e^{2\pi i/3}\). For \(f:\mathbb F_3^n\to\mathbb F_3\), set \(W_f(u)=\sum_x\omega^{f(x)-u\cdot x}\), \(S_f=\{u:W_f(u)\ne0\}\), and \(C_n=\{|S_f|:f:\mathbb F_3^n\to\mathbb F_3\}\). Constants and affine functions are included. This concerns scalar ternary functions, not binary-valued functions or a vectorial spectrum.

**Theorem.**
\[
 \bigcup_{n\ge1} C_n=\{1,3,6,7,9\}\cup[12,\infty)_{\mathbb Z}.
\]
In particular the impossible positive sizes, in every number of variables, are exactly \(2,4,5,8,10,11\). The first three dimension-specific sets are \(C_1=\{1,3\}\), \(C_2=\{1,3,6,7,9\}\), and \(C_3=\{1,3,6,7,9\}\cup[12,27]_{\mathbb Z}\). Each attainable size persists in every sufficiently large dimension. We do not determine \(C_n\) for every \(n\ge4\), or the least dimension where a given size \(r>27\) appears.

**Small-shape corollary.** Each of sizes 1, 3, 6 and 7 has one shape up to an affine isomorphism of the support hull, across all ambient dimensions. Size 9 has at least two shapes.

The target is the ternary eventual-attainability part of the final Open Questions paragraph of [Jauberty–Méaux, ePrint 2025/1651, April 2026 revision](https://opencryptology.org/2025/1651/versions/20260428T172000Z.pdf), §8 p. 49.

## 1. Three necessary geometric facts

Use normalized coefficients \(w(u)=3^{-n}W_f(u)\) for Fourier inversion: \(\phi(x)=\omega^{f(x)}=\sum_u w(u)\omega^{u\cdot x}\). Three consequences follow.

1. **Affine reduction.** Adding a linear function translates \(S=S_f\), and an invertible linear input change induces an invertible linear map on frequencies. If \(d=\dim\operatorname{aff}(S)\), translate its hull through 0 and move it to the first \(d\) frequency coordinates. Fourier inversion shows that the resulting \(\phi\) depends only on the first \(d\) input coordinates, so the same is true of \(f\), since the three phases are distinct. In particular \(S\) is realized in dimension \(d\) in these coordinates, or in any larger dimension by padding. If \(d=0\), the support is a singleton.
2. **Differences.** The identity \(\phi\bar\phi=1\) gives \(\sum_{u-v=z}w(u)\overline{w(v)}=0\) for each \(z\ne0\). A unique ordered pair in \(S\) with difference \(z\) would give one nonzero term. Equivalently, when counting distinct unordered pairs and recording differences up to sign, no nonzero signed difference occurs exactly once; exactly one orientation of each pair in the sign class has difference \(z\), since \(z\ne-z\).
3. **Midpoints.** The ternary phase identity \(\phi^2=\bar\phi\) gives \(\sum_{u+v=z}w(u)w(v)=\overline{w(-z)}\). Fix \(c\notin S\) and set \(z=-c\). A diagonal term would have \(2u=-c\), hence \(u=c\), so it is zero. Each distinct unordered pair with midpoint \(c=(u+v)/2=-u-v\) contributes twice the same nonzero term. Over \(\mathbb C\) a single such pair cannot give zero. Therefore each missing midpoint has either zero pairs or at least two.

These conditions hold in the reduced affine hull. An affine bijection transports midpoints since they are affine combinations and transports differences by its linear part. Pair multiplicities are preserved. The midpoint condition requires the ternary phase identity, not just unit modulus.

## 2. Dimension bound

Choose an affine basis \(B\subset S\) of size \(d+1\) and let \(T=S\setminus B\) have \(t=r-d-1\) points. Represent the hull in barycentric coordinates \(\sum_i x_i=1\) in \(\mathbb F_3^{d+1}\), so \(B=\{e_0,\ldots,e_d\}\). For every \(i\ne j\) the basis pair \(\{e_i,e_j\}\) has midpoint \(-e_i-e_j\notin B\) and needs one of the following witnesses:
- a new point equal to that midpoint, of type \(A=2e_i+2e_j\);
- a distinct pair with one old basis point \(e_k\) and one new point of type \(B'=e_i+e_j-e_k\) with \(k\ne i,j\);
- a pair of distinct new points whose sum is \(e_i+e_j\).

No other basis pair shares the midpoint. Each new point can directly witness at most one basis pair in the first two ways combined, since its coordinate pattern determines \(i,j\), and the two types are disjoint. Each new pair witnesses at most one basis pair because its sum determines \(i,j\). Thus \(\binom{d+1}2\le t+\binom t2=\binom{t+1}2\), so
\[
 d\le\lfloor(r-1)/2\rfloor.
\]
If \(t=d\ge4\), equality forces every new point to be of type \(A\) or \(B'\) and every distinct new pair's sum to have exactly two nonzero coordinates, both 1. Otherwise the available witnesses would be fewer than the obligations. Let \(J\) be the coordinates at which some new point has a 2. Every new point is nonzero on all of \(J\): if it has zero at a coordinate with 2 in a distinct point, their sum has a forbidden 2.

If a point of type \(A\) exists, its two coordinates are exactly \(J\), and that point is unique. Two type-\(B'\) points cannot have their 2 at the same coordinate in \(J\), since their other common \(J\)-coordinate would have \(1+1=2\). This gives at most three points in total. If all points are of type \(B'\), then \(1\le |J|\le3\). When \(|J|=3\), their full support equals \(J\), so there are at most three. When \(|J|=2\), the same \(1+1\) argument gives at most two. When \(|J|=1\), a pair sharing a positive coordinate would give a 2; a pair with disjoint positive coordinates would give five 1's, not two. Thus in this last case at most one point is possible. In every case \(t\le3\), a contradiction. We obtain
\[
 d\ge4\quad\Longrightarrow\quad r\ge2d+2.
\]

## 3. Excluding the six missing sizes

The direct residue test in [verify.py](verify.py) exhausts all 27 one-variable and 19,683 two-variable truth tables. If the counts for the exponents \(f(x)-u\cdot x=0,1,2\) are \(a,b,c\), then the coefficient is \((a-c)+(b-c)\omega\); it vanishes exactly when \(a=b=c\). The program checks each table against an independent Eisenstein-integer FFT, including its full list of coefficients.

- A size 2 forces \(d=0\) and a size 4 forces \(d\le1\), both impossible by cardinality.
- A size 5 forces \(d\le2\) and is excluded by the two-variable census and padding.
- A size 8 forces \(d\le3\). The two-variable census excludes \(d\le2\). If \(d=3\), map an affine basis of the support to \((0,e_1,e_2,e_3)\). [geometry.cpp](geometry.cpp) exhausts all \(\binom{23}{4}=8\,855\) choices for the remaining points, with zero surviving the midpoint test.
- A size 10 or 11 forces \(d\le4\) by §2. The three-variable census below excludes \(d\le3\). If \(d=4\), map an affine basis to \((0,e_1,e_2,e_3,e_4)\). The geometry verifier exhausts the \(\binom{76}{5}=18\,474\,840\) or \(\binom{76}{6}=218\,618\,940\) choices; no midpoint survivors.

Every spanning support is included by some affine basis, so possible repeats under affine equivalence do not affect the exclusion. In the first geometric pass the program recurses over increasing extra points and propagates bitsets of signed differences and midpoints occurring once or multiple times. In the second four-dimensional pass, it instead iterates colexicographic combination masks; it first checks coverage of all ten basis-midpoint obligations from §2, then uses integer bucket counts recomputed from each survivor. The basis check leaves 420 and 40,440 candidates at sizes 10 and 11 respectively; neither yields a full midpoint survivor. Both passes also check the difference condition. A known support and a simplex are controls. See [RESULTS.txt](RESULTS.txt).

### The exact three-variable census, up to support size 13

Let \(f,g,h\) be the two-variable slices at the last input coordinate \(0,1,2\). Their join has Walsh coefficient \(W_f(u)+\omega^{-t}W_g(u)+\omega^{-2t}W_h(u)\) at frequency \((u,t)\). To cover all possibilities efficiently, act on the first slice by every affine input map, output scaling by \(\pm1\), and addition of affine scalar functions. The same transformation applied to all slices preserves the three-variable cardinality, since it merely conjugates the phase, permutes frequencies up to phase, or translates frequencies. Normalizing by the unique affine function agreeing at \(0,e_1,e_2\) leaves \(3^{9-3}=729\) first-slice tables. On these normalized tables, the code generates the entire orbit of each unmarked representative by enumerating each ordered independent pair of columns, translation and output sign. There are 11 orbits; the scan checks that all 729 normalized tables are marked. This classifies only the first slice for purposes of coverage, not the three-variable functions.

One can then add a linear term in the last input coordinate to arrange \(g(0)=0\), while leaving the first restriction unchanged. The third restriction remains arbitrary. For each first-slice representative there are \(3^8\) choices of the second table and \(3^9\) of the third. This is an exhaustive reduced domain of \(11\cdot3^{17}\) triples, possibly with duplicates.

[exhaustive3.cpp](exhaustive3.cpp) evaluates every triple in two ways. The first uses exact Eisenstein coordinates and prunes with a support-mask lower bound: with one nonzero input a ternary Fourier fiber has three nonzero outputs, with two nonzero inputs it has at least two outputs (a one-frequency Fourier vector would invert to a nonzero character at all three inputs), and with three it has at least one. The second switches the second/third slice iteration order, adds the raw phase-residue histograms after cyclic rotations, and does no mask pruning. It cross-checks the complex-coordinate formula at each triple of histogram types. The total may be discarded once it exceeds 13, since all later fiber counts are nonnegative. The two scans give identical counts at every size up to 13 and zero for 10 and 11. Their totals refer to the reduced triple domain, not to the number of original three-variable functions or that of their affine classes.

## 4. Every remaining size is realized

The [witness file](witnesses.json) gives two-variable truth tables for sizes \(1,3,6,7,9\), and three-variable truth tables for all sizes 12 through 27, checked by both Fourier algorithms. The first coordinate is the least significant trit of the input index. For example, the size-13 witness is the word **001000000010000000111101110**. These tables and the exclusions give the claimed first three dimension-specific sets.

Suppose \(f\) has support size \(s\), and take two fixed witnesses \(g,h\) on two variables. Pad all three to a common dimension \(m\ge2\). On two new scalar coordinates \(y,t\), define the ternary function
\[
 F(x,y,t)=
 \begin{cases}
  f(x)+y & t=0,\\
  g(x) & t=1,\\
  h(x) & t=2.
 \end{cases}
\]
This definition produces actual phases of a ternary truth table. The sum over \(y\) shows that frequency \(v=1\) on the \(y\)-coordinate contributes \(3W_f(u)\) at each selector frequency \(\tau\); \(v=0\) contributes
\[
 3\left(\omega^{-\tau}W_g(u)+\omega^{-2\tau}W_h(u)\right)
 =3\omega^{-\tau}\left(W_g(u)+\omega^{-\tau}W_h(u)\right);
\]
\(v=2\) contributes zero. Thus the cardinality is \(3s+q\), where
\[
 q=\#\{(u,\tau):W_g(u)+\omega^{-\tau}W_h(u)\ne0\}.
\]
Padding \(g,h\) scales both coefficients by the same nonzero factor on their frequency plane and adds zeros elsewhere, leaving \(q\) unchanged. The phases here follow from the actual function definition, not from independently assigning spectral coefficients.

The eight pairs in the witness file supply \(q=3,14,15,16,19,20,22,23\), checked exactly by rotating and adding residue histograms. They give the following bridge from the explicit seeds to every size 28–57. An entry \(r\leftarrow s\) means \(r=3s+q\).

| \(q\) | \(r\leftarrow s\) |
|---|---|
| 3 | \(30\leftarrow9,\ 39\leftarrow12,\ 42\leftarrow13,\ 45\leftarrow14,\ 48\leftarrow15,\ 51\leftarrow16,\ 54\leftarrow17,\ 57\leftarrow18\) |
| 14 | \(32\leftarrow6,\ 35\leftarrow7,\ 41\leftarrow9,\ 50\leftarrow12,\ 53\leftarrow13,\ 56\leftarrow14\) |
| 15 | \(33\leftarrow6,\ 36\leftarrow7\) |
| 16 | \(34\leftarrow6,\ 37\leftarrow7,\ 43\leftarrow9,\ 52\leftarrow12,\ 55\leftarrow13\) |
| 19 | \(28\leftarrow3,\ 40\leftarrow7,\ 46\leftarrow9\) |
| 20 | \(29\leftarrow3,\ 38\leftarrow6,\ 47\leftarrow9\) |
| 22 | \(31\leftarrow3,\ 49\leftarrow9\) |
| 23 | \(44\leftarrow7\) |

For each \(r\ge58\), choose \(q=3,16,14\) for \(r\equiv0,1,2\pmod3\), respectively. Then \(s=(r-q)/3\) is integral and \(14\le s<r\); strong induction proves attainability. The verifier also constructs and checks the actual truth table at every bridge size and at several sizes after further recursion.

## 5. Small shapes

Sizes 1 and 3 give a point and an affine 1-flat by the bound in §2 and their cardinalities. A size-6 support has affine dimension two. The complete two-variable census checks that its three omitted points are collinear in all size-6 cases. Thus its unique shape is a plane minus a line. Size 7 cannot have affine dimension three: the geometry verifier exhausts \(\binom{23}{3}=1\,771\) candidates as above and finds no midpoint survivor. Its shape is an affine plane minus two distinct points, unique up to affine isomorphism. At size 9 the full plane occurs. For a different shape use the function with slices \(0,x,y\) at \(t=0,1,2\), respectively, with each slice on inputs \((x,y)\). Their first two-dimensional frequency singleton sets are disjoint, so the support is \(\{0,e_1,e_2\}\times\mathbb F_3\), of affine dimension three. No classification of all size-9 shapes is asserted.
