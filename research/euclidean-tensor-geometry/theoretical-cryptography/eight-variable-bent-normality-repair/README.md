# A replacement normality check for eight-variable bent functions

**Result.** Every bent Boolean function on $\mathbb F_2^8$ is affine on a four-dimensional affine flat. This is **Gillot–Langevin–Polujan's published theorem**, not a claim to a new theorem. We replace the last enumeration in its proof, retaining the authors' earlier seven-variable abnormal-function cover as an explicit external input. The check covers both slices in all possible relative positions, not just one extension for each lower slice. It does not show that every bent function is constant on a four-flat, or that all eight-variable quartics are weakly normal.

The [journal paper](https://doi.org/10.1109/TIT.2026.3685370), IEEE Transactions on Information Theory 72(6), 4352–4364 (2026), §V.C p. 4362, Theorem 7, uses an intermediate count of 30 expandable abnormal near-bent representatives. That count is incompatible with [explicit extensions of all 1,309 representatives](https://doi.org/10.5281/zenodo.24585725) ([code at a fixed commit](https://github.com/mxym/math/tree/5c5de0dfbaa9266edd913ad1bd066fa7ac95804c/research/euclidean-tensor-geometry/theoretical-cryptography/near-bent-extension-7-to-8)). An individual extension per representative neither proves nor refutes the normality theorem. The replacement below does not assume all near-bent functions extend; it independently checks all remaining potentially abnormal concatenations.

## 1. Reduction to two abnormal slices

Write $V=\mathbb F_2^7$, $F(x,0)=p(x)$ and $F(x,1)=q(x)$. Write $W_f(u)=\sum_x(-1)^{f(x)+u\cdot x}$ and $S(f)=\{u:W_f(u)\ne0\}$. The two Walsh coefficients of the concatenation at each $u$ are $W_p(u)\pm W_q(u)$. Both have absolute value 16 if and only if precisely one of $W_p(u),W_q(u)$ is zero and the other is $\pm16$. Thus both slices of any bent $F$ are near-bent and their supports are complementary. Also $\deg F\le4$ by the usual bent degree bound, so its slices have degree at most four.

If either slice is affine on a four-flat, that flat, in its own hyperplane, is already a witness. We need only examine pairs for which neither slice is affine on any four-flat. Call such seven-variable slices *abnormal*. The external input is **the coverage assertion** for the authors' [39,952 abnormal quartics](https://langevin.univ-tln.fr/project/indice/rd2-4-7.txt) from §IV, Algorithm 2 ([preprint Algorithm 4.1](https://arxiv.org/pdf/2504.21779)); lower degrees have no abnormal exceptions in this seven-variable classification. We do not regenerate the entire sieve from the cubic/quartic orbit classification and do not claim independence from that assertion. Extra records in a cover would be harmless; absent types would not be. The final expansion algorithm and its count of 30 are not inputs.

On the pinned 39,952 records, two different ANF/Walsh routines select exactly **4,085** near-bents. This agrees with the final journal §V.C and the [authors' supplementary page](https://langevin.univ-tln.fr/project/indice/indice.html). The [2025 preprint v1](https://arxiv.org/pdf/2504.21779v1), §5.3, instead prints 4,987 for this intermediate count. The present calculation is on the published raw file before EA deduplication and uses the ordinary Walsh criterion; we do not infer why the earlier figure differed.

One explicit extended-affine (EA) map per surviving record takes it to a member of the authors' [1,309-row file](https://langevin.univ-tln.fr/project/indice/representatives.txt). All 4,085 maps are checked on all 128 inputs. All 1,309 target indices are used. No unverified assumption about the authors' EA deduplication is needed for coverage, nor is pairwise inequivalence needed.

## 2. Complete relative affine-position reduction

Weak normality is invariant under an invertible affine input change and addition of an affine output. Normalize the lower slice to its listed representative $p_i$ using those operations on the whole $F$. The upper slice is still EA-equivalent to a representative $q_j$ and has the form
$$q_j(Ax+d)+b\cdot x+c,\qquad A\in {\rm GL}(7,2).$$
The input shear $(x,t)\mapsto(x+tA^{-1}d,t)$ leaves the lower slice fixed. On the upper it removes $d$ and changes only the displayed constant besides that removal. Add the appropriate constant multiple of $t$ to remove the upper constant while keeping the lower slice fixed. The normalized upper is therefore $q'_j(x)=q_j(L^Tx)+b\cdot x$ with $L=A^T$.

Its Walsh support is $L S(q_j)+b$. The necessary and sufficient condition for this normalized pair to be bent is thus
$$T(S(q_j))=V\setminus S(p_i),\qquad T(u)=Lu+b,\quad L\in{\rm GL}(7,2).$$
We enumerate **all** such $T$ for **all ordered pairs** $(i,j)$. No assumption on Walsh signs is needed; once the two supports are complementary the concatenation is bent. Translating a frequency support and translating the original upper input are distinct operations. The former, $b$, is exhaustively included; only the latter was removed by a legitimate shear. The two EA lifts of a pair need not themselves glue to an affine map: they identify the two classes separately, followed by this exhaustive relative-position argument.

## 3. A four-flat for every surviving position

Choose an independent triple $d_1,d_2,d_3$ spanning $D\subset V$ and offsets $v_0,v_1$. The union
$$\{(v_0+d,0):d\in D\}\ \cup\ \{(v_1+d,1):d\in D\}$$
is an affine four-flat: its independent directions are $(d_k,0)$ and $(v_0+v_1,1)$. On it $p_i\Vert q'_j$ is affine precisely when the two coset restrictions are affine with the same linear part on $D$. Their constants are arbitrary; their difference is the coefficient of the last basis direction. The enumerator searches the 11,811 three-dimensional directions, in unique reduced row-echelon form, and their 16 cosets. It stops for a given position only when it has found an actual common slope. The independent verifier checks the 16 output values directly on each indicated four-flat.

| Quantity | Verified value |
|---|---:|
| Ordered pairs of retained representatives before filters | 1,713,481 |
| Pairs passing initial (necessary only) incidence-color signatures | 11,662 |
| Ordered pairs admitting a complementary support alignment | 11,568 |
| Individual affine alignments, each with a four-flat witness | 37,132 |
| Ordered pairs with alignment, counting unreduced raw row labels | 4,296,389 |
| Affine alignments counting unreduced raw row labels | 77,339,359,954 |

The last two counts include multiplicities, not distinct eight-variable functions or EA classes. For multiplicity $m_i$ of a reduced representative, its ordered pair with $j$ contributes $m_i m_j$ times its transporter count. Both totals agree with separate direct graph counts on the 4,085 raw records and their complements, without invoking EA lifts. We did **not** check 77 billion individual four-flats: the proved reduction and 37,132 individual certificates cover them.

## 4. Two checks on the complete list of alignments

**Direct enumeration, no graph library.** Color the 128 points by support membership; refine equivariantly using their incidence with all 254 affine hyperplanes. An additional marked source point and its proposed image may be included in the refinement. Every affine isomorphism necessarily preserves every such color. Unsigned 64-bit fingerprints are pruning hints only: a collision can admit unnecessary branches but never reject a true affine isomorphism. Choose a source anchor and extend a source affine basis one point at a time. Try every target anchor of admissible color, and at each stage every same-colored image outside the already mapped affine span. Affinity forces the values on the doubled span; check their actual binary support membership and colors. A completed basis prescribes exactly one affine bijection. Every admissible bijection occurs, and distinct anchor/basis images cannot give the same map. Each leaf is a real support alignment and is assigned a witness as above.

**Independent graph and value audit.** Encode each support using the complete point–hyperplane incidence graph of affine seven-space, with three separate colors: points outside the support, points inside it, and hyperplanes. A color-preserving isomorphism acts on points by an affine bijection. Indeed the preimage of each coordinate hyperplane under its point permutation is an affine hyperplane, so every coordinate of the permutation is an affine Boolean function. A point permutation fixes the plane permutation uniquely since planes have distinct point sets. Conversely every affine transporter induces such a graph isomorphism. Consequently two graphs have equal canonical forms precisely when a transporter exists; in that case the number of different maps is the automorphism-group order. [McKay–Piperno's nauty](https://pallini.di.uniroma1.it/) via [PyNauty](https://github.com/pdobsan/pynauty) independently yields the same 11,568 source/target pairs and all expected counts. For every pair we check that the advertised transformations are distinct, invertible, and give the correct support image at every point; that there are exactly as many as the graph-group order; and that the indicated four-flat has dimension four and all 16 values fit a single affine form. The same graph routine checks the weighted raw counts. This audit does not use the C++ search's hash colors, search tree, flat list, or slope tables.

## 5. Reproduction and certificate format

Python 3.10+ and a GCC- or Clang-compatible C++17 compiler are sufficient for the primary route; no external Python packages are needed. The wrapper pins both author-hosted inputs. For offline use, supply their two local paths. No upstream ANF list is redistributed here.

~~~sh
python3 verify.py --download
# Or: python3 verify.py --raw rd2-4-7.txt --reduced representatives.txt
# Independent graph count and witness coverage in addition to the first route:
python3 -m pip install pynauty==2.8.8.1
python3 verify.py --download --nauty
~~~

To inspect output as plain text add `--export-trace alignments.txt`. `ea-lifts.txt` has rows $(i,j,b,c,d,A_0,\ldots,A_6)$: $i$ is the zero-based position *within the filtered raw list*, $j$ the reduced index, $A_k$ the columns of the input map, and $f_i(x)=f_j(Ax+d)+b\cdot x+c$. `alignments.xz.b64` holds the losslessly compressed, whitespace-delimited witness rows $(i,j,b,L_0,\ldots,L_6,d_1,d_2,d_3,v_0,v_1)$, with reduced indices and columns $L_k$. The two offsets and common three directions describe the four-flat in §3, with upper $f_j(L^Tx)+b\cdot x$. All vectors are decimal integers with coordinate $a$ in the low bit. Multiplication and dot products in the witnesses are over $\mathbb F_2$. The program regenerates the entire uncompressed witness stream byte-for-byte.

| Material | SHA-256 |
|---|---|
| Source, 39,952 ANFs | fc58fe0b3b11b67056ebb5f49c58aea8b338edb8d9cda9313d15494850dc7c80 |
| Source, 1,309 ANFs | f276d07eedeee1a8db90e0f453317d36ae420a168eb739a255d726eff5f1aa79 |
| 4,085 plain EA-lift witnesses | df2feefeb31417e4f43e656fe7166e89a91aeb1e6e8b004094a8d56965dc46ea |
| 37,132 plain four-flat witnesses | 5a958ec1101b847332ba3bcad0c29eb38c6d164f035bc329a6df06b92dd723ba |
