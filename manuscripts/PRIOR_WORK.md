# Limited prior-work and attribution comparison

The literature scout used the user-requested GPT-6 Luna model at high reasoning effort. It handled attribution only, not proof review. These notes summarize the repository comparison records and a limited current screen; an additional arXiv query timed out. Full-text read annotations refer to those historical comparisons, not to fresh rereading of every source in this finalization. The current theorem scopes were checked against the actual manuscript sources. No systematic novelty certification, first-proof or first-solution claim is made.

# Prior-work and attribution note: simplex stability

## Suggested manuscript text

The theorem is stated for every full-dimensional compact convex body \(K\subset\mathbb R^d\) and every prescribed maximum-volume inscribed simplex \(S\subset K\). Its deficit is the entry-005 projection/pyramid invariant \(e(K)\), and its target is the least dilation of \(S\), centered at \(S\)'s own centroid, that contains \(K\). The sharp exponent \(1/(d-1)\) is sharp for this precise deficit and target, as witnessed by the stated simplex-truncation family. The quadratic-dimensional refinement retains these quantifiers and improves the explicit coefficient to \(G_d\le4096d^2\), with \(G_d\sim16d^2\); the optimal dimension order is not determined.

There is a stronger direct planar comparison. Böröczky's stability theorem for the Rogers–Shephard inequality, after the identity relating the entry-005 invariant to \(|K-K|/|K|\), gives a linear planar Banach–Mazur estimate. It does not directly give the present all-maximizer, simplex-centroid containment estimate in dimensions \(d\ge3\). Other close stability results concern random-simplex moments or cone-volume concentration and use different deficits and target conclusions. Accordingly, we present the higher-dimensional result as a quantitative theorem for this specified invariant and containment functional, without a first-result or literature-wide optimality claim.

## Checked references and scope

- Károly Böröczky Jr., “The stability of the Rogers–Shephard inequality and of some related inequalities,” *Advances in Mathematics* 190(1) (2005), 47–76. DOI: [10.1016/j.aim.2003.11.015](https://doi.org/10.1016/j.aim.2003.11.015). Full text read (Theorem 1 and §8). This is the direct planar comparison described above.
- Károly Böröczky Jr. and Martin Henk, “Cone-volume measure and stability,” *Advances in Mathematics* 306 (2017), 24–50. DOI: [10.1016/j.aim.2016.10.005](https://doi.org/10.1016/j.aim.2016.10.005). Theorems 1.1–1.3 read; related stability framework, different hypotheses and conclusion.
- Gergely Ambrus and Károly Böröczky, “Stability results for the volume of random simplices,” *American Journal of Mathematics* 136(4) (2014), 833–857. DOI: [10.1353/ajm.2014.0030](https://doi.org/10.1353/ajm.2014.0030). Theorems 4–5 read; random-simplex moment deficits, not the present functional.

The project theorem and exact invariant normalization are recorded in the local sharp-stability source map and proofs. The cited papers were read as stated above; this is a targeted comparison, not an exhaustive convex-geometric literature review.

## Editorial cautions

- Do not say the result is restricted to product bodies, joins, or a special class of \(K\). It applies to all full-dimensional compact convex bodies.
- Any restriction belongs to the specific projection/pyramid deficit and the prescribed-maximizer, own-centroid containment metric.
- Do not conflate the separate unresolved product/join extremal-optimization question with the scope of this stability theorem.
- Do not call the planar exponent sharp for this project: the cited planar result is stronger for Banach–Mazur distance.


# Prior-work and attribution note: continuum power-avoidance

## Suggested manuscript text

Fix a prescribed nonempty countable family of configurations whose occupied dyadic logarithmic bins have bounded gaps. The theorem constructs a closed, nowhere-dense, one-periodic set of arbitrarily high density that simultaneously avoids infinitely many distinct outputs in every tail for every map in the stated family with a nonzero leading power and a power-controlled higher-order remainder. The configuration family is fixed before the set is chosen; the exponent, translation, coefficient, and admissible map vary after the set is chosen. The result does not choose one set for all possible configurations and does not settle the full Erdős similarity problem.

The proof explicitly credits the parameter-space grid and finite-representative method of Kolountzakis–Papageorgiou, and the nested-grid routing construction from the cited OpenAI research manuscript; the countable-profile viewpoint is also credited to the repository's earlier nonlinear-avoidance entry. Feng–Lai–Xiong provide a related differentiable embedding theorem under fast decay, but it promises an (o(a)) remainder rather than the positive power remainder addressed here. Burgin–Goldberg–Keleti–MacMahon–Wang ask a translated geometric-progression question, while their Theorem 1.1 treats untranslated progressions; the manuscript's geometric corollary gives the stated stronger measure and tail conclusion. These comparisons identify the scope of the theorem and its method inputs, not exclusive priority.

## Checked references and scope

- A. Burgin, S. Goldberg, T. Keleti, C. MacMahon, X. Wang, “Large sets avoiding infinite arithmetic / geometric progressions,” [arXiv:2210.09284v1](https://arxiv.org/abs/2210.09284). Question 1 and Theorem 1.1 read. The question includes translation; Theorem 1.1 excludes untranslated geometric progressions.
- M. N. Kolountzakis and E. Papageorgiou, “Large sets containing no copies of a given infinite sequence,” *Analysis & PDE* 18 (2025), 93–108. [arXiv:2208.02637v2](https://arxiv.org/abs/2208.02637), DOI [10.2140/apde.2025.18.93](https://doi.org/10.2140/apde.2025.18.93). Theorem 4.1 and proof, printed pp. 13–14, read; parameter-space grid arrangement and finite representatives are method precedents.
- D.-j. Feng, C.-K. Lai, and Y. Xiong, “Erdős similarity problem via bi-Lipschitz embedding,” *International Mathematics Research Notices* 2024(17), 12327–12342. [arXiv:2312.01319v1](https://arxiv.org/abs/2312.01319), DOI [10.1093/imrn/rnae167](https://doi.org/10.1093/imrn/rnae167). Theorem 1.1 read; fast-decay embedding with derivative one, without the asserted positive power rate.
- OpenAI, “The geometric case of the Erdős similarity conjecture,” research-source manuscript, 5 October 2026, pinned `openai/math` commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Source manuscript read; it fixes the ratio before choosing the avoiding set. Cite as a research manuscript, not as a journal publication.
- mxym, “Modulus nonlinear similarity,” repository source `preprints/006-modulus-nonlinear-similarity/v2/paper.md`, Theorem 3.1. Source text read; countable profiles under positive logarithmic upper Banach density are the relevant predecessor perspective.

The source audit and exact versions are recorded in the local `citation-audit.txt` and source map. The comparison is finite and does not certify worldwide priority.

## Editorial cautions

- State the bounded-gap configuration hypothesis; do not imply universality over all configurations.
- State the power-controlled remainder; do not imply avoidance for arbitrary differentiable or flat germs.
- Credit the inherited routing construction and finite parameter-grid method. The contribution should be positioned as the stated joint scope/quantifier extension and power-remainder result, not as invention of grid avoidance itself.
- Describe the translated geometric-progression consequence precisely; do not identify BGKMW's untranslated theorem with its translated question.


# Prior-work and attribution note: fractional frontier, stability, and matching spectrum

## Suggested manuscript text: sharp fractional frontier

For finite simple intersecting hypergraphs of rank at most \(r\), the manuscript proves the finite bound
\[
\tau^*(H)\le \max\left\{\frac{(k-1)r+1}{k},\frac{m}{k+1}\right\}\qquad(k\ge2),
\]
where \(m\) is the number of edges. Its limiting fractional-cover curve is
\[
\psi(c)=c/2\quad(0\le c\le1),\qquad
\psi(c)=\max\left\{\frac{a}{a+1},\frac{c}{a+2}\right\}\quad(a\le c\le a+1),
\]
so each integer interval has a plateau followed by a linear ramp. The manuscript proves this curve is sharp for every \(c\ge0\), even when the approximating hypergraphs are required to be uniform. The result concerns fractional vertex cover (equivalently fractional matching); it is not an unrestricted integer-cover formula.

The companion stability result characterizes near-extremizers at integer ratios by deleting \(o(r)\) edges to obtain bounded-degree near-Steiner cores, and derives an integer-cover consequence through Kahn's stated conditional rounding theorem. Separately, the fixed-matching-number manuscript proves the bounded-packing spectrum: for rank at most \(r\), matching number at most fixed \(s\), and \(m/r\to c\), the limiting curve is \(\Psi_s(c)=\max_{\sum c_i=c}\sum_{i=1}^s\psi(c_i)\), with an explicit finite error and a proved finite formula. The latter is a completed written theorem, not a conjectural extension. These statements should be attributed to their respective manuscripts and kept distinct from earlier \(m/r\)-dependent upper-bound candidates.

Classical results of Füredi, Füredi–Kahn–Seymour, and Kahn provide important degree, fractional-matching, and conditional rounding context, but the checked source comparisons do not state the same plateau/ramp curve or bounded-packing spectrum. This is a limited comparison, not a priority claim.

## Relevant sources and reading status

- Current source manuscripts: `notes/sharp-fractional-cover-frontier/paper.md`, `notes/fractional-design-stability/paper.md`, and `notes/fractional-matching-spectrum/paper.md`. The first proves the sharp \(\psi\) curve and gives its Wilson/Kahn-based sharpness constructions; the second gives the deletion stability and near-design characterization; the third proves the finite and asymptotic \(\Psi_s\) laws.
- Zoltán Füredi, “Covering pairs by \(q^2+q+1\) sets,” *Journal of Combinatorial Theory, Series A* 54(2) (1990), 248–271. DOI [10.1016/0097-3165(90)90034-T](https://doi.org/10.1016/0097-3165(90)90034-T).
- Zoltán Füredi, Jeff Kahn, and Paul D. Seymour, “On the fractional matching polytope of a hypergraph,” *Combinatorica* 13(2) (1993), 167–180. DOI [10.1007/BF01303202](https://doi.org/10.1007/BF01303202).
- Zoltán Füredi, “Intersecting designs from linear programming and graphs of diameter two,” *Discrete Mathematics* 127(1–3) (1994), 187–207. DOI [10.1016/0012-365X(92)00478-A](https://doi.org/10.1016/0012-365X(92)00478-A).
- Zoltán Füredi, “Maximum degree and fractional matchings in uniform hypergraphs,” *Combinatorica* 1(2) (1981), 155–162. DOI [10.1007/BF02579271](https://doi.org/10.1007/BF02579271).
- Jeff Kahn, “On a Problem of Erdős and Lovász. II: \(n(r)=O(r)\),” *Journal of the American Mathematical Society* 7(1) (1994), 125–143. DOI [10.1090/S0894-0347-1994-1224593-5](https://doi.org/10.1090/S0894-0347-1994-1224593-5). Corollary 5.4 is the conditional integer-cover input used in the construction/rounding discussions; it requires bounded edge/rank ratio and maximum pairwise edge intersection \(o(r)\).
- Richard M. Wilson, “An existence theory for pairwise balanced designs, III: Proof of the existence conjectures,” *Journal of Combinatorial Theory, Series A* 18(1) (1975), 71–79. DOI [10.1016/0097-3165(75)90067-9](https://doi.org/10.1016/0097-3165(75)90067-9). The earlier source comparison checked the publisher's primary abstract and metadata only; it did not read the full paper. The result supplies admissible Steiner-design constructions, not the finite upper bound.

**Reading-status note.** Full-text reading status for the Füredi and Kahn papers above comes from the repository's earlier novelty-assessment/source-comparison records; this finalization note did not re-read those papers. Wilson was checked only by primary abstract and metadata. Kahn–Kayll 1997 was not available as full text in that screen, so no claim about its detailed contents is made here.

## Editorial cautions

- Use \(\psi\) for the current sharp plateau/ramp frontier. Do not substitute an older harmonic/chord envelope or the prior \(U_k/\phi\) formula as the current main result.
- State explicitly that the frontier is fractional. Kahn rounding applies only under its codegree assumptions; do not infer an unconditional integer-cover curve.
- The fixed-matching spectrum has a complete written proof and explicit finite formula; do not label it merely proposed. The literature comparison remains finite, so avoid a first-result or priority claim.
- Keep the Wilson design existence theorem and Kahn rounding result on the sharpness/construction side; neither is an input to the signed-counting finite upper bound.


# Prior-work and attribution note: complex three-row permanent pencil

## Suggested manuscript text

The self-contained three-row complex matrix argument determines the exact coefficient lens for which
\[
|\operatorname{per}A+\lambda\det A|\le \frac{2}{\sqrt3}\prod_{i=1}^3\|A_{i,*}\|_2
\]
holds for every complex \(3\times3\) matrix, and gives the exact best constant for every complex \(\lambda\). The complete equality classification in the manuscript is for the sharp absolute-value endpoint inequality, not for the pencil norm at every \(\lambda\). The complex Hermitian proof of the pencil and coefficient lens is self-contained. It extends the repository's earlier real three-row endpoint result. Bristiel–Caputo's sharp permanent row-norm inequality is an input to the separate earlier all-arity robust-permanent note; it is not a premise of the complex pencil proof. The classical permanent-only complex inequality is due to Carlen–Lieb–Loss. We do not claim priority for the general permanent inequality or a literature-wide first exact coefficient classification.

## References and checked scope

- A. Bristiel and P. Caputo, “Entropy inequalities for random walks and permutations,” *Annales de l'Institut Henri Poincaré, Probabilités et Statistiques* 60(1) (2024). DOI [10.1214/22-AIHP1267](https://doi.org/10.1214/22-AIHP1267), Corollary 1.14. This result is cited as an input in the separate all-arity robust-permanent manuscript; do not list it as a premise of the complex pencil theorem.
- E. A. Carlen, E. H. Lieb, and M. Loss, “An inequality of Hadamard type for permanents,” *Methods and Applications of Analysis* 13 (2006), 1–18. This is the classical permanent-only complex inequality; it does not by itself state the present determinant pencil classification.
- OpenAI, “A strict four-row permanent inequality and permutation moments,” research manuscript, 26 September 2026. It supplies broader permutation-moment context and motivation; cite explicitly as a research manuscript, not a journal publication.
- Repository predecessor: `notes/sharp-robust-permanent/paper.md`, §9, real three-row endpoint. It is internal prior work and is explicitly credited in the complex note.

The exact coefficient-lens note reports its own algebraic certificate; its full equality classification concerns the sharp absolute-value endpoint only. Bibliographic reading status here is inherited from the repository's prior comparison/source records; this finalization note did not re-read each cited source. This is not a broad search of all complex permanent literature.

## Editorial cautions

- Attribute the real three-row endpoint in the complex-pencil manuscript; attribute Bristiel–Caputo specifically when discussing the separate all-arity robust-permanent note.
- Do not describe the permanent row-norm inequality itself as new.
- Scope the claimed addition to the complex coefficient lens / exact three-row pencil norm and stated equality classification; do not claim an (n\ge4) complex robustness region.
- Distinguish the local analytic certificate from a literature-wide novelty determination.


# Prior-work and attribution note: permutation atom-versus-TV constants

## Suggested manuscript text

For a finite permutation action, the manuscript reduces the sharp atom-versus-total-variation response under preservation of one-point marginals to a finite primal–dual linear program on conjugacy classes and orbitals. This is a general finite certificate framework; averaging over group symmetries and LP duality are standard tools, so the manuscript should not present those tools alone as a novelty claim. The concrete results include exact closed forms for the natural \(S_n\) action on two-subsets, the exact \(S_5\) case, and fixed rational primal–dual certificates for the action on three-subsets for \(n=6,\ldots,120\). The three-subset calculation is a finite classification over the specified finite degrees, not an all-\(n\) formula or a solution for arbitrary subset size. The integrated manuscript includes the later three-subset asymptotic, exact classification through 120, all-rank short-cycle transfer and four-subset degrees 11--50. Exact all-degree formulas beyond pairs and the higher-rank sharp asymptotic remain open.

The current source review did not establish a direct external precedent for the exact formulas/certificates. This is not evidence that none exists. The reported exact rational checks support the finite statements but do not establish a literature-wide priority claim.

## Scope and evidence

- Primary mathematical source: `notes/sharp-robust-permanent/paper.md`, Theorems 15–19 and the accompanying rational primal–dual certificate files. Section 18 gives the universal orbital LP characterization; Section 19 gives the three-subset cases (n=6,…,23), with 18 fixed rational certificates.
- In the two-subset action, the manuscript states the exact parity-dependent formula for every \(n\ge4\), with \(S_5\) as the first non-doubly-transitive example and exact value \(1/3\).
- The source manuscript gives exact primal and dual witnesses for each three-subset degree \(6\) through \(23\), checked by exact rational arithmetic and enumeration of all conjugacy classes. It explicitly does not extend that classification past \(23\).
- A targeted arXiv API search for permutation atom/TV, marginal-preserving laws, and orbital LP terminology was attempted but did not return usable results (rate limits/timeouts). No external theorem-level exclusion is asserted from that search.

## Editorial cautions

- Call Theorem 18 a finite orbital primal–dual characterization and certificate interface; avoid calling LP duality or orbit averaging unprecedented.
- Report the three-subset range exactly as \(n=6,\ldots,23\) (18 cases). Do not imply all \(n\), all \(k\), or an asymptotic solution.
- Distinguish exact closed formulas for the two-subset action from rational certificate-by-certificate results for the three-subset action.
- Avoid “first,” “only,” or “complete solution” without a separate literature review.



## Scope of the parallel additions incorporated during finalization

The integration snapshot includes a complete three-subset finite classification through 120, a separate analytic sharp 18/n asymptotic, all-rank transfer and rank hierarchy, four-subset certificates in degrees 11--50, and the sharp four-row permanent--determinant tradeoff. These are attributed to their original repository packages, not to this editorial finalization. The limited external screen above predates these additions and does not assess their novelty separately. The transferred character-polynomial dependence, LP duality, averaging, transfer matrices, Cauchy and Laplace expansions are classical tools; any originality claim must concern precise proved statements rather than those tools alone.
