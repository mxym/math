# Independent ordinary review of the Han Question 3.1 auxiliary argument

Decision: **PASS for the complete written mathematical claim, on the unchanged manuscript SHA-256 `0250c4792fdecbf5e14b4ea1300253329e7385d8593a4044efafa0a2767cb1ef`.** The source-map error found in v1 is corrected in separately frozen v2 and is recorded below. This is a private internal AI-agent review, not external human peer review, a formal proof, a priority certificate, or publication approval. The full Fourier entropy–influence conjecture is neither proved nor refuted. No major-result score or solved-index change is assigned or performed here.

## Inputs and actual reading

All six v1 packet files were copied privately and read in full. The capture verified their bytes against immutable Git commit `d83f9be16b9e4fb00437ca59fa79316b9de80960` and the worktree. `INPUT_MANIFEST.json` records each file. This includes the 129-line manuscript, the entire target/source map, the 88-line author checker, its 258-line stored result, the README, and the SHA manifest. Earlier NumPy controls and the earlier research derivation mentioned in the manuscript were not executed or separately audited; they are not needed for the proof checked here.

After the source-map finding, all eight v2 files were copied to `snapshot-v2/`. I read the new README, revision note and map correction in full. The mathematical manuscript, author checker and stored author result are byte-identical to v1. The map differs in exactly one JSON string field; its supplied unified diff matches that correction. The README has a version-title change and an added correction paragraph, separately recorded in `REVIEWER_README_md.diff`. The new manifest was checked against its listed bytes and hashes. `V2_CAPTURE.json` and `V2_BYTE_CHECK.json` distinguish these new metadata from unchanged mathematics; no Git commit for v2 is asserted.

Final reviewed metadata: v2 map `ebcf8f3e33a26d29eb1971e4b850668084eb6302adac8d165f6275312aa60545`, README `506f4e1009f7c39a8dcb608b5906f1b07368361c234e2a704f1ce39bedb42e71`, revision note `89e0a7128e99cfb011fb577b84a7f1d1be404479bb046be7fa39d2ea627e4893`, supplied map diff `84e496adc74b7c090aa80842f6a784bfddc9278651243607f4f84ffd1d89b385`, manifest `5ea98fcab52518077e4a0ff333eacac2ba49aeafc70a89a24d5b72edd08f3b6a`.

## Original target and its negation

I checked the question and surrounding normalization in Han's [current v2 primary text](https://arxiv.org/html/2312.08271v2) and the [publisher version](https://link.springer.com/article/10.1007/s00493-024-00133-z). Question 3.1, equation (3.18), asks for a single finite universal constant (c>0) such that every Boolean function on a nonempty uniform cube has at least one coordinate (i) with

\[
A_i(f):=\sum_{S\subseteq[N]\setminus\{i\}}|\widehat f(S)\widehat f(S\cup\{i\})|\le c I_i(f).
\]

Here the Fourier coefficient is the uniform expectation and (I_i\) is the probability that flipping coordinate (i\) changes (f\). This is single-coordinate influence, not total influence. The original question does not require balanced functions. A dummy coordinate would have both quantities zero, but its presence is not guaranteed and does not rescue an original function whose coordinates are all essential. The manuscript supplies, for every proposed (c\), one dimension (2^d\) and one function for which **every** coordinate is essential and violates the inequality. A subsequence of dimensions suffices for the universal-constant negation.

## Arbitrary-depth construction and all coordinates

The gate chosen at level (j\) depends only on the already determined number (p_j\), not on the current input. Both children are identical functions on disjoint independent variable blocks. Under the stated sign encoding, AND and OR have the gate polynomials printed in the manuscript, giving (p\mapsto p^2\) and (p\mapsto2p-p^2\). Their specified branches map ([1/4,3/4]\) into itself: the two images are ([7/16,3/4]\) and ((1/4,9/16]\). Induction from (p_0=1/2\) proves (|\mu_j|\le1/2\) for every integer depth.

The formulas are monotone and read each leaf once. Swapping the two identical subtrees at every internal node gives a transitive automorphism group on leaves. This means leaf transitivity, not invariance under every variable permutation. Fourier coefficients, the overlap and coordinate influence transform equivariantly under those automorphisms, so the same values apply to all coordinates. Independently of this symmetry argument, the recurrence below is valid for an arbitrary coordinate in either child. Its influence multiplier is (p_j\) for AND and (1-p_j\) for OR; under the selection rule it lies in ([1/2,3/4]\). Starting from influence one proves strict positivity at every depth. There are no hidden dummy leaves or illegitimate divisions.

## Restriction identity, signs and recurrence

For a fixed coordinate, write the paired coefficients of the original function as (c_T,d_T\). The restriction coefficients are (c_T+d_T,c_T-d_T\). Thus the exact squared-restriction distance is

\[
L_i=\sum_T|(c_T+d_T)^2-(c_T-d_T)^2|=4A_i.
\]

For a monotone child (g\), its discrete derivative ((g^+-g^-)/2\) is the indicator of a pivotal edge. Consequently its first Fourier coefficient equals (I_i(g)=\alpha\) and its two restriction means are (\mu\pm\alpha\). This step would fail for a general nonmonotone child; monotonicity has been proved for this family.

For AND, split the Fourier indices of the other leaves of (g\) and of (h\) into empty and nonempty sets. On nonempty (g\) indices the sum of sibling square weights is

\[
\frac{(1+\mu)^2+(1-\mu^2)}4=p.
\]

The old constant-index term (4|\mu|\alpha\) must first be removed from (L_i(g)\). Empty-(g\), nonempty-(h\) indices contribute exactly (\alpha(1+\mu)(1-\mu^2)\). The absolute value here can be removed because (\alpha\ge0\) and (1+\mu\ge0\); it is not discarded by cancellation. The new mean depends on the old child mean with slope (p\), so the new constant term is (4|\nu|p\alpha\). Dividing by (p\alpha>0\) gives

\[
R_{j+1}=R_j-4|\mu_j|+2(1-\mu_j^2)+4|\mu_{j+1}|,\qquad R_j=L_i/I_i.
\]

For OR the sibling square multiplier and the influence multiplier are (1-p\); the empty-(g\) term is (\alpha(1-\mu)(1-\mu^2)\), again nonnegative. The same ratio recurrence follows. In particular, negative constant coefficients have not silently been replaced by their signed values, and mixed signs of other Fourier coefficients do not change the square multipliers.

With (R_0=0=\mu_0\), telescoping yields, exactly for every finite depth,

\[
R_d=2\sum_{j<d}(1-\mu_j^2)+4|\mu_d|\ge\tfrac32d.
\]

Division by four gives (A_i/I_i\ge3d/8\) for every leaf. For any finite (c>0\), choose an integer (d>8c/3\). All coordinates then violate the proposed estimate simultaneously. This is the required logical negation, not a specified-coordinate obstruction or extrapolation of a finite table. The independent read found no mathematical gap in this argument.

## Independent controls and provenance

The author's script and stored result were read, not executed. Their result records exact truth-table/Fourier/edge checks for depths 0–4 and all 31 coordinates. Those executions remain author evidence.

I wrote `independent_checks.py` afresh, without importing or executing author code. Its one actual mathematical run, `runs/20261015T094830.926423Z/`, passed. The executed script is SHA-256 `cbc586b31ebf660d78443c381e5206e320deb7161d9697c286098be60669e2da`. It uses exact rational arithmetic and SymPy 1.9 and performs:

- Seven symbolic identities for the restriction factor and both gate signs, including square multipliers, constant differences and mean slopes.
- A different coefficient construction by multiplying disjoint gate polynomials, checked against direct truth/physical-edge evaluation for depths 0–4, all 31 coordinates. Direct character sums and restricted spectra are additionally checked through eight variables, covering 15 coordinates; I do not claim direct restricted-spectrum enumeration for the sixteen-variable case in this independent script.
- All 20 monotone three-variable functions, both gates and every coordinate: 84 essential recurrence cases and 36 zero-influence cases checked without division.
- Exact scalar recurrence through depth 16. This is finite diagnostic evidence; the written induction, not this loop, addresses arbitrary depth.

Seven incorrect variants actually raised and recorded their expected AssertionErrors: missing factor four; missing absolute values; signed terminal mean; replacing coordinate influence by total influence; treating one bad coordinate as the negation of existence of a good one; dropping bias control; and applying the monotone identity to parity. The all-essential five-variable product example in the fifth control has ratios (1,1,1,1,0\), explicitly retaining an essential good coordinate. `RESULT.json` and the seven `REJECTED-*.json` retain the actual observations. No unexpected mathematical checker failure occurred.

One later metadata-capture assertion did fail: I had incorrectly included README among files presumed unchanged between v1 and v2. The new README was in fact changed to describe v2, while the manuscript and two control files were unchanged. I recorded the actual assertion, then read and diffed the new README and ran a corrected byte-scope validation. This was my capture assumption, not a mathematical failure or evidence of an undisclosed theorem change. `CONTROL_HISTORY.md` preserves it.

## Current-primary screen and its limits

The separately detailed `LITERATURE_SCREEN.md` records actual inspected scopes and queries. In the inspected [González–MacManus–Pereyra v2](https://arxiv.org/html/2606.00246v2), Proposition 5.1 produces a bad specified splitting coordinate, and Section 5.2 supplies a different good coordinate for those examples. The normalization there is compatible with (L_i=4A_i\); those examples alone do not negate Han's existence quantifier. I read the relevant displayed proposition proof and selected surrounding sections, not independently audited the entire thirty-page paper.

[O'Donnell–Tan](https://arxiv.org/abs/1304.1347) already establish FEI for bounded-arity read-once formulas. I checked the introductory theorem and the Section 4.1 structural statement, not their entire composition proof. The new auxiliary obstruction lies inside that class and makes no contrary FEI claim. The recent [threshold/composition paper](https://arxiv.org/abs/2610.16069v1), [percolation paper](https://arxiv.org/abs/2609.15388v1), and [plateaued-functions paper](https://arxiv.org/abs/2609.21563v1) were inspected only in the specific metadata, introductory, selected-section and keyword scopes documented in the ledger. No exact prior all-coordinate negative answer was identified in those inspected scopes or the bounded searches. This is not a comprehensive citation graph, a full audit of those papers, or proof of priority.

The eight local primary/discovery files were copied from the author's previously downloaded evidence, with byte counts and hashes verified. They are not claimed as fresh reviewer downloads. I separately opened official primary pages and relevant text in the web tool. The author-reported OpenAlex budget exhaustion and Semantic Scholar HTTP 429 were not independently repeated. The copied OpenAI overview file was hash-checked but not independently searched or audited in this review.

## Finding and resolution retained

**F1, factual screen-scope error:** v1 map described a 100-entry Fourier-title Atom result, while XML parsing shows only 29 entries. The request parameter `max_results=100` was an upper limit; it was not the returned count. The broad second feed has 100 entries. These counts and parsed metadata are retained in `FEED_ENTRY_COUNTS.json`. The error affects discovery-scope reporting, not the arbitrary-depth proof. The author preserved v1 and made v2 with the correct 29-entry statement. I verified the one-field map diff and all v2 manifest bindings. No proof or target change was needed. V2's new README and revision note accurately disclose the correction; the immutable v1 error is not retroactively erased.

No unresolved mathematical objection remains for the exact auxiliary claim. This decision does not authorize a README solved entry, a submission, publication, a Release, a score of four, or any extension to full FEI. No such action, Git write or Lean execution was performed.
