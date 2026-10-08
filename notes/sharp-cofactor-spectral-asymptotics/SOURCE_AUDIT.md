# Source and scope audit

Checked through 8 October 2026. This is a finite literature audit, not a claim
of exhaustive priority verification. Source PDFs and full-text mirrors are not
included in this package.

## Prior inputs and accessible versions

- Drury, “A counterexample to a question of Bapat & Sunder”, Mathematical
  Inequalities & Applications 21 (2018), 517–520,
  https://doi.org/10.7153/mia-2018-21-37 . The publisher full text at
  https://files.ele-math.com/articles/mia-21-37.pdf was read. It supplies an
  order-eight finite cofactor counterexample. The assertion with constant one
  was therefore already false; this package does not claim that disproof.
- Pate, “Group algebras, monotonicity, and the Lieb permanent inequality”,
  Linear and Multilinear Algebra 40 (1996), 207–220,
  https://doi.org/10.1080/03081089608818438 . Publisher metadata and abstract
  were checked. The abstract displays the first-compound indicator refinement;
  the full article was not obtained. Our paper gives an independent complete
  double-coset contraction proof, so no inaccessible theorem is a proof premise.
  The 1996 volume date is used, not the later online-posting date.
- Neuberger, “Norm of symmetric product compared with norm of tensor product”,
  Linear and Multilinear Algebra 2 (1974), 115–121,
  https://doi.org/10.1080/03081087408817047 . Bibliographic metadata was checked;
  the full paper was not read. It is background for the classical symmetric-
  tensor contraction method. The needed identities are proved here.
- Pioge, Pietrasz, Seron, Novo, and Cerf, “A logical implication between two
  conjectures on matrix permanents”, Linear Algebra and its Applications 725
  (2025), 309–318, https://doi.org/10.1016/j.laa.2025.07.011 . The author
  preprint https://arxiv.org/abs/2508.00111v1 was read, including its precise
  cofactor conventions, local Hadamard expansion, and real-Rayleigh distinction.
  Publisher metadata was verified. The institutional typeset PDF endpoint
  https://quic.ulb.ac.be/_media/publications/2025-laa-725-309.pdf was unavailable
  in the retrieval attempts; no claim of a line-by-line formal-version check
  is made.
- Wanless, “Lieb's permanental dominance conjecture”, The Physics and Mathematics
  of Elliott Lieb, volume II (2022), 501–516,
  https://doi.org/10.4171/90-2/48 . The fixed author manuscript
  https://arxiv.org/abs/2202.01867v1 was read. It distinguishes full arbitrary-
  subgroup character dominance, ordinary immanants, cofactor spectra, and the
  full Schur-power permanent-on-top assertion. These are not interchangeable.

The preceding public unboundedness result of this research is preserved in
its existing history at
https://github.com/mxym/math/tree/7c214a69a6a14e04096c132b380ae3710c9d7cac/notes/cofactor-spectrum-unbounded .
The present package is a subsequent sharp-extremal stage; it does not rewrite
that earlier theorem or its proofs. The project had also already established
the CP1 ordered-row rank-two endpoint lower construction. Its proof is reproduced
in the present manuscript to make the new matching upper-constant result
self-contained, rather than relabeling the old disproof as new.

## Main conjecture status and limited exclusions

The latest checked primary preprints were
https://arxiv.org/abs/2608.21749 (arbitrary subgroups in order four) and
https://arxiv.org/abs/2609.13412 (ordinary irreducible immanants through order
fifteen). Neither is a full Lieb/Marcus resolution. Author-maintained pages
https://yair-lavi.com/mincs-list/conjecture-42/index.html and
https://yair-lavi.com/mincs-list/conjecture-9/index.html still list the unrestricted
questions as open; unlinked local claims on those pages are not treated as
proved inputs. Ordinary rank-two/two-row immanant dominance is classical and
is discussed in the checked Wanless survey.

Pate's older block results require care with variables: his block count is not
always the variable used for block size in later summaries. Our stage summary
uses m=number of blocks and k=block size and proves its own factorial exclusion.
It does not rely on a swapped-parameter interpretation of an asymptotic theorem.

## Pate 2008: unresolved full-text qualification

The publisher abstract of “On permanental compounds”, Linear Algebra and its
Applications 429 (2008), 1093–1101,
https://doi.org/10.1016/j.laa.2007.05.019 , was checked. It advertises a binary-
vector assertion for complementary permanental compounds. The publisher PDF
and text API could not be retrieved; ResearchGate explicitly had no full text,
and OpenAlex supplied no repository copy. The original theorem's full
qualifications and any correction were therefore not verified.

Our separate internal calculation disproves only the following unrestricted,
explicitly defined statement: for every Hermitian PSD B and every binary x,
x* C_k(B)x<=||x||² per B, where
C_k(B)[I,J]=per B[I,J] per B[I^c,J^c]. It is not attributed as a disproof of Pate's
actual theorem. That calculation is not an input to this paper and its data are
not part of the minimal public package. The first-compound result used here has
its own complete proof.

## Search boundary for the new quantitative assertions

Searches included cofactor spectrum growth, logarithmic cofactor eigenvalue
bounds, Bapat–Sunder amplification, relevant permanental-compound literature,
and the 2023–2026 bosonic perturbation papers already examined in the preceding
source audit. No source with the same sharp asymptotics R_N~log N and
R_N^R~(1/2)log N was located in this finite search. This is a search result, not
proof of worldwide priority. Global Hadamard amplification and full Schur-power
spectral amplification are different quantities and are not claimed as new here.
