# Sources, versions and reproducibility

- Sascha Kurz, [*Additive codes attaining the Griesmer bound*, arXiv:2412.14615v3](https://arxiv.org/html/2412.14615v3), 8 May 2026, Appendix E **Remark 18** following Table 18, asks for a projective additive \([66,5,\{48,56\}]_4\) code and specifically for a 66-line partition of the referenced binary \([198,10,\{96,112\}]_2\) point set. The equation linking the binary point expansion and additive line spectrum is standard in that work. The [Bayreuth published version, DOI 10.15495/EPub_UBT_00008788](https://doi.org/10.15495/EPub_UBT_00008788) numbers the question Remark 17 (printed page 109); the earlier Bayreuth preprint numbers it Remark 15. These are the same two questions, not separate claims.
- Axel Kohnert, [*Constructing two-weight codes with prescribed groups of automorphisms*](https://www.mathe2.uni-bayreuth.de/axel/twoweight07.pdf), Discrete Applied Mathematics 155(11), 1451–1457 (2007), [DOI](https://doi.org/10.1016/j.dam.2007.03.006), Table 3, is the source cited for the known binary parameters and multiplicities \(96^{825},112^{198}\). The generator used here is the exact published SageMath 10.8 [two-weight database entry](https://github.com/sagemath/sage/blob/10.8/src/sage/coding/two_weight_db.py), credited there to Eric Chen's database. This is one fixed representative of those binary parameters, not an assertion that all codes with those parameters are equivalent.
- Sascha Kurz, [*Computer classification of linear codes based on lattice point enumeration and integer linear programming*, arXiv:2403.17509v1](https://arxiv.org/pdf/2403.17509v1), Proposition 1, [published DOI](https://doi.org/10.1007/978-3-031-64529-7_11), excludes a projective \(\mathbb F_4\)-linear \([66,5,\{48,56\}]_4\) code. It does not exclude this additive one.
- Kanat Abdukhalikov and Duy Ho, [*On the equivalence between additive and linear codes*, arXiv:2603.15071v2](https://arxiv.org/html/2603.15071v2), Theorems 3.2–3.4 and equation (2), give the line-stabilizing algebra criterion and its augmented linear-system computation. They are credited for the general test; the ranks recorded here concern the explicit partition.

A bounded check on 2026-11-27 used the full Kurz titles, arXiv versions, “198 points”, “66 lines”, “48,56” together with “additive” or “two-weight”, and the equivalence-test paper. The 2026 arXiv v3 still lists the questions. No matching line partition or additive construction was found in the checked sources; no priority claim is made.

## Optional provenance from the public source

The mathematics replay is offline and needs only the new partition. To reproduce its identification with the public record, save [the exact tagged source file](https://raw.githubusercontent.com/sagemath/sage/10.8/src/sage/coding/two_weight_db.py) as `two_weight_db.py` outside this package, then run:

~~~sh
python3 verify_independent.py --sage-file /path/to/two_weight_db.py
~~~

- Raw SageMath file length: 23,363 bytes
- Raw SageMath file SHA-256: `842b8cbc8f3c9f0c1ac284b8ee3d0f46d45049f26ce9415ca03cebbf645f4d82`
- SageMath Git blob SHA-1: `8b546714bd25b3a71944995c5f823034293d3943`
- Canonical 10×198 record SHA-256, each binary row followed by LF: `898853c72c714e715a2d1d67a57180f903648746738ae07a79746b52ce9510b5`
- Sorted column labels SHA-256, one base-10 integer and LF per label: `e6f3575e9d60d73ee0791f27c29f3fac5d95c9318548a0436e83cb87d46d691e`

The optional parser treats the Sage source as bytes only; it neither imports nor runs it. No third-party source file or extracted generator text is bundled.
