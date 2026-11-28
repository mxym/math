# v1.0.0 source-slice notes

## Joined six-orbit classification

The enlarged admissible class is proved in research commit `b335081a1fc3f41d393c78851f4a2b2c87fcac16`: for any graph in the part-preserving free abelian class with at most six vertex orbits and no cycles of lengths 4, 8, 16, the quotient is exactly simple \(K_{3,3}\). The 798-vertex minimum and three equality graphs below therefore apply to that larger class. The separate subdivided-tetrahedron result is unchanged. The previous fixed-base staged snapshot is preserved at `bf87b606d4fcfb2870a0b148d71fd928389891be`; it is not needed as a separate release.

The main Node certificate replay passes 6, 31 and 6 relation states (20, 164 and 20 possible prefix-collision pairs in the deduplicated certificate), and the independent Euclidean row-Hermite replay passes all 7, 57 and 7 occurrences, checks all 190 reduced input matrices and rejects omission of any root branch. The old four-fiber corner is reproduced by a separate 17-state check. These are evidence for universal voltage statements, not brute checks of finitely many selected group orders.

## Fixed-base source and prior results

## Results and provenance

* Research branch source frozen at `7f525536c779f9e0720dbf74ef8da86b909db2a6`.
* \(K_{3,3}\) fixed-base minimum 798: 166,344,289 lower-index kernels, 2,896,000 equality-index kernels, 56 labeled-base maps, three abstract lift graphs.
* Once-subdivided \(K_4\) fixed-base minimum 95: 4,178 lower-index kernels, 381 equality-index kernels, exactly four 19-sheet maps in one orbit. The existing 19-sheet witness is Davis's, not a new construction.
* Rooted \(K_{3,3}\) companion: all regular abelian covers have a suitable dyadic cycle through every vertex; the elementary-abelian examples and minima are separate restricted-class results. The class-two companion is supporting context, not a claim of nonabelian minimum orders.
* The finite census is a joint project result: original synthesis and optimized Node verifier from the project research Dreamer, independently checked with fresh Python half words, modular masks and concrete lift graphs.

## Exact replay receipts

* Guarded primary bit-set verifier: one complete \(1\)–\(133\) replay; the version in this archive, with an extra multiplicative count assertion, replayed \(1\)–\(102\) (59,193,424 kernels) and \(103\)–\(133\) (110,046,865 kernels) to completion. All indices \(1\)–\(132\) excluded, index \(133\) has 56.
* Separate Python HNF implementation: independent short clauses derived by half-path pairing and exact quotient reduction, not read from Node. It used both portable integer and exact NumPy mask modes; the portable exact replay completed all rows 1–63, a further exact array replay completed 64–102 with 50,665,920 kernels, and the exact array replay completed 103–133 with the expected high-range counts and no survivors before 133. The stock file was also rerun on 132–133. Thus the later independent checks cover the entire 1–133 range in three parts; the manuscript conservatively records the partial independent coverage available when its research commit was frozen.
* Independent default Python: full two-character CRT equality census at index 133, coverage orbits \(24,24,8\), three literal trace pairs and literal \(32\)-cycles. Literal half-path check of all 4,559 subdivided-\(K_4\) covers through index 19. Both passed.
* Rooted companion checker passed in normal Python: all three elementary-abelian quotient tables and the concrete \(\mathbb F_7^3\) witness. Two-orbit companion passed 23,660 exact assertions across 9,555 triples. Class-two companion passed the fixed-word collision tables and both odd-order sharpness examples.
* [MANIFEST.sha256](MANIFEST.sha256) covers every artifact except the manifest itself. Programs are exact replays, not stand-alone published mathematical claims, and not Lean formalizations.

No conjecture about arbitrary cubic graphs or arbitrary regular covers is claimed.
