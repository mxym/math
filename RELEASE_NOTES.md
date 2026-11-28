# v1.0.0 source-slice notes

## General free abelian six-orbit classification

Source frozen at research commit 96cfd77f04048d6d643a9bae7a7e65a5749d7265. The theorem applies to all graphs satisfying the stated free abelian action and minimum degree conditions, including nonbipartite inputs and actions not assumed to preserve a bipartition. Excluding simple 4-, 8-, and 16-cycles forces precisely the simple \(K_{3,3}\) quotient, then the 798 minimum and three equality graphs by the fixed-base census. The 95-vertex fixed-base result is separate and unchanged.

The standard-library normal replay uses 130,348 labeled cubic quotient configurations in 291 isomorphism classes. The 290 non-\(K_{3,3}\) classes use 4,639 nonterminal exact integer-relation states, maximum depth five. Four distinct extra-orbit charts on \(K_{3,3}\) account for 7, 19, 43 and 10 nonterminal states, depths 1, 2, 5 and 2, respectively. This is a universal relation calculation, not a test over sampled orders, ranks, or exponents of abelian groups.

An independent author-external replay constructs the 156 simple support graphs by isomorphism-rejected edge augmentation and checks relation containment using a SymPy column-Hermite calculation, without importing the main checker. It reproduced the 130,348 configurations, 291 classes, 290 rejected classes, all 4,639 states, all four extra-orbit charts and the maximum depths. A second author-external review used a separate ternary multiplicity enumeration and exact Bareiss determinant/gcd index membership for all relation states; it also checked the disconnection reductions and each extra family. Replays of the included three-, four- and five-orbit predecessors passed in normal mode; the latter two cover 15/109 and 62/378 templates/nonterminal relation cells. These predecessors supply the quotient-component reduction.

## Supporting narrower classification

The previous part-preserving proof, frozen at b335081a1fc3f41d393c78851f4a2b2c87fcac16, is included with its independent Euclidean row-Hermite verifier. The main Node replay checks 6, 31 and 6 distinct relation states; its independent Python counterpart checks 7, 57 and 7 state occurrences, and all 190 reduced matrices. The old four-fiber corner uses a separate 17-state check. Optional supporting replays:

```sh
node verify_erdos_gyarfas_six_layer_extremal.mjs
python3 verify_erdos_gyarfas_six_layer_extremal_independent.py
python3 verify_erdos_gyarfas_bipartite_four_corner.py
python3 verify_erdos_gyarfas_class_two.py
```

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

The main theorem assumes a free abelian action with at most six vertex orbits. The census concerns the two displayed fixed bases, not arbitrary regular covers.
