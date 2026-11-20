# Twelve-dimensional binary Sidon sets: improved upper bound 80

The unrestricted interval is now **66–80**. The [new proof](upper80/README.md) excludes size 81 with no symmetry, graph or invariance assumption. Exact moment bounds reduce the putative set to four geometric profiles. Nineteen integer inequalities exclude three of them. The last profile is ruled out by two independent exact searches on each of its two cases. The previously known 66-point lower construction is unchanged; the exact maximum remains open.

The optimal binary linear `[80,68]` minimum distance is therefore **4**, closing [Grassl’s 4–5 bound](https://www.codetables.de/BKLC/BKLC.php?q=2&n=80&k=68). A distance-at-least-five matrix of 80 columns would give an 81-point Sidon set after adjoining zero. Distance four is attained by 80 distinct columns spanning the check space in the affine coset with first entry one.

[Full proof and checks](upper80/README.md) · [Frozen replay ZIP](upper80/Sidon12_no81_upper80_v1.zip), SHA-256 `37080023c020f2be050b5d376327f0a7a53b2d6bb4d8289e47cb1baf76708e1f`. In the extracted archive, `python3 -O replay.py --stage audit --jobs 2` validates certificates, recorded ledgers and positive controls; `python3 -O replay.py --stage full --jobs 3` additionally regenerates all 2,419 input sources with both implementations and reruns the exact negative search. In the 21+9 subcase both engines find 126 genuine 47-point joins; every one has largest section 32, above the required 30. The other subcase finds no legal layer under the required cap.

The preceding [upper bound 81](../binary-sidon-eleven/exact48/classification/Overview.md) and original [upper bound 83](README.md) proofs remain available.
