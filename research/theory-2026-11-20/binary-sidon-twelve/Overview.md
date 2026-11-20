# Twelve-dimensional binary Sidon sets: improved upper bound 79

The unrestricted interval is now **66–79**. The [new proof](upper79/README.md) rules out size 80 starting from the exact classification of dimension-eleven extremizers. Signed Fourier-moment inequalities and an independent reduction via Jaffe’s code theorem reduce size 80 to two types of 11-dimensional sections. Both are ruled out by two independently implemented exact searches; no automorphism or graph assumption is made. The 66-point lower witness is unchanged, and the exact maximum remains open.

The optimal binary linear minimum distances are **4** for `[79,67]` and **5** for `[80,67]`, closing the gaps in [Grassl’s 79-column table](https://www.codetables.de/BKLC/BKLC.php?q=2&n=79&k=67) and [80-column table](https://www.codetables.de/BKLC/BKLC.php?q=2&n=80&k=67). Distance at least five for `[79,67]` would yield 80 Sidon points in dimension twelve; distance at least six for `[80,67]` would puncture to the former forbidden code. The archive checks a rank-13 `[80,67,≥5]` witness.

[Proof and checks](upper79/README.md) · [Frozen replay ZIP](upper79/Sidon12_no80_upper79_v1.zip), SHA-256 `2b20bed8bdb697e0e9850e46b6125c458acd1c3bae9342768697ee4c55cb7297`. In the extracted `sidon12_no80` folder, the audit command checks all 82 exact inequalities, every archived per-engine ledger entry and positive controls; the full command independently reruns both engines on 2,419 source keys. The original exact per-engine results agree on every key. Neither search is truncated.

The preceding [upper bound 80](upper80/README.md), [upper bound 81](../binary-sidon-eleven/exact48/classification/Overview.md) and [upper bound 83](README.md) proofs remain available.
