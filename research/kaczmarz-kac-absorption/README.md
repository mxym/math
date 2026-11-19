# Two time scales for the Kaczmarz–Kac walk

**Yongxian Zhang.** Research note, with AI assistance and an independent internal mathematical review. Not externally peer reviewed; priority is not guaranteed.

* A well-conditioned matrix can still take about $\binom n2\log n$ random pair updates to attain fixed determinant accuracy. For every fixed condition-number cap $K>1$, error $0<\varepsilon<1$, and required success probability $0<p<1$, this is the worst-case time, up to an additive $O_{K,\varepsilon,p}(n^2)$. A rational two-column block repeated in disjoint planes disproves the faster determinant-time conjecture of Detherage and Shah. The upper direction uses their previously proved potential contraction.
* In exact arithmetic the finite walk eventually **stops** in every rank: every row is a signed member of one orthonormal basis of the original span. This answers Steinerberger's finite overdetermined terminal-configuration question; the rough hitting-time upper bound here is not the sharp approximate-accuracy time above.
* In a plane the surviving orthogonal cross is selected by the initial proportions, and for $m$ initially distinct crosses the mean number of single-pair updates to absorption is exactly $(m-1)^2$. These are consequences of the complete-graph voter model, not new voter-model formulas.

Read the [proof](PROOF.md), [sources and scope](SOURCES.md), and [internal review](REVIEW.md). The public proof differs from the internally signed draft only by a correction of author order. This note does not address finite precision, the continuum mean-field question, or optimal dependence on varying accuracy or condition number.

From this directory, run `sha256sum -c SHA256SUMS` and `python3 -O verify.py`. Compare with [the expected output](CHECKS.txt). The examples supplement the proof; no numerical fit or simulation is used.
