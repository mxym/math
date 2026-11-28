# Lieb's permanental dominance for the natural A₆ action

This isolated source slice accompanies catalogue **#071**. The [paper](FactorLiebAlternatingSix.md) proves the inequality for the natural alternating subgroup \(A_6\le S_6\), every character of that group, and every \(6\times6\) complex Hermitian positive semidefinite matrix. Its new argument concerns the two degree-eight split characters and gives the explicit gap \(\sum_{i<j}|a_{ij}|^2/10\) on correlation matrices, with equality only for diagonal matrices after positive-diagonal normalization. The other characters follow from the known ordinary \(S_6\) immanant inequalities and the sign-twist average. There is no rank, real-entry, or zero-pattern restriction.

This does not settle all subgroups of \(S_6\), the all-order Lieb conjecture, or the distinct permanent-on-top problem. The source notes credit [Lieb](https://doi.org/10.1512/iumj.1967.16.16008), [Heyfron's ordinary immanant range](https://doi.org/10.1017/S030500410006953X), the [ordinary \(A_6\) character table](https://arxiv.org/pdf/math/0703288), and the differing earlier subgroup results. The reported order-five general-subgroup result is not a proof input.

### Reproduce

~~~sh
sha256sum -c MANIFEST.sha256
python3 verify_factor_lieb_alternating_six.py
python3 independent-lieb-alternating-six.py
~~~

Use ordinary Python 3 with assertions enabled; no third-party libraries. See [REPLAY.txt](REPLAY.txt) for the pinned replay output. This archive is intentionally limited to the six-point theorem rather than other subsequent orders.
