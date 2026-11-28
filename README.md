# Chollet's permanent inequality in complex order eleven

This isolated source archive is for catalogue problem **#072**. For arbitrary \(11\times11\) complex Hermitian positive semidefinite matrices \(A,B\), the [proof](FactorCholletOrderEleven.md) establishes
\[
\operatorname{per}(A\circ B)\leq \operatorname{per}(A)\operatorname{per}(B),
\]
where \(\circ\) denotes entrywise multiplication. There is no rank, real-entry, or zero-pattern hypothesis. If both diagonals are strictly positive, equality holds exactly when both matrices are diagonal. If either has a zero diagonal entry, both sides vanish.

The proof reduces to the self-Hadamard inequality for a normalized correlation matrix and splits according to the maximum off-diagonal modulus \(r\). Random principal-block averaging and retained permutation-overlap estimates cover \(r\le21/50\); a rational double-border schedule covers \(417/1000\le r\le1\). The ranges overlap, with exact interval endpoints. The redundant endpoint calculation is accompanied by the direct \(r=1\) analytic strictness step.

[McBee, *Chollet's permanent conjecture through order ten*](https://hexagonmath.org/pdf/2611.01163v1) proved the unrestricted result through order ten, introduced the two-border geometry used here, and described the still-uncovered intermediate order-eleven range. We keep the order-7/9 McBee schedules credited separately from the new order-11 schedule. The finite paper proof also cites the one-border base argument of [Li, Zhao and Luo](https://www.preprints.org/manuscript/202608.2196), [Lieb's block inequality](https://doi.org/10.1512/iumj.1967.16.16008), and the [four-point permanent estimate of Grone and Pierce](https://doi.org/10.1137/0609016).

### Reproduce

Use ordinary Python 3.10 or later without optimization flags. No extra libraries or external schedule files are required. From this archive:

~~~sh
sha256sum -c MANIFEST.sha256
python3 verify_factor_chollet_small_entries.py --additional
python3 verify_factor_chollet_double_border.py
python3 verify_factor_chollet_support_independent.py
python3 independent-chollet-eleven-split.py
~~~

The first two scripts replay the author-side inequalities. The third is a separately implemented finite check of the combinatorial identities on small graphs and does not substitute for their general proof. The fourth is the independent author-external interval check; it changes the small-entry coordinate, the finite partition, and the large-entry basis and determinant calculation. It intentionally shares the 15 rational order-11 schedule knots and takes the analytic inequalities as inputs. See [RELEASE_NOTES.md](RELEASE_NOTES.md) and [REPLAY.txt](REPLAY.txt).

**Orders 12 and 13 are partial only.** The additional checks give the small-entry self-Hadamard bound for \(r\le2/5\) in order 12 and \(r\le3/8\) in order 13. For the two-factor version after positive-diagonal normalization, the respective cap must be imposed on both correlation matrices. The full problems at those orders and higher, and the all-order conjecture, are not claimed. The interval checks use exact rational/integer arithmetic, not Lean.
