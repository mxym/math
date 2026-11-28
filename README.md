# Global certificates for consecutive even-degree rotation symmetric Boolean functions

We prove the certificate-complexity equality asked by Yuan Li and Jing Zhang in [arXiv:2610.17100v2, §10](https://arxiv.org/html/2610.17100v2#S10), and extend their known block-sensitivity formula to shorter lengths \(n\ge2d-1\) with one eligibility condition. For their cyclic XOR of consecutive length-\(d\) monomials \(F_{d,n}\), write \(n=q(d+2)+\rho\), \(0\le\rho<d+2\). If \(d\ge4\) is even and \(n\ge2d-1\), then
\[
 C(F_{d,n})=bs(F_{d,n})=
 n-\min\{\lceil\rho/2\rceil,\ h\text{ if }h\le q+1\},
 \qquad h=d+2-\rho.
\]
The minimum omits the \(h\)-term when \(h>q+1\). For \(q\ge\max\{2,d/2-1\}\), this agrees with their formula without the eligibility condition.

The main new part is the certificate upper bound at every input. Between long runs, an inclusion-minimal set of fixed zeros simultaneously kills all windows and leaves enough coordinates free. Inside each long run, one parity class of individually insensitive coordinates is already jointly free, in every derivative order. These two constructions add along the circle. The matching block-sensitivity bound uses their witnesses, with the single long-run construction extended when the competing gap construction is infeasible.

This is a global result for consecutive supports, not pointwise equality, a classification below \(2d-1\), or a result for arbitrary nonconsecutive supports.

Run `sh replay.sh` with Python 3 and GNU sha256sum. Compare stdout with RESULTS.txt; the scripts have no network or external data dependencies. The exact checker constructs free sets and tests restricted normal forms. The independent checker instead derives constancy of all small subcubes from truth tables and directly tests the lower witnesses across short and large lengths. Sources and priority boundaries are in SOURCES.md.
