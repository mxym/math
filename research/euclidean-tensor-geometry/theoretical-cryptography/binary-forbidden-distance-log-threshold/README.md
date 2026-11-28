# A logarithmic reduction in the dimension bound for binary forbidden distances

Jiang and Yang proved the exact size and all extremizers for binary codes avoiding one even distance \(n-t+1\) once \(n\ge(t+1)^2\). Their proof supplies a more general finite binomial condition. We find its exact asymptotic threshold, including the second-order shift.

Put \(N=n-1\), with \(N\equiv t\pmod2\). As \(t\to\infty\), the least \(N\) satisfying [Jiang–Yang, Eq. (4.10)](https://arxiv.org/html/2611.04523v1) is
\[
 \frac{t^2}{2\bigl(\log t-\tfrac32\log\log t-\log(4\sqrt\pi)+o(1)\bigr)}.
\]
For every larger admissible \(N\), their exact size formula and parity-ball characterization apply. This improves the stated sufficient dimension by a logarithmic factor. It does **not** give the optimal threshold of the original extremal problem.

Run `sh replay.sh` to reproduce the exact finite threshold checks and an independent numerical window check.
