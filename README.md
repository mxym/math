# Exact guessing probability for almost-qudit sources

This proves the tightness conjecture following Eq. (221) in
[de Oliveira Junior et al., arXiv:2610.20725v1, §IV.7](https://arxiv.org/html/2610.20725v1#S4).
For $n$ equiprobable labels whose emitted states each have population at
least $1-\epsilon$ in the same $d$-dimensional subspace, $1\le d<n$,
the worst-case correct-label guessing probability is exactly
$$
 \left(\sqrt{\frac dn(1-\epsilon)}+
             \sqrt{\left(1-\frac dn\right)\epsilon}\right)^2
 \quad\text{for }0\le\epsilon\le1-\frac dn,
$$
and equals 1 at or above the threshold. A Fourier projection and a fixed
basis measurement attain the bound for every $n,d,\epsilon$.

An independent dimension-free upper proof permits mixed states and an
input-independent classical flag, including a single leakage average
over flags and labels. A separately stated extension gives an exact
finite allocation formula and an attaining ensemble for arbitrary priors
and unequal per-label population bounds. See the proof for $d=0$,
$d\ge n$, and feasibility edge cases.

Only an input-label guessing probability is being computed. When the
specified population bound covers the entire system available to the
observer, the result can calibrate the leakage parameter in
[Mishra et al., arXiv:2610.37296v1](https://arxiv.org/html/2610.37296v1).
It does not bound a correlated observer's joint system from its signal
marginal alone, certify any device, or give a coherent-attack or key-rate
theorem.

See [PROOF.md](PROOF.md), [SOURCES.md](SOURCES.md), and the frozen
[replay log](RESULTS.txt). Run `sh replay.sh` with Python 3 and
NumPy. The exact checker uses only the standard library; the independent
numerical checker tests physically realized matrices and the scalar
allocation rule.
