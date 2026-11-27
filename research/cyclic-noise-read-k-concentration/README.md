# Read-multiplicity concentration for binary cyclic convolution

This note applies the established read-\(k\) concentration theorem to the fixed-factor, independent-Bernoulli model in the noise-weight question of Bombar, Resch and Wiedijk (ePrint 2025/018, extended §1.2). It does not assume that the output coefficients are independent.

Let \(Y=\sum_j t_jR_j\) in \(\mathbb F_2[X]/(X^n-1)\), where each \(t_j\) is fixed and the \(R_j\) have independent Bernoulli coefficients (possibly a different parameter for each block). In a fixed set \(I\) of \(m\) positions, write \(W_I=\sum_{i\in I}Y_i\), \(p=\Pr(Y_i=1)\), and let \(k_I\) be the maximum number of positions of \(I\) affected by a single input bit. Then
\[
 \mathbb E e^{\lambda W_I}\le (1-p+p e^{k_I\lambda})^{m/k_I}
\]
for every real \(\lambda\), with deterministic cases treated separately. Consequently each one-sided tail is bounded by \(\exp[-m D(q\Vert p)/k_I]\) on its appropriate side of \(p\). On the full cycle \(k_I=\max_j\mathrm{wt}(t_j)\); for a window or other restriction it can be smaller. Cyclic subgroup supports attain the moment bound, so the read parameter cannot generally be removed.

[Proof](PROOF.md) · [Source and scope](SOURCES.md) · [Exact replay output](RESULTS.txt)

The conclusion concerns an abstract coefficient-noise model, not fixed-weight inputs, a decoder, or a security guarantee for any cryptosystem. The general concentration inequality is prior work; the contribution here is identifying and counting the reads in this model, and exhibiting sharpness within it.

Replay using Python 3 and a POSIX shell: <code>sh replay.sh | diff -u RESULTS.txt -</code>. The two checkers use coefficient-state enumeration and rational Fourier inversion respectively. They check small cases; the proof establishes the theorem for all parameters.
