# Finite alphabet clarification for the constant-pass lower bound

This supplements Section 2 of the fixed [constant-pass proof at 09dead42499780e321e58b7b995a547af89d2dec](https://github.com/mxym/math/blob/09dead42499780e321e58b7b995a547af89d2dec/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-constant-pass-memory-lower-bound.md). The theorem and its constants up to the stated dependence are unchanged. The finite alphabet can be chosen at a controlled size, without using an unbounded limit of the coding alphabet at fixed \(d\). This also directly meets the width-padding convention in [Lyu–Tal–Wu–Yang, arXiv:2310.08070v1 §8.1](https://arxiv.org/pdf/2310.08070v1#page=40), which absorbs the authors' counters into a width at least \((10\log_2|\mathcal X|)^2\).

In both positive Fourier representations one can move all modes with \(\|u\|_\infty>d\) to the dummy. Their probability is at most a constant times
\[
 d\Bigl(\sum_{j\in\mathbb Z}b^{j^2}\Bigr)^{d-1}
       \sum_{|j|>d}b^{j^2}=e^{-\Omega(d^2\log d)}
\]
uniformly for \(b\le1/(100d)\). Indeed, after the first term the last sum is bounded by a geometric tail in \(b\), and the power of the theta sum is bounded. The constant includes the uniform reciprocal Fourier coefficient in the odd case; the binary low-rank mode deletion is as before.

Counting the discrete mode, the coefficient, and, for the odd case, the grid translate, the finite public row support has cardinality at most
\[
 R_0=((2d+1)^d+1)q^{2d}.
\]
Use uniform row and concept alphabets of size \(2^n\), with
\(n=\lceil \log_2R_0+C d\rceil\), where \(C>0\) is any sufficiently large fixed constant. Allocate row labels to rounded row probabilities using integer counts that differ from each \(2^n\)-scaled probability by at most one, and map concept labels onto the \(q^d\) actual labels with fiber sizes differing by at most one. The prior density ratio changes by at most \(q^d 2^{-n}\), and the row law's TV changes by at most \(R_0 2^{-n}\); composing independent rows and reusing them on every pass thus changes the experiment by at most \(O((T+1)2^{-Cd})\) in addition to the high-frequency omission. The extractor inequalities retain their strict exponential slack. This construction uses \(n=O_q(d\log d)\) and the abstract extractor parameter satisfies \(r\ge c_q\sqrt{d\log d}\) for all the theorem's widths.

If needed, pad the simulated branching program with unreachable vertices to width at least \((10n)^2\); this is polynomial in \(d\log d\) and is much smaller than the admissible \(2^{c_P r^2}\). It has no effect on any transitions or posterior law. The real-valued response realization still freezes the same independent random table at each fixed row position, as before. These finite choices prove the same lower bounds.
