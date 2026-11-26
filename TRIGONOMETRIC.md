# Exact trigonometric singlet counts for every spin and allowed twist

Use the spin-\(\ell/2\) model in [Hagendorf §§3.1–3.2 and 3.5](https://arxiv.org/pdf/1207.0357), \(d=\ell+2\), \(\ell\ge1\). The momentum sector is the eigenspace \((-1)^{N+1}\) of the indicated twisted translation. Under the allowed twists of Eq. (15), the classification is:

- Zero twist: at odd length exactly one state per magnetization \(M=-\ell/2,-\ell/2+1,\ldots,\ell/2\); at even length none.
- Any nonzero allowed twist: exactly one state at \(M=0\) at each even length, none at odd length.

The paper gives a periodic Witten index and anticipates the odd-length periodic pattern. The open-chain problem is related but different; see [Hagendorf–Liénardy](https://arxiv.org/abs/1612.02951). For the fermion counterparts and the lower-spin XXZ cases see [Fendley–Nienhuis–Schoutens](https://arxiv.org/abs/cond-mat/0307338) and [Razumov–Stroganov](https://arxiv.org/abs/cond-mat/0102247). We compute the signed spin-chain sectors rather than the full Hamiltonian on other momenta.

## Truncated-polynomial realization

Index the local dual basis \(e_i\) by \(1\le i\le d-1\); its corresponding physical letter \(i-1\) has magnetization \(i-d/2\). The coefficients of the split in Eqs. (14),(18) give the dual product
\[
e_i e_j=\sqrt{[i+j]/([i][j])}\,e_{i+j}\quad(i+j<d),
\]
and zero otherwise, with the sine quantum integers nonzero in the indicated range. Sending \(e_i\mapsto z^i/\sqrt{[i]}\) identifies this with the augmentation ideal of \(A=\mathbb C[z]/(z^d)\). Put \(\eta=e^{i\phi}\). The condition \(e^{i\phi d/2}=1\) means the local phase on this ideal is \(\eta^i\), up to inversion in the cyclic convention, and \(\eta^d=1\). In the allowed range a nonzero twist has \(\eta\ne1\). Fix the positive preserved weight \(w=M+dN/2\). The [cyclic normalization argument](CYCLIC-NORMALIZATION.md) identifies the dimension with \(HC_{N-1}^{\theta}(A)_w\), where \(\theta(z)=\eta z\). Only \(\theta\)-invariant weights enter.

## Hochschild calculation and cyclic reduction

Use the standard periodic free bimodule resolution of the truncated polynomial algebra; see [the resolution for truncated polynomials](https://doi.org/10.1016/j.topol.2013.06.010). The two differentials alternate
\[
z_L-z_R,\qquad \sum_{j=0}^{d-1} z_L^{d-1-j}z_R^j,
\]
with generator weights \(md\) in degree \(2m\) and \(md+1\) in degree \(2m+1\). Tensor with the twisted bimodule: the differentials are \((1-\eta)z\) and \((\sum_{j=0}^{d-1}\eta^j)z^{d-1}\), up to swapping \(\eta\) with its inverse. The resolution is equivariant with the displayed weights, and finite invariants are exact.

At \(\eta=1\), the odd differential is zero and the even one is \(dz^{d-1}\). For every positive weight \(w=md+j\) with \(1\le j\le d-1\) there is one Hochschild class in each of degrees \(2m,2m+1\), and no other class. At \(\eta\ne1\) the even differential is zero and the odd one is a nonzero scalar times \(z\). The only positive weights are \(w=md\), \(m\ge1\), with a one-dimensional pair in degrees \(2m-1,2m\). These weights are invariant.

At any such weight suppose the pair of Hochschild classes is in degrees \(r,r+1\). The cyclic coinvariant chains at positive \(w\) may be taken unit-free, and thus vanish above degree \(w-1\). From the [Connes SBI exact sequence](https://math.mit.edu/~hrm/palestine/weibel/09-hochschild_and_cyclic_homology.pdf), cyclic homology is zero below degree \(r\), and \(HC_r=HH_r\). Above the pair, the periodicity map is an isomorphism from \(HC_s\) to \(HC_{s-2}\) for \(s\ge r+3\). Eventual vanishing forces zero in all degrees \(>r\), including \(r+1,r+2\). If there is no Hochschild pair, the same sequence gives zero in every degree. Consequently at zero twist \(N=2m+1\) and \(M=j-d/2\); at nonzero twist \(N=2m\) and \(M=0\). This proves the full stated count.
