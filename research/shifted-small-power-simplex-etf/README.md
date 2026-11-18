# An explicit small-power bound for repeated simplices and equiangular tight frames

Fix a real equiangular tight frame (ETF) of $\ell$ unit vectors in $\mathbb R^d$ with common absolute inner product $\alpha$. For $N=k\ell+m\ge\ell$, $0\le m<\ell$, consider the energy of **any** $N$ unit vectors
$$E_{\alpha,p}(X)=\sum_{i\ne j}\big|(x_i\cdot x_j)^2-\alpha^2\big|^p.$$
Define $M=(\ell-m)\binom{k}{2}+m\binom{k+1}{2}$. For every
$$0<p\le \frac{1}{8\ell^2(M+1)^2}$$
the minimum is $2M(1-\alpha^2)^p$. The minimizers are exactly the balanced repetitions of the lines of **some** ETF of the given size and coherence. Each line occurs $k$ or $k+1$ times, and signs may be chosen independently. This includes nonmaximal ETFs with positive coherence; an ETF need not attain the real Gerzon bound $\ell=d(d+1)/2$. Its existence is assumed, not proved for arbitrary parameters.

The [same proof](PROOF.md) gives the signed spherical counterpart: set $\ell=d+1$ and replace the summand by $|x_i\cdot x_j+1/d|^p$. The minimum is $2M(1+1/d)^p$, attained exactly by balanced repetitions of the vertices of a regular simplex. Here independent sign changes are not symmetries.

These are the two fixed-parameter questions of [Glazyrin and Park, Conjecture 5.2](https://arxiv.org/pdf/1901.06096). The [prior-work note](SOURCES.md) explains why the qualitative assertions **including the equality cases** already follow from Lim–McCann in the spherical, maximal-ETF and orthogonal-ETF cases. The present contribution is the explicit sufficient interval and a single elementary argument that also covers nonmaximal, nonorthogonal real ETFs. The bound depends on $N$ and $\ell$ and is not claimed optimal. Neither Glazyrin–Park Conjecture 5.1 nor the Fejes Tóth angle conjecture is resolved here.

**Reproducibility:** `python3 verify.py` checks the constants and one actual nonmaximal real ETF (10 vectors in dimension 5). `python3 independent.py` checks the extremal-graph counts, numerical parameters and projector identities using exact arithmetic; both scripts use the standard library. See [check output](CHECKS.txt), the [internal audit](REVIEW.md), and `sha256sum -c SHA256SUMS`. The proof itself does not rely on computer enumeration.

AI-assisted research with independent internal AI review. No external peer review, machine-checked formal proof, or guarantee of historical priority is claimed.
