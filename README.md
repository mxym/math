# All regular spiders are 0-rotatable

Join one endpoint from each of k paths of length ℓ to form a regular spider. For all k, ℓ ≥ 1 and every prescribed vertex, there is a graceful labeling assigning 0 to that vertex. The vertex labels are exactly 0 through kℓ, and the edge differences are exactly 1 through kℓ.

This proves the equal-leg conjecture in [Rofa, arXiv:2611.29448v1](https://arxiv.org/abs/2611.29448v1). It does not cover unequal-leg spiders or the general Graceful Tree Conjecture. See the proof for the path-labeling sources and the leaf-rooted bouquet construction.

- [Proof](FactorGracefulRegularSpiderBouquet.md)
- [Exact supplemental checker](verify_factor_graceful_spider_bouquet.py): run `python3 verify_factor_graceful_spider_bouquet.py`. The finite check supplements, not replaces, the proof.
- Run `sha256sum -c SHA256SUMS` to verify the files.

Research source: [0d596c2](https://github.com/mxym/math/commit/0d596c28bfa1d6208c6f09a330a3c01c1727907d).
