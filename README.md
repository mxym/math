# Trailing-zero distance spectra of cyclic subspace orbits

Fix a prime power \(q\) and \(1\le k<n\). A one-orbit cyclic subspace code is \(r\)-FWS when its nonzero subspace distances are exactly \(2,4,\ldots,2(k-r)\).

Every such orbit has diameter \(2\min(k,n-k)\). Thus the only possible value is \(r=\max(0,2k-n)\). When \(k>n/2\), taking ambient trace annihilators identifies the entire classification, including linear-equivalence classes, with ordinary FWS codes of dimension \(n-k\). Applying the known ordinary FWS theorems gives both families and exact equivalence criteria.

This answers the trailing-zero classification question in [Castello–Polverino–Zullo, §7](https://arxiv.org/html/2405.19911v1) and the corresponding equivalence question in [Shi–Song, §5](https://arxiv.org/html/2506.13418v1). It also corrects an omission in Shi–Song Theorem 4.6 as printed in arXiv v1: that theorem leaves out the ambient trace duals of the second ordinary-FWS family. An explicit binary \((n,k,r)=(8,5,2)\) example is verified below using two independent field models.

This is about abstract Grassmann codes, not a protocol or a security claim. Run `sh replay.sh` for the exact finite checks.
