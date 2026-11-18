# Verification, sources and limitations

A separate internal AI review checked the equality case of the operator estimate (including $r=0$), bilinear interpolation from the essential extrema of $f$, feasibility of every block, the possibility that $h_0$ lies outside the degree-feasible interval in the necessary direction, root selection, compactness, and uniqueness at $p_0$. The review also derived the parametrization in $w$ independently of the Sylvester determinant.

Run the following from this directory with Python 3 (standard library, assertions enabled):

```sh
python3 verify.py
python3 independent.py
sha256sum -c SHA256SUMS
```

[CHECKS.txt](CHECKS.txt) contains the output. These are exact arithmetic checks that supplement the proof, not a formalization. No external peer review or priority claim.

* Basit, Granet, Horsley, Kündgen and Staden, [*The semi-inducibility problem*, arXiv:2501.09842v2](https://arxiv.org/abs/2501.09842v2), Theorems 1.9 and 2.7, §7.2 and §9.1: the RRRB objective, undirected normalization, original upper-density result and question about extending it. Their following Problem 9.3 instead concerns alternating four-cycles.
* The repository's [preceding RRRB note](../rrrb-quasirandom-threshold/README.md) establishes the scalar relaxation, the distinct quasirandom threshold $p_*$ and the exact profile on $[1/2,1]$. The addition here is the precise lower endpoint of attainability of that relaxation, its critical equality graphon and an extension of the profile below $1/2$. The [alternating-cycle note](../alternating-four-cycle-fixed-density/README.md) and [Balogh et al.](https://arxiv.org/abs/2601.03433) address a different pattern.
* For compactness and convergence of graphon homomorphism densities, see [Lovász and Szegedy, *Szemerédi's lemma for the analyst*](https://doi.org/10.1007/s00039-007-0599-6) and [Lovász, *Large Networks and Graph Limits*](https://lovasz.web.elte.hu/bookxx/hombook-almost.final.pdf). The compactness step gives a strict gap separately at each fixed $p<p_0$, without computing its size.
* Targeted searches of three-red/one-blue four-cycles, fixed-density RRRB, the path-minus-cycle formulation and the new critical value did not locate an earlier matching profile. The repository check covered the full tree, formalizations, searchable archives, PDFs, 48 tags and 47 releases (175 assets) at `0bbd0f585b682695c4fbb646e87b3fd247e6b681`, then the trine, preceding RRRB and Laplacian-entropy additions through `a14fd61e6229562a615a705ec0853c4e15e66172`. These checks can miss differently worded, unindexed or unpublished work. Third-party material retains its own rights; only original exposition and two original verifiers are included here.
