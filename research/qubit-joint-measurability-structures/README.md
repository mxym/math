# Every finite joint-measurability structure has a qubit realization

Andrejic and Kunjwal asked whether one qubit can realize every prescribed pattern of jointly measurable subsets of finitely many measurements. This note gives a constructive affirmative answer with arbitrary finite outcome sets. If the pattern has M maximal compatible subsets, no measurement in the construction needs more than 2M+1 outcomes. All its effects are rational real symmetric 2×2 matrices, acting on the same qubit.

The key is to assign one qubit basis to each maximal face. A setting reports the signed basis labels of the faces **not** containing it, as well as a small private signal and a null outcome. Compatible subsets miss at least one shared label and admit an explicit parent POVM. Incompatible subsets collectively see every shared label: since distinct rank-one rays cannot support a common positive part, their prescribed weights would exceed the identity in any putative parent. The large classical outcome alphabet is essential to this argument; we do not claim that this proof yields binary measurements or that it resolves any fixed-outcome variant.

* [Construction and proof](PROOF.md)
* [Prior work and scope](SOURCES.md)
* [Independent internal review](REVIEW.md)
* [Author's exact-rational checks](verify.py) and [separate checker](independent.py); see [output](CHECKS.txt)

To replay from this directory:

```sh
python3 -O verify.py
python3 -O independent.py
sha256sum -c SHA256SUMS
```

The mathematical argument proves the general statement; finite enumerations are regression checks, not a proof for unbounded N. The manuscript and checking were AI-assisted and underwent a separate internal AI review. They have not undergone external peer review. No claim of worldwide priority is made.
