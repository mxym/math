# Exact three-collision threshold for seeded privacy amplification

[Regula and Cheng, arXiv:2611.33270v1, §IV.5](https://arxiv.org/html/2611.33270v1)
ask how much universality is needed for their matching trace-distance
converse. Their \(4^*\)-universal families are sufficient. **Even
strong 3-wise independence is not sufficient.** Moreover, exact two-,
three-, and four-collision classes give three distinct optimal error
exponents for equiprobable i.i.d. bits and positive output rate below one.

The proof gives a finite classical lower bound for every \(3^*\)-universal
family from the second and third moments of a random output bin. A single
random affine hash achieves that lower bound to within a constant for
any source that, conditional on a classical register, is uniform on
binary affine subspaces (which can overlap and have different
dimensions). It achieves the leading constant in the large-support
regime. This gives the exact optimum exponent across *all*
\(3^*\)-universal ensembles for i.i.d. affine conditioning, including
binary erasure side information, and a constructive upper guarantee
after arbitrary quantum postprocessing of that classical register.
The underlying affine hashing and binary erasure coding expression are
not new; see [sources](SOURCES.md) for the distinction.

The scope is average trace distance with an independent public seed,
not worst-seed error, general quantum-side-information converse or
the weakest possible structural assumption beyond collision order.
The three-wise example has *smaller* error than the four-wise formula;
the separation does not invalidate privacy-amplification achievability.

Replay: `bash replay.sh` (Python 3.10+, standard library only).
The primary argument is in [PROOF.md](PROOF.md).
