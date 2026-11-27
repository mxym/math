# Walsh supports: the last unique size is 21

This answers the first Open Question in §8 (p. 49) of [Jauberty and Méaux, IACR ePrint 2025/1651, April 2026 revision](https://opencryptology.org/2025/1651/versions/20260428T172000Z.pdf). Among all finite-dimensional Boolean functions, the largest cardinality at which every Walsh support has the same affine shape is **21**. All size-21 supports have affine dimension 5. Every integer from 22 onward has at least two affine-inequivalent support shapes, and both are realized in every sufficiently large dimension. Equivalence is on the affine hulls of the supports; this is not a classification of functions up to extended affine equivalence (EA).

- [Proof](PROOF.md): the six-variable base and the complete join table give the size-21 induction. Explicit constructions give two shapes for every even size at least 42 and every odd size at least 87.
- [Finite witnesses](witnesses.json): two explicit truth tables for each of the 65 sizes 22–86. Every pair is separated by the dimension of the affine hull or the number of affine planes it contains, or both.
- [Exact verifier](verify.py) and [full replay output](RESULTS.txt): integer Walsh transform, an independent direct-transform and set-count replay on all 130 witnesses, a join-case check, a negative control, and an optional replay against the public six-variable EA catalogue.
- [Source notes](UPSTREAM.md) and [upstream manifest](upstream.json): exact source version and dependencies. The external catalogue is not redistributed.

Run the self-contained witness and joining checks with Python 3.10+ (standard library only):

    python3 -B verify.py

For the six-variable base as well, use the official catalogue listed in [UPSTREAM.md](UPSTREAM.md):

    curl --fail --location --retry 2 --max-time 600 \
      https://langevin.univ-tln.fr/project/agl/class-2-6.txt \
      --output /tmp/walsh-class-2-6.txt
    python3 -B verify.py --catalogue /tmp/walsh-class-2-6.txt

The verifier checks the entire catalogue's byte count and SHA-256 before parsing it, then scans all 150,357 representatives. Catalogue completeness comes from the cited classification, not from searching for witnesses at random or from summing orbit weights alone.
