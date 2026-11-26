# Three-direction planar Hadwiger–Debrunner (4,3) piercing

The exact worst-case piercing number is three for finite planar convex polygon families satisfying the (4,3)-property and using three fixed edge directions. This is sharp even among pairwise-intersecting translates of one proper hexagon. The unrestricted planar problem is not resolved by this proof.

- `proof.md`: upper bound and rational sharpness construction.
- `verify_three_direction_piercing.js`: exact verification of the nine-hexagon example. Run `node verify_three_direction_piercing.js`.
- `CITATION.cff`: citation metadata.
- `SHA256SUMS`: run `sha256sum -c SHA256SUMS` from the archive root.

Source: [research commit](https://github.com/mxym/math/commit/72c137b7a06ef0de26f408cd44d7b8aab20c8c3c). The proof credits the homothetic triangle case and lower-bound prototype to Kynčl and Tancer. This is a research note, not a peer-reviewed publication.
