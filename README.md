# Spherical cap discrepancy of finite real reflection systems

For the sample of two unit normals per distinct mirror, this archive gives the exact discrepancy and maximizing cap directions for every essential finite real reflection system. It includes an independent composition theorem for antipodal samples on orthogonal subspaces. This is not an unrestricted kissing-number or sphere-packing bound.

- [Irreducible systems and extremizers](MirrorRootSphericalCapDiscrepancy.md)
- [Orthogonal joins and exact cap-count composition](MirrorRootOrthogonalJoinDiscrepancy.md)
- [All-aperture tables for E6](KissingE6AllCapAngles.md) and [E7/E8](KissingE7E8AllCapAngles.md)

The eight proof and checker files are unchanged from source. Run the following with Node.js; the E8 exhaustive checker is the longest:

```sh
node verify-mirror-root-spherical-cap-discrepancy.js
node mirror-join-discrepancy.js
node verify-kissing-e6-all-cap-angles.js
node verify-kissing-e7-e8-all-cap-angles.js 7
node verify-kissing-e7-e8-all-cap-angles.js 8
sha256sum -c SHA256SUMS
```

The irreducible theorem and supporting data are from `50532f94116915933d5e16ede9f1bdebeee67270`; the join theorem is from `b026734f1ba08e9b4c75857fa93e93e57880126e`. The [separate E6 blocker spectrum](https://github.com/mxym/math/blob/50532f94116915933d5e16ede9f1bdebeee67270/research/euclidean-tensor-geometry/KissingE6ExactBlockerSpectrum.md) is related context, not a replay dependency. See the proof for related work by Heitsch and Henrion.
