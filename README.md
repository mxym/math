# Exact Maxima for Coherent Condorcet Domains through Ten Alternatives

For the coherent fixed-axis restriction, the exact maxima for 9 and 10 alternatives are 465 and 1046. At 10 there are 40 fixed-axis maximizing domains and six ordinary isomorphism classes. With one exceptional triple admitted, the verified 9-alternative maximum is 476. These are not the unrestricted Condorcet-domain maxima.

See [the main proof](CondorcetCoherentExactMaxima.md) and [the extension to ten](CondorcetCoherentTenExact.md). Run `bash replay.sh` with Python 3.10+; the exhaustive ten-alternative replay can take several minutes. The independent checker implements a separate exact enumeration. Check the bytes with `sha256sum -c SHA256SUMS`.

Pinned original research commits: `fddc86db7123823a5b3f8812498f20807730df6e` and `1dd6e0a1d79a54f8bebaf1cfa60fda9419974be3`. For unrestricted bounds see [the published preprint table](https://arxiv.org/html/2601.07336#S6).
