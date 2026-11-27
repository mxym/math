# Point-transitive kissing configurations in seven dimensions

A seven-dimensional kissing configuration whose orthogonal symmetries can move any one point to any other has at most 126 points. Every point-transitive configuration with 126 points is congruent to the normalized E7 roots, which attain the bound. Neither the bound nor the uniqueness claim is asserted without point transitivity. Nontransitive 126-point codes are known.

The core geometric argument uses exact certificates covering every projection radius. A finite linear group argument treats the irreducible cases; at equality it forces antipodality, after which Anstreicher's previously known antipodal classification applies. [Tomar's unrestricted upper bound](https://www.mefyi.com/papers/kissing-numbers-five-seven/) gives the starting bound 132; [Wales's classification](https://msp.org/pjm/1970/34-1/pjm-v34-n1-p21-p.pdf) and [Anstreicher's antipodal classification](https://optimization-online.org/wp-content/uploads/2001/01/248.pdf) provide inputs, not the point-transitive conclusion.

- [Optimal value proof](KissingSevenVertexTransitive.md) and [equality classification](KissingSevenTransitiveUniqueness.md)
- `python3 verify-kissing-seven-vertex-transitive.py` and `python3 verify-kissing-seven-uniqueness.py` replay the source certificates using the Python standard library.
- `python3 verify-kissing-seven-independent-audit.py` is a separately implemented exact audit of both certificates, the E7 witness, and the unitary group fixed-space check.
- `sha256sum -c SHA256SUMS` checks the archive payload.

Research sources: [bound b462adb](https://github.com/mxym/math/commit/b462adb228913b0805817a448a1f80d27edc10cd), [uniqueness b5afdb6](https://github.com/mxym/math/commit/b5afdb63289bb142425b348924fb077e08a6e3b2).
