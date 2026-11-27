# Nine-variable cubic and sextic cases of the CFS basis questions

For Boolean functions of degree 3 or 6 in nine variables, both Open Problems 1 and 2 in [Carlet, Feukoua, and Sălăgean (2025)](https://doi.org/10.1007/s10623-025-01702-z) have affirmative answers in these exact parameters. The unrestricted questions remain open. The proof uses a published orbit classification. Our files provide change-of-basis and obstruction certificates, not a new classification. See PROOF.md for assumptions.

Download the third-party catalogue **separately** from the authors' [university project page](https://langevin.univ-tln.fr/project/cubics/), link “A file of 349 representatives”; or use the [direct official download](https://langevin.univ-tln.fr/project/cubics/classification.txt). Store the unmodified 37,877 bytes *outside* this directory. No redistribution license was found on the project page; the external source table and its historical header are not supplied. Keep the original file byte-for-byte; verify.py checks the length and SHA-256 recorded in UPSTREAM.md. No raw monomial/source records appear in the certificates. Only our derived positive bases, a tuple for each basis label, or a single exceptional direction are included, keyed to upstream orbit numbers.

Run with Python 3.9+:

    python3 -B verify.py /path/to/classification.txt --negative-controls

The program parses all 349 source equations, checks the nonzero obstruction or chosen basis on every orbit, and tests four corruptions for each table. It does not trust the original search code. No nonstandard dependencies, network access or writes are required by the verifier. Numerical coordinate vectors are little-endian bit masks. Tuple indices in the certificates are 0-based.
