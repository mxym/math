# A certified answer to Lou–Wang's nine-variable question

Among nine-variable, 3-resilient Boolean functions with algebraic immunity 5, the exact maximum nonlinearity is **240**, not merely 224. This answers the [unrestricted existence question in Lou–Wang (2024), §3](https://doi.org/10.1587/transfun.2023EAL2111), without changing their result for nine-coordinate rotation-symmetric functions.

The [witness](witness.txt) was already constructed by [Andrey Khalyavin, IACR ePrint 2007/212](https://eprint.iacr.org/2007/212), §7. Khalyavin reports its resiliency and nonlinearity; the [certificate](PROOF.md) establishes its exact algebraic immunity. It checks both degree-four Reed–Muller evaluation matrices using binary elimination and independently using the seven-cycle Fourier blocks over \(\mathbb F_8\). The underlying Boolean function is not a new construction.

    python3 -B verify.py

Run with Python 3.10 or newer, with no external dependencies. See [RESULTS.txt](RESULTS.txt) and [SOURCES.md](SOURCES.md) for the replay and attribution.
