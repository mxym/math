# All quartic cyclic monomials of width five

We determine the exact maximum sensitivity of each of the four width-five reflection types, including short orbits and all dilations that remain quartic. The shapes 0125, 0135 and 0145 have bounded sensitivity deficit, with least eventual deficit periods 6, 6 and 66. The fourth, 0235, has a linear deficit and asymptotic sensitivity fraction 11/12.

See [PROOF.md](PROOF.md) for the formulas and derivation; [RESULTS.txt](RESULTS.txt) is the generated check record. The proof uses four explicitly verified whole-matrix max-plus equalities, plus independent truth-table optimization of every length from 6 through 20. It addresses the fixed width-five case of the general question in Li–Zhang, not all widths.

Run from this directory, with any standard C++17 compiler:

    c++ -std=c++17 -O3 -Wall -Wextra -Werror verify.cpp -o /tmp/quartic-width5-verify
    /tmp/quartic-width5-verify

No network, external data or third-party libraries are required. The compiled program is not part of this package.
