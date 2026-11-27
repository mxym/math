# Exact worst-case nondeterministic degree at each support size

Among Boolean functions on n variables with exactly s≥1 ones, the largest nondeterministic degree over the reals is

    floor(log2(2^n−s+1)).

This gives an exact support-size refinement of the singleton characterization in Rajagopalan–Saurabh, Proposition 22. It also gives the corresponding maximal rational degree by taking the larger of the support and complement formulas. At the upper endpoint for each degree class, all extremizing supports are characterized by punctured minimum-support subcubes with signed coordinate blocks, and their number is computed.

The proof is an exact identity between nondeterministic degree on a finite Cartesian grid and the least degree needed to hit a given support at exactly one point. It uses an infinite coefficient field, weighted interpolation duality, and the known generalized Alon–Füredi minimum-support bound. The cube endpoint classification uses Valyuzhenich's known minimum-support theorem for real bounded-degree polynomials. These ingredients are credited explicitly.

This is a deterministic worst-case profile, not a claim about typical random functions or a solution to de Wolf's degree/query-complexity conjecture.

Run `sh replay.sh | diff -u RESULTS.txt -` with Python 3. Two checkers use independent exact zero-set and dual-space feasibility tests on small cubes and nonbinary grids.
