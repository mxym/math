# Exact MCA bounds at the minimum-distance threshold

This note determines the sharp number of exceptional seeds for the univariate powers generator near the integer threshold `Delta=(d+2)r`. It also gives precise finite-sample corrections to two printed formulas. FlashProve already flagged the line-case numerator discrepancy; the additions here are the sharp all-degree strict and equality formulas, the packing extension, and their matching constructions at the stated thresholds.

* If `Delta>(d+2)r`, every code has exact worst-case numerator `min(|S|, d(r+1))`.
* If `Delta=(d+2)r`, the exact worst case over codes is `min(|S|, max(d(r+1), floor(n/r)))` for every finite field and nonempty seed set. A packing bound applies for the next `r-1` distance deficits as well.
* At the endpoint, an explicit ordinary Reed–Solomon construction realizes the same full-field extremum when `r | (q-1)` and `n<=q-1`. A separate syndrome tuple identifies every exceptional seed exactly.
* The quantitative Reed–Solomon instances show why Manzur's general bound cannot discard its Johnson-gap term uniformly. This is not a correction to Manzur's bound, nor a solution to his separate list-decoding questions.

Here `d>=1` is the generator degree, `r>=1` counts coordinate errors, `n` is the code length, `Delta` is the absolute minimum Hamming distance, and `S` is the set of scalar seeds. Divide a numerator by `|S|` to obtain the error probability. The integer radius is inclusive. Section 3.1 of the proof also gives the r=0 and d=0 cases. The scope is purely coding-theoretic and does not concern any deployed parameter choice.

[Proof and explicit witnesses](PROOF.md) · [Source and overlap audit](SOURCES.md)

Run `./replay.sh` with Python 3.8+ and standard shell utilities. The two dependency-free checks use direct punctured-codeword enumeration and independent finite-field syndrome-space computations, respectively. They check finite instances and do not replace the proof.
