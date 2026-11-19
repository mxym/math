# The exact packing density of 21354

The symmetric four-layer construction proposed by Albert, Atkinson, Handley, Holton and Stromquist in 2002 attains the maximum possible limiting density of the permutation pattern **21354**. The matching upper bound is proved here; the construction, its layer proportions and the associated cubic are prior.

Writing $\beta$ for the real root of $40\beta^3-32\beta^2+9\beta-1=0$, the answer is $\tfrac{15}{2}\beta^2(1-2\beta)(8\beta^2-4\beta+1)$ (about $0.16515$). The proof compares adjacent layers, reduces the search to at most ten, then eliminates all but one small four-layer neighborhood by exact interval arithmetic. This is an asymptotic density, not a formula for the maximum count at each finite size or a classification of all extremal permutons.

* [Proof](PROOF.md) · [Sources and attribution](SOURCES.md) · [Independent internal review](REVIEW.md).
* Replay with Python 3, standard library only: `python3 -B -O cert.py | diff - CHECKS.txt`; verify file integrity with `sha256sum -c SHA256SUMS`. The integer boxes cover continuous layer masses; they are not a sampling grid.

AI-assisted working note, independently checked within the AI-assisted research process. It has not been externally peer reviewed. No claim of priority is made.
