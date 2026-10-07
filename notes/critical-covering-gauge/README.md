# Arbitrarily slow critical covering excess in Banach nonembedding obstructions

[Complete proof](paper.md) · [PDF with supporting analytic proof](paper.pdf) · [Editable LaTeX](paper.tex) · [Independent proof audit](PROOF_AUDIT.md) · [Source provenance](../avoidance-covering-provenance/README.md)

For every finite-valued nondecreasing gauge h:[1,infinity)->[1,infinity) with h(t)->infinity and every infinite-dimensional real Banach space, there exists a countable compact subset K with no bi-Lipschitz embedding into any finite-dimensional real normed space, upper box dimension zero, Assouad dimension exactly two, a universal doubling bound, and all-scale intrinsic covering bound `350000 (R/r)^2 h(R/r)`. Its normalized exponent-two covering content is nevertheless unbounded.

The new theorem uses the scale-flexible sheet construction of entry 003. The PDF incorporates entry 003's complete supporting proof and analytic appendix. Exact source snapshots and immutable repository bindings are bundled. The finite witnesses are chosen anew for the new schedule; the old schedule's coordinates are not reused.

The packing specification gives exact rational finite packings and the lower bound `2^j/144`. It is not a finite computational certificate of nonembedding into every finite-dimensional real normed space or of Dvoretzky transfer into an arbitrary Banach space. No optimum or minimality claim is made for Assouad dimension two. Another construction with a genuine exponent-two bound is not excluded.

The independent audit passed the full stated mathematical scope. The public copy adds only the audited optional exposition: explicit dyadic rounding, fresh witness selection for the new schedule, finite-valued gauge wording, and the precise nondecreasing excess-profile interpretation.

Run `bash build.sh` to rebuild the PDF. Run `python3 ../avoidance-covering-provenance/verify.py` for public package and primary-source integrity checks and the bounded-cluster finite-evidence replays.
