# Global quantitative orthogonal tensor rigidity

This additive research package contains three connected manuscripts, with complete written proofs. It was developed with AI assistance and self-reviewed; mathematical novelty and publication tier are unestablished.

The strongest **unconditional** result is the [all-orders theorem](all-orders.md): for every real symmetric tensor of order p >= 3 in every finite dimension, the distance to the orthogonally decomposable class is at most K(m,p) times the square root of its complete contraction-commutator defect. The explicit constant is K(m,p) = (p^p/p!) sqrt(2p) m^(p/2) for m >= 2, polynomial in dimension for each fixed order. Weights may vanish or repeat, and no smallness assumption or spectral-gap hypothesis is imposed. The power one half is optimal for each fixed order and dimension at least two. [PDF](all-orders.pdf).

The [cubic companion](global-odeco.md) gives the improved constant 5 m^(3/2) and an exact binary-cubic distance formula. In dimension two the best universal constant is sqrt(3)/2. [PDF](global-odeco.pdf).

The [nonlinear Jacobian manuscript](paper.md) proves a local linear coercivity theorem and an unconditional Gaussian transport consequence. Its application to square-root Wasserstein stability for the sharp log-concave entropy inequality is **conditional on the explicitly stated OpenAI-101 transport remainder R**. The truncated-exponential obstruction to powers above one half is unconditional. [PDF](paper.pdf).

These are related stages of one research direction, not three claimed resolutions of famous open problems. The general theory of orthogonally decomposable tensors is prior work. See [literature and dependency notes](DEPENDENCIES.md) and the [self-review record](AUDIT.md).

## Reproduce

Python 3.11+ and its standard library suffice for the finite checks and integrity verification:

    python3 -B verify.py

The runner checks the package hashes, executes four exact checkers normally and under python -O, and requires equal reports. It also replays the byte-preserved upstream scalar checker. These finite checks do not prove the analytic theorems.

The separate Lean project uses official Lean 4.34.1 and the exact mathlib revision pinned by its manifest:

    cd formal
    bash bootstrap.sh
    cd ..
    python3 -B verify.py --lean

If elan already exists elsewhere, export its ELAN_HOME and prepend its bin directory to PATH. Bootstrap defaults to project-local ignored tool and cache directories. It checks the pinned elan archive checksum, keeps TLS verification enabled, uses the exact dependency manifest and official module cache, and never runs lake update.

Lean checks seven exported algebraic lemmas: the cubic first-order kernel implication and binary polynomial identities/inequality. Its axiom sets are propext, Classical.choice and Quot.sound. **The all-orders maximizing-vector proof, analytic coercivity, transport and entropy remainder are not Lean-formalized.** The project makes no whole-paper formalization claim.

To rebuild the three PDFs without modifying publication files, install Pandoc and ordinary LaTeX packages, then run:

    bash build.sh /tmp/jacobian-pdf
    bash build.sh /tmp/cubic-pdf global-odeco.md
    bash build.sh /tmp/all-orders-pdf all-orders.md

Successful builds require no overfull boxes or undefined-reference warnings. PDF bytes need not match across TeX versions.

## Boundaries and next questions

The independent algebraic theorem is ready as a research note with a complete proof; broader novelty checking remains open. A harmonic direct-sum construction proves that its constant must grow at least as dimension to the power one quarter for every fixed order, so a dimension-free estimate in these norms is impossible. The optimal dimension growth and a polynomial-time algorithm remain open in this note. The exact binary formula supplies a concrete sharp benchmark.

The entropy application needs an independent audit or formalization of its imported global remainder before being presented as an independently established entropy breakthrough. No Mahler, Fujita, Ryser, Borsuk, or convex-body Banach–Mazur theorem is claimed.

Authorship attribution: mxym repository account, AI-assisted. Upstream copied sources retain their Apache-2.0 attribution and license. No additional license for the authored material is assigned here.
