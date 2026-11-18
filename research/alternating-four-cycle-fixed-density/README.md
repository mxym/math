# Alternating four-cycles at prescribed edge density

Balogh, Lidický, Mubayi, Pfender and Volec ask whether a union of nearly equal cliques attains the largest alternating four-cycle density at every red-edge density $0<\beta<1/2$. Their construction is optimal at $\beta=1/k$. **At every other density in that interval, one can strictly improve it.** Keep one large clique and the small clique together, and recolour inside their union without changing its edge density. This leaves every mixed contribution unchanged and produces more alternating four-cycles inside the union.

The [general proof](PROOF.md) is an elementary block comparison; no computation is needed. A separate [exactly regular example at $\beta=2/5$](WITNESS.md) gives $54/625=0.0864$, compared with approximately $0.08566601$ for the proposed clique union. Neither argument determines the maximum at a new density.

* [Sources and prior work](SOURCES.md): the specific 2026 question, the broader fixed-density problem and the known 2-switch identities.
* [Checks and independent derivation](REVIEW.md): Python 3 certificates, finite counts and a spectral calculation.

**Status:** AI-assisted research note with separate internal AI review, not external peer review. No priority or optimality claim. External papers are linked, not redistributed.
