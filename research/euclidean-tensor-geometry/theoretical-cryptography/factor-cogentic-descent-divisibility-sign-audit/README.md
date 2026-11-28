# Withdrawn: Cogentic descent divisibility sign audit

**Status: withdrawn on 2026-11-28. Do not cite this directory as a mathematical
finding.**

The earlier files in commit `b93381c64f6b7fb461c4ff2050a7a5ce4d1cba00`
were based on the Valency HTML rendering of Definition 4.5. That rendering
dropped the negation slash in `q \nmid D_{t_1,t_2}` and displayed the
opposite condition.

The authoritative Google Research PDF at commit
`4a7bc8ab0bc770e71a259b7966c500496b99010a`, Git blob
`19f36b2f189ed41ec8e112b92aa9b88a96c6bd1e`, page 38, explicitly states

`q \nmid |b^*_{t_1}a^*_{t_2}-a^*_{t_1}b^*_{t_2}|`.

Thus Definition 4.5 agrees with Lemma 4.4 on this point. The alleged sign
conflict does not exist in the fixed source. The proof, checker, results, and
source note from the erroneous audit have been removed from the live research
branch; Git history is retained only for traceability.
