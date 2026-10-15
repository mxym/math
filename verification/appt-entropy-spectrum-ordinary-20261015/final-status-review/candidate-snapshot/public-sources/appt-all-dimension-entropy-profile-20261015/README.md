# One relative APPT entropy profile for both dimensions and every order

The [complete final manuscript](author-v2/PAPER.md) and its
[separate independent mathematical read](REVIEW.md) prove a single
total-dimension relative equivalent. For the original complex trace-one
densities APPT after every global unitary, put

    E_alpha(m,n)=log(mn)-min_APPT S_alpha,   D=mn.

For every epsilon>0 there is ONE N such that every integer 2<=m<=n,
D>=N and every extended real order 0<=alpha<=infinity satisfy

    |E_alpha(m,n)/C_(m,D)(alpha)-1|<=epsilon.

The specified positive scalar profile C is in Sections 2-3 of the paper.
It keeps the finite-m two-level value B_m, the exact one-hole floor,
the balanced surplus, and the calibrated finite two-parameter profile V.
For qubits it is an exact finite union of compact one-dimensional scalar
optimizations with integer multiplicities. Its zero and infinity endpoints
are separately exact. It covers fixed, growing and alternating smaller
dimensions and orders tending to zero arbitrarily quickly.

The new ingredients are the relative small-width replacement uniform down
to tiny positive orders, the O(alpha/D^2) physical-rank lattice loss on each
fixed-m bounded-order interval, and their total-dimension synthesis.
The already proved growing-m all-order theorem and fixed-m eventual exact
theorem are credited inputs; the logarithmic expansions are also existing.
The qubit reduction explicitly uses the published statement of
[Song--Chen Theorem 10](https://arxiv.org/html/2409.14347v1#S3).
Its statement and context were read; this is not a fresh complete proof audit
of that external paper.

See the literal [source binding](OWNER_SOURCE_BINDINGS.json),
[proof map](author-v2/THEOREM_MAP.md), [current status](STATUS.md),
[independent evidence](../../verification/appt-entropy-spectrum-ordinary-20261015/README.md)
and [final source/status/index binding](FINAL_STATUS_BINDING.json).
The finite D=4 qubit exception is outside sufficiently large thresholds.
The threshold is not effective, and no general finite-m exact optimizer or
complete spectral rigidity is asserted by this value theorem.

Yongxian Zhang, South China University of Technology; no external funding;
OpenAI AI assistants assisted. Original rights reserved; third-party notices
retained. Ordinary internal independent AI-agent review, without a new Lean
audit, external human review, priority certification or major-problem count.
