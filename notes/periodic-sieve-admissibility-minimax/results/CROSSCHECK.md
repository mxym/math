# Logical cross-checks of the abstract minimax theorem

Unlike the `197` instantiation, the general minimax theorem needs no computer data. The following explicit edge cases independently exercise its quantifiers and are verified algebraically in the manuscript:

- **One-dimensional odd residue sieve.** `F={-1,+1}`, `U_2={1}`, and `U_p=Z/pZ` for every odd rational prime. Every singleton pattern admits an allowed translation at every modulus; a two-point connected shape is two consecutive integers and cannot avoid the forbidden parity at p=2. Thus the universally admissible maximum is 1. The sieve P={2} leaves exactly odd integers, each isolated, so the finite-sieve optimum is also 1.
- **All residue sets full.** All finite connected shapes are universally admissible, provided the step graph admits unbounded connected finite subsets. Every finite sieve is the full lattice; both extrema are infinity. If the step set is empty, both extrema are instead one (only singleton connected shapes).
- **At least one local set empty.** Choose that prime as the finite sieve; it leaves an empty allowed graph with maximum component size zero. No singleton can be universally admissible, so the dual maximum is zero.

These checks are illustrative and do not replace the complete CRT and rooted-finite-shape proof in `paper.md`.
