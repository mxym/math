# Perfectly private simultaneous messages for arbitrary modulus

For one input bit per sender, let MOD(q,n)(x) be 1 exactly when q divides the Hamming weight of x. With n ≥ 2 and q ≥ 2, its perfectly private PSM communication, measured in worst-case total bits, is Θ(n log min(q,n+1)). The same asymptotic optimum holds for support privacy. The lower bounds are from Ball, Crawford-Kahrl, Podolskii and Prior. The contribution here is the matching perfect-privacy upper bound for composite q ≤ n, including nonprime prime powers. Their §3.1 Theorem 18 states the sharper n⌈log₂ q⌉ construction for prime q only.

The upper bound uses a primitive root of unity in a field of polynomial size and a width-two matrix product. Independent changes of basis and a terminal scalar mask give an exact simulator for the entire transcript. A projective quotient reduces the message alphabets and identifies the construction as a small-group specialization of the classic permutation-garbling method. The same linear-algebra lemma handles weighted modular equality and sparse residue tests.

This is one noninteractive message per input party with a private shared uniform finite seed and an external referee who does not have the seed. It does not address colluding senders, active corruption, seed reuse, open complexity bounds for arbitrary symmetric functions, exact optimal constants, or the complexity of finding the field in poly(log q) time.

See [PROOF.md](PROOF.md) and [SOURCES.md](SOURCES.md). Run `bash replay.sh` from any directory. The two finite checkers exhaust small examples, not the asymptotic theorem.
