# Distance from integer and rational lines modulo primes

Doerner–Haitner–Ishai–Makriyannis, ePrint 2025/1722, Definition 5.36 and Conjecture 5.37, print the distance comparison in a direction that is always nonpositive. Reversing the sign, as the AICR c/0074 formulation does, gives a false assertion with the source's integer coefficients, already for the deterministic two-point graph {(0,2),(2,3)}. Its distance is 1/2 over the integers and zero for every odd prime. This does not depend on whether natural numbers include zero.

A separate positive theorem changes the comparator to rational affine graphs. It gives exact preservation for p>n² (sharp in the range p>n), and a uniform average comparison over any finite set of primes, including primes smaller than the grid. This theorem does not repair the original integer assertion or establish any security statement for a protocol.

See PROOF.md and SOURCES.md. Reproduce with: sh replay.sh | diff -u RESULTS.txt -
