# Circular sorting on the antipodal centralizer

**Status:** complete *restricted* extremal theorem; unrestricted circular
sorting questions remain open. Complete self-contained proof: [paper.md](paper.md).

For any odd `m >= 3`, every permutation `pi` of `Z/(2m)` commuting with
half-turn `x -> x+m` has a shift `j` for which `pi(x+j)` has at least
four cycles. For odd primes `p`, this is sharp in the entire centralizer:

```text
max_{pi: pi(x+p)=pi(x)+p} d_{2p}(pi) = 2p - 4.
```

The maximizing example is `pi(x) = a*x mod 2p`, where `a` is odd and
primitive modulo `p` (all even shifts have four cycles, all odd shifts
have three). The proof works for all odd half-sizes, but sharpness is
asserted only for odd prime half-sizes. This neither proves nor
refutes `t(2p) = 2p-3` for unrestricted permutations.

## Reproduce computational checks

```sh
cd research/circular-sorting-antipodal
g++ -std=c++17 -O2 -Wall -Wextra -pedantic verify.cpp -o /tmp/circular-antipodal-verify
/tmp/circular-antipodal-verify
```

The checker is standalone ISO C++17, requires no external dependencies,
and exits with nonzero status if any check fails. Its full enumeration
of `2^m * m!` permutations for `m=3,5,7` is independent of the written
proof and is **not** offered as a proof of the theorem for arbitrary `m`.

Author: Yongxian Zhang, South China University of Technology;
mxymmxym1@gmail.com; ORCID 0009-0000-3864-3536.
No external funding; AI-assisted research; no external peer review.
See [paper.md](paper.md) for references, precise scope and full proof.
