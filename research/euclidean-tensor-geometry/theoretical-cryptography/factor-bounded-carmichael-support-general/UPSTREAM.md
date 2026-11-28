# Prior art and scope

The local identity
\[
 \lambda(p^a)=p^{a-1}(p-1)
\]
for odd prime powers, together with lcm composition of the Carmichael
function, is standard. The algorithmic observation here is to enumerate
all \(\mathcal S\)-smooth predecessor candidates \(p-1\), rather than
first reconstructing the exact value of \(\lambda(N)\).

## Repository context

* Commit 4e0f3489260d13e8b3607d63fe8f29e3d3f94cdc constructs an
  annihilating exponent from Carmichael support and gives a general
  deterministic bound in terms of the largest unlisted prime factor.
* Commit 3c4258ea82dd571c4ddfedb077103af82685cfb7 gives a general
  deterministic \(L_N[2/3,1+o(1)]\) bound for unrestricted support
  cardinality.
* Commit a4830b7bb2409fef8838af37d508097bca5e636e gives unconditional
  Las Vegas polynomial time for unrestricted support cardinality.
* Commit 12e25227867225539ad9e4567ef431097090743a handles semiprimes by
  enumerating support-compatible exact \(\lambda\) values.

The present theorem supersedes the last result for fixed support
cardinality: direct predecessor enumeration works for arbitrary
factor counts and multiplicities.

## Limits

* The list must contain every prime divisor of \(\lambda(N)\). False
  positives are allowed; omissions invalidate the guarantee.
* Polynomial time is claimed for fixed support cardinality. For
  arbitrary \(|\mathcal S|\), the exact deterministic bound is (2).
* The result does not recover the support from \(N\).
* No claim of absolute historical priority is made.
