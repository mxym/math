# Sharp F8 principal-sieve periods in two quadratic orders

**Entry 002, version 4 — 7 October 2026. Complete written proofs and exact integer replays.**

Version 4 now contains two sharp principal-sieve classifications for the eight-neighbor coefficient graph:

- in \(\mathbb Z[i]\), the minimum common scalar period is \(130\); at the sharp period at least five generators are required, and the five-generator list is unique up to associates and order;
- in \(\mathbb Z[\sqrt2]\), the minimum common scalar period is \(14\); at the sharp period at least two generators are required, and the two-generator lists are exactly \(\{\sqrt2,3+\sqrt2\}\) and \(\{\sqrt2,3-\sqrt2\}\), up to associates and order.

The real-quadratic theorem is in [sqrt2_period.md](sqrt2_period.md).

Version 4 proves that the period \(Q=130\) certificate from version 3 is not
merely one successful choice: it has the **smallest possible common scalar
period among all finite principal-ideal periodic sieves** for the Gaussian
eight-neighbor step set
\[
F_8=\{-1,0,1\}^2\setminus\{0\}.
\]

## Result

For any finite list of nonzero nonunit Gaussian integers
\(\mathcal G\), let \(Q(\mathcal G)\) be the lcm of their least scalar
periods. If the induced \(F_8\)-graph outside the union of their principal
ideals has only finite components, then
\[
Q(\mathcal G)\ge130.
\]
The five-generator list
\[
1+i,\quad2\pm i,\quad3\pm2i
\]
attains equality.
Moreover, at the sharp period 130 every successful sieve uses at least five generators. If exactly five are used, then up to associates and reordering the list is uniquely
\[
1+i,\quad2+i,\quad2-i,\quad3+2i,\quad3-2i.
\]
The endpoint-rigidity certificate exhausts all 47 nonunit Gaussian divisor ideals of 130, all 31 proper prime subsets, and all 123 proper-subideal replacement cases.


The proof reduces an arbitrary principal list of period \(Q\) to the
maximal sieve formed from all Gaussian prime ideals over
\(\operatorname{rad}Q\). Exact nonzero-voltage witnesses then rule out every
one of the 79 squarefree radicals below 130.

This upgrades the version-3 statement “the displayed \(Q=30\) candidate
fails while \(Q=130\) succeeds” to a complete lower-period classification.

## Files

- paper.md: theorem and proof.
- PROOF_AUDIT.md: independent logical audit.
- code/period_optimality.json: 79 exact nonzero-voltage witnesses.
- code/check_period_optimality.py: independent exact checker.
- code/generate_period_optimality.py: deterministic witness producer.
- code/endpoint_rigidity.json: 154 exact endpoint-rigidity failure witnesses.
- code/check_endpoint_rigidity.py: independent endpoint-rigidity checker.
- code/generate_endpoint_rigidity.py: deterministic endpoint witness producer.
- results/replay.txt: recorded Gaussian period replay.
- sqrt2_period.md: sharp period and endpoint classification in Z[sqrt(2)].
- code/sqrt2_period_endpoint.json: exact real-quadratic lower-period and endpoint witnesses.
- code/check_sqrt2_period.py: independent exact real-quadratic checker.
- code/generate_sqrt2_period.py: deterministic real-quadratic witness producer.
- results/sqrt2_period_replay.txt: recorded real-quadratic replay.

## Replay

From this directory:

~~~sh
python3 code/check_period_optimality.py
python3 -O code/check_period_optimality.py
python3 code/check_endpoint_rigidity.py
python3 -O code/check_endpoint_rigidity.py
python3 code/check_sqrt2_period.py
python3 -O code/check_sqrt2_period.py
~~~

The outputs are byte-identical and report:

- 79 failed squarefree radicals below 130;
- maximum failure-walk length 129;
- successful endpoint period 130;
- 4608 allowed endpoint residues;
- maximum endpoint quotient component size 580;
- inherited Gaussian full-component bound 92820;
- 47 Gaussian endpoint divisor ideals, 31 failed proper prime subsets and 123 failed proper-subideal replacements;
- for Z[sqrt(2)], 9 failed lower radicals, 11 endpoint divisor ideals, 5 failed prime subsets and 24 failed proper-subideal replacements;
- sharp real-quadratic endpoint period 14, quotient bound 6 and inherited irreducible bound 351232.

All proof decisions in the negative certificates use exact integer
arithmetic. The positive endpoint is independently replayed from the
historical v3 certificate.

## Scope

These are optimality statements **within the finite principal-ideal periodic-sieve
framework** of entry 002 v3. They are not lower bounds on every conceivable
method for bounding irreducible walks, and they do not claim that 92820 or
351232 is the true optimal component size.

No novelty, priority, external-referee, or proof-assistant claim is made.
