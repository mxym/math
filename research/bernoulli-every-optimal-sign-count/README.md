# Every Bernoulli sign count can be the best one

Yongxian Zhang

Fix an odd number of independent 0-or-1 trials. Give each trial a plus or minus sign, and compare the largest probability assigned to a single total. **Every possible number of plus signs wins for some non-fair bias**, and at that bias the winning count is unique up to reversing all signs. This answers the [fixed-size question of Juškevičius and Kurauskas, §5](https://web.vu.lt/mif/v.kurauskas/files/2020/08/general_200704.pdf). Even sizes are different: balancing is already known to be optimal.

The proof constructs the bias. If the desired imbalance is $T=|2\ell-n|\ge3$, take $p=(1-(1-1/n)/T)/2$; for $T=1$ take $p=1/(4n)$. For example, at $n=9$ and $p=37/90$, seven pluses and two minuses give the unique optimal count up to reversal, with most likely total 2 in the majority-plus orientation. Strictness means each example persists on an open interval of biases. This is **not** a classification of every interval or of all extremal real weights.

[Read the proof](PROOF.md). It gives a uniform analytical comparison for $n\ge150$, and checks all 2,775 remaining nontrivial finite cases by exact integers. The [source comparison](SOURCES.md) distinguishes this fixed-size question from Singhal's result and the repository's [fixed-bias eventual-periodicity theorem](../bernoulli-optimal-sign-period/README.md).

**Replay (Python standard library).** From this directory:
```sh
sha256sum -c SHA256SUMS
python3 -O finite.py | diff - CHECKS.txt
python3 -O independent.py | diff - INDEPENDENT-CHECKS.txt
python3 -O constants.py | diff - CONSTANTS.txt
```
The first verifier updates the entire probability polynomial across sign counts. The second derives successive coefficients within each count from a differential identity and checks the same complete finite domain independently. The last replays the explicit rational comparisons in the large-size proof.

AI-assisted manuscript with [independent AI-assisted internal review](REVIEW.md); not externally peer reviewed. No guarantee of priority.
