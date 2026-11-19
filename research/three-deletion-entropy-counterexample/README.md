# Three deletions: an alternating observation need not maximize Shannon entropy

**Yongxian Zhang.** AI-assisted, independently checked within the AI workflow, not externally peer-reviewed. No claim of worldwide priority.

Take a uniform 67-bit input and delete three uniformly chosen positions. The received word $(01)^{16}(10)^{16}$ leaves strictly more uncertainty about the original input than either length-64 alternating word. The only structural change is one equal pair at its center. The increase is between $45/383240$ and $46/383240$ bits. The comparison is integer-exact; its small magnitude does not depend on rounding.

This disproves the three-**deletion** assertion of [Ma and Zhang, Conjecture 6.2](https://arxiv.org/html/2611.01064v1). The three-**insertion** assertion of the same conjecture has a [separate affirmative result](../three-insertion-entropy/README.md). The present counterexample does not identify the true maximizer or the first counterexample length.

- [Proof, complete histograms and exact quotient](PROOF.md)
- [Primary sources and scope](SOURCES.md)
- [Independent internal review](REVIEW.md)

Reproduce with standard-library Python 3.10 or later:
```sh
python3 -B -O verify.py
python3 -B -O greedy.py
python3 -B -O verify_integer_insertion.py
sha256sum -c SHA256SUMS
```
The corresponding outputs are [mask enumeration](CHECKS.txt), [distinct-host enumeration and embedding DP](GREEDY-CHECKS.txt), and [independent mask check](INDEPENDENT-CHECKS.txt).
