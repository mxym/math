# Maximum posterior entropy after three binary insertions

**Yongxian Zhang.** AI-assisted research note, independently checked within the AI workflow; not externally peer-reviewed. No priority guarantee.

A uniformly random binary word of length $n-3$ is sent through a channel that inserts exactly three unbiased random bits into uniformly chosen positions. Which length-$n$ received words leave the most Shannon uncertainty about that shorter input?

**For every received length $n\ge7$, exactly the two alternating words maximize the entropy.** The [proof](PROOF.md) establishes the insertion half of [Ma and Zhang's Conjecture 6.2](https://arxiv.org/html/2611.01064v1); their first assertion, about inferring a *longer* input after three deletions, remains open in the sources checked. Their prior work gives the maximum's numerical formula, all exceptions for $n<7$, and the exact comparison through $n=18$. The new step is a strict comparison against every nonalternating received word, at every larger length.

The proof counts the ambiguity of three missing sites in the received word. The counts in its constant runs and alternating segments together identify those sites. This gives a strict entropy bound except in a family with one doubled bit, where most of the possible ambiguities must be counted more precisely. A finite remainder is certified by **two separate exact integer implementations**: after reductions, each directly counts the masks of 343 words with at least two equal bonds, plus 22 boundary representatives with one. There is no floating-point comparison in the certificate.

- [Proof and finite reduction](PROOF.md)
- [Sources and repository antecedents](SOURCES.md)
- [Independent internal review](REVIEW.md)

To reproduce both certificate outputs with standard-library Python 3.10 or later:

```sh
python3 -B -O verify.py
python3 -B -O independent.py
sha256sum -c SHA256SUMS
```

The expected outputs are [CHECKS.txt](CHECKS.txt) and [INDEPENDENT-CHECKS.txt](INDEPENDENT-CHECKS.txt). This is a computer-assisted proof for the stated finite part, not a Lean formalization.
