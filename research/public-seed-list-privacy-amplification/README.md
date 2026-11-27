# Public-seed list privacy amplification: three distinct guarantees

A list of keys can be required to be jointly uniform; only its selected
key can be required to be uniform; or the selected key can be required
to remain uniform after exposing the other keys. These are different
ideal states and have different entropy costs.

- **Jointly uniform list:** independent two-universal hashes concatenate
  to one two-universal hash. The quantum leftover-hash bound uses the
  **total output length**. A flat source shows the matching entropy
  scale, already with trivial side information.
- **Only a selected key, no other keys disclosed:** when an independent
  index is public, the secrecy error is exactly the average of the
  corresponding single-key errors. No additional entropy comes
  from selecting the index.
- **Selected key and all other keys disclosed:** we prove a sharp
  entropy budget valid with arbitrary, even noncommuting, quantum
  side information, and with different key lengths.

These results distinguish public from private seeds in [Kulkarni's
arXiv:2603.18097v1](https://arxiv.org/html/2603.18097v1), Definitions
6 and 8 and Theorems 10 and 12. The seed-omitted state in its hybrid
and the public-seed state in its converse are different models.
Under a seed-omitted model with independent private shared seeds,
strong universality on a domain of at least two points makes
the entire output list exactly uniform after averaging the seeds
away. This uses the private randomness.
With public seeds, its published entropy-length formula does not
guarantee the stated jointly uniform list.

This is an abstract, defensive statement about the proof model.
It does not evaluate physical devices or a BB84 implementation.
See [PROOF.md](PROOF.md), [SOURCES.md](SOURCES.md), and the two
independent verification scripts.

~~~sh
sh replay.sh | diff -u RESULTS.txt -
~~~
