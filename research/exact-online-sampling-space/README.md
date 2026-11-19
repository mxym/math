# Exact online random sampling: zero loss and the sharp leading space constant

**Yongxian Zhang** · Research note · 19 November 2026

How much information must a sampler carry from one draw to the next if it draws from fair bits and must output the requested distribution *exactly*? This note answers the *Distribution Dependence* question and the universal leading-coefficient part of the *Constant Factors* question in [Draper and Saad, §9](https://arxiv.org/pdf/2607.14503v1).

* **Which fixed laws admit zero loss?** For a finite or countably supported iid target, a fixed finite persistent state space can attain zero asymptotic loss per draw exactly when every positive atom is a power of $1/2$. The sufficiency is the classical dyadic prefix code. For necessity, a recurrent hidden state need not itself emit the target law: the [proof](PROOF.md) extracts rationality from a bounded, finite-valued likelihood ratio, then uses a constant-symbol cycle.
* **How much space suffices for positive loss?** With arbitrary target laws supplied successively on a countable alphabet, and excess cost at most $\varepsilon$ fair bits per draw in the asymptotic expected rate, the least persistent space is $\log_2(1/\varepsilon)+O(\log\log(1/\varepsilon))$ bits. The leading coefficient **one** is sharp: the lower bound, even for a specified Bernoulli subfamily, is already Draper and Saad's Theorem 1(1.2). Our [upper bound](UNIVERSAL.md) assigns variable-length prefixes to finite memory states. A rare correction step exactly restores the target law and the auxiliary state law independently. For $L+1$ states the rate loss is $O((\log L)/L)$ with a universal constant.

The model charges **persistent** space, not temporary storage, evaluation of an input law, or running time. The upper bound includes the initialization of a deterministic starting state. For infinite-entropy targets the criterion is the expected *pathwise* excess length; no difference of infinite expectations is taken. The universal constant is not asserted to be necessary for each individual fixed law. We do not address the separate questions in §9 about generating successive binary digits of a continuous random variable.

[Source and prior comparison](SOURCES.md) · [Internal zero-loss review](REVIEW.md) · [Internal universal-bound review](UNIVERSAL-REVIEW.md). AI-assisted research; independently reviewed internally using AI, not externally peer-reviewed or formally verified. Priority is not guaranteed.

**Finite reproduction.** Run the standard-library check with Python 3 from this folder:
~~~sh
sha256sum -c SHA256SUMS
python -O check.py
~~~
The [recorded counts](CHECKS.txt) check exact packing, decoding and correction on finite rational distributions (including rare symbols and alphabets larger than the persistent state set). These checks complement, but cannot establish, the countable-alphabet theorems.
