# How much information can an adaptively stopped bandit search collect?

**Yongxian Zhang.** AI-assisted research note, internally checked by AI; not externally peer reviewed. No global priority or publication claim.

One of n arms, chosen uniformly, has Bernoulli mean (1+Δ)/2; the other arms have mean (1−Δ)/2. The experimenter can choose which arm to sample, when to stop, and can randomize. The budget t bounds the *average* number of pulls under this model, not under a fictitious environment.

For every n≥2, t≥0 and 0<Δ≤1, the information in the full stopped transcript is at most
  
    min{log n, 16(2+log n)tΔ²/n}.

This matches, up to universal constants in their stated regime, the lower bound in [Gu–Han–Qian, NeurIPS 2025, Proposition 4.4](https://papers.neurips.cc/paper_files/paper/2025/file/71cdf0b117bb85329523fdd26ff195a7-Paper-Conference.pdf). Their Appendix C.5 explicitly asks for the converse. The short proof compares each pair of possible planted locations through a common experiment in which *both* locations are planted; it never assumes that the expected budget holds in that auxiliary experiment.

- [Main proof](PROOF.md): pairwise comparison and the averaged cost under the actual models.
- [Extension to known observation laws](KNOWN-LAWS.md): if the planted arm has law U and all other arms law V, the optimal information has order `log(n) min{1,t H²(U,V)/n}`, with universal constants, even for singular laws. The lower bound is a likelihood-based knockout tournament; the upper bound uses the established sequential Hellinger inequality.
- [Alternative proof](BARRIER.md): localize the original all-low likelihood comparison at a data-dependent barrier and bound the information lost beyond it.
- [Elementary noiseless comparator](ENDPOINT.md): at Δ=1 the exact optimum is min{1,t/c} log n for c=(n−1)(n+2)/(2n). This is **not** a sharp-constant claim at positive noise.
- [Sources and scope](SOURCES.md) and [internal mathematical review](REVIEW.md).

For exact finite decision-tree checks run `python3 -O verify_bridge.py` for the pairwise and tournament checks, and `python3 -O verify.py` for the barrier and noiseless checks. The [bridge output](BRIDGE-CHECKS.txt), [barrier/noiseless output](CHECKS.txt) and SHA-256 digests are supplied. The trees illustrate the identities and event accounting; the proofs cover all adaptive rules, stopping times, and horizons.
