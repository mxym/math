# Four solutions on permutation polynomials of Fernando and Kousik

Four complete answers to questions in Neranga Fernando and Bhitali Kousik, [A further study of polynomial g_{n,q} over finite fields](https://arxiv.org/abs/2606.01037v1). The proof folders preserve the audited research files exactly.

| Problem | What is proved |
| --- | --- |
| [Conjecture 5.23](conjecture-5-23/README.md) | The multivariate construction is a permutation polynomial precisely under the conjectured gcd and univariate conditions. |
| [Question 6.2](question-6-2/README.md) | The specified q=4 polynomial permutes the target field precisely at e=3. The old positive case is credited; the exclusion of every other e is new here. |
| [Question 6.6](question-6-6/README.md) | The digit-defined polynomial permutes for every even e>2 in the question. A larger family has an exact gcd criterion and exact image sizes. |
| [Question 6.8](question-6-8/README.md) | The specified q=4 polynomial permutes precisely at e=4. The old positive case is credited. The definition, printed representative, and equality as target-field functions are distinguished. |

Run `bash replay.sh` from within each proof folder. The exact research inputs are fixed at:
- conjecture-5-23: `26372fef229929369f7666ace24fc5561d6d1121`
- question-6-2: `a68aa0481bf817d3889628215976bfe2e9337c2e`
- question-6-6: `466125aba53ec8f3222d03c4d5f4d2f01ff00c95`
- question-6-8: `12ffe7ef7d0c90a2227c6ab181e514065ac5339e`

Run `sha256sum -c SHA256SUMS` in this directory to verify the archive contents. These are abstract finite-field classifications, not claims about the security of a particular scheme.
