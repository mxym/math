# Sources and scope comparison

## Primary sources

1. Eric Chitambar, Sarah Hagen, David W. Kribs, Zhao Ma, Mike I. Nelson,
   and Andrew Nemec, "Codes for Quantum Secret Sharing with a Helper,"
   arXiv:2609.00234v1 (2026):
   https://arxiv.org/abs/2609.00234

   This introduces and analyzes blind helper stabilizer codes and proves
   noiseless one-way recovery for a single encoded qubit. It does not give the
   noisy-classical-link fidelity formulas in this note.

2. Eric Chitambar, Sarah Hagen, David W. Kribs, Mike I. Nelson, and Andrew
   Nemec, "Quantum Secret Sharing with a Helper and Programmable Access
   Structures," arXiv:2609.00220v1 (2026):
   https://arxiv.org/abs/2609.00220

   This introduces helper QSS and programmable access structures.

3. The exact equal-dimension stabilizer fidelity theorem used as the algebraic
   input is frozen in this repository at:
   https://github.com/mxym/math/tree/2574099cc8826586c90697a55cd638737b09d7a7/research/stabilizer-helper-fidelity

   It proves the defect formula p^(-r), the finite noiseless-message tradeoff,
   the N=p^(2m-r) canonical branches, and the matching twisted-Pauli spectral
   bound. The present note adds a noisy forward classical channel.

4. Ibrahim Issa, Aaron B. Wagner, and Sudeep Kamath, "An Operational Approach
   to Information Leakage," arXiv:1807.07878, IEEE Transactions on Information
   Theory 66(3), 1625-1657 (2020), DOI 10.1109/TIT.2019.2962804:
   https://arxiv.org/abs/1807.07878

   For a finite channel and a full-support input distribution, maximal leakage
   is the logarithm of sum_z max_x W(z|x); maximizing over the input support
   gives the same channel quantity. The present proof uses the coefficient
   sum_z max_x W(z|x) as a one-shot reliability upper bound. It does not identify secrecy leakage with
   recovery fidelity.

## Prior-art search and nonclaims

Searches on 2026-11-27 covered the two helper-QSS manuscripts above, one-way
LOCC stabilizer recovery, noisy classical communication in QSS, one-shot
entanglement manipulation, and maximal leakage/channel guessing. No source
located the same defect-dependent noisy-forward-link theorem.

This note does not claim:

* an exact formula for every channel when r>0;
* noisy quantum-share transmission or noisy stabilizer hardware;
* multiple channel uses, feedback, or asymptotic capacity;
* arbitrary target dimension or non-stabilizer helper codes;
* any attack or insecurity of a cryptographic implementation.

The result is a positive/limiting reliability statement in a precisely
specified information-theoretic model.
