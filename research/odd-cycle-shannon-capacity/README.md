# Explicit lower bounds for the Shannon capacities of the 21-cycle and 7-cycle

**Draft, 18 November 2026.** The main result is a finite, fully explicit code: the eighth strong power of the 21-cycle contains an independent set of **132,636,042 words**. This gives
$$
\Theta(C_{21})\ge 132636042^{1/8}>10.359354480853559 .
$$
Its construction and two exact checkers are self-contained; neither the code nor its proof depends on the 7-cycle material. The size exceeds the square of [Buys–Polak–Zuiddam’s public 11,466-word fourth-power certificate](https://github.com/spectra-research/shannon-capacity-lean/blob/aa21eeb12b75b0413d3fa9fb4208b5d0bf2c4d65/ShannonBounds/CosetC21.lean) by **1,166,886 words**. The methods of cyclic packing, floor maps and inner cosets have prior literature.

- **[21-cycle construction and proof](C21.md).** Compress a 682-element cyclic orbit to four labels modulo 21, then replace each label by a 21-word fiber in two coordinates.
- **[7-cycle application](C7.md).** Removing a common isolated box from a known seven-family construction gives an asymptotic rate $>3.258834499096250$. [Stavriianov](https://doi.org/10.5281/zenodo.22728595) already gave the unpeeled 560th-power construction and rate $3.258834362237710794\ldots$. The gain over *that particular rate* is about $1.37\times 10^{-7}$, not a new discovery of the 560th-power construction. The proof uses [Tandon’s explicit earlier family realizations](https://arxiv.org/html/2608.30273v1). Their dimensions and integer weights were cross-checked, but their underlying neighborhood counts were not independently rebuilt here.
- **[Internal review and source comparisons](REVIEW.md).** No 11-cycle improvement is proposed: a trial rate of $5.295495077846038\ldots$ falls short of [Protti’s earlier R10 certificate](https://github.com/matthewprotti/c11-shannon-capacity-lower-bound/blob/dfaef37e60e55c55b1744d9badd1f26c5364c7d5/shannon_checked_release/source/ShannonBounds/C11R10D213.lean).

## Reproduce

In this directory, using Python 3 and only its standard library:
```sh
python3 -B -O verify_c21.py
python3 -B -O audit_c21_cells.py
python3 -B -O verify_c7.py
```
No network, solver, floating-point comparisons, or optimization-sensitive assertions are used. The first script checks every pair of compressed outer words and inner vertices. The second independently checks disjoint cells. The third checks finite-table admissibility, exact earlier 7-cycle integers, and both sides of the new decimal bracket; it is not a verification of the upstream family realizations from primitive vertices.

**Scope and credit.** AI tools assisted the search, proof writing, verification code and a separately implemented internal audit. There has been no external peer review or proof-assistant verification of these results. The literature comparison is targeted, not exhaustive: no worldwide priority, globally best bound, or exact Shannon capacity is claimed. The re-encoded BPZ tables in `c7_data.json` are adapted from [the authors’ repository](https://github.com/spectra-research/shannon-capacity-lean/tree/aa21eeb12b75b0413d3fa9fb4208b5d0bf2c4d65/ShannonBounds), copyright © 2026 Pjotr Buys, Sven Polak and Jeroen Zuiddam, distributed under the included [Apache 2.0 license](LICENSE-BPZ.txt).
