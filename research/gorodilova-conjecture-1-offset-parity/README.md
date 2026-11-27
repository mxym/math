# Parity of the affine differential offset of a quadratic APN map

**Gorodilova's 2020 Conjecture 1 holds.** For every quadratic APN map \(F:\mathbb F_2^n\to\mathbb F_2^n\) in odd dimension, the offset function \(\varphi_F\) in the associated Boolean function has *even* weight. In the source's convention, the combined odd- and even-dimensional rule is
\[
  \operatorname{wt}(\varphi_F)\equiv n+1\pmod2.
\]
The even part was already known (Gorodilova, Proposition 1).

[The proof](PROOF.md) constructs a linear right inverse \(P_F\) of the polar map \(B_F:\Lambda^2 V\to W\) by summing the plane bivectors in each nonzero value fiber of \(B_F\). Identifying its coordinates with second moments of the ortho-derivative converts the trace \(\operatorname{tr}(B_F P_F)\) into the top Boolean coefficient of \(\varphi_F\), with a correction of one for the stipulated value \(\varphi_F(0)=1\). The main odd-dimensional proof is self-contained. This is the offset-function conjecture, not the ortho-derivative component-degree conjecture resolved earlier by Carlet and Thornburgh.

## Reproduce the finite checks

Requires Python 3.10+ and a POSIX shell, without third-party packages:

    sh replay.sh | diff -u RESULTS.txt -

The script independently obtains \(\varphi_F\) by explicit derivative images and \(P_F\) by enumerating planes, then checks the trace identity and the top ANF coefficient. It covers the Gold exponents in dimensions 2 through 10, plus switched-cube and affine-shifted examples in dimensions 3 through 10. The checks include a negative control for the origin convention.

An additional replay of all 488 seven-variable representatives in the pinned public catalogue (download separately, see [source notes](SOURCES.md)):

    sh replay.sh /path/to/QAPN-7-7 | diff -u FULL_REPLAY.txt -

The finite checks are examples and audit aids; the theorem holds in every dimension in its statement, without a catalogue assumption.
