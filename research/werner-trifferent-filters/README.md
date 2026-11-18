# Trifferent filters for Werner tensor powers

**AI-assisted research draft, 18 November 2026.** [Proof](PAPER.md) · [Coordinate-support results](COORDINATE_SUPPORTS.md) · [Independent AI review and scope](REVIEW.md) · [Exact checker](check.py)

Project Alice's registers onto the span of a specified classical code and leave Bob unfiltered. If every three codewords take three different letters in at least one coordinate, the resulting partial transpose at the Werner endpoint is nonnegative on every Schmidt-rank-two vector. No restriction is placed on the co-range of the test matrix.

When every codeword pair has the same odd Hamming distance $D$, the exact threshold for nonnegativity on tests of Schmidt rank at most $r$ is

$$
t_r=\frac{1}{1+(r-1)^{1/D}},\qquad 2\le r\le M,
$$

where $M$ is the number of codewords and each physical Werner factor is proportional to $I-t F$. The filtered state is separable for $t\le t_M$, and has negative partial transpose above $t_M$. For the length-four ternary simplex code, Alice's 81-dimensional input is compressed to a nine-dimensional code span; $D=3$, $t_9=1/3$, and $t_2=1/2$. The rank threshold measures **test vectors**, not the Schmidt number of the state.

**Scope.** This is a result about one filtered block. It does **not** settle the unrestricted four-copy Werner endpoint, distillability of arbitrarily many filtered blocks, or the NPT bound-entanglement problem. The three-block corollary invokes [Tomar's finite-copy theorem](https://hexagonmath.org/2611.00464v1); the principal single-block result does not. Prior Hamming-sign sector and charging arguments are credited in [the proof](PAPER.md#relation-to-prior-work-scope). This draft makes no claim of global priority, formal verification, or external peer review.

**中文摘要。** 固定 Alice 端的码空间过滤，Bob 端不限。在三分码的行支持上得到任意副本数的秩二非负性；等奇距时给出每个测试秩的精确门槛。结论仅针对该过滤，不是一般 Werner 态的不可蒸馏定理。

**Reproduce.** Run `python3 -B -O check.py` in this directory. It needs only Python's standard library. It compares all entries for the four-qutrit example at four rational parameter values and verifies the finite witnesses. The written argument, not finite enumeration, establishes the general result. AI systems assisted in developing and writing the proof and conducting the separate adversarial review; the work has not been independently reviewed by human specialists.
