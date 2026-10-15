# A negative answer to Han's Fourier-overlap auxiliary question

The [complete proof](PAPER.md) constructs monotone, leaf-transitive
read-once Boolean formulas f_d on N=2^d independent uniform bits with

    A_i(f_d)/I_i(f_d)>=3d/8=(3/8)log_2 N

for EVERY coordinate i, all of which are essential. Here
A_i=sum_(S not containing i)|fhat(S)fhat(S union i)|, and I_i is the
probability that flipping i changes f. Thus no universal c makes
A_i<=c I_i hold for some coordinate of every Boolean function. This
negates the exact existence quantifier in
[Han's Question3.1/Eq3.18](https://arxiv.org/html/2312.08271v2).

The gate chosen at each level keeps the output bias in [1/4,3/4]. An exact
Fourier restriction recurrence proves the lower bound at every finite
depth and every leaf; it is not a small-dimension extrapolation or merely
one badly chosen splitting coordinate.

This does NOT prove or refute the Fourier entropy-influence conjecture.
[O'Donnell--Tan](https://arxiv.org/abs/1304.1347) already prove FEI for
bounded-arity read-once formulas, including this family. The whole FEI
research stage remains open and adds no completed major-conjecture count.
The bounded source screen found no exact prior all-coordinate negative
answer, but is not a comprehensive priority certificate.

[Target map](THEOREM_MAP.md), [full independent read](REVIEW.md),
[source/execution binding](REVIEW.json), [final metadata binding](FINAL_STATUS_BINDING.json),
and [retained evidence](../../verification/han-fourier-overlap-ordinary-20261015/README.md).
One author and one separate independent mathematical program actually
passed; exact controls supplement the induction, rather than certify
arbitrary depth computationally. The standalone author checker uses only
Python's standard library: `python3 han_q31_exact_controls.py`.

The author v1 map wrongly called a 29-entry Atom response a 100-entry
response, confusing the requested maximum with the returned count. V1 is
retained unchanged and v2 corrects that field. The independent reviewer
also retained a genuine failed metadata assertion that had wrongly
presumed v2's new README was unchanged. No mathematical source changed.
Both full frozen packets and their pre-review notices remain historical;
the current review and final binding record the passed ordinary status.

Yongxian Zhang, South China University of Technology; no external funding;
OpenAI assisted. Internal AI-agent review, no external human peer review
or Lean. Original rights reserved and prior authors/questions credited.
No submission, email, Release, DOI, priority certificate or new major count.

The earlier derivation and NumPy checker named by the paper are literal
historical author files from the recorded commit, not additional newly
audited results; HISTORICAL_INPUTS.json binds their scope and bytes. The
top-level HAN_Q31_TARGET_AND_SOURCE_MAP.json is the literal frozen v2
pre-review source record. Current ordinary status is given by REVIEW.json
and FINAL_STATUS_BINDING.json, not retroactively inserted into that record.
