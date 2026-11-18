# Five planar steps with probability 3/16 of reaching the root-mean-square radius

Reviewed draft; independent AI review only. Define O_d as in V. Dvořák and O. Klein (2022): the infimum over finite independent uniform signs and v_i∈R^d satisfying Σ||v_i||²=1, of Pr(||Σ_i ε_i v_i||≥1). No isotropy, zero vector sum, or requirement that the individual norms coincide is imposed. See their Proposition 7.1 and ensuing discussion, and the restatement in Hollom–Portier (2025), §6. The inside constant T_d has the opposite non-strict inequality (≤); it is a different problem in any fixed dimension.

Take the five planar vectors u_i=(0,1),(1,−1),(1,−1),(1,−1),(2,1), and set v_i=u_i/√12. Their squared norms are 1,2,2,2,5; hence Σ||v_i||²=1. The covariance matrix of the unnormalized sum is [[7,−1],[−1,5]], not a scalar matrix. The example is for the original definition, not for a covariance-normalized variant. The normalized sign sum has expected squared norm 1.

For independent fair signs put a=ε₁, b=ε₅, h=ε₂+ε₃+ε₄. The unnormalized sum is (h+2b,a−h+b). Among the 32 equally likely sign patterns its squared length has the following multiplicities:

    squared length     2     10     26     34
    multiplicity       6     20      4      2

For a direct derivation, by simultaneously flipping all signs take b=1, then double multiplicities. The h values −3,−1,1,3 have respective weights 1,3,3,1. The ordered pairs of squared lengths for a=−1,+1 are respectively (10,26), (2,10), (10,10), (34,26). Exactly 6 of 32 exceed or equal 12; none equals 12. Thus

    O₂ ≤ 3/16 < 7/32.

This answers in the affirmative Dvořák–Klein's specifically planar question whether O₂<7/32 can occur. It is not a determination of O₂, nor the first counterexample to dimension-free equality: the latter was already disproved in the published version of Hollom–Portier. The known scalar constant is O₁=7/32.

## The old sign pattern and the planar realization

The sign event itself is already present in [Dvořák–Klein, §7](https://arxiv.org/pdf/2104.10005#page=34): it is their three-dimensional **inner** event. Here is an explicit equivalence, not just agreement of the two event probabilities. With their signs δ₁,…,δ₅, their centered squared length is

    D=(7/30)(δ₁+δ₂)²+(δ₁−δ₂+δ₃)²/9
        +(δ₁−δ₂−δ₃+δ₄+δ₅)²/25−1.

Set ε=(−δ₄,−δ₁,δ₂,δ₃,δ₅). Then h=−δ₁+δ₂+δ₃. By simultaneous sign change it suffices to check h>0. Below the four entries in each row are 225D in order (δ₄,δ₅)=(−,−),(−,+),(+,−),(+,+):

    (δ₁,δ₂,δ₃)       h           225D
    (−,−,+)          1       91,   19,   19,   19
    (−,+,−)          1       81,    9,    9,    9
    (−,+,+)          3       25, −119, −119, −191
    (+,+,+)          1       91,   19,   19,   19

For h=1 the planar event never occurs (directly from (h+2b)²+(a−h+b)²); for h=3 it occurs precisely when (a,b)≠(+,−), equivalently (δ₄,δ₅)≠(−,−). Thus the planar outer event equals the old inner event on every sign vector after this signed permutation. What changes is the positive-semidefinite realization in dimension two **and** the side of the mean. See [the review](REVIEW.md) for an alternative derivation by a small deformation of the old matrix; no priority is claimed for a new Boolean sign pattern.

## Finite-length sharpness

Let n=5 and identify full cube sign configurations with their simultaneous negatives, giving 16 classes. For any d and any vectors, f(ε)=||Σ_i ε_i v_i||²−Σ_i||v_i||²=2Σ_{i<j}(v_i·v_j)ε_i ε_j has zero mean. If f≥0 on at most two classes, select representatives x,y of these two classes, repeating a class if necessary (if none exist, the zero mean already contradicts strict negativity). There is a four-element subset S of {1,…,5} with ∏_{i∈S}x_i=∏_{i∈S}y_i: choose signs so that x,y differ in at most two positions. If the distance is 0 choose any S, if 1 omit its differing coordinate, if 2 omit a matching coordinate. Parity on S is independent of global sign. On the halfcube where that parity has the *opposite* value, every f is strictly negative. Yet on this halfcube E(ε_i ε_j)=0 for all i≠j, since the uniform conditional density relative to the whole cube is 1±∏_{k∈S} ε_k, and no size-two character equals the size-four character. Contradiction. Hence the probability f≥0 is at least 3/16 for five summands, in any dimension (including zeros); equality is attained in the plane above and hence in each fixed dimension d≥2 by zero-padding coordinates. This does not assert attainment in dimension one.

For only four summands there are eight antipodal classes. If f≥0 on at most one class, conditioning on opposite four-bit parity again contradicts mean zero. Thus probability≥1/4 for n≤4 (pad with zeros). Five summands are necessary to get a planar witness <7/32. The same argument can be negated for the sign-counts of any centered homogeneous quadratic form, but makes no statement about length ≥6 or the unrestricted optimal O₂.
