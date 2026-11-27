# Exact resources with ideal helpers in matching-selector secret sharing

## 1. Model and statements

Let X = {X_1,...,X_m} and Y = {Y_1,...,Y_m} be disjoint endpoint sets,
m>=1, and let M_1,...,M_r be pairwise edge-disjoint perfect matchings
between them, 1<=r<=m. There is a helper h_s for each M_s. A coalition is
authorized iff for some s it contains h_s and at least one endpoint of
every edge of M_s. In particular, any coalition consisting only of
endpoints, or only of helpers, is unauthorized. Williamson's structure
[W, §3] has m=r=k>=3 and M_s = {{Y_i,X_(i+s)} : i in Z_k}.

A perfect scheme is a distribution of a finite secret S and finite shares,
with conditional entropy H(S|A)=0 for each authorized share tuple A and
independence of S and A for every unauthorized share tuple. Participant
labels also denote their shares. The secret has D>=2 positive-probability
values, and L=log2 D. We call a helper ideal if H(h_s)=L. All helpers have
H(h_s)>=L; the proof below gives the stronger atom bound P(h_s=a)<=1/D.
An ideal helper has a uniform D-value marginal. This terminology
fixes the size of the secret alphabet; when S is uniform, L=H(S).

For any scheme put e_s=H(h_s)-L, and let e_(1)<=...<=e_(r) be these
nonnegative excesses in increasing order. Write

    B = max over 0<=j<=r of [jL - sum_(u=1)^j (j-u+1)e_(u)]
      = sum_(j=1)^r max(0, L - sum_(u=1)^j e_(u)).                 (1)

**Theorem 1 (stability).** For every endpoint on either side,

    H(X_i | X without X_i) >= B,   H(Y_i | Y without Y_i) >= B.     (2)

In particular B >= max(0,rL-(r+1)/2 sum_s e_s). The entire X-side
share tuple, and likewise the Y-side tuple, has entropy at least mB.
If a dealer computes the shares from S and an independent discrete
private tape R, then H(R)>=mB.

**Theorem 2 (ideal-subset pointwise bound).** If J is a subset of j ideal
helpers, then for every endpoint and every conditioning value of positive
probability on the other endpoints of the same side,

    max_x Pr[X_i=x | X without X_i] <= D^(-j),                     (3)

and analogously on the Y side. Consequently the largest joint atom on
either endpoint side is at most D^(-mj), and any independent discrete
dealer tape has maximum atom at most D^(-mj).

**Corollary (exact minimum-helper frontier).** If all helpers are ideal,
the minimum individual entropy at each endpoint is rL, the minimum of
the largest share entropy is rL, and the minimum total share entropy
is (2m+1)rL. Both minimum dealer-tape Shannon entropy and minimum
dealer-tape min-entropy are mrL. These bounds are all attained by one
scheme. A uniform secret on D=2^b values admits the scheme with exactly
mrb fair random bits in addition to its input secret, and no fixed-length
fair-bit tape with fewer bits suffices in this regime. The same
conditional construction works for any prior with the same positive support.
The theorem does not give an unrestricted optimum when helper
entropies are larger.

## 2. Basic facts and reduction to a uniform secret

Correctness means that a deterministic decoder exists on all
positive-probability pairs of its authorized inputs. The support bound
for a helper uses the decoder for (X,h_s), an authorized coalition. Fix
a helper value z of positive probability. For each secret x in the
positive support let A_x(z) consist of all X-side values on which that
decoder with helper value z returns x. The sets A_x(z) are pairwise
disjoint. Independence of S from h_s, and also from X, gives

    Pr[X in A_x(z)] = Pr[X in A_x(z)|S=x]
                       >= Pr[h_s=z | S=x] = Pr[h_s=z].

This holds for every x, because any pair of positive joint probability
given S=x is decoded correctly. Summing over x proves
Pr[h_s=z]<=1/D. In particular H(h_s)>=L, with equality only if
every positive-probability helper value has probability 1/D. This
bound is also a special case of the error-free perfect-secrecy bound
of Ho–Chan–Grant–Uduwerelle.

Every perfect scheme on a prior with D positive values remains perfect
when the secret is made uniform on those values and the dealer's
conditional distribution given each value is kept. Indeed authorized
decoding holds on the same supports, and by privacy each unauthorized
view has the same conditional law for every secret value. Thus all
unauthorized marginal laws stay fixed. These include the full X-side view,
the full Y-side view, and the marginal of each helper. It suffices to
prove (2) and (3) assuming the secret is uniform, as the stated
entropies and conditional maximum atoms only concern those fixed views.
We assume uniformity for the next two sections.

For any endpoints-only tuple A (always unauthorized), when adding h_s
authorizes it, the chain rule gives

    H(h_s | A)   = L + H(h_s | S,A),
    H(h_s | S,A) <= H(h_s)-L = e_s.                               (4)

Here H(S|A)=L, H(S|A,h_s)=0, and
I(S;h_s|A)=H(h_s|A)-H(h_s|S,A). If adding h_s leaves it unauthorized,
instead H(h_s|S,A)=H(h_s|A) by privacy for the joint tuple (A,h_s).

## 3. One missing endpoint pair at a time

Fix X_i and let B_i be all X-side endpoints except X_i. For a helper
index s let Y_v be the partner of X_i in M_s, and Q_s be all endpoints
except X_i and Y_v. Then Q_s contains B_i. The coalition Q_s+h_s
is unauthorized because it misses both endpoints of one edge of M_s.
For every t!=s, Q_s+h_t is authorized: the only possible uncovered
edge after losing that pair is {X_i,Y_v}, which is not in M_t by
edge-disjointness. Let W denote the tuple of all endpoints. Equation
(4) with W, and conditioning, give

    H(h_s|S,Q_s) = H(h_s|Q_s) >= H(h_s|W) >= L,
    H(h_t|S,Q_s) <= e_t  for t!=s.                                 (5)

Choose any ordered list of distinct helper indices (s_1,...,s_j), of
length j<=r. For a position a let V_a denote the tuple of earlier
helpers in the list. Conditioning on Q_(s_a) in the entropy of the
a-th helper and using I(U;V|W)<=H(V|W) gives

    H(h_(s_a)|S,B_i,V_a)
       >= H(h_(s_a)|S,Q_(s_a),V_a)
       >= H(h_(s_a)|S,Q_(s_a)) - H(V_a|S,Q_(s_a))
       >= L - sum_(u<a) e_(s_u).                                   (6)

All conditioning statements use the actual full coalition privacy;
no independence between helpers was assumed. Write H_J for the tuple
of these j helpers (the symbol is a random tuple, not entropy).
The chain rule gives a lower bound on H(H_J|S,B_i) by summing (6).
The full X side covers every matching, so (4) gives
H(H_J|S,X)<=sum_(u<=j)e_(s_u). Their difference is
I(H_J;X_i|S,B_i), at most H(X_i|S,B_i)=H(X_i|B_i). Hence

    H(X_i|B_i) >= jL - sum_(u=1)^j (j-u+1)e_(s_u).                  (7)

For fixed j, the weighted penalty is minimized using the j smallest
excesses in increasing order: coefficients are positive and exchanging
a larger earlier excess with a smaller later one never increases the
penalty. This proves the first form of (1). The value for each j is a
sum of the first j increments L-sum_(u<=a)e_(u); these increments are
nonincreasing, so the maximum of their prefix sums is the sum of the
positive increments. Averaging the right side of (7) over all orders
with j=r gives the simpler total-excess bound. Interchanging X and Y
does not change the argument. Finally H(X)>=sum_i H(X_i|B_i) by the
chain rule and conditioning. For an independent tape computing the
shares, H(R)>=H(X|S)=H(X). This last implication also applies to the
original prior, since the X marginal stays fixed and is independent of S.

## 4. Exact ideal-subset bounds and attainment

For j ideal helpers, apply (6) to these indices only, so every lower
bound is L. Each marginal has entropy L and is uniform on D values.
Therefore equality holds at every chain step. It follows that each
selected helper is independent of (S,B_i,earlier helpers). Equivalently,
for every positive-probability (S=x,B_i=b), the joint helper tuple H_J
is uniform on the Cartesian product of its j D-element supports.
By (4) with A=X, H(H_J|S,X)=0. Fix any such (x,b). The map from
X_i to H_J given (x,b) is deterministic on its support. Every possible
X_i value is therefore mapped into one atom of probability D^(-j), so
its conditional atom cannot have larger probability. Since the entire
X side is independent of S, the conditional distribution of X_i given
(x,b) is exactly that given b. This proves (3). The identical argument
on the Y side is valid.

A conditional law with fewer members of X without X_i specified is
a mixture of the laws in (3) and has the same upper atom bound.
Factoring the probability of any positive-probability X tuple in any
order gives at most D^(-mj). A dealer tape value r_0 of positive
probability is mapped to one X tuple for each fixed S=x. The tape is
independent of S; therefore its probability cannot exceed the
probability of that X tuple conditional on x, which equals its
unconditional probability by privacy. This proves the tape atom
bound and, when j=r, its stated min-entropy consequence.

For attainment, identify the D secret values with the cyclic additive
group Z_D. For every matching index s and edge f in M_s, draw an
independent uniform R_(s,f) in Z_D, also independently of S. Both
endpoints receive this pad in their s-th coordinate. Helper h_s
receives

    h_s = S - sum_(f in M_s) R_(s,f)                                 (8)

in that group. A coalition with h_s covering M_s has one copy of
every relevant pad and adds them to h_s. For a fixed unauthorized
coalition, condition on its endpoint pads. For every helper s it holds,
at least one pad in matching s is missing. The missing pads are
independent uniform even after this conditioning. Distinct matchings'
pad coordinates are independently sampled, so all visible helper
values are jointly uniform independent of S and of the observed
endpoint values. Thus (8) is perfectly private against every
unauthorized coalition, not merely each helper separately.

Every endpoint receives r independent uniforms and each helper gets
one uniform. The dealer drew exactly mr independent uniforms, so
each endpoint has entropy rL, and the dealer tape has both entropy
measures mrL. This is the Benaloh–Leichter sharing of the monotone
formula: share the same S into each OR branch; additively split it
between the AND arguments of that branch; duplicate each edge pad
into the two endpoints of its OR. For D=2^b the group may instead
be bitwise XOR, requiring exactly mrb fair bits; arbitrary D uses
uniform finite random choices, not a fixed fair-bit budget. With a
nonuniform secret the conditional scheme is identical. Perfect
privacy depends on the positive support, and the stated costs
are the same.

## 5. Scope and an edge-overlap negative control

Edge-disjointness is essential for asserting (7) with all r helpers
selected. If the matchings overlap, the same proof works for any
subset whose partner of the chosen endpoint is different for each
selected helper. One cannot generally take all helpers: take the same
matching repeated r times and assign all r helpers the very same
masked secret, with one independent pad per edge. The exact access
rule is now any helper plus a cover of that single matching. The
scheme is perfect, every helper is ideal, and each endpoint needs
only one pad, not r. For distinct edge-disjoint matchings our
observations concern helper-size constraints; they neither replace
nor contradict Williamson's unrestricted lower bounds in [W,
Theorem 2 and Corollary 3].
