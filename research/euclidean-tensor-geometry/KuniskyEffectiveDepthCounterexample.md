# An unbounded counterexample to Kunisky's effective-depth certificate

**Yongxian Zhang.** AI-assisted proof development and internal verification; no external peer review or priority claim.

We disprove the universal resolution-proof quantifier in [Kunisky, arXiv:2111.02974, Conjecture 4.4](https://arxiv.org/pdf/2111.02974#page=18). The proposed objective can become arbitrarily large, even on minimally unsatisfiable formulas. For each number of variables the formula is fixed; only its tree resolution refutation varies. This does **not** disprove the weaker existential certificate question in the paragraph after the conjecture, the read-once theorem, or any proposed value of the sharp Komlós constant.

## 1. Formula and certificate

Fix \(n\ge3\). Let \(F_n\) contain all \(2^n\) clauses with exactly one literal on each of \(x_1,\ldots,x_n\). Put \(C=x_1\lor\cdots\lor x_n\). Every assignment falsifies exactly its own clause; in particular \(F_n\) is minimally unsatisfiable. Every non-tautological partial clause \(S\) on these variables is derivable by an exhaustive binary split on all variables not in \(S\), resolving the two opposite extensions at each step. This derives \(S\) exactly from the full clauses extending it and uses no weakening or tautologies.

For a tree resolution refutation \(T\), let \(p_D\) be the probability that fair coin choices from the root reach a leaf labeled \(D\in F_n\). This is \(2^{-d(D)}\) with the paper's effective depth \(d(D)\). The proposed objective in (41) is
\[
Q(T)=
\frac{1+\sum_{i=1}^n\sqrt{\sum_{D:\,x_i\text{ occurs in }D}p_D}}
{\sum_{D\in F_n}\sqrt{p_D}}.
\]
Occurrence includes either sign. Every variable occurs in every full clause, so the numerator here is exactly \(n+1\).

## 2. A reverse resolution walk concentrates the leaf law

Use states \(C\) and all non-tautological clauses of size at most \(n-1\). Start at the empty clause. State \(C\) is absorbing; in the proof it is made a leaf. A transition specifies the two children of a reverse resolution step, one for each possible fair coin outcome.

- If \(S\) is a proper all-positive subset of \(C\), choose a missing variable \(x_i\). Use \(S\lor x_i\) and \(\neg x_i\). The first child adds a positive literal to \(S\), so repeated first choices reach \(C\).
- If \(S\) contains a negative literal and has size \(<n-1\), choose a missing variable \(x_i\). Use \(x_i\) and \(S\lor\neg x_i\). The first child resets the process to a positive unit clause.
- If \(S\) contains a negative literal and has size \(n-1\), split it into one literal \(u\) and the rest, choosing \(u\) positive if possible. Resolve \(u\lor x_i\) and \((S\setminus\{u\})\lor\neg x_i\), with \(x_i\) the missing variable. Both children have size at most \(n-1\). For \(n\ge4\), the first child has size \(2<n-1\), hence is in one of the preceding cases. For \(n=3\), the first choice makes a positive two-literal clause if \(u\) is positive. Otherwise it makes a mixed clause; another first choice takes the positive literal in that mixed clause and thus makes a positive two-literal clause.

In each case there is a genuine ordinary resolution on \(x_i\), and a route to \(C\) of length at most \(n+2\). Conditional on any current state there is therefore probability at least \(2^{-(n+2)}\) to hit \(C\) in the next \(n+2\) steps. The nonabsorption probability after \(d\) steps is bounded by \((1-2^{-(n+2)})^{\lfloor d/(n+2)\rfloor}\).

Unroll the rules from the empty root to depth \(d\), stopping at \(C\). At each remaining frontier state attach its exhaustive resolution derivation described in Section 1. All leaves now belong to \(F_n\), and every edge pair is a valid resolution. Completion does not erase any already-absorbed leaf, so \(p_C\) tends to 1 as \(d\) goes to infinity. The number of possible leaf labels is the fixed number \(2^n\). Hence the denominator of \(Q\) tends to 1 and \(Q(T_d)\to n+1\). Since \(Q\le n+1\) for every proof on \(n\) variables (each inner probability is at most 1 and the denominator is at least 1), this is also the exact fixed-variable supremum. Taking \(n\) arbitrarily large proves unboundedness and, already at \(n=3\), contradicts the proposed \(1+\sqrt2\) bound.

## 3. Small exact instance and the quantifier distinction

The [exact checker](verify-kunisky-effective-depth.js) resolves every state locally, verifies the disjoint cover and frontier completion, and propagates dyadic masses using integers. Choose the smallest missing pivot in each step and, at a largest mixed state, take the smallest-index positive literal when one exists or the smallest-index literal otherwise. At \(n=3\) and \(d=46\), the completed proof has
\[
p_C=\frac{550690232438488}{562949953421312}.
\]
By Cauchy–Schwarz its objective is at least
\[
\frac{4\sqrt{p_C}}{\sqrt{p_C}+\sqrt{7(1-p_C)}}>\frac52>1+\sqrt2,
\]
where the first strict inequality is the integer test \(9p_C>175(1-p_C)\). The checker also tests four and five variables.

The complete truth-table resolution tree, with no repeated leaf labels and no concentration, gives the same formula \(F_n\) a certificate value \((n+1)/\sqrt{2^n}\). Thus our counterexample isolates the conjecture's claim about **every refutation**. It does not exclude the existence of a good refutation for every formula, nor does it increase any matrix discrepancy lower bound.

## 4. In fact every leaf-label law can be approximated

For the same fixed \(F_n\), the achievable effective-depth laws are dense in the full probability simplex on \(F_n\). To see this, choose an arbitrary dyadic approximation to a desired law with denominator \(2^k\). Construct \(k\) complete levels of reverse resolution while keeping every node at size at most \(n-1\). Use a missing pivot, put the existing literals in one child if the size is at most \(n-2\), and split them into two nonempty parts if the size is \(n-1\). All augmented children stay below full size, since \(n\ge3\). Assign desired target clauses to the \(2^k\) frontier nodes in the dyadic proportions. At each frontier node use the same concentration process, after flipping the signs of variables for its assigned full target clause. The probability of missing that particular target can be made uniformly as small as desired, with exhaustive completion as above. The final leaf-label law differs from the assigned dyadic law by at most this miss probability in total variation. This availability of a wide range of proof-dependent weights reinforces the distinction between universal and existential certificates.
