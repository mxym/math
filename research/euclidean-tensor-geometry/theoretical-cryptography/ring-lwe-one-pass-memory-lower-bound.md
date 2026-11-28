# A one-pass memory–sample lower bound for broad-noise Ring-LWE

This is a computational restriction, not another sample threshold:
when a learner must keep a small finite state between consecutive
samples, it still fails even in a regime where polynomially many
samples contain enough information. The lower bound allows arbitrary
computation on each current sample, including access to the full
continuous response. It is **not** a lower bound on unrestricted
classical running time, not a solver, and not a statement about
an implementation or a concrete cryptographic parameter.

## 1. Model and theorem

Fix an odd integer \(q\ge3\). Let \(d\to\infty\) through powers
of two and set \(R_d=(\mathbb Z/q)[x]/(x^d+1)\).
The hidden label \(S\) is uniform in \(R_d\).
Conditional on the label, independent observations are
\[
      A_i\sim\operatorname{Unif}(R_d),\qquad
      Y_i=(A_i S)/q+E_i\bmod1 ,
\]
using coefficient-grid coordinates in \(\mathbb T^d\).
The coefficient errors are independent, with circle density
\(f_b(t)=\sum_{j\in\mathbb Z}b^{j^2}e^{2\pi i jt}\);
the error law is known and \(b=b_d\in(0,1)\).
This is scalar continuous dual Ring-LWE in the orthogonal
power-basis coordinates, with \(b=e^{-\pi d s^2}\) for
canonical spherical width \(s\).

A **one-pass learner with \(s_{\rm mem}\) bits** has at most
\(2^{s_{\rm mem}}\) states at each layer. Its state transition
may be any measurable function, with fresh independent
randomness, of the state and the current full sample
\((A_i,Y_i)\). It cannot read previous samples again or keep
additional data outside the state. Its final exact-label
guess uses only the final state and independent randomness.
The observation horizon is deterministic and may depend on \(d\).
This is the nonuniform layered branching-program model with a
continuous input alphabet, not a bit-complexity restriction
on the computation *within* a layer.

**Theorem.** There exist positive constants \(b_0,c_1,c_2,c_3\)
depending only on \(q\) such that for all sufficiently large \(d\),
all \(0<b\le b_0\), and all one-pass learners with
\[
        s_{\rm mem}\le c_1\,\frac{d^2}{1+db},
       \qquad T\le \exp(c_2d),
 \tag{1}
\]
the uniform-prior success probability is at most
\(\exp(-c_3d)\).

For instance with \(b=d^{-1}\) the persistent memory lower
bound is quadratic in \(d\) for any nonnegligible success
in a polynomial-length stream. By contrast, the
[growing-odd-modulus statistical theorem](ring-lwe-growing-odd-modulus-broad-threshold.md)
implies that \(O(d^2)\) such observations already suffice
for success tending to 1 with *unrestricted* inference.
Indeed any fixed multiplicative margin above the scalar
full-grid mean-information threshold makes its standardized
offset diverge positively. Thus (1) concerns lost
computational access to the data, not a shortage of
samples or a hypothesis that the statistical optimum is
attainable efficiently.

## 2. A continuous-output extraction inequality

All hidden densities below are relative to the uniform
probability \(U\) on \(R_d\). Write
\(\|h\|_2^2=\mathbb E_U h^2\) and
\(\langle f,h\rangle=\mathbb E_U f h\).
For the response, use reference probability \(Q\) on
\(\mathbb T^d\) with density
\[
     g(y)=\prod_j f_{b^{q^2}}(q y_j)
\]
relative to Haar. This is the full-grid average
of \(p=f_b^{\otimes d}\).
The one-response density given \(a,x\), relative to \(Q\), is
\[
      w_{a,x}(y)=p(y-a x/q)/g(y).
\]
For sufficiently small absolute \(b\),
\[
     0<w_{a,x}(y)\le B:=\exp(C d b)
 \tag{2}
\]
uniformly. This follows from \(f_b=1+O(b)\) uniformly
and the same estimate for \(f_{b^{q^2}}\).
For a nonnegative function \(h\) on \(R_d\) let
\(M_a h(y)=\mathbb E_U h(x)w_{a,x}(y)\).

Every nonzero ideal in \(R_d\) has size at least
\(\exp(\alpha_q d)\) for some \(\alpha_q>0\) and large
\(d\). To see this, any such ideal has a simple module
quotient, isomorphic to a residue field of \(R_d\), by
taking a maximal proper submodule and a nonzero generator
in the resulting simple module. At an odd prime \(p\mid q\)
the residue-field order is \(p^{\operatorname{ord}_{2d}(p)}\)
because the cyclotomic root has exact order \(2d\).
The degree is a fixed positive fraction of \(d\) for fixed
\(p\): if \(d=2^k\) and \(k\) is large,
\(\operatorname{ord}_{2d}(p)=2^{k+2-v_2(p^2-1)}\)
by the valuation under repeated squaring.
There are only finitely many \(p\mid q\).
This uses the same elementary ideal size fact as the
[fixed-modulus stabilization](ring-lwe-fixed-odd-modulus-threshold.md).

Let \(h\) be a probability density relative to \(U\).
In the Fourier expansion of \(M_a h(y)\), the frequencies
\(u\in q\mathbb Z^d\) give exactly \(1\) after division
by \(g\), since \(\mathbb E_U h=1\).
The other Fourier coefficients of the undivided expression
are \(b^{\|u\|^2}\widehat h(\bar a u\bmod q)\).
In fact the coefficient dot product in the dyadic power
basis is \(\operatorname{Tr}(u\bar x)/d\), so the
adjoint of multiplication by \(a\) is multiplication by
\(\bar a\). Using the opposite sign convention for the
Fourier transform only conjugates this formula.
For a uniformly random \(a\), \(\bar a u\bmod q\)
is uniform on the nonzero ideal generated by \(u\bmod q\).
Finite Parseval and Cauchy–Schwarz therefore give
\[
      \mathbb E_a|\widehat h(\bar a u\bmod q)|
                         \le e^{-\alpha_q d/2}\|h\|_2.
\]
Taking an absolute Fourier sum, and using
\(\sum_{j\in\mathbb Z} b^{j^2}\le e^{C b}\) and
\(1/\min_y g(y)\le e^{Cdb}\), yields
\[
 \mathbb E_a\sup_y|M_a h(y)-1|
       \le \exp(-\alpha_q d/2+C' d b)\|h\|_2 .
 \tag{3}
\]
The use of the actual tilted reference \(g\) is important:
frequencies trivial on the signal grid are not counted
as information about the hidden label.

Choose \(r>0\) depending only on \(q\), for example
\(r=\alpha_q/16\), and decrease \(b_0\) if needed.
By (3) and Markov, uniformly for every nonnegative
probability density \(h\) with \(\|h\|_2\le e^{rd}\),
\[
  \Pr_a\left(\sup_y|M_a h(y)-1|>\epsilon\right)\le\epsilon,
                   \qquad \epsilon=e^{-rd}.
 \tag{4}
\]
The bad-row sets can depend on \(h\).
The estimate is pointwise in the continuous response
coordinate, outside the small bad set of public rows.

## 3. A bounded-density extension of the branching-program argument

We use the posterior truncation and high-moment overlap
method of [Garg–Raz–Tal, §§4.1–4.3](https://arxiv.org/abs/1708.02639),
who analyze deterministic binary labels from an extractor matrix.
We give the needed extension to continuous stochastic responses:
(2), (4) replace the balanced discrete label condition.
The envelope \(B\) appears explicitly in the moment order
and hence in the allowed width.

Let \(\ell=r/64,\ \eta=r/8,\ L=\log(2B)\).
Decrease \(b_0\) so that \(L\le\ell d/16\) for large \(d\).
We first analyze a deterministic state program, which suffices
by fixing all independent learner randomness.

Define a truncated version of the program path inductively.
For a state \(v\) reached by the truncated path, \(f_v\)
is the posterior density of \(S\) conditioned on reaching it.
A state with \(\|f_v\|_2>H:=e^{\ell d}\) is
**significant** and stops the path.
At any nonsignificant nonterminal state, stop if the true
\(S\) is in the heavy set \(f_v(S)>F:=e^{(2\ell+\eta)d}\).
Otherwise stop if the next public row is bad for \(f_v\)
in (4). On the surviving outcomes take the program transition.
This truncation is a mathematical device, not an action
the learner performs. At a nonsignificant state the
conditional probability of discarding a heavy hidden label
is at most \(e^{-\eta d}\), because
\(\mathbb E_{f_v U} f_v=\|f_v\|_2^2\le H^2\).
The next public row is independent and uniform given
the state and past. Hence the probability of a bad row is
at most \(\epsilon\) by (4).
For \(T\le e^{rd/64}\), all such stopping probabilities
over the path sum to \(\exp(-\Omega_q(d))\).

For an accepted row and response, put
\(\tilde f_v=f_v1_{\{f_v\le F\}}\).
The conditional density of the exact observation, without
renormalizing for survival, is
\[
       c_v(a,y)=M_a\tilde f_v(y)\ge
              1-\epsilon-B e^{-\eta d}=:1-\delta,
\]
relative to the row law times \(Q\), on good rows.
Here the removed mass is at most \(e^{-\eta d}\) and
its observation density bounded by (2).
The resulting posterior on that edge is
\[
       f_{v,a,y}(x)=\tilde f_v(x)w_{a,x}(y)/c_v(a,y).
 \tag{5}
\]
For large \(d\) we have \(\delta\le e^{-rd/16}\), and
\(\|f_{v,a,y}\|_2\le2BH\).
Each next state is a mixture of its incoming observation
posteriors, so by convexity the same norm bound holds
for every reached state (the initial state has density 1).
This formulation integrates over a response alphabet rather
than counting its possible symbols.

Fix a reached target significant state \(s\) and use its
posterior as the reference \(f_s\). Set
\[
 k=\left\lfloor \frac{rd}{8L}\right\rfloor,\qquad
 Z_i=\sum_{v\text{ in layer }i}\Pr(v)
                 \langle f_v,f_s\rangle^k
\]
for the truncated path. In particular \(Z_0=1\) and
\(k\ge rd/(16L)\ge1\).
For a nonsignificant state \(v\) write
\(z_v=\langle f_v,f_s\rangle\),
\(h_v=\tilde f_v f_s\), and \(u_v=\mathbb E_U h_v\le z_v\).
The overlap after an accepted observation equals
\(M_a h_v(y)/c_v(a,y)\), by (5).

If \(u_v<1\), this overlap is bounded by \(2B\)
by (2) and the lower bound for \(c_v\).
If \(u_v\ge1\), \(h_v/u_v\) is a probability density with
\[
       \|h_v/u_v\|_2
         \le F\cdot2BH
         = \exp((3\ell+\eta)d+L)\le e^{rd}.
\]
Then (4) applies to it. On rows good for both tests,
the updated overlap is at most
\((1+\epsilon)u_v/(1-\delta)\le (1+O(\delta))z_v\).
On those exceptional rows that are still accepted,
the updated overlap is at most \(2B z_v\); their
conditional total probability is at most \(\epsilon\),
since the fresh row law is uniform and survival can
only remove mass. Thus the expected outgoing powered
overlap at \(v\), treating stops as zero outgoing mass,
is bounded by
\[
   \bigl((1+O(\delta))^k+\epsilon(2B)^k\bigr)z_v^k+(2B)^k .
\]
Merging observations into states does not increase
this convex-power potential, by Jensen applied to
their mixture posterior. This proves the recurrence
\[
 Z_{i+1}\le\bigl((1+O(\delta))^k+\epsilon(2B)^k\bigr)Z_i
                         +(2B)^k .
 \tag{6}
\]
All observations here have legitimate conditional densities
relative to \(Q\); no discretization of a current sample is
used in the proof.

Since \((2B)^k\le e^{rd/8}\), the multiplicative factor
in (6) is \(1+O(d e^{-rd/16})+e^{-7rd/8}\).
For \(T\le e^{rd/64}\) its total product is at most 2
for large \(d\). Therefore \(Z_i\le2(1+T e^{rd/8})\).
At the target state itself the overlap is
\(\langle f_s,f_s\rangle>H^2\).
Its probability of being reached by the truncated path
is consequently at most \(2(1+T e^{rd/8})e^{-2\ell dk}\).
A union over at most \(2T W\) states, with \(W\) the
bound on the number of states in one layer, is
\(\exp(-\Omega_q(d))\) whenever
\[
                \log W\le\frac{\ell r}{32}\frac{d^2}{L}.
\]
Indeed \(2\ell dk\ge(\ell r/8)d^2/L\);
after paying the width, the remaining negative
term dominates \(2\log T+rd/8+O(1)\) using
\(L\le\ell d/16\).
This completes the bound on significant stops.

If the path reaches a nonsignificant final state,
the maximal posterior atom is at most
\(H/\sqrt{|R_d|}=\exp(\ell d)q^{-d/2}\),
again exponentially small. Add all the stopping
probabilities to bound the full program's success.
Since \(L=\log2+Cdb\), this proves (1) after adjusting
constants, and also for randomized state transitions
by averaging the fixed randomness.

## 4. Comparison to prior models

The scalar torus observation convention is
[Lyubashevsky–Peikert–Regev, Definitions 3.1–3.2](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf).
The extractor method and significant-state potential are
classical [Garg–Raz–Tal](https://arxiv.org/abs/1708.02639);
[Garg–Kothari–Liu–Raz](https://arxiv.org/abs/2107.02320)
analyze noisy binary matrix labels.
[OpenAI's subsphere preprint](https://github.com/openai/math/tree/main/preprints/Subsphere-methods-for-memory-sample-lower-bounds-in-noiseless-Gaussian-regression-September-27-2026)
studies a different real, noiseless regression model.
The ingredients here are the ideal-size Fourier bound for
the full ring-product response and a continuous bounded-density
posterior argument with explicit envelope dependence.
The earlier [response interaction-degree obstruction](ring-lwe-response-degree-obstruction.md)
restricts a function of all response records instead.
Here each transition may have arbitrary degree and
arbitrary nonuniform processing; the restriction is a
finite state between successive records.
Neither bound decides the complexity of unrestricted
Ring-LWE or guarantees anything for a deployment.
The companion checker verifies only finite Fourier/ideal
bookkeeping and potential-parameter inequalities.
