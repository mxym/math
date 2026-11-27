# A field-size bound with exponents \((6,6)\)

We use \(p\) for the prime of the underlying two-query proof and \(P\)
for the target prime. A fully linear verifier samples a tuple
\((q_1,q_2,A)\) without accessing \(x\) or the proof \(\pi\). On
\(v=x\mathbin\Vert\pi\) it obtains the two scalar products
\(y=(\langle q_1,v\rangle,\langle q_2,v\rangle)\) and accepts if
\(y\in A\). A DPP instead samples one query vector and a subset of
\(\mathbb F_P\); the set can be specified by its polynomial-time
membership test, as in Definition 3.1 and Remark 3.2 of [BHIRW].
The promise limits the tested input \(x\) to Boolean vectors, not the
alleged proof \(\pi\).

## 1. Modular packing lemma

Let \(P\) be prime and \(B_1,B_2\) be nonnegative integers with
\(4B_i<P\). Write
\[
\mathcal B=([-B_1,B_1]\times[-B_2,B_2])\cap\mathbb Z^2,\quad
N=(2B_1+1)(2B_2+1),\quad
D=(4B_1+1)(4B_2+1)-1.
\]
The box and its difference box both inject coordinatewise into
\(\mathbb F_P^2\). Assume that each genuine proof's response pair always
lies in \(\mathcal B\), and the old decision test rejects outside
\(\mathcal B\). If the original definition only promises the bound on
genuine responses, intersect its acceptance predicate with \(\mathcal B\);
this does not affect the honest acceptance or increase the old
soundness error.

Independently of \((q_1,q_2,A)\), draw \(t\) uniformly in \(\mathbb F_P\)
and make the single query \(q_1+tq_2\). The response is
\(z=L_t(y)=y_1+ty_2\). This is an ordinary dot product; its query vector,
and the following accepting-set description, do not depend on \(v\).

**Global injectivity variant.** A slope is bad if \(L_t\) fails to be
one-to-one on \(\mathcal B\). If a collision of two distinct box points
occurs, their nonzero integer difference \((d_1,d_2)\) lies in the
difference box and satisfies \(d_1+td_2=0\) in \(\mathbb F_P\). When
\(d_2=0\), \(d_1\ne0\) remains nonzero modulo \(P\), so no collision
occurs. Otherwise \(d_2\) remains nonzero modulo \(P\) and prescribes
exactly one slope \(t=-d_1/d_2\). Thus there are at most \(D\) bad slopes.
Conversely each nonzero difference vector in the kernel does represent
the difference of two box points, so this test exactly detects badness.

On a bad slope let the accepting set be \(\mathbb F_P\). On a good slope
it is \(L_t(A\cap\mathcal B)\): reject if \(z\) has no lift in the box;
otherwise decode the unique lift and apply the old predicate. A true
accepted pair always remains accepted. On a fixed rejected pair
\(y\in\mathcal B\), acceptance can occur only on a bad slope. On a fixed
pair \(y\notin\mathcal B\), a good slope can accept only if there is a box
point \(b\) such that \(L_t(y)=L_t(b)\); for each \(b\), field-coordinate
difference zero in the second coordinate permits no slope, and otherwise
there is at most one. Thus soundness increases by at most
\((D+N)/P\). This argument conditions on \((q_1,q_2,A)\) and on the
fixed input-proof pair before sampling \(t\). It never assumes a
distribution of the old answers, nor does it restrict erroneous
answers to be small integers.

**Fiber-local variant.** In fact, we only need to count lifts for the
actual \(z\). With zero lifts, reject. With one lift, apply \(A\) to it.
With at least two lifts, accept. If the fixed original pair is accepted,
then it lies in the box, and this rule still accepts for **every** slope.
If it is in the box and rejected, the new rule can accept only if a
different box point projects to the same answer. For each of the
\(N-1\) other points there is at most one slope, by the same field
equation. If the true pair is outside the box, any acceptance requires
at least one lift, again prescribing at most \(N\) slopes in total.
Consequently, for any fixed verifier draw and any true pair, the new
acceptance probability is bounded by the old decision plus
\[
\delta=N/P . \tag{1}
\]
This is the thesis used below. It also preserves any existing strong
soundness dichotomy up to adding \(\delta\) to the error: probabilities
cannot decrease, and a formerly low-acceptance pair increases by at
most \(\delta\). This transfer observation does not assert strong
soundness of our starting bounded embedding. If the first query's
proof part is \(\tau\)-hyperplane-evading conditional on the second
query in the sense of [BHIRW, Definition 5.5], so is the packed query:
conditional on fixed \(q_2,t\), the condition of hitting any fixed
affine hyperplane translates to one such condition on the first query.
Averaging over the fixed values preserves the bound.

## 2. Deterministic bit-polynomial decision and decoding

For integer bounds \(a\le b\), \(c\le d\) with \(b-a<P\), the number of
box lifts of \(z\) is
\[
\begin{split}
C_{t,z}(a,b,c,d)
  &=\sum_{u=c}^{d}
  \left\{\left\lfloor\frac{b-z+t u}{P}\right\rfloor-
             \left\lfloor\frac{a-1-z+t u}{P}\right\rfloor\right\}.
\end{split} \tag{2}
\]
For each fixed \(u\) the difference counts the possible integers \(j\)
with \(a\le z-tu+Pj\le b\), hence counts exactly the first-coordinate
values. This includes negative values and modular wraparound. In the
global version, badness is exactly
\(C_{t,0}(-2B_1,2B_1,-2B_2,2B_2)>1\), since the zero difference is
included once. In the fiber-local version, count only the original
rectangle.

Equation (2) takes the difference of two floor sums
\(F(n,m,r,s)=\sum_{i=0}^{n-1}\lfloor(ri+s)/m\rfloor\), with
\(n=d-c+1\). Here is an exact Euclidean recurrence. Write
\(r=q_r m+r_0\), \(s=q_s m+s_0\), using remainders in \([0,m-1]\),
and add \(q_r n(n-1)/2+q_s n\) before passing to \(r_0,s_0\).
With \(0\le r,s<m\), put \(rn+s=mQ+R\). For \(Q=0\) the reduced
sum is zero. Otherwise \(r>0\), and
\[
F(n,m,r,s)=F(Q,r,m,R).
\]
Indeed, by counting the inequalities \(m j\le ri+s\) for
\(1\le j\le Q\), each \(j\) contributes
\(n-\lceil(mj-s)/r\rceil
=\lfloor(m(Q-j)+R)/r\rfloor\). Endpoints at which that contribution
is zero are included harmlessly. Reducing the swapped coefficient
makes the successive moduli an ordinary Euclidean remainder sequence.
For our initial intervals and canonical representatives \(t,z\),
all intermediate integers have \(O(\log P)\) bits, and there are
\(O(\log P)\) Euclidean steps. These bounds follow also from the facts
that the length \(n\) never increases in a reduced step and the
products in the recurrence are at most polynomial in \(P\).

If the count is one, binary search the least \(u\in[c,d]\) for which
the prefix count \(C_{t,z}(a,b,c,u)\) is positive. This takes
\(O(\log P)\) prefix counts. Its first coordinate is the unique
representative of \(z-tu\) in \([a,b]\), computed as
\(a+((z-tu-a)\bmod P)\). Thus deciding membership needs a
deterministic polynomial in \(\log P\), plus at most one invocation
of the old predicate. The query vector is produced in linear field
operations in its length once the two old vectors are produced.
The acceptance descriptor stores the slope and the old predicate
description; it does not list residues.

An alternative is fixed-dimensional integer programming [Lenstra]:
with three integer variables \(u_1,u_2,j\), impose the four box
inequalities and \(u_1+t u_2-Pj=z\) (two inequalities).
All coefficients have \(O(\log P)\) bits. Feasibility and recovery of
one point have bit-polynomial time with this fixed dimension. The
global kernel test may be done with four feasibility calls on the
difference box after imposing one of
\(u_1\le-1,u_1\ge1,u_2\le-1,u_2\ge1\); equivalently one can use the
exact count. The dimension does not grow with circuit size. No
integer-programming theorem is needed for the floor-sum decoder.

## 3. Instantiation with the two-query Boolean-circuit proof

Let \(s\ge1\) count inputs and fan-in-two NAND gates, \(0<\varepsilon<1\),
and \(n\le s\) be the number of input bits given to the verifier by
linear access (the witness's input wires also count in \(s\)).
A bounded-fan-in Boolean circuit of size \(S\) in the source's
convention has such a representation with \(s=O(S)\). If unused
input wires are not counted in a gate-size convention, the proof
can omit them and pad their query coefficients by zero.
Choose \(\eta=\varepsilon/4\) and a prime
\[
p\in(L,2L],\qquad L=\left\lceil16(s+400)/\varepsilon\right\rceil.
\]
Bertrand's postulate gives existence. We use \(p\) as an auxiliary
construction parameter, as in [BHIRW]. Given the parameters, the
algorithms are uniform. If it is to be generated, uniform interval
prime search with deterministic primality testing has expected
bit-polynomial setup time by the prime number theorem and can be
run once independently of the statement; deterministic prime
generation in time polynomial in \(\log p\) is not asserted.
Only a dyadic target in \((\varepsilon/2,\varepsilon]\) is needed
if the numerical parameter must be represented in finitely many bits.

Use [BHIRW, Corollary B.6], the square-span-program two-query FLPCP
implicit in [DFGK14]. It has perfect completeness, proof length
\(2s\), soundness \((2s+1)/p<\eta\), and acceptance
\((\alpha,\alpha^2)\). Swap the queries, so for fixed second answer
exactly one first answer passes the test. This yields the required
evasiveness at most \(1/p\le\eta\) for the embedding. Encode each
honest proof coordinate in \(\ell=\lceil\log_2 p\rceil\) bits, lifting
the linear queries via their weighted bit coefficients as in
[BHIRW, Claim 5.3]. For arbitrary purported bits over \(\mathbb F_p\)
the same weighted map gives an ordinary old proof, so no assumption
that the alleged proof is Boolean is needed. Append 400 zero bits to
an honest proof, ignored by the old query. The proof length is then
\(m=2s\ell+400\) and \(\mu=n+m\ge400\).

Apply [BHIRW, Theorem 5.6] with this \(\eta\), the integer
\(\gamma=\lceil100\mu p/\eta\rceil\), and any prime
\[
P\ge \left\lceil\mu^2\gamma p^2/\eta^2\right\rceil . \tag{3}
\]
This is the cited bounded embedding theorem, not a new embedding
estimate. It yields a two-query promise FLPCP over \(\mathbb F_P\)
with the same proof length and honest proof, soundness at most
\(1.01\eta\), and coordinate bounds
\[
 B_1=\lfloor\mu(p\gamma-1)/2\rfloor,\qquad
 B_2=\lfloor\mu(p-1)/2\rfloor.
\]
The old decision checks the centered bounds and then uses the
residue predicate modulo \(p\). The main hypotheses of the source
theorem are \(p,P\) prime, \(\eta\ge p^{-1}\), \(\mu\ge400\),
\(\gamma\ge100\mu p/\eta\), (3), a Boolean honest proof, and the
evasive accepting set; all have been checked above. Its first query
has hyperplane-evading parameter \(\gamma^{-1}\).

We have \(P>4B_i\), since \(4B_1<2\mu p\gamma\) and
\(P/(\mu p\gamma)\ge\mu p/\eta^2>2\), and \(B_2\le B_1\).
Moreover \(2B_1+1\le\mu p\gamma\),
\(2B_2+1\le\mu p\), so \(N\le\mu^2p^2\gamma\) and \(N/P\le\eta^2\).
Thus (1) gives soundness at most \(1.01\eta+\eta^2<\varepsilon\).
Even the global variant has error at most
\(1.01\eta+5\eta^2<\varepsilon\), since \(D+N\le5N\).
When a worst-case bit-budget sampler is desired for the new slope,
reduce \(\lceil\log_2 P\rceil\) fresh fair bits modulo \(P\).
Each atom is then at most \(2/P\), so all slope-loss bounds at most
double and still fit within \(\varepsilon\). The exact-uniform
version follows the old field-sampling convention and adds
\(\log_2 P\) verifier randomness in the log-of-support convention of
the source. The honest prover does not use the new slope or change
its proof.

Finally \(p=O(s/\varepsilon)\), \(\mu=O(s\log(2s/\varepsilon))\), and
\(\gamma\le101\mu p/\eta\). The right side of (3) is at most
\(101\mu^3p^3/\eta^3+1\), which is
\(O(s^6\log^3(2s/\varepsilon)/\varepsilon^6)\). Thus a fixed
sufficient \(C\) works for **every** prime \(P\) above the headline
threshold. The original length remains \(O(S\log(2S/\varepsilon))\)
field elements. There is no reliance on enumerating \(P\), a box,
or \(\varepsilon^{-1}\) at verification. For \(\varepsilon\ge1\) a
trivial verifier suffices, and a nonpositive \(\varepsilon\) is not
a parameter of the theorem.

## 4. What is and is not being compared

Relative to the exponent 9 stated in [BHIRW, Theorem 1.3], this
gives exponent 6 without changing the underlying two-query
square-span proof, the Boolean promise, or the proof length.
The new savings occur because modular collisions are charged once
per short difference (or, fiber-locally, per possible reconstruction
of a fixed answer), and modular decoding has no mixed-radix
no-wrap requirement. The scalar form \(q_1+tq_2\) itself is old:
Theorem 5.8 and its preceding construction already use a scalar
with a restricted integer range. See SOURCES for the exact comparison.
The result does not settle the optimal large-field soundness
exponent, improve the bounded embedding, guarantee strong soundness
of that embedding, or make packed responses small in the target
field. Accordingly it is not a claim that a particular succinct
argument, encryption construction, or deployed verifier inherits
these parameters.
