# Statistical robust additive randomized encodings from residual histogram separation

## 1. Model and statement

Fix a number \(n\ge1\) of parties and fixed finite input and output
sets. A partition \(\mathcal B\) of the party positions defines
exchangeability blocks. Parties in the same block have the same
input set. Write \(f\) for a function invariant under every
permutation within each block.

For \(H\subseteq[n]\) and an honest input assignment \(x_H\), let
\(f_{H,x_H}\) be the whole residual function on the free positions
\([n]\setminus H\); its equality to another residual is pointwise
equality on every free completion. The **block histograms** of
\(x_H\) record all multiplicities in each \(H\cap B\), for
\(B\in\mathcal B\). The following condition is only for proper
\(H\):
\[
      f_{H,x_H}=f_{H,x'_H}
       \ \Longrightarrow\
      x_H,x'_H\text{ have identical block histograms}.       \tag{1}
\]
Invariance gives the reverse implication. Condition (1) does
not ask an output from one particular free completion to
determine the histograms.

**Theorem 1.** Under (1), \(f\) has a PPT statistically correct,
statistically robust additive randomized encoding in the sense
of [HIKR, Definitions 3.1 and 3.4]. For every proper \(H\) its
partial-sum simulation is **exact**, including all public parameters.
The encoders use independent private randomness conditioned on
the public setup. In fact we only require an ordinary statistical
ARE for \(f\) over an explicit finite Abelian group whose elements
can be indexed efficiently; the finite-function result of [BEGI]
supplies such an ARE. The compiler does not depend on a security
assumption or on private setup.

This is a subclass of [BEGI, §1.4]'s finite-function robust ARE
question, not an answer for every finite function. In the model
the observer receives public parameters and the aggregate of the
honest encodings, not separately identified honest messages.
Number of parties and all finite domains are fixed as the
security parameter grows.

## 2. A carrier whose collision hides the sum of pads

Let \(F=\mathbb F_q\), \(q=2^m\), with a binary basis. Write
\(X=(u,v)\in F^2\times F^2=F^4\) and
\(Q(X)=u_1v_1+u_2v_2\in F\).
Let \(G\) be the desired pad group, of size \(M\), with a public
bijection between \(\{0,\ldots,M-1\}\) and \(G\). Identify \(F\)
with the integers \(0,\ldots,q-1\) using the binary basis and
let \(\phi:F\to G\) take the value at the index reduced modulo
\(M\). This map need not be linear. Its image of a uniform field
element has TV distance at most \(M/(2q)\) from uniform on \(G\),
since each singleton probability differs from \(1/M\) by at
most \(1/q\).

For independent uniform \(X,X'\in F^4\), let \(Z=X+X'\).
Conditional on \(Z=z\), \(X\) is uniform and \(X'=X+z\).
For \(z=(a,b)\ne0\) define
\(L_z(X)=u\cdot b+a\cdot v\); then
\(Q(X+z)=Q(X)+Q(z)+L_z(X)\).
For any nontrivial additive character \(\chi\) of \(F\), the
characters of \(F^2\) are \(\chi(sx+ty)\), \(s,t\in F\).
For \(s=0,\ t\ne0\), the mean of
\(\chi(sQ(X)+tL_z(X))\) is zero because \(L_z\) is a
nonzero linear form. For \(s\ne0\), first average over \(v\):
this average vanishes unless \(su+ta=0\), which fixes a unique
\(u\in F^2\); at that \(u\) the surviving character has modulus
one. The mean therefore has modulus \(q^{-2}\).
By Parseval followed by Cauchy–Schwarz, the distribution of
\((Q(X),L_z(X))\) has TV distance from uniform on \(F^2\) at most
\[
    \frac12\left(q(q-1)q^{-4}\right)^{1/2}<\frac1{2q}.       \tag{2}
\]
Indeed, with Fourier coefficients normalized as character expectations,
the chi-squared distance to uniform is the sum of the squared
nonconstant coefficients. The affine bijection
\((r,l)\mapsto(r,r+Q(z)+l)\) gives the same distance bound for
\((Q(X),Q(X+z))\). Applying \(\phi\) to both outputs and then
adding the pads in \(G\) costs at most an additional \(M/q\) in
distance by the product coupling bound. Thus for every \(z\ne0\)
the conditional pad sum is \((1/(2q)+M/q)\)-close to uniform.
The atom \(Z=0\) has probability \(q^{-4}\); no conditional
guarantee is required on that atom. In particular for the joint
law, preserving the actual carrier sum,
\[
 (X+X',\phi(Q(X))+\phi(Q(X')))
    \quad\text{is }\kappa\text{-close to }(Z,U_G),
 \qquad
 \kappa=q^{-4}+1/(2q)+M/q,                                  \tag{3}
\]
where \(U_G\) is independent. The same statement remains true
when adjoining any independent variables, and applying any
deterministic function to all of them cannot increase TV.

## 3. Compiling an ordinary ARE

Let \(G=G_\lambda\) be the ordinary ARE group, with encoder
\(E(j,x)\) taking a designated party role \(j\) and decoder \(D\)
for the sum. Write \(\epsilon_0,\delta_0\) for its negligible
correctness and simulation errors. Use a public field
\(F\) with \(q\ge 2^{\lambda+3}M\), so (3) is at most
\(2^{-\lambda}\). The chosen base ARE has no private or public
setup other than the given explicit group description. A fresh
independent ordinary public setup per round can be included
without changing the proof when the group interface has the
same requirements; that variant is not needed here.

In one trial, each party \(i\) in block \(B\), on input \(x_i\):
1. Chooses a role \(r_i\) from the positions in \(B\), with
   the same input-independent distribution for all parties in
   the block. Each role has probability at least \(1/(2|B|)\).
2. Draws an independent uniform carrier \(X_i\in F^4\) and
   an independent base encoding \(E(r_i,x_i)\).
3. Sends the group element
   \[
   \bigl(e_{r_i},\ (\mathbf1_{j=r_i}X_i)_{j=1}^{n},\
                  E(r_i,x_i)+\phi(Q(X_i))\bigr)
   \in(\mathbb Z/(n+1))^n\times(F^4)^n\times G ,
   \]
   where \(e_r\) is the \(r\)-th unit vector. All additions
   in the first two fields are their indicated group additions.

The decoder uses the count vector to detect a *good* trial, one
in which every role is occupied exactly once. Counts never wrap
even on the full membership set. In a good trial the carrier
slot for each role holds precisely its individual carrier.
Subtracting the sum of recovered pads gives the ordinary
ARE sum. The role assignment is a permutation within each
block, so \(D\) recovers \(f(x)\) except with probability
\(\epsilon_0\). The roles and base randomness are independent.
For block size \(s\), the chance it has no duplicate role is
\(s!\prod_{j\in B}\Pr[r_i=j]\ge s!/(2s)^s\). Thus a good trial
has probability at least \(p_*=\prod_{B\in\mathcal B}|B|!/
(2|B|)^{|B|}>0\), a constant because \(n\) is fixed.

Use \(t=\lceil \lambda/p_*\rceil\) independent trials in the
direct product group, and decode the first good one; if there is
none, return a fixed output. The probability of the latter event
is at most \(e^{-\lambda}\). The first good trial's base-ARE
error is at most \(\epsilon_0\), because selection uses only
roles and each role permutation computes the same function.

**Full honest set.** Fix the role assignment in one trial;
it is independent of inputs. In a good trial the observable
carrier vector is independent of the ordinary ARE sum. For
two full inputs with the same \(f\)-output the two ordinary-sum
laws have distance at most \(2\delta_0\), including after any
fixed permitted role permutation. Revealing the count and
carrier vectors and adding the pads to the ordinary sum are
independent sampling and deterministic postprocessing, so the
same bound applies to the aggregate of the good trial.

In a bad trial, choose a fixed pair of participants whose roles
coincide, as a deterministic function of the role assignment.
For this analysis condition on all base encodings and all other
carriers. They are independent of the selected pair's carriers.
The aggregate carrier slots are now determined by the selected
pair's sum \(Z\), including when three or more parties chose the
same role. By (3), replacing the selected pair's total pad by an
independent uniform element of \(G\), preserving its carrier
sum, costs at most \(\kappa\). All the other pads and the
ordinary aggregate are merely added to that uniform group
element. After removing the extra conditioning, the comparison
law has the actual distribution of role counts and carrier sums
and an independent uniform last slot. It does not depend on the
inputs. This argument can reveal the entire role assignment
for analysis; it does not reveal individual carriers of the
selected pair and does not assume independence after revealing
those carriers.

Hence views for two full inputs with the same output are at
distance at most \(2t(\delta_0+\kappa)\), by mixtures over roles
and product/hybrid accumulation across all trials, including
the rejected ones. The all-honest simulator reads the output
from its residual oracle and samples the encoding of any fixed
representative full input with that output. Such a representative
is computable in time constant in \(\lambda\), because the
function is fixed and finite.

**Proper honest sets.** The full local distribution of a party's
message depends only on its block, its input, and public
parameters, not on its identity in the block. Consequently the
aggregate law on any \(H\), including all trial slots jointly,
is unchanged by permuting the inputs among \(H\cap B\) in
every block. This follows directly by relabeling independent
local random coins (or by commutativity of convolution). In
particular it holds on every public setup value, and for any
role-count law, not merely on good trials. For proper \(H\) the
simulator can query the entire fixed finite residual table,
enumerate honest assignments to find any representative with
that table, and sample the actual honest aggregate on it. By
(1) this is exactly the real law, including the publicly chosen
setup. For \(H=\varnothing\), the aggregate is zero.

**Bit complexity and public setup.** In the finite-function
application [BEGI, §4.1, §5.2] gives a polynomial-time
ordinary ARE from a finite DRE and bit-OT ARE (see also the
first corollary in §5.3), in explicitly
represented groups. Its groups are products of the explicit
coordinate groups in the construction (cyclic and binary
coordinates suffice), so their size and an indexing can be
computed using mixed radix. Security parameters can be chosen
so \(\epsilon_0,\delta_0\) are negligible and \(\log M\) is
polynomial in \(\lambda\). Here \(m\) is of order
\(\lambda+\log M\). For each fixed block, the role distribution
can be sampled by reducing a fixed number of fair bits
modulo its size \(s\), using \(2^{\lceil\log_2(2s)\rceil}\)
possible draws; thus every role probability is at least \(1/(2s)\).
A field may be generated publicly by testing random monic binary
polynomials of degree \(m\) for irreducibility, with a fixed
cutoff of \(2m\lambda\) candidates. For \(m\ge2\) the fraction
irreducible is at least \(1/(2m)\), since elements in proper
subfields of \(\mathbb F_{2^m}\) are at most
\(\sum_{d=1}^{\lfloor m/2\rfloor}2^d\le2^{m-1}\), and each
degree-\(m\) minimal polynomial has \(m\) roots. Divisibility
against \(X^{2^j}-X\) for \(j\le m/2\) via modular powering
and polynomial gcd gives a deterministic polynomial-time test.
Setup failure has probability at most \(e^{-\lambda}\);
on failure flag it publicly, use zero messages and a fixed
decoded output. This adds at most \(e^{-\lambda}\) to correctness
error and none to privacy. The failed public group may simply
be defined using binary vector carrier addition. In all cases the total correctness error is at most
\(\epsilon_0+2e^{-\lambda}\), and the full-set simulation error
is at most \(2t(\delta_0+2^{-\lambda})\); proper sets have zero
error. If an ordinary group element takes \(b_G\) bits and a
base encoder takes at most \(r_G\) private random bits, one
compiled message uses at most
\[
 t\bigl(n\lceil\log_2(n+1)\rceil+4mn+b_G\bigr)
\]
bits and
\(t(\lceil\log_2(2n)\rceil+4m+r_G)\) private random bits.
The field setup uses at most \(2m^2\lambda\) random bits and
publishes the polynomial and success flag. Consequently all
coins, operations, and lengths are polynomial in \(\lambda\).
The estimate does not assert efficiency as the number of parties,
domain sizes or descriptions of the finite functions grow.

## 4. Concrete scope and comparison

### 4.1 All symmetric Boolean functions on three bits

If \(f\) is symmetric on three Boolean inputs, it is given by a
word \(a_0a_1a_2a_3\) of output values indexed by total weight.
For two honest positions, the residual table of honest weight
\(w\in\{0,1,2\}\) is \((a_w,a_{w+1})\).
If these three words are pairwise distinct, the proper
two-position residual identifies the honest weight. The two
one-position residuals are also distinct, since equality would
give \(a_0=a_1=a_2=a_3\) by testing completions of weights
0, 1 and 2. Thus (1) holds. In particular majority has word
\(0011\), whose pairwise residual words are \(00,01,11\).
For one honest position the words on lexicographically ordered
two-bit completions are \(0001\) and \(0111\). This illustrates
why neither the simulator nor the claim should be read as giving
only one fixed completion and its output.

Up to output complementation the eight words start with 0:
\[
 0000,\ 0001,\ 0010,\ 0011,\ 0100,\ 0101,\ 0110,\ 0111.
\]
The third, fourth, fifth and seventh have the distinct-window
property. The other four are constant, AND, parity and OR.
They already have robust AREs: a constant message for a constant
function; XOR addition for parity; for OR, encode 0 as zero and
1 as uniform on a large explicit binary group. In the latter
case, the honest sum is zero or uniform depending on honest OR,
which is determined by testing the residual at the all-zero
completion. Decode by nonzeroness with error \(1/|G|\).
AND follows by complementing all inputs and the output.
Thus every symmetric three-bit Boolean function has a statistical
RARE, without implying the same statement for asymmetric functions.

### 4.2 An infinite family of fixed-finite examples

For any fixed \(n\ge3\), choose an alphabet of size \(b\) with
\(n+1>b\) and \(n\le b^2\), for example \(b=\lceil\sqrt n\rceil\).
Take an Eulerian cycle in the complete directed graph on the \(b\)
symbols, loops included, and the first \(n+1\) vertices along it.
Use this sequence as \(f(0),\ldots,f(n)\) on total Boolean weight.
Its neighboring ordered pairs are all distinct. Any proper
residual distinguishes honest weights by testing an all-zero
completion and one with exactly one 1. The all-honest output,
however, does not distinguish all weights because the sequence
is longer than its alphabet. This is not simply publication of
the whole histogram in every execution.

### 4.3 Why a richer decoded count would not suffice for majority

If an ordinary/robust ARE for a function \(g\) is reused and only
its decoding is publicly postprocessed to majority, then the
aggregate still allows computing \(g\). For privacy to become
negligible for majority, \(g\) must be constant on each
majority fiber, since different \(g\)-values would remain
distinguishable by correctness. To recover majority it must
give different values on the two fibers.

This is impossible for one-sided capped addition with arbitrary
integer local preprocessing. If the capped sum gives two distinct
values, at least one fiber is unsaturated and its actual additive
sums agree. Each majority fiber contains a corner (all zeros
or all ones) and its three single-coordinate changes, all still
in that fiber. Agreement forces the local integer contribution
of a bit to be unchanged by switching it, for each party.
Then the capped sum is constant. This argument covers upper
or lower caps (including a special saturation symbol), not
arbitrary functions of multiple obscured counts.

It is also impossible for multiplication modulo an arbitrary
integer with arbitrary local preprocessing. Pass to a prime
power factor \(p^e\) on which the two outputs differ.
At least one output is nonzero there. Its fiber's corner and
three single-coordinate changes yield the same nonzero product.
Writing the truncated \(p\)-valuations of the factors, this
forces equality of the valuations of the two symbols of each
party: these products have common valuation \(v<e\), equal to
the sum of their individual valuations. Hence all inputs have
that same unsaturated total \(v\). Divide by \(p^v\) and reduce
modulo \(p^{e-v}\). Now the factors are units, and the same
corner comparisons, cancelling the other units, show the unit
parts of both symbols agree for each party. All products must
then coincide, a contradiction. This argument concerns the
specific decoded modular-product primitive, not arbitrary
combinations of protocols.

The original [HIKR, Lemma 4.18] obstruction to *perfect privacy*
also applies to majority: its slices when one party is 0 or 1
are AND and OR; on the three completions \(00,01,11\) their
outputs have exactly the two patterns in that claim. The
present theorem only gives statistical privacy on the full
honest set and does not run afoul of that obstruction.
