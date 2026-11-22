# A true prime rebate on the small-factor negative half-zero rows

Use the quartic half-zero detector \(H\) with squarefree own-log
coordinates from [the negative-arm union](OneArmRoughDebit.md);
it is zero on nonsquarefree integers. Let \(N\) be an individual
large even integer, \(L=\log N\), \(J\Subset(1/3,2/3)\) a fixed
nondegenerate interval, \(x\in NJ,\ y=N-x\), and
\(M=|J|N\mathfrak S(N)\). Keep the actual target units and genuine
prime weight \(\Pi(n)=(\log n)1_{\{n\ {\rm prime}\}}\).

**Theorem.** At every sufficiently large even target,
\[
 \sum_{\substack{x\in NJ,\ (x,N)=1\\
                  \omega(x)\in\{3,4,5\}\\
        N^{.005}<p_1(x)<p_2(x)\le N^{.132}}}
               [-H(x)]_+\,\Pi(N-x) > .105\,M,                 \tag{1}
\]
where \(p_1(x),p_2(x)\) denote the smallest two distinct actual
prime factors; nonsquarefree rows already have weight zero.
The reflected result holds on \(1-J\).
The proof uses a specified subset of these rows in which the
remaining factor is rough at a cell-dependent polynomial floor.
In particular these rows are **outside** the very rough negative
source \(P^-(x)>N^{.132}\). This is a positive actual prime cross
which can enter a signed complement estimate through
\(-\langle S,H\rangle=\langle S,\Pi\rangle-
 \mathfrak S(N)\sum S+o(M)\) for the same finite-angle source \(S\).
It is not by itself a lower bound on the mixed composite
remainder or on binary Goldbach. Its size must not be added to
a prime-positive rebate on overlapping unpartitioned ranks.

## 1. The actual tags and their rough quotient

For \(i=5,\ldots,131\) take the half-open target-log angle
interval \((i/1000,(i+1)/1000]\); use pairs of cells \(i<j\).
On one such fixed pair let \(t_1,t_2\) be the actual angles of
distinct genuine primes \(p_1,p_2\) from the two cells. Define
\[
 \begin{gathered}
  h=p_1p_2,\quad
  \kappa_-=(i+j)/1000,\quad \kappa_+=(i+j+2)/1000,\qquad
  c_-=1-\kappa_+,\quad c_+=1-\kappa_-,\\
  D=.555-\kappa_+,\qquad
  z=\max(.1325,D/3),\qquad s=D/z .
 \end{gathered}
\]
The actual event is \(h\mid x\) and \(P^-(x/h)>N^z\).
Since \(z>.132\), the tags are uniquely the two smallest actual
factors of every retained \(x\). The events on different tag
pairs or cells are disjoint. In particular no one prime row
can be counted several times by factoring \(h\).
On each cell \(2<s\le3\), \(z<.187\), and all parameters have
fixed strict power margins where needed.

First use the dimension-one Rosser lower sieve on the quotient,
with level \(N^D\) and threshold \(N^z\), on the **genuine prime
opponent** \(y=N-x\) in the corresponding central interval.
The actual congruence at quotient divisor \(d\) is
\(y\equiv N\pmod{hd}\). Weight the two actual tags by \(t_1t_2\)
and use the two log weights \(\log y\), \(L\) at this step.
On this fixed cell the resulting lower, in units of \(M\), is
\[
 \frac{1}{10^6}\,\frac{2}{D}\log(s-1)+o(1).                   \tag{2}
\]
Here is the needed verification of distribution at the **marked**
moduli, since ordinary unweighted below-root BV would not
justify (2).

Split the sieve primes into a small bank below \(N^\xi\) and
its complement; use the same independent small-bank
fundamental-lemma weights as in
[the central lower sieve](../central_rough_chen_2663/Proof.md),
taking its support exponent \(b\) sufficiently small after
the applicable packing slack, then \(\xi\ll b\) and \(\xi<.005\).
For the literal nonnegative lower vector-sieve inequality use
the two lower/upper products minus the upper/upper product:
if \(l_i\le I_i\le u_i\), \(u_i\ge0\) on each bank, then
\(l_1u_2+u_1l_2-u_1u_2\le I_1 I_2\).
The small-bank principal ratios tend to one in the usual
successive choice of \(\xi/b\) and mesh. Use ordinary lower and
upper Rosser weights of level \(N^D\) for the other bank.
Their actual prime labels satisfy the square-prefix tests.
For the upper weights the odd cubic prefix tests imply the
square tests, using the previous odd test at each even position.
For the lower weights the even cubic prefix tests similarly
give the odd square tests from the preceding even one, except
the first square; that first test holds because \(2z<D\).
An empty residual label is allowed.

Now insert both true forced labels \(p_1,p_2\) into the
**decreasing** list of large-bank prime labels; they need not
be larger than all sieve factors. A square prefix at a
residual sieve prime spends at most the whole forced log
angle \(\log h/L\le\kappa_+\), and hence is bounded by
\(D+\kappa_+=.555\). At a forced prime of angle \(t\), if there
is a preceding residual prime of angle \(t_0\), the square
test there implies that the sum of preceding residual angles
is \(\le D-t_0\), and \(t_0\ge t\). The earlier forced angles
sum to at most \(\kappa_+-t\); thus the new square prefix
is at most \(D-t_0+\kappa_+-t+2t\le.555\).
If there is no preceding residual prime, the square prefix
is at most \(\kappa_++t\le\kappa_++D\) directly. This checks
all prefix positions even with the two tagged slots interleaved.

The maximum of the joined list is below \(.187\), and each
joined vector satisfies the actual square-prefix conditions
just verified. Therefore exactly the packing in
[the .555 angular sieve, §1](../angular_prime_level_555/Proof.md)
applies to these **actual joined vectors**, using
[Lichtman, Propositions 5.2 and 6.1](https://arxiv.org/html/2309.08522v1#S6),
not the bare theorem for well-factorable coefficients.
Its notional level \(.55525\) leaves fixed slack. In brief:
if the largest label exponent is at least \(.1107\), the
three entries of (6.2) strictly dominate \(.55525\) on this
range; otherwise use the active \(w\)-branch for vectors
of length at least three, as in the cited exact check.
At length at most two and largest exponent \(<.1107\),
the full modulus is below \(N^{.2214+b+o(1)}\) and ordinary
BV suffices. Choose the polynomial medium Heath–Brown
source slot and the notional scale \(A\) as in that proof.
The remaining bank joins the third group after its size
\(N^b\) is chosen much smaller than the packing slack.
For the other source-variable configurations use the same
one-free CRT and two-free uniform-residue Proposition 3.2
branches checked for the true prime source in
[the central lower sieve, §1](../central_rough_chen_2663/Proof.md).
The literal residue here is \(N\), not a fixed small
integer, and the central spatial window is kept by the
same genuine prefixes/endpoint separation.

For clarity, to transfer the joined support one first uses
log-angle rounded Rosser trees on the residual labels, as
in the cited lower proof, then refines the finitely many
bins of the joined list. The forced labels, their two fixed
cells and weights \(t_1,t_2\) stay separately identified in
every bin. Using the representative at strictly feasible
upper edges, the chosen three index groups remain the same
throughout each bin; rounding and moving to dyadic edges
spends less than the fixed packing margin. The three factors
are then genuinely separated convolutions, allowing
factorial normalizations for repeated *bins*. Artificial
repeated *primes* in the large list cost a power: their
modulus is divisible by \(p^2\) with \(p>N^\xi\), and
\(\sum_{q\le N^{.555+b},\ \exists p>N^\xi:\,p^2\mid q}1/q
\ll N^{-\xi}L\); the \(+1\) floors are also power-small.
This includes any collision of a tested prime with a forced
tag, or one can omit the two tag primes from the sieve:
actual \(x\) divisible by their squares has power-small
total weight, and their local omission costs \(1+o(1)\).
Distinct genuine labels of a fixed modulus have bounded
divisor multiplicity. Thus the joined support evaluates the
whole weighted sieve remainder, not the discrepancy at a
prescribed individual tag pair. Fixed angular box endpoints
are retained; for the harmonic model only, the error from
rounded prefix walls tends to zero in the mesh refinement
at fixed positive \(\xi\). This is the same order of
limits as in the original two-bank lower calculation.

The actual principal first has \(1/\varphi(h)\) for the
tag pair. The quotient local density is \(1/(p-1)\) at
sifted primes outside \(Nh\), and zero at excluded primes;
omitting \(p_1,p_2\) costs \(1+o(1)\). All actual tag primes
dividing \(N\) are omitted and have power-small total
harmonic weight. Thus the local product is
\((1+o(1))e^{-\gamma_{\!E}}\mathfrak S(N)/(zL)\).
The usual \(s\in(2,3]\) dimension-one lower coefficient is
\(2e^{\gamma_{\!E}}\log(s-1)/s\).
The principal prime mass in the actual interval is
\((1+o(1))|J|N\), with its log weight; proper prime powers
in a \(\Lambda\) expansion are power-small with these
fixed divisor multiplicities. Finally
\[
   \sum_{p_i\ {\rm in\ each\ cell}}\frac{t_i}{p_i-1}
                            =1/1000+o(1)
\]
by the ordinary prime log harmonic. This proves (2).
Replacing the outer \(L\)-weight by \(\log x\) costs only
\(1+O_J(1/L)\) in nonnegative terms.

## 2. Subtract every actual high quotient rank

The squarefree restriction is harmless at the displayed
positive least tag floor: actual squares have fewer than
\(O(N^{1-.005})\) rows, power-small even with the log and
actual multiplicity weights. For an actual quotient of rank
\(j\), set \(c=\log(x/h)/L=1-(t_1+t_2)+O_J(1/L)\).
Its angular density with the \(\log x\) weight, at scaled
cofactor total \(c\), is \(J_j(c/z)/c\). Here \(J_1(u)=1\)
on \(u\ge1\) and
\[
       J_j'(u)=J_{j-1}(u-1)/(u-1)\quad(j\ge2),
       \qquad J_j(u)=0\quad(u<j).
\]
These are the literal ordinary prime-product harmonic
integrals: fix \(j-1\) prime slots with reciprocal measures,
apply the ordinary PNT in the remaining actual fixed-relative
prime interval, and divide by \(j!\). The displayed recurrence
follows by multiplying the simplex integrand by the sum of the
angles and integrating a boundary variable. The two genuine tags
remain the unique two smallest factors. In particular every
quotient rank is finite here, and every included label exceeds
a fixed positive power. Target-unit and repeated-prime exclusions
may only decrease this unopposed upper.

Apply the [3.446 genuine prime-opponent upper](../angular_prime_first_composite/Proof.md)
to the **actual** product of the two tags and each quotient
of rank \(j\ge4\), with the same \(J\), log weights and tag
angle weights. Monotonicity of \(J_j\ge0\) yields the combined
upper in units of \(M\):
\[
           \frac{1}{10^6}\,\frac{3.446}{c_-}
                  \sum_{j\ge4}J_j(c_+/z)+o(1).                \tag{3}
\]
All \(j\ge4\) have been included; \(c_+/z<8\) on every
cell. Actual quotient endpoint shifts are \(O_J(1/L)\)
on fixed-angle compact sets, where ordinary source
densities are continuous. Equation (3) is an upper over real
primes, not subtraction of predicted opposite ranks.
After (3) is subtracted from (2), every true surviving
squarefree row is rank \(3,4\), or \(5\) with the two tags.

## 3. Transfer the actual negative weights

The two smaller own-log angles are \(u_1,u_2\);
they differ from \(t_1,t_2\) by \(O_J(1/L)\).
For rank three, the remaining factor is a giant and
the negative score divided by \((\log x)u_1u_2\)
is at least \(36c_-^2-14-o(1)\), by (2) of the
negative-arm note. For rank four its exact negative
score gives at least \(144z(c_--z)-o(1)\) in the same
normalization, since the two remaining angles are \(\ge z\)
and sum to at least \(c_-+o(1)\).

For rank five use equation (3) of that note:
\(-H/(\log x)\ge288 b_5(0)\prod u_i\).
The maximum of this centered symmetric unimodal density
is \(b_5(0)\), and
\[
               b_5(0)\ge (\textstyle\sum_i u_i^2)^{-1/2}.
\]
Indeed among probability densities capped by \(B\), the
uniform density \(B\) on the centered interval of length
\(1/B\) minimizes the second moment, by moving mass toward
zero; its variance is \(1/(12B^2)\). The actual variance of
the independent sum is \(\sum_i u_i^2/12\). On these cells
\[
        2(.132)^2+2z^2+(c_+-2z)^2<25/49 .
\]
This rational inequality is checked cellwise below; it is an
upper on \(\sum_i u_i^2+o(1)\) by maximizing the convex
sum of squares of the three residual angles \(\ge z\) at a
corner. Their product is at least \(z^2(c_--2z)-o(1)\)
by the analogous concave log minimization. Therefore on all
three ranks the actual negative weight is at least
\[
 (B-o(1))L t_1t_2,\qquad
 B=\min\left(36c_-^2-14,\ 144z(c_--z),\
                    \tfrac75\,288z^2(c_--2z)\right)>0 .
\]
We already inserted \(t_1t_2\) on **both** sides of the
subtraction, so both lower and upper use the true signed
log-harmonic weights once. The remaining factor \(L t_1t_2\)
is \(1+O_J(1/L)\) relative to \((\log x)u_1u_2\).
Multiplying the nonnegative residual lower by \(B\) and
summing the disjoint fixed cells proves (1) once the constant
is bounded below.

The [exact checker](check_two_least_rebate.py) uses only rational
and integer operations for the inequalities. It builds upper
values for \(J_j\) on a \(10^{-3}\) grid by right endpoint
numerators and left endpoint denominators in their delay
equations, rounding the integrated upper increment upward.
A positive series for \(\log(s-1)\) gives a lower on (2).
The weighted sum of the nonnegative resulting cell lower
bounds, rounded downward at each step, is
\(0.105769197972637>.105\).
All weights are on genuine reflected prime rows; no assumption
about the sign of the remaining complement is used.
