# Tight label discrimination under an almost-dimension bound

## 1. Statement and scope

Let $X$ have $n\ge1$ possible labels with positive probabilities
$p_x$. The states $\rho_x$ are density operators on a common
Hilbert space, with no upper ambient dimension. For a POVM $(M_x)$
the guessing success is $\sum_x p_x\operatorname{Tr}(\rho_x M_x)$.
This is normalized success probability, not $n$ times that
probability. We optimize over all source ensembles and measurements
subject to a *single common* projection $P$ of rank $d\ge1$:
$$
 \operatorname{Tr}(P\rho_x)\ge b_x,\qquad b_x=1-\epsilon_x\in[0,1].
 \tag{1}
$$
The projection need not be known to the observer, but must be independent
of the label for this constraint. The theorem is about the whole system
given to the observer. It does not assume a low-dimensional marginal on
only a part of a pre-entangled state.

**Uniform labels and common leakage.** Let $p_x=1/n,\ b_x=1-\epsilon$
for all $x$. If $1\le d<n$, the exact maximal success is
$$
 P^*_{\rm g}(n,d,\epsilon)=
 \begin{cases}
 \big(\sqrt{(d/n)(1-\epsilon)}
     +\sqrt{(1-d/n)\epsilon}\big)^2,&0\le\epsilon\le 1-d/n,\\
 1,&1-d/n\le\epsilon\le1 .
 \end{cases}
 \tag{2}
$$
For $d\ge n$, the value is 1. The nontrivial branch of (2), after
expansion, is the upper bound in Eq. (221) of
[de Oliveira Junior et al., arXiv:2610.20725v1, §IV.7](https://arxiv.org/html/2610.20725v1#S4).
They conjecture tightness when the zero-deviation success is $d/n$
under the almost-dimension assumption. The construction in Section 3
establishes that tightness. This does not concern the same equation's
different assumption of fidelity to each of a prescribed set of target
states.

Equation (2) still gives the exact worst-case value if (1) is relaxed
to the single uniform mean $\sum_x\operatorname{Tr}(P\rho_x)/n\ge
1-\epsilon$. It also holds when the observer has an independent-of-$X$
classical flag $\Lambda$, rank at most $d$ for a possibly
flag-dependent projector $P_\lambda$, and the population bound is
imposed only after averaging over both $x$ and $\lambda$.
For the original uniform-label statement and these extensions,
allowing mixed states never increases the worst-case value.

**Arbitrary positive prior and per-label bounds.** Define
$$
 F(a,b)=(\sqrt{ab}+\sqrt{(1-a)(1-b)})^2,\qquad
 g(a,b)=\begin{cases}F(a,b),&a\le b,\\1,&a\ge b.\end{cases}
 \tag{3}
$$
For $1\le d<n$ the exact value under (1) is
$$
 P^*_{\rm g}(p,d,b)=
  \max_{\substack{0\le a_x\le1\\ \sum_x a_x=d}}
       \sum_x p_x\,g(a_x,b_x).
 \tag{4}
$$
One can replace (1) by the per-label flag-averaged condition
$\mathbb E_\lambda\operatorname{Tr}(P_\lambda\rho_{x,\lambda})\ge b_x$
without changing (4), when flags are independent of the label and
all branch projectors have rank at most $d$.
These are extensions of the conjectured uniform case, not additional
claims about its statements.

The edge cases are literal: at $d=0$ the condition is feasible only
when every required $b_x$ is zero (or $\epsilon=1$ for the uniform
mean); in that unconstrained case the value is 1. It is not meaningful
to extrapolate the first branch of (2) to a zero-dimensional reference
with positive required support weight. For $d\ge n$ use orthogonal
states in the reference subspace; if an exact rank $d$ is required,
pad the ambient space accordingly. This includes $n=1,\ d\ge1$.
The optimizations refer to the stated nonempty source model, not to a
fixed small ambient space incapable of containing those states.

## 2. Independent upper proof including mixed states

The function $F$ in (3) is the squared classical fidelity of two binary
distributions. It is jointly concave on $[0,1]^2$. For a direct check,
write $u=a(1-a),v=b(1-b)$ in the open square. The three Hessian entries
are
$$
 F_{aa}=-\frac{\sqrt v}{2u^{3/2}},\quad
 F_{bb}=-\frac{\sqrt u}{2v^{3/2}},\quad
 F_{ab}=2+\frac{(1-2a)(1-2b)}{2\sqrt{uv}} .
 \tag{5}
$$
The determinant is nonnegative because
$$
 |4\sqrt{uv}+(1-2a)(1-2b)|\le1,
$$
the Cauchy--Schwarz inequality for the two real unit vectors
$(2\sqrt u,1-2a)$ and $(2\sqrt v,1-2b)$.
Continuity gives concavity at the boundary. For fixed $a$, $F(a,b)$
increases up to $b=a$ and decreases thereafter. This follows either
by differentiating or by writing $a=\cos^2 A,\ b=\cos^2 B$,
$A,B\in[0,\pi/2]$, so that $F=\cos^2(A-B)$.
Thus $g(a,b)=\max_{b'\ge b}F(a,b')$; $g$ is nonincreasing in
$b$, nondecreasing in $a$, and jointly concave. For the last
claim, two maximizing choices $b'_1,b'_2$ yield a feasible convex
combination of them for the convex combination of the input pairs;
apply concavity of $F$.

For a given POVM use the isometric dilation $V\psi=\bigoplus_x
\sqrt{M_x}\psi$ into $n$ copies of the ambient space. Let $Q_x$
be the coordinate projections, $P'=VPV^\dagger$, and
$A_x=\min\{1,\operatorname{Tr}(P'Q_x)\}$. Then
$M_x=V^\dagger Q_xV,\ \operatorname{rank}P'=d$, and
$\sum_x A_x\le\sum_x\operatorname{Tr}(P'Q_x)=d$.
For a unit signal $\psi$, let $\eta=V\psi$, $B=\|P'\eta\|^2$.
If $Q_x\eta\ne0$, put $e=Q_x\eta/\|Q_x\eta\|$. The squared
projection $A'=\|P'e\|^2$ is at most $A_x$, since
$|e\rangle\langle e|\le Q_x$. Splitting the overlap along
$P'$ and $I-P'$ and applying the triangle inequality
and Cauchy--Schwarz yields
$$
 \langle\psi,M_x\psi\rangle
 =|\langle e,\eta\rangle|^2
 \le F(A',B)\le g(A_x,B).
 \tag{6}
$$
The same last bound is trivial if the outcome has probability zero.
Importantly, $A_x$ depends only on $P'$ and the measurement, not on
the signal or its pure-state decomposition.

For a mixed state, apply (6) to its spectral decomposition and use
concavity in $B$. The upper bound becomes
$g(A_x,\operatorname{Tr}(P\rho_x))$. A trace-class density operator has
at most countably many nonzero eigenvalues; Jensen with bounded
continuous $g$ gives the same result in arbitrary ambient dimension.
For classical flags independent of $X$, apply this branchwise
with the branch measurement and projector and average over the flag.
The conditional guessing success for label $x$, averaged over the
flag, is bounded by $g(\bar A_x,\bar B_x)$ by joint concavity.
Here $\bar A_x=\mathbb E A_{x,\lambda}$,
$\bar B_x=\mathbb E\operatorname{Tr}(P_\lambda\rho_{x,\lambda})$,
and $\sum_x\bar A_x\le d$. This proof also works for continuous flags
with measurable strategies, and uses only the average rank bound.
No flag may depend on the message label.

With the per-label conditions, monotonicity in $b$ replaces
$\bar B_x$ by $b_x$; optimizing the remaining variables yields
the upper bound in (4). Since $g$ is nondecreasing in $a$,
the inequality $\sum a_x\le d$ can be replaced by equality if $d<n$.
With a uniform mean population bound, average $g(\bar A_x,\bar B_x)$
over $x$ and apply joint concavity once more to obtain
$g(d/n,1-\epsilon)$, which is (2). In particular the uniform mean
extension is an upper bound even if individual labels have very
different tolerated leakage.

## 3. Exact attainment of the uniform bound

Let $e_1,\ldots,e_n$ be the standard basis of $\mathbb C^n$.
An $n$-point unitary discrete Fourier matrix has all entries of
modulus $n^{-1/2}$. Take the projection $P$ onto any $d$
of its columns. Then $a=\langle e_x,Pe_x\rangle=d/n$ for every
label $x$. For $0<a<1$, the vectors
$$
 |\psi_x\rangle=
 \sqrt{1-\epsilon}\,\frac{Pe_x}{\sqrt a}
       +\sqrt{\epsilon}\,\frac{(I-P)e_x}{\sqrt{1-a}}
 \tag{7}
$$
are normalized, since the summands have orthogonal supports and
squared norms $1-\epsilon,\epsilon$. Thus
$\langle\psi_x,P\psi_x\rangle=1-\epsilon$. Their success with
the fixed computational-basis measurement is
$$
 |\langle e_x,\psi_x\rangle|^2=
 \big(\sqrt{a(1-\epsilon)}+\sqrt{(1-a)\epsilon}\big)^2
$$
for **each** label, proving equality when $\epsilon\le1-a$.
At the boundary $\epsilon=1-a$, the vector in (7) equals $e_x$.
For all larger $\epsilon$, use $e_x$ directly and get unit success
with population $a$. Since the uniform strategy already satisfies
the stronger label-wise bound, it also attains the upper bound for
the uniform mean and flag variants. Neither an optimizer nor a
pretty-good-measurement optimality theorem is needed: the explicit
measurement attains the proved global ceiling.

## 4. Exact attainment for arbitrary prior and label-wise budgets

The projection-diagonal case of the Schur--Horn theorem says that every
$a_1,\ldots,a_n\in[0,1]$ with integer sum $d$ is the diagonal of
a rank-$d$ projection on $\mathbb C^n$. Here is a short elementary
proof. A $0$--$1$ list is trivial. Otherwise there are at least two
fractional entries $a_i,a_j$, since their total sum is integral.
Replace those two entries by $(a_i+a_j,0)$ if their sum is at most
one, or by $(1,a_i+a_j-1)$ if it is greater than one.
This reduces the number of fractional coordinates and keeps the sum.
By induction assume there is a projection with that new diagonal.
Its $i,j$ off-diagonal entry is zero because one of the two
coordinate vectors, with diagonal zero or one, is an eigenvector
of the projection. A real Givens rotation in the $(i,j)$ plane
preserves the sum of those two diagonal values and produces any
intermediate division of that sum between the two original values.
Both $a_i,a_j$ are within that interval. Other diagonal entries
are unchanged. This proves the statement for all lists, even with
a real projection.

Choose a maximizing list in (4), which exists by compactness.
Use a rank-$d$ projection of that diagonal and the computational
measurement. For $0<a_x<b_x$ take
$$
 \psi_x=\sqrt{b_x}\,Pe_x/\sqrt{a_x}
       +\sqrt{1-b_x}\,(I-P)e_x/\sqrt{1-a_x}.
 \tag{8}
$$
This attains $F(a_x,b_x)$ at population $b_x$. If $a_x\ge b_x$
use $e_x$, attaining one. If $a_x=0<b_x$, choose any unit vector
$f$ in the range of $P$ and use
$\sqrt{b_x}f+\sqrt{1-b_x}\,e_x$; since $e_x$ is perpendicular
to that subspace, its success is $1-b_x=F(0,b_x)$.
If $b_x=1$, the formula with $0<a_x<1$ uses just its first summand.
These cases exhaust all endpoints and attain the right side of (4).
The pure strategy needs no flag.

For computation, if $\sum_x b_x\le d$, the optimum is one. Otherwise
one can restrict $a_x\le b_x$: moving surplus from any value above
$b_x$ to a deficient label cannot reduce the objective. Since all
prior weights are positive and at least one label must remain
deficient, an optimum uses exactly $d$. Here is an explicit scalar
multiplier rule for this remaining case. Let $\mu\ge0$ be the
multiplier on $\sum a_x=d$. For $0<b_x<1$ and $\mu>0$, put
$$
 z_x=\mu/p_x-(2b_x-1),\qquad
 a_x(\mu)=\frac12\left(1-\frac{z_x}{\sqrt{z_x^2+4b_x(1-b_x)}}\right).
 \tag{9}
$$
This is the unique interior solution of $p_x\,\partial_a F(a_x,b_x)=\mu$;
it decreases continuously from $b_x$ to zero. At $b_x=0$ choose
zero; at $b_x=1$, use $a_x=1$ if $p_x>\mu$, zero if $p_x<\mu$,
and any fraction in the equality case. Choose $\mu$ to meet the sum,
filling any ties. Existence follows from these monotone rules:
the total runs from $\sum b_x>d$ at $\mu=0$ down to zero, and
the only jumps are the fillable linear ties. Since each scalar
choice maximizes $p_x g(a_x,b_x)-\mu a_x$ on the restricted interval,
the sum constraint makes the resulting list globally optimal.
No algorithm is required for the uniform closed form.

## 5. Defensive source calibration

For uniform inputs, the rescaled quantity called $P_{{\rm g},n}$ by
[Mishra et al., arXiv:2610.37296v1](https://arxiv.org/html/2610.37296v1)
is $nP_{\rm g}$. If the characterized system is the complete emitted/
available system, with no prior entanglement extending the observer's
access outside the model, a verified almost-$d$ population bound
therefore justifies declaring $G=nP^*_{\rm g}(n,d,\epsilon)$.
Likewise, when an independent preheld system is in the same product
factor for all labels, it is redundant for discrimination. The
classical-flag extension covers setting-independent classical
fluctuations with the stated conditional subspaces and population
average. Subsequent setting-independent quantum processing cannot
increase success, since a measurement on its output can be pulled
back by the adjoint channel to a POVM on its input.

In particular $G=2+4\sqrt{\epsilon(1-\epsilon)}$ for $n=4,d=2$
and $0\le\epsilon\le1/2$, and $G=4$ thereafter. At $n=6,d=2$
the exact leading correction is $4\sqrt{2}\sqrt{\epsilon}$
as $\epsilon\downarrow0$, with an $O(\epsilon)$ remainder.
The bound calibrates a source assumption; a positive key rate also
requires the protocol's observed statistics and its own security
proof. It does not imply a joint rank-$d$ bound from a marginal on
only the transmitted subsystem when the observer already holds
correlated quantum information. In particular ordinary dense coding
already falsifies such a deduction at $\epsilon=0$. Nor does this
resolve the cited paper's sequential/coherent-attack question,
prove anything about an implementation, or settle the separate
fidelity-to-prescribed-target-states case.
