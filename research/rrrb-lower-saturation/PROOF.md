# The lower endpoint of the exact scalar profile

In a red/blue complete graph, count ordered injections $(1,2,3,4)$ with $12,23,34$ red and $41$ blue; the diagonals are unrestricted. Let $M(p)$ be the maximum limiting count per $n^4$ at red density tending to $p$. The graphon formulation is equivalent, by graph limit compactness and sampling; see [sources](REVIEW.md).

## Scalar bound and its unique parameters

Fix $0<p<1/2$ and put $x=4p-1$, $a=(1-x^2)/4>0$, $C(r)=a+xr-4r^2$. The [operator bound](../rrrb-quasirandom-threshold/THRESHOLD.md) gives
$$
M(p)\le U(p)=p^3(1-p)+\max_{r\in\mathbb R}\left\{[C(r)_+]^2/8-r^4\right\},\qquad z_+=\max(z,0).
$$
Indeed, in $L^2=\mathbb R1\oplus1^\perp$ the red adjacency operator has blocks $p,u^*,u,A$. Set $q=\|u\|^2$. At $q=0$ there is no positive excess over the constant graphon. For $q>0$ set $-r=\langle u,Au\rangle/q$. The scalar excess before maximizing $q$ is bounded by $qC(r)-2q^2-r^4$; the best $q$ is $C(r)_+/4$. At $r=0$ the scalar excess is positive, so any maximizing $r$ has $C(r)>0$.

The maximizing $r$ is unique. At $x=0$ it is zero. Otherwise its sign must agree with $x$, since reflecting the opposite sign strictly improves a positive excess. Set $z=|x|$, $\rho=|r|$. The derivative at zero on the positive branch is $az/4>0$, and stationarity requires $C(r)(z-8\rho)=16\rho^3$, hence $0<\rho<z/8$. The derivative numerator $az+(z^2-8a)\rho-12z\rho^2+16\rho^3$ is strictly concave there, positive at zero and negative at $z/8$. Hence it has exactly one zero there. This also gives continuity of $r(p)$ by compactness and uniqueness. In signed form its equation is
$$
K(p,r)=ax+(x^2-8a)r-12xr^2+16r^3=0.
$$
Thus $U(p)=p^3(1-p)+C(r)^2/8-r^4$ with unambiguous parameters. Set $q=C(r)/4$ in what follows.

## Which equality graphons can realize this bound?

At equality the two separately nonnegative losses $4(\|Au\|^2-qr^2)$ and $\operatorname{tr}(A^4)-r^4$ must vanish. The first gives $Au=-ru$, and then the second forces every other eigenvalue on $u^\perp$ to vanish. This argument includes $r=0$. Hence, writing $f=u/\sqrt q$, the graphon must have the form
$$
W(v,w)=p+\sqrt q\,[f(v)+f(w)]-r f(v)f(w),\qquad \mathbb Ef=0,\quad\mathbb Ef^2=1.
$$
Conversely any such admissible kernel with these parameters realizes $U(p)$.

The degree function $p+\sqrt q f$ lies in $[0,1]$. Let $-l$ and $v$ be the negative and positive essential extremes of $f$; these are finite. The displayed bilinear polynomial lies in $[0,1]$ at all four corners of $[-l,v]^2$, since every neighborhood of either extreme has positive measure and the polynomial is continuous. It therefore does so everywhere on that rectangle by separate affine interpolation. Further, $lv\ge1$ because $\mathbb E[(f+l)(v-f)]=lv-1\ge0$.

For **every** $h\in[1/v,l]$ we may now replace $f$ by the two values $-h,1/h$ with probabilities $1/(1+h^2),h^2/(1+h^2)$. The mean and variance stay zero and one, respectively, and all kernel entries remain admissible. Thus existence of any equality graphon is equivalent to feasibility of at least one such $h$. This is not a moment reduction for arbitrary, non-extremal graphons.

## The feasibility test

The two diagonal entries $L,H$ and the cross entry $B$ in this parametrization are
$$
L=p-\sqrt C\,h-rh^2,\quad H=p+\sqrt C/h-r/h^2,\quad B=p+r+\tfrac{\sqrt C}{2}(1/h-h).
$$
Here $C=C(r)$. The degree bounds give $\sqrt q/(1-p)\le h\le p/\sqrt q$. The inequalities $L\ge0,H\le1$ require
$$
\sqrt C\le\min\{B_1(h),B_2(h)\},\qquad B_1=p/h-rh,\quad B_2=(1-p)h+r/h.
$$
The two functions cross at $h_0^2=(p-r)/(1-p+r)>0$; $B_1-B_2$ has the sign of $h_0-h$. For $0<p\le1/3$ the minimum on the right is at most its common value at $h_0$, strictly less for every degree-feasible $h\ne h_0$. To verify this comparison:
* When $r\le0$ and $p\le1/4$, $B_2$ increases everywhere. Also $B_1$ decreases up to $p/\sqrt q$ since $q\ge a/4\ge p/4>p|r|$.
* When $r\ge0$ and $1/4\le p\le1/3$, $B_1$ decreases everywhere; $B_2$ increases above $\sqrt q/(1-p)$ since $q\ge a/4\ge1/18>r(1-p)$. Here $r\le1/24$.

In both cases $C\ge a$ follows from $|r|\le|x|/8$. If $h<h_0$, compare $B_2$ from $h$ to $h_0$; if $h>h_0$, compare $B_1$ from $h_0$ to $h$. This works even when $h_0$ is not known to be degree-feasible. The common value is $[P+r^2]/\sqrt{(p-r)(1-p+r)}$, where $P=p(1-p)$. Squaring gives the necessary condition
$$
D(p,r)=(P+r^2)^2-(p-r)(1-p+r)C(r)\ge0. \tag{1}
$$

For $1/4\le p\le1/3$, this condition also suffices: choose $h=h_0$. Then $L\ge0$, $H\le1$, and $L\le p$ because $r\ge0$. Also $H\ge0$ since $r+r^2\le x/8+x^2/64<p^2$ (the gap is $(4+3x^2)/64$), which gives $r/h_0^2\le p$. Finally $1/4\le p-r\le1/3$, whence $1/3\le h_0^2\le1$ and $0\le1/h_0-h_0\le2/\sqrt3$. As $C\le a+x^2/16=(4-3x^2)/16\le1/4$, the cross entry is between $p$ and $p+1/(2\sqrt3)+1/24<1$. The [companion calculation](FEASIBILITY.md) proves directly that the same choice is feasible throughout $1/3\le p<1/2$.

## Conclusion and uniqueness at the endpoint

The [critical-root calculation](ALGEBRA.md) shows that along the true scalar-maximizing branch $D$ is negative for $0<p<p_0$, zero at $p_0$, and positive for $p_0<p\le1/3$. Hence the displayed kernel attains the scalar bound throughout $[p_0,1/2)$; the exact profile on $[1/2,1]$ is given in the [preceding note](../rrrb-quasirandom-threshold/PROFILE.md).

At $p_0$ the common value $B_1(h_0)=B_2(h_0)$ is exactly $\sqrt C$, so the strict comparison forces $h=h_0$. Thus $L=0$ and $H=1$. For any equality graphon, *every* $h\in[1/v,l]$ was feasible. Therefore $lv=1$ and $\mathbb E[(f+l)(v-f)]=0$. The integrand is nonnegative, so $f$ takes only its two extreme values; their probabilities and the cross entry are then fixed. This proves uniqueness up to graphon equivalence at $p_0$.

Below $p_0$ no graphon can realize the upper bound. At fixed $p$ a maximizer exists because the graphon quotient is compact in cut distance, the density fiber is closed, and the objective is the difference of two continuous simple-graph homomorphism densities. Consequently $M(p)<U(p)$ for each fixed $0<p<p_0$. This is not a uniform gap, an evaluation of $M$ there, or a proof about the number of classes in its optimizers.
