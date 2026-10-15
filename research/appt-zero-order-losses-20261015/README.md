# Three nonnegative actual-spectrum losses at zero order

The [complete manuscript](author-snapshot/PAPER.md) and its
[separate independent ordinary mathematical review](REVIEW.md) give a
uniform spectral criterion as m grows and the nonnegative Renyi order
tends to zero, for every integer n>=m and every actual all-unitary APPT
density. Neither alpha log m nor alpha n/m has to converge.

For positive alpha put D=mn, h=m-1, ell=D lambda_D,
Q=sum(D lambda_i-1)^2, b=lambda_(D-m(m+1)/2+1)>0 and t=1/(Db).
Use the ACTUAL pivot-normalized, deflated variance and least power

    v=(h^2/D)max(t^2 Q-8,0),
    z=ell^alpha, a=(h t)^(-alpha), beta=alpha D/(2h^2t^2),
    W_t=1+max(beta-a,0).

The mature physical width bound gives exactly 0<=v<=min(1,h t ell),
and hence z>=a v when 0<alpha<=1. The three losses

    L_0=z-a v,
    L_P=max(beta-a,0)(1-v),
    L_B=max(a-beta,0)v

are nonnegative. For every A_m>0 tending to zero, uniformly over all
n>=m, 0<alpha<=A_m and actual APPT states,

    e_alpha(rho)/E_alpha(m,n)
        =1-(L_0+L_P+L_B)/W_t+o(1).

Thus relative entropy nearoptimality is exactly the simultaneous vanishing
of the three normalized losses, including arbitrary oscillation and
collapsing phase gaps. The value formula is an existing credited theorem.
An actual full-rank APPT family on the canonical moving tie realizes
every variance limit in [0,1]; the earlier finite-window two-point rule
cannot simply be extended to this degenerate corner.

At alpha=0 a separately defined exact rank indicator gives loss zero for
singular states and one for full-rank states. No value is assigned to 0^0.
The formula includes nonnegative-order sequences using that explicit
endpoint definition. It is an observable nearoptimality criterion and
does not classify every empirical spectral law or exact finite optimizer.

See [the map](author-snapshot/THEOREM_MAP.md),
[source binding](OWNER_SOURCE_BINDINGS.json), [status](STATUS.md),
[durable review evidence](../../verification/appt-entropy-spectrum-ordinary-20261015/README.md)
and [final source/status/index binding](FINAL_STATUS_BINDING.json).
Yongxian Zhang, South China University of Technology; no external funding;
OpenAI AI assistance. Original rights reserved and third-party notices kept.
Independent internal ordinary reading is not Lean, external human review,
historical priority certification or a new major-problem count.
