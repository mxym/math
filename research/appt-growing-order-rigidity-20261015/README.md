# Actual APPT spectral criteria in two growing-order windows

Two complete ordinary mathematical manuscripts have separate independent
AI-agent decisions PASS. Both concern original complex PSD trace-one
densities APPT after every global unitary, actual ordered eigenvalues,
integer n>=m and arbitrary aspect-ratio oscillations. They keep different
optimality scales and their own exact hypotheses.

Let D=mn, y_i=D lambda_i, u=3D/(D+2), chi=alpha log u-log D and
h=alpha log(u/y_1)>=0. Define M=D^-1 sum y_i^alpha and M*=max_APPT M.
Relative entropy nearoptimality means log M/log M* tending to one;
sharp moment nearoptimality means (M-1)/(M*-1) tending to one.

## Sublinear growing order

[The S5 manuscript](sublinear/PAPER.md) covers m tending to infinity,
alpha tending to infinity and alpha/m tending to zero, for every n>=m.
With gamma=n/m, U=u^alpha, V=alpha(alpha-1)gamma/2,
wp=U/(U+V), wb=V/(U+V), and the actual middle loss

    d_b=(2-L)+|theta-1/2|+J,

its exact necessary and sufficient asymptotic tests are

    sharp moment:   wp min(1,h)+wb min(1,d_b) ->0;
    relative entropy:
        wp min(1,h/(1+max(chi,0)))+wb min(1,d_b) ->0.

The actual definitions of L, theta, J and their zero-width conventions
are fixed in the paper. The middle interval has D-m^2+2 entries, even
in square systems. A weighted SUM is required when both contributions
remain relevant. The full empirical scaled spectrum converges in W2 to
equal atoms at -1,+1 precisely on retained positive-bulk-weight
subsequences when d_b tends to zero. Vanishing bulk weight imposes no
unweighted W2 condition. Simultaneously retained peak and body weights
also force the stated necessary width margin. See
[the separate S5 review](sublinear/INDEPENDENT_REVIEW.md).

## Diverging peak contribution at at most linear order

[The S6 manuscript](growing-peak/PAPER.md) covers every fixed C>0,
m tending to infinity, alpha tending to infinity, alpha<=Cm eventually,
and chi tending to positive infinity. It allows every n>=m and does not
require alpha/m to converge. In this window,

    sharp moment nearoptimality iff h ->0;
    relative entropy nearoptimality iff h/chi ->0.

Either criterion forces the full nonleading normalized spectrum uniformly
to one, eventual full rank, and the sum of all nonpeak alpha-powers to be
negligible relative to the actual peak power. The proof first establishes
the actual peak limit and then uses a state-relative logarithmic estimate;
it does not log a coarse error relative to the optimum. The paper's actual
integer exponential-ceiling example distinguishes h/chi from h/alpha.
See [the separate S6 review](growing-peak/INDEPENDENT_REVIEW.md).

The [two-scope review index](REVIEW.md), [source bindings](OWNER_SOURCE_BINDINGS.json),
[status](STATUS.md), [complete durable evidence](../../verification/appt-entropy-spectrum-ordinary-20261015/README.md)
and [final source/status/index binding](FINAL_STATUS_BINDING.json) preserve
the exact inputs and all real reviewer failures. These are two windows,
not a claimed complete all-order/all-dimensional spectral classification.
Yongxian Zhang, South China University of Technology; no external funding;
OpenAI AI assistance. Original rights reserved, third-party notices kept.
