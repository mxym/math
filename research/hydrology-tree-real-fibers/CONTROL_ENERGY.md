# Exact finite-horizon control energy for the root-leak tree model

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. No external funding; AI-assisted work.
Existing repository and third-party notices remain in force.

## Statement

For any original finite OrderedTree whose actual root response is a full
normalized positive Stieltjes sum, every T>0 and every pair of real state vectors
z0,z1 admit an actual continuous signed control achieving the terminal state.
Among ALL globally continuous controls with a classical trajectory satisfying
those endpoints, a minimum of E(u)=integral_0^T u(s)^2 ds is attained. The minimum
and equality classification are exact, not numerical optimizations.

The simple modal witness is derived from the actual compartment matrix. In its
coordinates y=analysis*z the equation is

    y_i'=-r_i*y_i+b_i*u, with distinct real r_i and b_i != 0.

An endpoint-feasible trajectory necessarily satisfies

    integral_0^T exp(r_i*s)*u(s) ds=d_i,
    d_i=(exp(r_i*T)*y1_i-y0_i)/b_i.

This equivalence is proved from the actual interval-integral solution and the
actual matrix ODE, rather than supplied as an assumption about feasible inputs.

## Construction and proof

Define the actual integral matrix H_ij=integral_0^T exp(r_i*s)exp(r_j*s) ds.
For c != 0 its quadratic form is the integral of (sum_i c_i exp(r_i*s))^2.
If this integral vanished, continuity would make the exponential sum vanish on
the interval. Repeated actual differentiation and the invertible Vandermonde
matrix force c=0, a contradiction. Thus H is strictly positive for every T>0.

Set c=H^(-1)d and u*(s)=sum_i c_i exp(r_i*s). Matrix multiplication is proved to
coincide with the actual exponential moment integrals, so u* satisfies every
constraint and gives the exact endpoints. Its energy is d^T H^(-1)d.

For any other continuous endpoint-feasible u, all exponential moments of
v=u-u* are zero. Hence integral_0^T u*(s)v(s) ds=0. Expanding the square gives

    E(u)=d^T H^(-1)d+E(u-u*).

The remainder is nonnegative. Its vanishing is equivalent, by continuity and
strict integral positivity, to u=u* on the complete closed interval [0,T].
This proves a global optimum over all continuous feasible inputs, not just
finite exponential candidate controls. Comparing the two attained minima also
proves that the cost does not depend on a chosen modal witness for the same
physical matrix and physical endpoints.

## Exact formalization scope

The principal entry is `HydrologyTree.real_full_response_minimum_energy_control`.
The definitions use actual matrices, real interval integrals and actual classical
HasDerivAt solutions. All modal, positivity, Gramian and endpoint bridges are
proved. No external controllability or optimization theorem is an axiom.

Controls are signed real functions. This is not arbitrary reachability under
nonnegative-rainfall constraints. The equality statement does not identify
control values outside [0,T]. Real endpoint vectors need not be nonnegative.
The independently presented graph and alternate leak-location extensions remain
separately unproved. This standard control-theoretic refinement is not claimed
to be a historically new mathematical theorem or an empirical hydrological law.

Verification must be read at the source-specific checkpoint: fresh Lake build,
separate owned-source build, axiom audit, empty trust-zero kernel replay and
intentionally false energy/sign/equality controls. Development compilation is
not itself an independent replay receipt or external human peer review.
