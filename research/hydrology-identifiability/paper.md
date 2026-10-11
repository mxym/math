# Exact identifiability and equifinality in a two-storage rainfall--runoff model

## 1. Model

Let (pcolon I	omathbb R) be a known rainfall input. For rates
(a,b,c>0), consider

\[
 \dot x_1=p-(a+b)x_1+cx_2,
 \qquad
 \dot x_2=bx_1-cx_2,
 \qquad
 Q=ax_1.
\tag{1}
\]

The states are fast and slow storage compartments and (Q) is the observed
outflow. The equations have an exact balance law, obtained by adding the two
state equations:

\[
 \frac{d}{dt}(x_1+x_2)=p-Q.
\tag{2}
\]

## 2. Observable differential equation

Put (B=a+b), (S=a+b+c) and (P=ac). Since (Q=ax_1), differentiating
(1) twice and eliminating (x_2) gives

\[
 Q''+S Q'+P Q=a p'+Pp.
\tag{3}
\]

This calculation is exact. In particular, for constant rainfall (p), the
entire scalar output trajectory depends on the three rates only through

\[
 S=a+b+c,qquad P=ac,
\tag{4}
\]

unless initial-state information or additional forcing experiments are used.

## 3. A physical equifinality theorem

The rates ((2,2,2)) and ((1,1,4)) both have (S=6) and (P=4). Take
(p(t)=1) and (Q(t)=1). The corresponding nonnegative equilibrium states are

\[
 (x_1,x_2)=(1/2,1/2),qquad (x_1,x_2)=(1,1/4),
\]

respectively. Substitution in (1) gives (dot x_1=dot x_2=0) in both
models, and both have exactly the same observed runoff for all (t). Thus even
perfect continuous discharge data do not identify the three physical rates when
initial storage is unobserved. This is an exact physical counterexample, not a
numerical calibration ambiguity.

More generally, if (S,P) are fixed and (a'>0), set

\[
 c'=P/a',qquad b'=S-a'-c'.
\tag{5}
\]

Whenever (b'>0), the scalar output equation (3) is unchanged. A state
reconstruction from (Q) then gives the same output trajectory; positivity of
the reconstructed initial state is an open condition around an interior
equilibrium. This produces a local one-parameter equivalence family.

## 4. Identifiability under a controlled initial state

Assume (p(t)=p_0>0) is constant and (x_1(0)=x_2(0)=0). Directly from (1),

\[
 Q'(0)=ap_0,qquad
 Q''(0)=-a(a+b)p_0,qquad
 Q'''(0)=a((a+b)^2+bc)p_0.
\tag{6}
\]

Hence

\[
 a=\frac{Q'(0)}{p_0},quad
 B=-\frac{Q''(0)}{Q'(0)},quad
 b=B-a,quad
 c=\frac{Q'''(0)/Q'(0)-B^2}{b}.
\tag{7}
\]

The rates are therefore globally identifiable from the first three output
derivatives under the zero-storage intervention. The same formulas show why
the initial-state hypothesis cannot be silently omitted.

## 5. Model-design consequence

The result separates two questions that are often combined in calibration:

1. the output law can be estimated accurately;
2. the physical rates are uniquely determined.

Equation (5) proves that the second question has a genuine symmetry obstruction
under a single unknown-state constant-rainfall experiment. Equation (7) gives a
minimal exact intervention that removes the obstruction in this two-storage
model. A next theorem should classify the analogous equivalence classes for
threshold or power-law outflows and finite-time integral observations.

No claim of solving general conceptual-model identifiability is made here.
