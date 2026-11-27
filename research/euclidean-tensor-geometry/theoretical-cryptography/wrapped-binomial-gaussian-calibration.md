# Optimal Gaussian calibration for strongly wrapped centered binomial noise

**Scope.** This compares standalone residue distributions: a centered binomial modulo an integer and a discrete Gaussian modulo the same integer. It provides a positive statistical transfer bound in a strong-wrapping asymptotic model and a matching optimum over independent Gaussian replacements. The result does not use public rows, keys, ciphertexts, an implementation, or parameters of any specific scheme. In Ring/Module-LWE an upper bound on abstract error-law replacement can be pushed through the same addition and quotient channel, but the converse need not survive that channel.

The wrapped binomial's Fourier formula is classical; see [A cylindrical Galton Board at the Galton Board's 150th anniversary, §4](https://academic.oup.com/jrsssa/advance-article/doi/10.1093/jrsssa/qnag110/8861127). [Fu–Li](https://arxiv.org/abs/2608.16144) give lattice Rényi CLT and Edgeworth expansions for comparison before wrapping. In contrast the first and second surviving modes below yield different exponential scales after strong wrapping, and we optimize after that wrapping rather than match unwrapped variance.

## 1. Models and critical parameters

For m>=1 take a centered binomial B=Bin(2m,1/2)-m. Write P for B mod q, on Z/qZ. For b>0 and t real let G_(b,t) be the law on the integers proportional to exp(-(x-t)^2/b), and Q_(b,t) its reduction modulo q. A centered unwrapped variance match to first order is b=m, t=0; the binomial's variance is m/2.

Let q tend to infinity and m/q^2 tend to infinity, with m and q integers. Put x=pi/q and

    a_0=m x^2,
    mu=-2m log cos(x),
    kappa=-2m log cos(2x)-4mu,
    Delta=e^(-4mu) (1-e^(-kappa)),
    Delta_1=e^(-a_0) (1-e^(-(mu-a_0))).

Both kappa and mu-a_0 are positive for all sufficiently large q; they satisfy

    mu-a_0 ~ pi^4 m/(6 q^4),
    kappa  ~ 2 pi^4 m/q^4.                                (1)

The first-mode calibrated width is the explicit value b_*=mu q^2/pi^2 and t=0. It does not match the unwrapped variance exactly. The ratio Delta/Delta_1 tends to zero exponentially in m/q^2.

Let D be the number of independent residue draws. There are two exact comparison windows:

1. If D Delta_1^2 tends to tau_1 in [0,infinity],

       TV(P^D,Q_(m,0)^D) -> 2 Phi(sqrt(2 tau_1)/2)-1.      (2)

2. If D Delta^2 tends to tau in [0,infinity],

       TV(P^D,Q_(b_*,0)^D) -> 2 Phi(sqrt(2 tau)/2)-1,
       inf_(b_i>0,t_i real) TV(P^D, tensor_i Q_(b_i,t_i))
                          -> 2 Phi(sqrt(2 tau)/2)-1.       (3)

Here Phi is the standard normal CDF, the exponents denote products, and both profiles have endpoint one at infinity. The infimum in (3) allows each independent Gaussian factor to have its own arbitrary width and real center. A correlated Gaussian alternative is not covered.

## 2. Fourier series and the sufficient profiles

Use Fourier coefficients E exp(2 pi i j Y/q). For the binomial, the finite characteristic function is exact:

    P_hat(j) = cos(pi j/q)^(2m).                            (4)

The discrete Gaussian satisfies the Poisson formula

    Q_hat_(b,t)(j) =
      exp(2 pi i j t/q)
      [sum_(l in Z) exp(-pi^2 b(l-j/q)^2) exp(-2 pi i l t)]
      / [sum_(l in Z) exp(-pi^2 b l^2) exp(-2 pi i l t)].    (5)

When b tends to infinity, for integer j with |j|<=q/2 this equals
exp(2 pi i j t/q) exp(-pi^2 b j^2/q^2)+O(exp(-c b))
for an absolute c>0, uniformly in t and j. Indeed all omitted terms in the numerator have |l-j/q|>=1/2, and the denominator is 1+O(exp(-pi^2 b)). For j=1 the error is also multiplicatively O(exp(-c b)) relative to its main coefficient, for all sufficiently large q. A midpoint frequency at even q causes no difficulty for the absolute estimate.

For jx<=pi/4, Taylor's formula gives

    0 <= -2m log cos(jx)-j^2 a_0 <= C m j^4/q^4,
    0 <= -2m log cos(jx)-j^2 mu  <= C m j^4/q^4.

The second nonnegativity follows because -log(cos z)/z^2 is increasing on (0,pi/2): write it as the integral of tan and use that tan(z)/z is increasing, since sec^2 is increasing. The first follows either from the same observation or from tan z>=z. The expansion -2 log cos z=z^2+z^4/6+O(z^6) proves (1). The matching intensity scales in (1) imply that (1-e^(-kappa))/(1-e^(-(mu-a_0))) is bounded, so Delta/Delta_1=O(exp(-3a_0)).

For Q_(b_*,0), (5) has exponential core exp(-j^2 mu). Its first Fourier coefficient agrees with (4) to O(exp(-c m)). At j=2 the excess of that core over (4) is exactly Delta. The total absolute difference at |j|>=3 is o(Delta). To verify the latter, for 3<=|j|<=q/4 bound each difference by

    exp(-j^2 mu) min(1,C j^4 m/q^4)
                 <= C' Delta j^4 exp(-(j^2-4)mu),

using (1) and comparability of 1-e^(-kappa) to min(1,m/q^4). The sum tends to zero relative to Delta. For q/4<|j|<=q/2 both cores are exponentially small in m; their sum and the aggregate alias error from (5) are negligible. In detail mu=O(m/q^2) and 1-e^(-kappa)>=c' q^(-2) since m/q^2 tends to infinity, so q exp(-c m)=o(Delta). The identical argument starting at j=1 for b=m gives the dominant first-mode discrepancy Delta_1 and a higher-mode sum o(Delta_1), now with exponents a_0 and the first Taylor bound.

Both target Gaussian references and P have densities tending uniformly to one relative to the uniform law on Z/qZ. This follows by summing their nontrivial Fourier coefficients, bounded by a Gaussian series starting at exp(-a_0) or exp(-mu), plus negligible aliases. Accordingly the calibrated likelihood under Q_(b_*,0), minus one, is uniformly

    -2 Delta cos(4 pi y/q)+o(Delta).                       (6)

For the variance match replace Delta by Delta_1 and frequency two by one. Uniform averaging of the squared cosine is 1/2 for q>=5. Thus in either comparison, if delta denotes the respective Delta, the likelihood difference U has mean zero, ||U||_infinity=O(delta) and E U^2=(2+o(1)) delta^2.

Under an independent product reference the log likelihood is
sum U_i - (1/2)sum U_i^2 plus a remainder bounded by C sum|U_i|^3. If D delta^2 tends to finite positive tau, bounded increments give the CLT for the linear term, and the squared term concentrates; the remainder tends to zero in mean. The log-likelihood limit is N(-tau,2tau). Evaluating TV as E_reference (1-exp(log likelihood))_+ gives (2) and the first part of (3). If D delta^2 tends to zero, product chi-squared gives TV tending to zero. If it tends to infinity, one-copy Hellinger affinity is 1-(1+o(1)) E U^2/8; the product overlap tends to zero. These prove both endpoints.

## 3. Optimality against arbitrarily retuned independent factors

It is enough to prove the lower bound at a finite positive tau in (3). Suppose a sequence of product alternatives tensor_i Q_(b_i,t_i) has total distance bounded away from one along a subsequence; otherwise the claim is automatic there. Its product Hellinger affinity with P^D is bounded below, since affinity is at least overlap. Therefore the sum of the individual deficits 1-Aff(P,Q_(b_i,t_i)) is bounded. For any unit-modulus Fourier test, the squared expectation difference is at most 8 times that deficit, by the TV/affinity inequality. Thus

    sum_i |Q_hat_(b_i,t_i)(1)-e^(-mu)|^2 = O(1).           (7)

Take M=e^mu and retain those indices for which the summand's absolute square root is at most M Delta. The retained fraction tends to one, since D Delta^2 tends to positive tau and M grows. For all the retained indices we claim, uniformly,

    Q_hat_(b_i,t_i)(2)=e^(-4mu)+o(Delta),
    ||q Q_(b_i,t_i)-1||_infinity=o(1).                     (8)

Here the second norm is for the residue probabilities as a function of the residue.

To justify localization, first note that Q_hat(1) tends to zero uniformly over the retained factors, because M Delta/e^(-mu) tends to zero. This forces b_i/q^2 tending to infinity uniformly there. If b_i remains bounded, shift its center by an integer into [-1/2,1/2] without changing the modulus of the coefficient. The Gaussian tails relative to a nearest integer point then give a uniform bound on E|X| about that integer: for |k|>=2 the exponent difference is at least (k^2-|k|)/b_i. Thus the modulus of the first coefficient tends to one. If instead b_i tends to infinity while b_i/q^2 stays bounded, (5) bounds the modulus away from zero. Subsequence selection proves the uniform localization.

Write a_i=pi^2 b_i/q^2 and theta_i=2 pi t_i/q. The relative version of (5) at j=1 yields, on the retained set,

    a_i=mu+o(1),

because Q_hat(1) has modulus (1+o(1)) exp(-mu). Hence b_i~m uniformly, so all aliases are now exponentially small in m. Applying the magnitude and phase of the same first coefficient again gives

    |a_i-mu| + |exp(i theta_i)-1|
                     = O(M Delta exp(mu)) + O(exp(-c' m)).

The error in the main second coefficient exp(2i theta_i) exp(-4 a_i) is then at most O(M exp(-3mu) Delta)+O(exp(-c' m)), which is o(Delta) since M=e^mu. This gives the first claim of (8); the second follows by summing the Fourier coefficients using (5) and a_i~mu.

Now use the real frequency-two cosine C(y)=cos(4 pi y/q) on the retained coordinates only. For every retained coordinate its mean under the Gaussian replacement exceeds its mean under P by Delta+o(Delta), by (4) and (8). Its variance tends uniformly to 1/2 under either law, since both approach uniform relative densities there. Subtract the P means and divide the sum of the retained variables by sqrt(number retained / 2). Under P this converges to N(0,1); under the independent replacements it converges to N(sqrt(2tau),1), by the bounded-variable triangular-array CLT and the retained fraction tending to one. The threshold halfway between the means gives TV lower bound 2 Phi(sqrt(2tau)/2)-1, matching the calibrated choice. This holds for every sequence of near-minimizers, including subsequences at distance tending to one, and proves the positive finite window. At tau=0 the upper bound suffices. At tau=infinity restrict to enough of the coordinates to give an arbitrary fixed positive critical value, apply this lower bound, then send that value to infinity.

The high-dimensional gain from calibration therefore uses no theorem about a pre-wrapping Gaussian fit. The first Fourier mode must be matched exceedingly closely for any valid alternative, and after that the second mode is asymptotically rigid. This is an unforced noise-law comparison after a single integer quotient, not a tool for inferring or testing hidden information.

## Reproduction

    node verify-wrapped-binomial-gaussian-calibration.js

This checks exact finite centered-binomial weights and residue moments, direct Gaussian sums versus their Poisson Fourier representation, and the two dominant harmonic scalings in synthetic examples.
