# A sharper Fourier bound for the same smooth Goldbach ledger

This refines only the numerical envelope in [SmoothAllLeastFactorDebit, §3–4](SmoothAllLeastFactorDebit.md). No weights, distribution inputs, least-factor restrictions, or physical packets are changed.

**Subquadratic envelope with an explicit constant.** Write I(y)=∫_0^y 2|sin(t/2)|dt/t and a=4/π. For all y≥0,
     
    exp I(y) ≤ 5 max(1,y^(51/40)).

For y≤1, I(y)≤1. For 1≤y≤2π, the only interior local maximum of I(y)−a log y is the larger solution of 2sin(y/2)=a. This lies in (4.8,5) by the sine Taylor bounds at 2.4 and 2.5, and at that point I(y)−a log y ≤ I(5)−1.27 log 4.8 < 3.57−1.27·1.568 < log 5. The endpoint 1 already works. At 2π, use the following tail argument. The periodic primitive F of 2|sin(t/2)|−a starting at zero satisfies F(2π−t)=−F(t), and on [0,π] is nonpositive with
     
    F(t)=4(1−cos(t/2))−at ≥ (1/2−π²/96)t²−at.
     
Thus |F|<1.1 by minimizing the quadratic. Integration by parts from T=2π gives I(y)−a log y ≤ I(T)−a log T+1.1/T for y≥T. This is less than 3.72−1.27·1.837+1.1/6.28<log 5. Both I(5)<3.57 and I(2π)<3.72 follow by integrating the sine Taylor series through its positive z⁹ term, the polynomial upper bound 2[z−z³/18+z⁵/600−z⁷/35280+z⁹/3265920] at z=y/2. Finally 51/40>a. The compact log lower bounds follow from the increasing atanh series.

**Integrate the published cosine kernel directly.** With β=.310, f₀(t)=(1−t)g(t), and g its normalized cosine autocorrelation, put u=βξ and S(v)=sin(v)/v. Direct Fourier integration gives ĥg(ξ)=βG(u), where
     
    G(u)=2π² S((u−π)/2)²/(u+π)²  for u≥0.
     
The expression has no singularity at u=π. By symmetry and |ĥf₀|≤ĥg+|ĥg′|, the profile integral in §3 is at most
     
    ∫_0^∞ [(G(u)+β|G′(u)|)/π] · (10/.679) max(1,(.689u/β)^(51/40)) du.

The two endpoints .679 and .689 keep the upper uniform for every permitted p. The [companion integer replay](check_smooth_fourier_176.js) bounds the [0,20] integral by 167.751. It uses 800 intervals of length 1/40, sinc and derivative at each midpoint by 24 Taylor terms, and their respective Lipschitz bounds 1/2 and 1/3 from the integral definition of sinc. The per-point fixed-scale rounding plus Taylor error is <10^−10 for |argument|<9: bound the two integrated Taylor remainders by 9^48/48! and 9^47/47!, respectively. The code uses a rational π bracket between 3.14159265358970 and 3.14159265358990 and all arithmetic for upper sums rounds outward. The rational power 51/40 is bounded by binary integer comparison of the 40th and 51st powers. Replay recorded 167.75073813865163 for the upper sum. 

For u≥20, v=(u−π)/2 gives |S(v)|≤2.374/u and |S′(v)|≤2.656/u. Direct differentiation gives G≤112/u⁴ and |G′|≤137/u⁴, so the bracket divided by π is ≤50/u⁴. The rest is ≤15·3u^(51/40); the integrated tail is below 8, also by an exact rational power comparison in the replay. Thus the f₀ integral is less than 175.751. The same affine-neighborhood perturbation as in the published proof contributes o(1) as its fixed small scale shrinks. Its stated weighted Fourier norm already controls the envelope with exponent 4/π, which the first argument bounds without replacement by 51/40. Choose the scale so the sum is less than 176. No change to the analytic Shiu/PNT limit or BV step is needed. [Shiu's original theorem](https://doi.org/10.1515/CRLL.1980.313.161)

**Effect on the existing ledger.** The two positive estimates are linear in that uniform Fourier constant and the recalibrated mean is independent of the constant. Both upper charges scale by 176/286. The updated [packet checker](check_smooth_all_least_debit.py) gives upper bounds 0.498138424 and 0.001606436, with exact sum below 0.500. This leaves more than half of the same single mean before additional charges. This is a margin on the already measured portions, not a lower bound for the unrestricted sum.
