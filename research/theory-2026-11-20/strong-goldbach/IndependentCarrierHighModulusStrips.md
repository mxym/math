# Higher active modulus strips for the actual mixed carrier

This is an application of **Proposition 2** in the November 16 Hexagon preprint of [Sarvagya Jain, *Smooth Numbers in Arithmetic Progressions with Uniformity in the Residue Class*, version 1](https://hexagonmath.org/2611.00530v1) ([primary PDF, pp. 5–6](https://hexagonmath.org/pdf/2611.00530v1)). It gives fixed but unspecified-width open strips near the modulus exponents .598, .613, and .618 in which the actual signed sum (61) cancels, on precisely narrowed versions of the earlier mixed carriers. The .598 and .618 applications do **not** require the extra prime marker. The .613 application uses its exact independent suffix split. This uses the proposition as stated in that separate preprint, not its smooth-number Theorem 1, not Proposition 3 of arXiv:2611.21136, and not a contiguous modulus level through the higher endpoints.

## 1. Source, constants, and factor lengths

Keep \(x=N/2,\ I=(x/2,x]\), macro prime exponents .240 and .250, disjoint nine \(q_i\)-labels centered at \(.054+(i-5)10^{-7}\), and a rough suffix \(v\) of exponent .024. The marked version additionally requires \(v=A_0w\) with \(A_0\) an actual .015 prime and \(w\) .009 rough, as in [the previous seam note](MarkedCarrierTypeISeam.md). We distinguish the fixed target \(N\) from the *middle factor length* named \(N\) in the primary proposition.

The proposition treats any independent 1-bounded triple with lengths \(M,N_{\rm len},L\) and \(X'=M N_{\rm len}L\). The residue is \(a_1\overline{a_2}\) with \(|a_1|\le(X')^{1+\delta}\), \(|a_2|\le(X')^\delta\), and \((a_1,a_2)=1\); here take \(a_1=N=2x,\ a_2=1\). Let \(m,u,\ell\) denote the three factor exponents in \(x\), and \(r\) the exponent of the modulus dyad \(R\). Since \(X'\asymp x\), all of the following length inequalities, with their stated positive margins, transfer to exponents normalized using \(X'\):
\[
\begin{split}
 u&\ge\kappa,\qquad u+\ell\le 2/3-5\kappa,\qquad \ell\le m-\kappa,
       \qquad m\le r\le u+\ell-\kappa,\\
 2u&\le \tfrac12-\kappa,\qquad
 2u+3\ell-1-r\le-\kappa,\qquad
 C_*(u+\ell-r)+u+\tfrac12-2\ell\le-\kappa .
\end{split}
\tag{1}
\]
Here \(C_*>1\) is the absolute constant in Proposition 2, not numerically specified in the preprint. The result bounds the absolute average after removing characters of conductor at most \(D\) by \(O_\kappa(X'(\log X')^4/\sqrt{\min((X')^\delta,D)})\), for every \(1\le D\le (X')^\kappa\). The source explicitly handles arbitrary coefficients including nonsquarefree support after its intermediate reductions. In the .613 and .618 applications our middle factor is in fact one actual prime, \(A_M\).

Choose a fixed
\[
       \lambda=\min\{10^{-5},10^{-3}/(C_*+1)\},\qquad \kappa=\lambda/8 .
\tag{2}
\]
In each original macro and \(q_i\) band narrow its half-width to \(\rho=\min\{10^{-10},\lambda/1000\}\) around the *same old center*. For the .613 strip narrow also \(A_0\) around .015 to half-width \(\rho\). Keep \(s\) fixed sufficiently large and choose the original rough exponent \(\varepsilon<.0088\). The total suffix exponent constraint \(|\log_xv-.024|\le20\rho\) is redundant on \(I\) with these narrow labels once \(x\) is large. The implication follows because the sum of all nine offsets is zero, all eleven label deviations add by at most \(11\rho\), and \(\log_x(n/x)=O(1/\log x)\) on \(I\). With a narrowed \(A_0\) the rough cofactor interval \(|\log_xw-.009|\le25\rho\) is likewise redundant. Thus one can impose these total or split suffix bands independently of all other groups. To allow \(v=A_0w\) in a *single* group without narrowing \(A_0\), keep the old \(A_0\)-band and test the unique factorization inside the independently constrained \(v\)-coefficient.

Let \(Q_{2}=q_1q_9\) (symmetric offsets), \(Q_{7}\) the product of the remaining seven labels, and \(Q_{3},Q_{4}\) a partition of these seven into \((q_2,q_5,q_8)\) and \((q_3,q_4,q_6,q_7)\); their offsets separately sum to zero. The assignments for the three claims are
\[
\begin{array}{c|c|c|c|c}
 \text{carrier}& M\text{-group}&N_{\rm len}\text{-group}&L\text{-group}&(m_0,u_0,\ell_0)\\\hline
 C\text{ or }C_\sharp & A_M Q_3 & Q_4 & B_M Q_2 v &(.402,.216,.382)\\
 C_\sharp& Q_7 w & A_M & B_M Q_2 A_0 &(.387,.240,.373)\\
 C\text{ or }C_\sharp& B_M Q_2 v & A_M & Q_7 &(.382,.240,.378)
\end{array}
\tag{3}
\]
Here \(v\) is the actual full suffix, grouping its marked factors together if the chosen carrier is marked. Each label appears precisely once. Distinct exponent bands and uniqueness of the large suffix marker (\(w<A_0\)) imply each group coefficient is 0 or 1; one may retain arbitrary Mellin phases arising from the product endpoint. Dyadic factor-length changes perturb each central exponent by at most \(\Delta=\lambda/20\) for sufficiently large \(x\) by the displayed narrowing; the bound also absorbs the \(X'\)-normalization error (take \(x\) still larger).

For each row set \(U_0=u_0+\ell_0\); take only moduli with
\[
                         U_0-2\lambda\le r\le U_0-\lambda .
\tag{4}
\]
The upper margin before subtracting \(\kappa\) is at least \(.9\lambda\), and \(C_*(u+\ell-r)\le 2.1 C_*\lambda\le .0021\). The central complementary margins \(-u_0-\tfrac12+2\ell_0\) are respectively .048, .006, .016; their worst losses are \(3\Delta\). So the last condition of (1) retains more than .0038 in all cases. The central diagonal lower limits \(2u_0+3\ell_0-1\) are .578, .599, .614, giving \(U_0\)-margins .020, .014, .004, respectively. Their losses are at most \(2\lambda+5\Delta<.000023\). Also \(m_0-\ell_0\ge.004\), \(2u_0\le.480\), \(u_0+\ell_0\le.618<2/3\), \(u_0\ge.216\), and the \(r-m\) margins exceed .19. Thus all hypotheses (1), with the actual fixed \(\kappa>0\), hold in every contributing dyad. The constants and the required threshold for \(x\) can depend on \(C_*\) and the absolute proposition parameters, but do not depend on \(N\) at fixed choices. With \(|a_1|/(X')^{1+\delta}=O(x^{-\delta})\), the residue-size restriction has positive reserve as well.

## 2. Transfer to the actual signed Type I strip

For each of the three carriers just specified, write it as \(C^\dagger\). Each row proves, **only for the moduli in (4)**,
\[
 \sum_r\sup_t\left|
   \sum_{\substack{m\in J\\m\le t,\,r\mid m}} C^\dagger(N-m)
       -\frac{1_{(r,N)=1}}{\varphi(r)}
           \sum_{\substack{m\in J\\m\le t}}C^\dagger(N-m)\right|
                         \ll_{s,B,\lambda} x(\log x)^{-B}.
\tag{5}
\]
In (5) the summation \(r\) denotes the integer modulus with exponent in (4), and \(J=N-I\). The proof from the stated Proposition 2 is the same transfer as in [the previous seam note, §2](MarkedCarrierTypeISeam.md#2-unweighted-maximal-distribution-and-reference): choose \(D=x^\eta\) with \(0<\eta<\min(\kappa,\delta,\varepsilon/10)\) after all length parameters, use the ordinary maximal primitive prime-character mean after fixing all labelled/suffix factors but an independent actual \(q_i\), and sum the reciprocal fixed factors. This is valid whichever slot contained the chosen \(q_i\), because undoing the grouping for this low-conductor comparison retains independence; the product constraint is only an endpoint for the last prime. The missing unit and nonreduced terms all have a prime \(\ge y\) dividing the carrier or its modulus, or else the nonreduced carrier residue is empty. The harmonic estimates of the seam note still apply through the largest .618, strictly below 1. Smooth Mellin separation of the product interval and the logarithmic mesh cost fixed log powers only, since the full carrier is 0 or 1 and the number of moduli is at most \(x^{.618}\). No result for an arbitrary convolution of below-main-term density is used for the low conductors.

For the sequence \(c_N^\dagger\) subtracting the own mesh-matched rough reference, the CRT proof of (59) likewise works on these strips. In particular the same \(r^{-1}\prod_{p\mid r,p<Z}(1-1/p)^{-1}\)-to-\(1/\varphi(r)\) replacement applies for reduced moduli, and fixed prefix balancing is independent of the size of the modulus exponent below 1. Hence
\[
 \sum_{\substack{U<d\le x^{.560},\ p\le V\ {\rm prime}\\
                  \log_x(dp)\in[U_0-2\lambda,U_0-\lambda]}}
       \mu(d)\log p\,\sum_{h\ge1}c_N^\dagger(dph)
                   \ll_{s,B,\lambda} x(\log x)^{-B}.
\tag{6}
\]
One can also impose factor intervals with their moving \(h\)-prefixes, by collecting \(r=dp\) and using \(\sum_{p\mid r}\log p\le \log r\). In each strip there are fixed-width allowed log-exponent boxes for this **active** term (61); for example choose \(\log_x d\) near .490, \(\log_x p\) near \(U_0-.490-\tfrac32\lambda\), and \(\log_x h\) near \(1-U_0+\tfrac32\lambda\), with widths sufficiently small relative to \(\lambda\). All \(dp\) are above the earlier .586 Type I range, \(p\le V=x^{.286}\), and \(d\le x^{.560}\). The containment in the fixed positive carrier nevertheless does not prove a weighted signed sum where the factor \(K_{P_i}(N-dph)\) is left on the row.

## 3. Positive-cell normalization and genuine gaps

For either \(C\) or \(C_\sharp\), all geometric sign and uniqueness tests defining the previous positive mixed cell survive shrinking the labelled intervals around their unchanged centers. Its reference mass after normalization remains a fixed **strictly positive** constant times \(M_N/\varepsilon\) in the earlier iterated limit. Indeed every genuine prime interval contributes a positive harmonic constant \(\log(b/a)\) for its endpoints \(x^a,x^b\), by PNT/partial summation, and the rough cofactor still has its exponent bounded below by a fixed positive number (approximately .024 or .009). Uniform rough counts therefore give the same leading factor in \(\varepsilon\) as in the old positive-cell proof. The fixed harmonic product can be very small, depending on \(\rho\) and hence \(C_*\). No lower bound independent of the narrowing and no Goldbach positivity follows.

The ratios in (1) do not justify a claim that the *intervals between the strips* are covered. In fact the necessary inequalities \(u+\tfrac12<2\ell,\ m+u+\ell=1,\ \ell<m\) give \(m+3\ell>1.5\). Consider simply the old central factors and, **even more generously than actual factorization**, allow the entire suffix mass .024 to be allocated fractionally among the independent groups. There is no admissible group with \(m\) in \([.393,.398]\). Such an \(M\)-group cannot contain a macro: with two .054 labels and the full suffix even .25 reaches only .382, while three labels with .24 already give .402. With no macro it must contain seven .054 labels; those labels account for .378, leaving suffix mass at most \(.024-(m-.378)\) for other slots. Both macros cannot be put in the \(L\)-group (which must be smaller than \(M\)), or in the middle group (where \(2u<.5\)). In the largest possible \(L\)-group the larger macro, both remaining labels and the maximum remaining suffix give \(\ell\le .25+.108+.024-(m-.378)=.760-m\). But then \(m+3\ell\le 2.280-2m<1.5\). Fixed exponent perturbations of the old widths preserve these strict exclusions via the displayed margins. In particular a modulus near .605 cannot be treated by tuning the upper endpoint \(u+\ell=1-m\) arbitrarily close to it using a split of the old suffix alone. One cannot conclude that .605 is impossible for every fixed \(C_*\), only that the near-upper-endpoint argument with an unspecified \(C_*\) does not guarantee that bridge.

The untouched terms include most of \(dp>x^{.586}\) in (61), the upper-\(d\) quotient block, and all other low sectors that do not admit these independent groupings. Neither the full marked covariance nor binary Goldbach follows from this strip application.

For a related referee-published convolution input, see [Pascadi, *Smooth numbers in arithmetic progressions to large moduli*, Theorem 4.2](https://doi.org/10.1112/S0010437X2500747X). Its principal smooth-number statement has different residue hypotheses. The limited fixed-factor groupings and the precise application of Jain's coefficient proposition, not the general smooth-number distribution exponent or the method of triple factorization, are the subject of this note.
