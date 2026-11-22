# A whole semiprime and triprime subtraction on a genuine short-tag covariance

For every sufficiently large even target, this removes **all squarefree semiprimes and all squarefree triprimes**, with no angular or least-prime cutoff, from a genuine marked shared-index centered covariance. It also removes all actual squarefree inputs with a prime factor exceeding \(x^{.505}\) and determines the sign of the whole squarefree rank-four input. This uses a smaller actual prime mark than the earlier single-tag theorem and still restricts the shared index to be squarefree. The result is a signed reduction to the actual rough rank-\(\ge4\) terms, not a bound on their covariance and not a Goldbach positivity theorem.

## 1. Literal setup and positive acute angle

Let \(N=2x\) be any sufficiently large even integer, \(Y=\sqrt{x}\), \(L=\log x\), \(\ell=\log L\), \(z=\exp(L/\ell^2)\), \(R_z(y)=1_{P^-(y)>z}\). On
\[
 d,e\in[.65Y,.8Y],\qquad k\in[Y,1.1Y],\quad (dek,N)=1,\quad k\text{ squarefree},
\]
use the genuine prime multiplicity
\[
 \beta_{\rm sh}(e)=\sum_{\substack{p\mid e,\ p\ {\rm prime}\\x^{.002}\le p\le x^{.003}}}1
\]
and the same weight on \(d\). Write \(y=N-ek\); thus \(y\in I_k=[N-.8Yk,N-.65Yk]\subset(1.1x,1.4x)\), and after fixing the marked \(p\), \(y\equiv N\bmod A\) with \(A=kp\). The unit on \(e\) outside \(A\) is exactly \((y,N)=1\). The incidental labels \(p\mid k\) cost \(O(x^{3/2-.002+o(1)})\) after both slope sums, since before weights their pair count is \(\ll\sum_{p\ge x^{.002},\ p\le x^{.003}}(Y/p+1)^2\). The same power estimate permits deleting such labels on either side. For every remaining label \(A\) is squarefree and \(x^{.502+o(1)}\le A\le x^{.503+o(1)}\).

Use
\[
 a_{\rm p}(y)=\log y\,1_{y\ {\rm prime}},\qquad
 b_z(y)=R_z(y)/V_z,\qquad V_z=\prod_{p'\le z}(1-1/p'),\qquad R=x^{.5003}.
\]
The original above-root score is now
\[
 K_R(y)=R_z(y)\sum_{\substack{rs=y\\r>R}}\mu(r)\log s.
 \tag{1}
\]
The proof of [the \(F_R-b_z\) transfer, §§1–2](https://github.com/mxym/math/commit/48786012bff7073486a373df69f35611a803e916) applies with this smaller \(R\) and with actual \(e=ph\). Briefly the independent short true prime slot is \(p\), and the long slot \(hk\) includes the arbitrary \(k\)-weight and its squarefree mask. The sharing labels are allowed at this step and can be paid afterwards, so there is no cross-slot short-prime restriction. As in the proof, use log-fine prefixes in the real interval and clip the actual reflected divisor weights. The true short-prime sequence satisfies Fouvry's auxiliary Siegel–Walfisz by the same prime and coprimality exclusions. In [Fouvry's primary Corollaire 1, pp. 617–619](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf), the allowed power rails in the actual source scale, up to a fixed small loss, are \(1/2+\alpha/2\) and \(4/7-6\alpha/7\) for \(\alpha\in[.002,.003]+o(1)\). Each strictly exceeds the required \(.5004\), with the first at least \(.501+o(1)\) and the second at least \(.5688+o(1)\). The scale for the moving integer residue \(N\) remains \(4M_0N_0\ge(2.6-o(1))x>N\). The exact opened moduli \(r\lambda\) never exceed \(x^{.5004}\) after the true roughness expansion. All masks and actual progression principal terms of the cited argument are unaltered. The masked zero and first harmonic \(\mu/\varphi\) prefixes in that proof apply at the new polynomial endpoint \(R\), so the exact two matched main terms remain \(\mathfrak S(Nek)\). Hence the signed replacement of \(a_{\rm p}-b_z\) by \(K_R\) holds against every actual opposite row within the earlier fixed divisor envelope, with \(O_B(x^{3/2}L^{-B})\) error. Proper prime powers cost \(O(x^{1+o(1)})\) after the two sides are summed.

The new mark is not an empty or exceptionally sparse family of genuine prime rows. For a concrete lower subfamily on the *opposite* side only, additionally require one prime divisor of \(d\) in \([x^{.0981},x^{.0983}]\) and take the first mark in \([x^{.0022},x^{.0025}]\). These two independent modulus factors have positive reciprocal prime masses. The exact common-residue progression proof of [the prior Maynard wedge §1](https://github.com/mxym/math/commit/bafa9b8f) applies to this new compact subwedge. Indeed its two strict inequalities are \(u+v>.10024\) and \(.6u+v<.09992\); here \(u+v\ge .1003\) and \(.6u+v\le .0998\), and \(u\) lies strictly in \((.0008,.04986)\). Use the same triple slot assignment with the auxiliary \(j\) in the last factor and a maximal prefix mesh in the true prime output length; \(j\) may be any fixed-log-power auxiliary. In particular to retain squarefree \(k\) insert \(\sum_{f^2\mid k}\mu(f)\) and use \(j=f^2\), truncating \(f\) at a sufficiently large log power. Its physical tail is \(O(xL^{-B})\) before the other slope; the model has the complete positive factor
\(\prod_{r\nmid N}(1-\varphi(d)/\varphi(d r^2))\gg1\), as in [the one-tag squarefree-prime-occupancy proof, §5](../one_tag_balanced_three_free/Proof.md). Counting the residual free factor of \(d\) with true \(N\)-unit mask, just as in that proof, gives \(\gg Y\varphi(N)/N\) such weighted opposite slopes \(d\). Thus the actual weighted opposite genuine-prime mass is \(\gg x\varphi(N)/N\) even with squarefree \(k\). This is not a quantitative abundance assertion for the balanced prime pairs sought by Goldbach.

## 2. Exact free-slot labels and the complete triprime rank

Use the old base threshold \(T_0(s)=\min(x^{.766}s^{-1/2},x^{.918}/s)\) but cap it at \(x^{.505}\):
\[
 T(s)=\min(T_0(s),x^{.505}),\qquad
 F(y)=-R_z(y)\!\sum_{\substack{s c a=y\\ ca>R,\ a>T(s)}}\mu_2(c)\log s.
 \tag{2}
\]
Here \(\mu_2=\mu*\mu\). First use the elementary proof of [the base huge-free subtraction](../full_free_hb_splice/Proof.md) with \(T_0\). On \(s\le x^{.304}\) its one-free cutoff and its two error conditions \(Q S<x\), \(Q^{5/4}<W\sqrt S\) retain even more slack because \(Q\le x^{.503+o(1)}\). The original \(ca>R\) is automatic in these low \(s\)'s. The no-wrap condition and \(S<Q\) remain intact. On the two-free part \(s>x^{.304}\), the original \(sa>x^{.918}\) gives the same bound \(c<1.5x^{.082}\); the maximal true \(s\) is now \(y/R\), and \(a>R/c\gg x^{.4183}\). The incomplete-rectangle exponent is at most \(.082+(3/2)(.504)=.838\), and the terms proportional to \(W+S\) save a fixed power since \(s,a\) have these positive lower exponents. In particular its exact zero mode (7) still has the masked \(\mu_2(c)/c\) prefix, the same \(c\) endpoint \(y/x^{.918}\), and the true upper \(s<y/R\); the local unit factors and roughness expansion do not change. No factored-annulus result is needed.

The cap adds only the free range \(x^{.505}<a\le T_0(s)\), empty unless \(s<x^{.413}\). On it \(ca>R\) is automatic and \(sc\le1.4x^{.495}\). This extra range has a simpler direct uniform signed cancellation: fix the actual \(s,c,A,k,p\), keep \((sc,AN)=1\), and expand just the roughness of \(a\) by the same signed Bonferroni truncation. The full \(N\)-unit test on the free \(a\) can be dropped on the rough support by the previously paid large target factor estimate. Count \(a/\lambda\) in its exact reduced class modulo \(A\), in the literal intersection of the \(y\)-range and \(x^{.505}<a\le T_0(s)\). The error \(O(1)\) per interval costs at most
\(x^{.495+.503+o(1)}=x^{.998+o(1)}\) after all \(s,c,A\), rough divisors and fixed divisor multiplicities, before the outer \(d\)-length. This uses \(\sum_{sc\le1.4x^{.495}}1\ll x^{.495}L\) and the actual upper scale \(.503+o(1)\) of \(A\), not the more generous \(.504\) comparison used later. The progression principal after \(y=csa\) has \(W_z(A)/A\) times the \(dy\) integral of
\[
 -\sum_{\substack{T_0(s)>x^{.505}\\(s,AN)=1}}
 \frac{R_z(s)\log s}{s}
 \sum_{\substack{y/(sT_0(s))\le c<y/(s x^{.505})\\(c,AN)=1}}
             \frac{\mu_2(c)R_z(c)}c .
\]
Both \(c\) endpoints are at least \(y/x^{.918}\gg x^{.082}\) on the nonempty interval. Its masked harmonic signed prefix difference is therefore uniformly arbitrary-log small; the \(s\)-sum costs only log powers. The cap requires no new scalar zero mode.

For the common exact finite Möbius identity take the truncation threshold \(U=x^{.496}\) (its fifth power exceeds the whole physical input). The single selected free slot \(a>T(s)\) is unique since \(T(s)>\sqrt r\) for all physical \(r>R\): this holds separately for the two old thresholds as \(s<y/R\), and for the constant cap since \(r<1.4x\). Every unselected complementary product is \(\le1.4x^{.495}<U\) in the cap branch, and is already \(<x^{.24}\) in the old branch, so the same exact aggregate \(-\mu_2(c)\) applies throughout. The older cancellation of its actual score does not depend on the choice of a valid identity truncation once its aggregate has been formed.

Let \(C=x^{.0002}\) and \(\mu_3=\mu*\mu*\mu\). Define the exact further score
\[
 G(y)=R_z(y)\sum_{\substack{s a b c=y,\ c\le C\\
                         a,\ bc\in[x^{.080},T(s)]\\a b c>R}}
                   \mu_3(c)\log s .                             \tag{3}
\]
The output \(v=bc\), rather than \(b\), is used in the two upper and lower shape tests, with the **new capped** upper threshold \(T(s)\). The \(s\) slot has **no** lower power cutoff, and the \(s=1\) term vanishes. Formula (3) is a selected exact branch of the same five-term Möbius identity with truncated factors \(\le U=x^{.496}\). Indeed the two free indices occupied by \(a,b\) are the only free indices exceeding \(x^{.0797}\) since \(a\ge x^{.080}\), \(b\ge x^{.0798}\) and the product \(c\le x^{.0002}\). Assign \(a,b\) to the two index positions in their original order. All unselected factors have product \(c\), their truncations are automatic, and the coefficient \(\mu_3(c)\) follows from \(\sum_{j=3}^5(-1)^{j-1}\binom5j\binom{j-1}2=1\). This argument is unchanged if some numerical values coincide or \(y\) is squareful. No tuple is shared with (2): \(a,b\le T(s)\), and the other free factors are below \(x^{.0002}<T(s)\).

We now check the physical support on all squarefree ranks \(\le3\), not just in a selected exponent simplex. On a prime every score is zero. On a squarefree semiprime, the only possible nonzero \(K_R\) term has \(r\) the larger prime and \(s\) the smaller, and it vanishes if \(r\le R\). When it is nonzero the unique \(a=r\) term in \(F\) passes \(a s=y>x^{.918}\); hence \(K_R-F=0\), and \(G=0\) there. On a squarefree triprime, any nonzero summand of \(K_R\) has \(s>1\), and either \(r\) is one prime (deleted for the same reason), or \(s\) is a prime singleton and \(r=P_1 P_2>R\). In this second case \(a=r\) always qualifies in (2). A proper \(a> T(s)\) can only be the larger factor \(P_2\), since \(T(s)>\sqrt r\). That additional term has \(\mu_2(c)=-2\). Thus the **exact** remaining coefficient of \(\log s\) in \(K_R-F\) is zero when \(P_2>T(s)\), and \(2\) when \(P_2\le T(s)\).

In the latter case both \(P_1,P_2>x^{.080}\) automatically: \(P_1\le x^{.080}\) would imply \(P_2 s=y/P_1\ge x^{.920}>x^{.918}\), making \(P_2>T(s)\). On such a genuine triprime any term in (3) must choose \(a,b>1\) from \(r=P_1P_2\); hence \(c=1\), and the two orderings \(a,b\) contribute exactly \(2\log s\). The cut \(P_2\le T(s)\) agrees with the strict versus non-strict choices in (2) and (3), including equality. The same reasoning allows an arbitrarily small genuine \(s\) on a nonzero triprime row: only a small factor *among the two nonlog slots* forces cancellation already by \(F\). It follows that \(H=K_R-F-G\) vanishes on **every** squarefree integer of rank at most three on physical support. It vanishes off \(R_z\) as well.

**Giant factor.** For squarefree \(y=P w\) and a true prime \(P>x^{.505}\), every \(r=y/s>R\) contains \(P\), as \(w<1.4x^{.495}<R\). In particular \(s\mid w\). In (2), the eligible \(a\)'s are exactly the divisors of \(r\) containing \(P\): they automatically pass \(T(s)\le x^{.505}<P\), and any divisor omitting \(P\) is at most \(w/s\le1.4x^{.495}/s\), below **each** of the three threshold branches. Thus its weight in \(F\) is \(-\sum_{c\mid r/P}\mu_2(c)=-\mu(r/P)=\mu(r)\); this uses \(\mu_2*1=\mu\) and squarefreeness. Meanwhile (3) contains no such \(P\) in the nonlog slots since \(a,bc\le x^{.505}\), and \(P\mid s\) would imply \(abc<R\). Therefore \(H=0\) for all these genuine giant-prime inputs, independently of rank.

**Rank four.** For a genuine squarefree rank-four input, any summand with \(r=y/s\) having rank one or two is deleted by the same coefficient computation as above, valid even when \(s\) is composite. For rank-three \(r\) and singleton \(s\), write \(n_j\) for the number of proper \(j\)-factor divisors \(a>T(s)\) of \(r\). The exact coefficient of \(\log s\) in \(K_R-F\) is \(-2n_2+4n_1\). At most one singleton can pass, because \(T>\sqrt r\); if one does, its two associated pair products pass as well. Thus the coefficient is always nonpositive.

The only positive correction from subtracting \(G\) could come from \(c>1\). If \(r\) has no prime \(\le C\), none occurs. If it has at least two such primes, no two outputs in (3) can reach \(x^{.080}\), even by multiplying both tiny primes. Otherwise let \(p\le C\) be its unique tiny prime and \(r=pqt\). The product \(qt>T(s)\), since \(sqt=y/p\ge x^{.9998}>x^{.918}\); thus \(n_2\ge1\). The only possible admissible output partitions in (3) are \(\{q,pt\}\) and \(\{t,pq\}\). Each such valid partition contributes two \(c=1\) orderings and one \(c=p\) ordering of weight \(-3\), i.e. total \(-1\); all the shape tests are exactly in the output variables so there is no ordering or endpoint mismatch. If \(n_1=0\), the at most two units added by \(-G\) are paid by \(-2n_2\). If \(n_1=1\), every such partition has at least one output \(>T(s)\), so adds nothing. This proves \(H\le0\) on **all** squarefree rank-four inputs. This is a sign of a physical coefficient, not a cancellation or bound on the positive rank-four-by-rank-four covariance term.

## 3. Three independent free boxes, with the size of a long slot retained

For the polynomial three-free part of (3), the following extension of [the squarefree three-box proof, §1](../one_tag_balanced_three_free/Proof.md) will be used. The entire result is uniform over the reduced residue \(t\bmod A\), which here depends on the actual target \(N\) and the open labelled divisors. Let an actual smooth box have lengths \(X_1,X_2,X_3\) with \(X=X_1X_2X_3\), \(\min X_i\ge X^{.008}\), and squarefree \(X^{.501}\le A\le X^{.504}\). The desired three-box difference is the true progression count minus the product of the three exact \(A\)-unit counts divided by \(\varphi(A)\), with an error \(O(X^{1-\varepsilon_0}/A)\) for some absolute \(\varepsilon_0>0\). Smooth normalized derivatives may cost fixed log powers.

If \(\max X_i>X^{.520}\), fix the other two unit variables. In the long variable the literal class modulo \(A\) has ordinary smooth Poisson main \((X_i/A)\int W_i\), and its nonzero modes have arbitrarily strong power-decay uniformly in the residue because \(X_i/A>X^{.016}\). Summing this estimate over all unit classes also gives the exact \(A\)-unit model for that variable to the same power precision. Thus this case needs no squarefree restriction, regardless of which of the actual slots is longest, and preserves both other free weights.

If all \(X_i\le X^{.520}\), use the same squarefree CRT zero masks, dual coprimality opening, exact reduced-trace factor \(1/E\), and shifted-divisor Mellin gluing as proved there. Since \(\min X_i\ge X^{.008}\), the original independent small-power frequency truncation is available with the same exact normalizations. Retain the same trivial low-conductor branch \(d'\le X^{.498}\), saving \(X^{-.004+o(1)}\) up to a small-power loss. For \(d'>X^{.498}\), write \(M',N'\) for the glued long and separate shortest dual lengths. They obey
\[
 M'\ll X^{2(.504)-1+.520+o(1)}=X^{.528+o(1)},\qquad
 N'\ll X^{(3(.504)-1)/3+o(1)}=X^{.170\overline6+o(1)} .
\]
Here as before a sufficiently small fixed power can be used instead of the displayed \(o(1)\) from the Fourier and Mellin truncations. The exact condition in [Sharma's primary Theorem 1.2 and Lemma 5.2](https://arxiv.org/pdf/2303.06087),
\[
 N'\le (d')^{1/2}(1+M'/d')^{-2},
\]
holds with slack: the right side is at least \(X^{.249-2(.030)-o(1)}\). Use the previously derived two trace bounds, now retaining the common factor \(1+M'/d'\ll X^{.030+o(1)}\) on both of them (the individual smaller powers of this factor may harmlessly be replaced by the first power). The minimization and conductor bookkeeping in the previous note then give relative to \(X/A\)
\[
 X^{.030+o(1)}\left(A^{5/4}X^{-2/3}+A^{15/8}X^{-1}\right),
\]
with additional arbitrarily small fixed power allowances as before. The two final margins at \(.504\) are \(1/150\) and \(.025\), both strictly positive. This proof uses the weighted dual theorem, not an unweighted \(d_3\) statement or invariance under a residue replaced by zero. It covers the intermediate actual angles, not just the region where a free coordinate alone is longer than the modulus.

## 4. Uniform signed subtraction of the entire score (3)

All progressions use the actual \(A=kp\). Discard the nonunit-on-\(N\) part from the polynomial free variables only on the physical rough domain: a violating \(y\) is a multiple of a prime \(>z\) dividing \(N\), giving \(O(xL/z+L)\) values before the fixed moments and ordered-factor multiplicities. Keep \((c,N)=1\), and in the short-\(s\) branch below also \((s,N)=1\). Retain the full \(A\)-unit conditions throughout. Each actual rough free variable is opened by the same independent Bonferroni polynomial at \(J=\lceil C_BL_2\rceil\), where \(L_2=\log L\). The true fixed high-moment factorial bound and telescoping product argument of the earlier three-box proof are unchanged, now once with two variables and once with three. The largest opened divisor \(z^J=x^{o(1)}\), and the surviving congruence unit is always \(N\overline{c\prod\lambda}\bmod A\), with an additional \(\bar s\) for a fixed short \(s\).

The radial \(I_k\) cuts and the individual or moving boundaries \(a,v\in[x^{.080},T(s)]\), \(a v>R\) can be made exact after log-fine relative meshing. Work in fixed \(c\) and original \(s,a,v=bc\) coordinates first, and keep only boxes away from a relative \(O(L^{-J_0})\) thickness of the moving boundaries. The threshold \(T(s)\) is continuous and piecewise log-affine with slopes of magnitude at most one, so such boxes are independent in the free variables after fixing the labels. The contribution of the radial \(I_k\) strips is arbitrary-log small because \(e\) lies within \(O(YL^{-J_0})\) of a fixed endpoint. For each internal surface, fix \(s,c\) and one of \(a,b\) and vary the other; the affected free interval has relative thickness \(O(L^{-J_0})\), and integer floor error one per fixed tuple. If the affected boundary is in \(s\) only (the split below), either keep it literally when \(s\) is fixed or smooth from the polynomial side. The varied \(a,b\) have lengths \(\ge x^{.0798-o(1)}\), and at the large-\(s\) split \(s\asymp x^{.01}\); in each case the remaining length product including \(c\) is a fixed power below \(x\). Divisor moments of \(y,N-y\), and the earlier opposite-row envelope with an extra \(d\)-length, thus pay these errors as well as all smoothed artificial box joins with narrower transitions. The integrated corresponding volume errors have the same arbitrary-log control after the harmonic marked \(A\)-sum. This keeps all moving cutoffs in the final main.

* **True \(s\le x^{.01}\).** Fix \(s\) with its original \(R_z(s)\log s\) and \((s,N)=1\), and fix \(c\le C\). There are only \(\le x^{.0102}\) \((s,c)\) labels. The actual free variables are \(a\) and \(b\); the complete reduced-unit rectangle main is \(\varphi(A)/A^2\) times their interval product. Apply the elementary incomplete hyperbola bound (4) of the huge-free proof to each independent rectangle after the two rough divisions. Its \(A^{1/2+o(1)}\) error, summed over all actual \(A\) and then enlarged to all moduli in the dyad, is \(O(x^{.0102+(3/2)(.504)+o(1)})=O(x^{.7662+o(1)})\) before the opposite \(d\)-length. The full-period error \((W_1+W_2)A^{-1+o(1)}\) in each label, summed over moduli, is also power-small as \(sc(W_1+W_2)\ll x/\min(W_1,W_2)\) with both free lengths polynomially long. The principal after restoring the exact windows and putting \(v=bc\) is
  \[
    \frac{\varphi(A)W_z(A)^2}{A^2}
    \sum_{\substack{s\le x^{.01}\\(s,AN)=1}}R_z(s)\log s
      \left(\sum_{\substack{c\le C\\(c,AN)=1}}
               \frac{\mu_3(c)R_z(c)}c\right)
    \int_{\substack{a,v\in[x^{.080},T(s)]\\av>R,\ sav\in I_k}}da\,dv ,
  \]
  with \(W_z(A)=\prod_{r\le z,\ r\nmid A}(1-1/r)\). In particular neither the upper \(T(s)\) nor the original \(av>R\) changes when \(c\) is isolated.

* **True \(s>x^{.01}\).** All three free variables \(s,a,b\), after c and the independently opened rough divisors, have product scale \(X\asymp x/(c\lambda_s\lambda_a\lambda_b)\ge x^{.9998-o(1)}\). Their minimal size has exponent at least \(.01-o(1)\), so \(\min X_i\ge X^{.008}\). The strict rails \(X^{.501}\le A\le X^{.504}\) hold since \(.504(.9998)>.503\) and the actual lower \(A\) has exponent \(.502+o(1)\). Section 3 therefore applies to every independent box, whether or not its longest slot exceeds \(A\). The box principal is the exact reduced-unit one. The unweighted unit sums can then be replaced by \((\varphi(A)/A)\) times their integrals with elementary divisor-floor errors, since all three lengths are polynomial. After completion of the rough scalar factors and the exact substitution \(v=bc\), the model is
  \[
   \frac{\varphi(A)^2W_z(A)^3}{A^3}
      \left(\sum_{\substack{c\le C\\(c,AN)=1}}
                 \frac{\mu_3(c)R_z(c)}c\right)
   \int_{\substack{s>x^{.01},\ a,v\in[x^{.080},T(s)]\\av>R,\ sav\in I_k}}
         \log s\,ds\,da\,dv .
  \]
  The different model powers of \(W_z(A)\) and \(\varphi(A)/A\) in the two branches reflect that only the free slots were integrated. One cannot interchange the integer short-\(s\) measure with the three-free model. The \(X^{1-\varepsilon_0}/A\) errors sum with polynomial savings over the subpower rough divisor lists, log-fine boxes, the actual \(c\)-labels weighted by \(1/c\), and the marked modulus harmonic sum.

In both models the exact complete \(c\)-prefix is \(O_B(L^{-B})\) uniformly by the masked rough harmonic \(\mu_3(c)/c\) estimate of [the prior signed proof, §4](../one_tag_balanced_three_free/Proof.md). It is essential that \(C\) is polynomial and the exact moving tests have no \(c\) after \(v=bc\). The other factors in each model are \(O((x/A)L^C)\) with a fixed log exponent (denote that exponent separately from the cutoff \(C\)); for the small-\(s\) sum this follows by \(sav\asymp x\) and the harmonic sums over actual \(s\). Thus for every fixed divisor envelope as in the original proof the total is
\[
 \sum_d\left|\sum_{e,k}\beta_{\rm sh}(e)u_{d,k}G(N-ek)\right|
       \ll_B x^{3/2}L^{-B}
\]
uniformly in every even \(N\). The earlier marked \(\varphi(A)\) factors have not been dropped or borrowed from a different prime model.

## 5. Final actual covariance and non-negligible labelled scales

Replacing \(a_{\rm p}-b_z\) by \(K_R\), then subtracting (2) and (3) in each leg using the arbitrary opposite-row estimates, gives
\[
 \sum_{d,e,k}\!\beta_{\rm sh}(d)\beta_{\rm sh}(e)
   (a_{\rm p}-b_z)(N-dk)(a_{\rm p}-b_z)(N-ek)
 =
 \sum_{d,e,k}\!\beta_{\rm sh}(d)\beta_{\rm sh}(e)
    H(N-dk)H(N-ek)+O_B(x^{3/2}L^{-B}).
\]
The indices are still exactly the stated actual box, units and squarefree \(k\). The right side can be restricted to squarefree reflected integers: among the rough domain a repeated prime \(r>z\) costs \(O(x/z+\sqrt{x})\) possible \(y\)'s before divisor weights, and the standard true fixed moments with \(y,N-y\) and the opposite row give more than any log saving. Thus its two nonzero physical inputs both have at least four distinct prime factors, no prime factor exceeding \(x^{.505}\), and nonpositive coefficient whenever their rank is exactly four. This is stronger than deleting a bounded near-equal triprime window.

Neither sign in the deleted divisor-labelled branch is individually log-small. Keeping just \(c=1\), or just \(c\) prime in \([x^{.00004},x^{.00008}]\), gives opposite weights \(+1\) and \(-3\). Restrict \(s,a\) to exponents \([.330,.334]\) and \(y\) to \([1.22x,1.26x]\); then \(v\) has exponent in \([.332,.340]+O(L^{-1})\), both shape cutoffs have strict room, and \(av>R\). The second main of §4, before cancellation in c, and the true opposite prime occupancy of §1 give each mass \(\gg x^{3/2}\ell^6\varphi(N)/N\), using the same corrected \(A\)-unit Euler factor as the previous note. This is labelled mass, not an assertion that actual triprimes in that shape attain a Hardy–Littlewood asymptotic.

The restriction to squarefree shared indices is genuine. The previous smaller-angle arbitrary dual-phase argument for powerful parts does not automatically extend through all intermediate three-box geometries; in the \(X^{.520}\) regime the Eisenstein gluing really is used. Nor is the new smaller mark interchangeable with the earlier two-mark covariance at modulus exponent near \(.605\). The remaining higher-rank correlation is not estimated.

The accompanying checker uses exact rational exponent rails and symbolic prime-coordinate scores; it does not test any analytic estimate.
