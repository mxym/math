# A sharp uniform multiplicative gap after the first projection-body nesting transition

**Research note, 8 October 2026.** A continuation of the independently certified 005 finite first-nesting theorem and two-layer spectral inequalities. Prepared with AI assistance; no priority, external peer-review or complete proof-assistant verification claim is made.

## Abstract

Let \(\mathcal C_d\) be the \(d\)-dimensional polytopes generated from a point by arbitrary finite Cartesian products and affine joins, modulo invertible affine equivalences. Let \(\mathcal B_d\) be the smaller two-layer family of joins of points and two-simplex products. Previous exact work found that their sharp normalized projection-body-volume maxima agree through dimension 54 and first differ in dimension 55. We prove that **the strict separation persists in every dimension thereafter**. More strongly, the **minimum ratio of their respective sharp maxima over all \(d\ge55\) is exactly its 55-dimensional value**, a rational number greater than \(1.007\), and occurs only at 55. For every \(d\ge56\) the ratio is greater than \(1.01\), while for every \(d\ge85\) it is greater than \(209/200=1.045\). A second explicit amplification provides the exponential lower bound \(\rho_d>45^{-1}(1009/1000)^{d-84}\) for all \(d\ge85\), so the ratio of the two sharp extrema actually diverges exponentially. The finite bridge \(55\le d\le84\) follows from an independently checked exact Pareto certificate with 11,234 new states and 2,837,399 new dominance checks; all larger dimensions follow from two known sharp two-layer block inequalities, an elementary one-variable maximum, and eleven strictly rational residue checks applied to one explicit 85-dimensional nested body. This gives a sharp global, **dimension-uniform structural gap**, without claiming the unknown sharp values over \(\mathcal C_d\) for arbitrary \(d>55\) or the full recursive-class asymptotic spectral optimum.

## 1. Geometry, normalized extremal values, and statement

For a \(d\)-dimensional convex polytope \(K\), let \(\Pi K\) be its projection body and put
\[
 R(K)=\frac{|\Pi K|}{|K|^{d-1}},\qquad
 g(d)=\frac{d^d}{d!},\qquad c_d=(d+1)g(d).
 \tag{1.1}
\]
The value \(c_d\) is the projection-body ratio of every \(d\)-simplex. Throughout, the affine maps permitted in our construction grammars are isomorphisms on affine hulls, not rank-dropping maps.

Let \(\mathcal C_d\) contain *all* point-generated products and joins in dimension \(d\). Let \(\mathcal B_d\subset\mathcal C_d\) contain precisely the joins of any finite multiset of points and products \(B_{p,q}=T_p\times T_q\), with \(p,q\ge1\) and \(T_p\) a \(p\)-simplex. These are the same classes as in the preceding [first-nesting theorem](../projection-first-nesting-d55/paper.md). Define
\[
 M_\mathcal A(d)=\max_{K\in\mathcal A_d}\frac{R(K)}{c_d}
 \qquad (\mathcal A\in\{\mathcal B,\mathcal C\}),
 \qquad \rho_d=\frac{M_\mathcal C(d)}{M_\mathcal B(d)}.
 \tag{1.2}
\]
Every maximum exists because each finite-dimensional product/join grammar reduces to finitely many affine-invariant states, as proved in entry 005's earlier Pareto note. The classes have nonempty positive-dimensional members in every dimension.

Recall the explicit 55-dimensional optimal values, **inherited** from the exact two-certificate classification:
\[
\begin{aligned}
 M_\mathcal C(55)
 &=\frac{333068659627091928809841719168016922609375}
 {83816757831946947640666468303298107539456},\\
 M_\mathcal B(55)
 &=\frac{9444402294359878125}{2393367762580799488}.
\end{aligned}
 \tag{1.3}
\]
Their reduced ratio is
\[
 \boxed{\rho_*:=\rho_{55}
 =\frac{666588049410094050176708629890606697662639715}
 {661941565426077453299492872184552524829687808}
 >\frac{1007}{1000}.}
 \tag{1.4}
\]

**Theorem 1 (sharp persistent nesting gap).** For every integer \(d\ge55\),
\[
 \boxed{\rho_d\ge\rho_*,\qquad
 \rho_d=\rho_*\ \Longleftrightarrow\ d=55.}
 \tag{1.5}
\]
The coefficient \(\rho_*\) is therefore the **best possible universal multiplicative separation constant over all \(d\ge55\)**. Quantitatively,
\[
 \boxed{\rho_d>\frac{101}{100}\ (d\ge56),\qquad
 \rho_d>\frac{209}{200}\ (d\ge85),\qquad\rho_d>\frac1{45}\left(\frac{1009}{1000}\right)^{d-84}\ (d\ge85).}
 \tag{1.6}
\]
In particular every dimension \(d\ge55\) strictly benefits from allowing a product above a join, relative to the entire two-layer class. There is no dimension at which the two maxima reconverge. The main theorem does **not** give a closed expression for \(M_\mathcal C(d)\) at \(d>55\), does not characterize all maximizers, and is not about arbitrary convex bodies.

## 2. Input: the two sharp inequalities for all two-layer blocks

We recall the exact 005 v2 invariant calculus, re-proved or cited in both precursor notes. For \(K\in\mathcal C_d\), let
\[
 D=d+1,\qquad H=1/a(K),\qquad Q=\frac{a(K)R(K)}{g(d)},
 \qquad \frac{R(K)}{c_d}=\frac{H Q}{D}.
 \tag{2.1}
\]
The formal point has \((D,H,Q)=(1,1,1)\). Affine joins add \(D,H,\log Q\). If \(X,Y\) have positive dimensions \(r,s\), \((H,Q)(X)=(h,u)\), \((H,Q)(Y)=(j,v)\), and \(n=r+s\), then
\[
 H(X\times Y)=\frac{n}{r/h+s/j},\qquad
 Q(X\times Y)=uv\frac{g(r)g(s)}{g(n)}\frac{sh+rj}{n}.
 \tag{2.2}
\]
For a two-simplex product \(B_{p,q}=T_p\times T_q\),
\[
 H_{p,q}=\frac{p+q}{p/(p+1)+q/(q+1)},\qquad
 Q_{p,q}=\binom{p+q}{p}\frac{p^pq^q(p+q+2pq)}{(p+q)^{p+q+1}}.
 \tag{2.3}
\]
In particular
\[
 (D,H,Q)(B_{4,4})=(9,5,175/128),\qquad
 (D,H,Q)(B_{5,5})=(11,6,189/128).
 \tag{2.4}
\]

Set
\[
 A=\frac1{11}\log\frac{189}{128},\qquad
 B=\frac14\log\frac{175}{128},\qquad
 Q_5=\frac{189}{128},\quad Q_4=\frac{175}{128}.
 \tag{2.5}
\]
The previously published [sharp two-layer theorem](../two-layer-projection-depth-separation/paper.md), including its exact finite and infinite-tail proofs, establishes for **every** \(K\in\mathcal B_d\)
\[
 \boxed{\log Q(K)\le AD,\qquad
        \log Q(K)\le B(D-H).}
 \tag{2.6}
\]
These are universal inequalities for the entire two-layer class, not numerical extrapolations; that preceding proof classifies the unique optimizing blocks for each inequality and treats unbounded \(p,q\) analytically. We import (2.6) explicitly rather than claim to have re-proved it here.

### Lemma 2 (continuous two-layer envelope)

For every \(D\ge24\) and every \(K\in\mathcal B\) with state \((D,H,Q)\),
\[
 \boxed{\frac{HQ}{D}\le t_* Q_5^{D/11}
          <\frac{11}{20}Q_5^{D/11},\quad
        t_*=1-\frac AB.}
 \tag{2.7}
\]

**Proof.** Since \(0<H\le D\) for all these bodies, write \(t=H/D\in(0,1]\). From (2.6),
\[
 \frac{HQ}{D}\le t\min\{e^{AD},e^{BD(1-t)}\}.
 \tag{2.8}
\]
The constants satisfy
\[
 \frac{27}{50}<t_*<\frac{11}{20}.
 \tag{2.9}
\]
Indeed \(t_*=1-4\log Q_5/(11\log Q_4)\), so the two strict inequalities in (2.9) are *equivalent* to the rational-power comparisons
\[
 \boxed{Q_5^{80}>Q_4^{99},\qquad Q_5^{200}<Q_4^{253}},
 \tag{2.10}
\]
both checked exactly by the certificate. The positive logarithmic series for \(z=(Q_4-1)/(Q_4+1)=47/303\) gives
\[
 \log Q_4>2\left(z+\frac{z^3}{3}\right)>\frac{31}{100},
 \qquad B>\frac{31}{400}.
 \tag{2.11}
\]
Hence for every \(D\ge24\),
\[
 DBt_*>24\cdot\frac{31}{400}\cdot\frac{27}{50}>1.
 \tag{2.12}
\]
If \(0<t\le t_*\), the first term of the minimum in (2.8) gives \(t\min(\cdots)\le t_*e^{AD}\). If \(t\ge t_*\), the second term applies and the function \(t e^{BD(1-t)}\) is strictly decreasing because its logarithmic derivative \(1/t-BD\le1/t_*-BD<0\). Thus its value is at most its value at \(t_*\), equal to \(t_*e^{AD}\). This proves (2.7), including the final strict bound from (2.9). \(\square\)

The fact that (2.7) uses **one continuous optimizing value of \(t\)** makes it useful even where a sharp finite-dimensional two-layer computation is unavailable. All its numerical premises are strict integer-power or rational Taylor bounds.

## 3. The finite bridge \(55\le d\le84\)

Here we use exact computation only within a **fixed finite range**. The separate [first-nesting theorem](../projection-first-nesting-d55/paper.md) already independently certified the full two-layer Pareto frontiers through \(D=56\), with \(D=d+1\). We extend their exact Pareto recursion for point and block joins to \(57\le D\le85\). The [new certificate](certificates/extension57to85.json) refers to the exact previous base-file SHA-256

```text
101ffdf287f984965c941b1f98f93de89ae4a3bd0d4e796f02558a8039cb3d9f
```

Let \(E_D\) denote the Pareto set of possible two-layer states \((H,Q)\) at total join size \(D\), with a formal empty-join state \(E_0=\{(0,1)\}\). For every \(D\ge1\), the two-layer grammar yields
\[
 E_D=\operatorname{Max}\Bigg(
 \{(h+1,q):(h,q)\in E_{D-1}\}
 \cup\!!!
 \bigcup_{\substack{p,q\ge1\\p+q+1\le D}}
 \{(h+H_{p,q},vQ_{p,q}):(h,v)\in E_{D-p-q-1}\}
 \Bigg).
 \tag{3.1}
\]
Here \(\operatorname{Max}\) deletes coordinatewise dominated candidates. Its soundness and attainability are a simple induction: the join law is coordinatewise increasing, so replacing any dominated smaller join does not worsen the result, and every retained state comes from an explicit operation on attained parent states. In particular
\[
 \boxed{M_\mathcal B(d)=\max_{(h,q)\in E_{d+1}}\frac{hq}{d+1}.}
 \tag{3.2}
\]

The **separate** verifier [`code/check.py`](code/check.py) *first runs* the earlier independent base checker through \(D=56\), then checks the attainability and full point/block-operation closure of every new Pareto level \(57\le D\le85\). It verifies **11,234** new states and **2,837,399** new candidates using only exact fractions, and independently recomputes every sharp two-layer value (3.2) in dimensions 56–84.

### A two-parameter family of nested witnesses

Put \(V=B_{4,4}*B_{4,4}\), so \((D,H,Q)(V)=(18,10,Q_4^2)\) and \(\dim V=17\). For every integer \(p\ge1\) let
\[
 N_p=T_p\times V.
\]
The product identity (2.2) gives the **exact rational state**
\[
 \boxed{\begin{aligned}
 D(N_p)&=p+18,\\
 H(N_p)&=\frac{p+17}{p/(p+1)+17/10},\\
 Q(N_p)&=Q_4^2\frac{g(p)g(17)}{g(p+17)}\frac{27p+17}{p+17}.
 \end{aligned}}
 \tag{3.3}
\]
This is an allowed member of \(\mathcal C\), but is not by itself an allowed *block* in the smaller two-layer grammar.

For each integer \(D\in\{56,57,\ldots,85\}\), the finite certificate identifies **one** choice \(p_D\in\{6,7\}\) and **one attained** filler state \((h_D,q_D)\in E_{D-(p_D+18)}\). Taking the join of \(N_{p_D}\) with that filler gives a body in \(\mathcal C_{D-1}\), with exact normalized ratio
\[
 \boxed{W_D=\frac{(H(N_{p_D})+h_D)\,Q(N_{p_D})\,q_D}{D}}.
 \tag{3.4}
\]
The independently replayable certificate verifies all thirty strict/equality inequalities
\[
 \boxed{W_{56}=M_\mathcal C(55),\qquad
 \frac{W_{56}}{M_\mathcal B(55)}=\rho_*,\qquad
 \frac{W_D}{M_\mathcal B(D-1)}>
 \max\left\{\rho_*,\frac{101}{100}\right\}
 \quad(57\le D\le85).}
 \tag{3.5}
\]
For \(D=56\), the witness is precisely the published \(55\)-dimensional maximizer from (1.3). For \(D>56\), no full-tree optimality calculation is needed: \(M_\mathcal C(D-1)\ge W_D\), and the *independently exact* two-layer optimum is in the denominator. This proves Theorem 1 and its \(1.01\) corollary for all dimensions \(55\le d\le84\).

Crucially, this is a complete finite bridge, not a sampled trend or a claim derived by projecting the 55-dimensional example. The producer's selected witness indices are treated as untrusted until the checker re-evaluates every geometric state and compares it against a certified **sharp** two-layer maximum.

## 4. Uniform separation for all \(d\ge85\) using eleven rational inequalities

The infinite tail uses **one explicit nested body**, not a larger exact front-end DP. Let
\[
 X_0=T_5,\quad
 X_1=(X_0\times X_0)^{*2}=B_{5,5}*B_{5,5},\quad
 X_2=(X_1\times X_1)^{*2}.
 \tag{4.1}
\]
Using (2.2),
\[
 \boxed{(D,H,Q)(X_2)=(86,24,Q_2),\qquad
 Q_2=\left[12 Q_5^4\frac{g(21)^2}{g(42)}\right]^2.}
 \tag{4.2}
\]
This was already a known construction in the earlier two-layer depth-separation paper, but its new use here is to cover *every* sufficiently large dimension with a **uniform explicit separation factor**, rather than prove only an asymptotic comparison.

For arbitrary integer \(D\ge86\), write uniquely
\[
 D=86+11k+r,\qquad k\in\mathbb Z_{\ge0},\quad 0\le r\le10.
 \tag{4.3}
\]
Join \(X_2\), \(k\) copies of \(B_{5,5}\) and \(r\) points. The resulting body belongs to \(\mathcal C_{D-1}\) and has state
\[
 D=86+11k+r,\qquad H=24+6k+r,\qquad Q=Q_2 Q_5^k.
 \tag{4.4}
\]
Consequently,
\[
 M_\mathcal C(D-1)\ge\frac{24+6k+r}{86+11k+r}\,Q_2Q_5^k.
 \tag{4.5}
\]
Lemma 2 gives the strict upper bound
\[
 M_\mathcal B(D-1)<\frac{11}{20}Q_5^{D/11}.
 \tag{4.6}
\]
For fixed \(r\in\{0,\ldots,10\}\), the rational factor
\[
 \theta_r(k)=\frac{24+6k+r}{86+11k+r}
\]
is **strictly increasing** in real \(k\ge0\), since
\[
 \theta_r'(k)=\frac{6(86+r)-11(24+r)}{(86+11k+r)^2}
 =\frac{252-5r}{(86+11k+r)^2}>0.
 \tag{4.7}
\]
The \(Q_5^k\) factors in the comparison of (4.5) and (4.6) cancel. It therefore suffices to prove the following eleven inequalities at \(k=0\):
\[
 \frac{24+r}{86+r}Q_2>
 \frac{209}{200}\frac{11}{20}
 Q_5^{(86+r)/11},\qquad 0\le r\le10.
 \tag{4.8}
\]
All exponents on the left are rational, so raising to the **positive integer eleventh power** yields a completely rational equivalent form:
\[
 \boxed{\left(\frac{20(24+r)}{11(86+r)}\,
           \frac{Q_2}{209/200}\right)^{11}
          > Q_5^{86+r}}
 \quad (r=0,\ldots,10).
 \tag{4.9}
\]
The checker reconstructs \(Q_2\) from integer factorial ratios, proves all eleven strict rational inequalities (4.9), verifies \(252-5r>0\), and verifies \(209/200>\rho_*\). It additionally replays the rational inequalities (2.10)–(2.12), which establish the continuous bound used in (4.6).

By (4.5)–(4.9),
\[
 \boxed{M_\mathcal C(d)>\frac{209}{200}M_\mathcal B(d)}
 \qquad(d\ge85).
 \tag{4.10}
\]
Since \(209/200>\rho_*\), this closes the infinite tail of Theorem 1, completing the proof of sharpness and strict inequality in every dimension \(d\ge55\). \(\square\)

### Corollary 4 (explicit exponential divergence of sharp maxima)

The preceding dimension-uniform $209/200$ factor can be supplemented by a bound that **grows exponentially with dimension**:
\[
 \boxed{\frac{M_{\mathcal C}(d)}{M_{\mathcal B}(d)}
 >\frac1{45}\left(\frac{1009}{1000}\right)^{d-84}}
 \qquad(d\ge85).
 \tag{4.11}
\]
Consequently the ratio of the **maximal unnormalized** values $R(K)$ in the two classes, in matching dimensions, also diverges at least exponentially. This is a statement about the ratio of the two restricted-class maxima, not an exponential gap between two bodies of equal dimension chosen independently of $d$.

**Proof.** Put $s=1009/1000>1$. The same exact factorial value $Q_2$ from (4.2) satisfies the strict **integer-power** inequality
\[
 \boxed{Q_2^{11}>Q_5^{86}s^{946}},
 \tag{4.12}
\]
checked by the rational certificate. Thus $Q_2>Q_5^{86/11}s^{86}$. For any $D=d+1\ge86$, instead of the $11$-periodic join construction from (4.3), write
\[
 D=86k+r,\quad k\ge1,\quad 0\le r\le85,
\]
and join $k$ copies of $X_2$ from (4.1) with $r$ points. Its $(H,Q)$ coordinates are $(24k+r,Q_2^k)$. Since $\frac{24k+r}{86k+r}\ge12/43$, Lemma 2 implies
\[
 \rho_{D-1}>
 \frac{240}{473}\frac{Q_2^k}{Q_5^{D/11}}
 >\frac{240}{473}Q_5^{-r/11}s^{86k}.
\]
Now $r\le85<88$ and $Q_5>1$, so $Q_5^{-r/11}>Q_5^{-8}$. The further exact rational inequality
\[
 \boxed{\frac{240}{473}Q_5^{-8}>\frac1{45}}
 \tag{4.13}
\]
is checked in the same program. Because $86k=D-r\ge D-85=d-84$, we obtain (4.11), as asserted. $\square$

The bound in (4.11) is intentionally conservative at moderate dimensions; together with (4.10) it gives
\[
 \rho_d>\max\left\{\frac{209}{200},\ \frac1{45}(1009/1000)^{d-84}\right\}
 \quad(d\ge85).
\]

## 5. Certificate trust boundary and exact reproduction

The source and results are all committed inside this directory:

- [`code/build.py`](code/build.py) is an exact rational **certificate producer** extending the already pinned \(E_0,\ldots,E_{56}\) frontiers by 29 additional levels and saving the 30 chosen finite witnesses. No floating optimization or external solver is used even at this discovery stage.
- [`certificates/extension57to85.json`](certificates/extension57to85.json) records the 11,234 retained states, construction pointers and witnesses, along with its parent source hash.
- [`code/check.py`](code/check.py) is a **separately written verification program**. It replays the predecessor's independent base checker, checks every new state for rational exact attainability, every new point/block operation for dominance coverage, the strict Pareto ordering, all thirty exact finite ratios, the sharp \(d=55\) baseline, and the eleven infinite-tail rational inequalities and the two additional exact exponential-amplification comparisons. It does **not** import the producer.
- [`code/negative_controls.py`](code/negative_controls.py) deliberately corrupts an attained state, a frontier required for coverage, a global constant, and the parent hash. All four attacks must be rejected by explicit exceptions.

Reproduce from the repository root:

```sh
python3 notes/projection-persistent-nesting-gap/code/check.py
python3 -O notes/projection-persistent-nesting-gap/code/check.py
python3 notes/projection-persistent-nesting-gap/code/negative_controls.py
(cd notes/projection-persistent-nesting-gap && sha256sum -c SHA256SUMS)
```

Optional regeneration (standard-library Python, no network):

```sh
python3 notes/projection-persistent-nesting-gap/code/build.py
# This deterministically regenerates the same package-local JSON certificate.
```

The ordinary and optimized checker outputs must match byte for byte, and all published file hashes are pinned in [`SHA256SUMS`](SHA256SUMS). Importantly, **the exact computation only certifies the finite dimension range \(55\le d\le84\)**; the entire \(d\ge85\) conclusion is proved by the analytic one-variable envelope and the eleven rational-power checks, not by a finite scan. The two sharp block inequalities (2.6) and the 55-dimensional exact maxima (1.3) are openly attributed **imported theorems**; this note is not an independent formal re-proof of those inputs.

## 6. Context, limits, and next problem

The [all-tree finite note](../exact-product-join-finite-optima/README.md) first certified the sharp values through dimension 48; the [two-layer spectral note](../two-layer-projection-depth-separation/README.md) found a dimension-85 witness and an asymptotic gap; the [first-crossover note](../projection-first-nesting-d55/README.md) determined that 55 was the **first necessary nesting dimension**. Those historical proofs remain valid and unchanged. This note goes strictly further: the transition at 55 is **permanent** for all larger dimensions, and the exact smallest multiplicative gain is known, attained uniquely as a dimension at 55.

Nothing here proves the sharp value of \(M_\mathcal C(d)\) for all \(d>55\), the exact unrestricted recursive-class exponential growth constant, a classification of every maximizing tree, or a projection-body inequality valid for all convex bodies. The already published Bellman upper bounds and recursive lower families remain separate work. No priority, first-in-literature, journal acceptance or independent human-review status is asserted.
