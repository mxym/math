# A finite-range theorem for the Segre oval in a flock herd

**Theorem (certified finite range).** Let $q=2^n$ where $n$ is any odd integer from 3 to 127 inclusive. If a flock generalized quadrangle of order $(q^2,q)$ contains a subquadrangle isomorphic to $T_2(\mathcal O)$ for the Segre oval
$$\mathcal O=\{(1,t,t^{1/6}):t\in\mathbb F_q\}\cup\{(0,1,0)\},$$
then it is isomorphic to the Payne flock generalized quadrangle. Equivalently in the herd formulation, the presence of this oval up to projective semilinear equivalence forces the Payne herd up to the associated GQ isomorphism. The theorem is for 63 specific field degrees; **it does not prove the conjecture for unbounded odd $n$.** It does not classify flocks in general or assert that all flocks giving the Payne GQ are projectively equivalent.

This is the stated finite portion of [Penttila–Storme, *Monomial Flocks and Herds Containing a Monomial Oval* (1998), Conjecture 5.6, p. 40](https://doi.org/10.1006/jcta.1997.2855). Here $T_2$ is the usual Tits generalized-quadrangle construction on an oval. We prove the stronger fixed-coordinate result below without assuming a monomial second coefficient or any symmetry of the purported flock. The finite ranks are computer-assisted and reproducible, not empirical samples over a few field elements.

## 1. Reduction from an arbitrary subquadrangle to a fixed clan coordinate

For readers starting from a normalized clan whose first coefficient is already $t^{1/6}$, this section is unnecessary. It matters if the starting point is an arbitrary occurrence of the abstract subquadrangle, rather than an already designated herd member.

* A subquadrangle of order $q$ in an even-order flock GQ which misses its base point forces the ambient GQ to be classical and the subquadrangle to be $W(q)$. This is the even case of Brown–Thas, [*Subquadrangles of order s …*, Part I (2004)](https://doi.org/10.1016/j.jcta.2003.12.006); a direct statement in flock rather than dual notation is [Thas–Thas (2009), Theorem 7.5 and Remark 7.6](https://doi.org/10.2140/iig.2009.10.133). Since $q$ is even, $W(q)\cong Q(4,q)$, and $T_2(\mathcal O)\cong Q(4,q)$ iff $\mathcal O$ is a conic ([O’Keefe–Penttila 2001, Theorem 2](https://doi.org/10.1006/jcta.2000.3119)). Our oval is not a conic: substituting $(1,x^6,x)$ into a general homogeneous quadratic gives the six powers with exponents $0,12,2,6,1,7$. They are all distinct in the unique degree-$<q$ representation for every $q\ge8$ in our range (for $q=8$, $x^{12}=x^5$). Thus no nonzero quadratic even vanishes on its entire affine part. The off-base-point alternative is impossible.
* The same [O’Keefe–Penttila paper, Theorem 8, p. 226](https://doi.org/10.1006/jcta.2000.3119) takes an order-$q$ subquadrangle through the base point by an ambient automorphism to one of the standard herd subquadrangles. Isomorphic nonconic $T_2$'s here yield projectively semilinearly equivalent defining ovals (their Corollary 12(i), p. 228, which treats isomorphisms between nonclassical Tits GQs). Thus the herd contains an oval equivalent to the specified $\mathcal O$.
* [Penttila–Storme, Theorem 2.1 and Remark 2.2, pp. 28–29](https://doi.org/10.1006/jcta.1997.2855) explain precisely how a specified monomial representative of a herd oval can be put in the first clan coefficient after replacing the clan by one with isomorphic GQ. Compare [O’Keefe–Penttila (2000), Lemma 10, pp. 182–184](https://doi.org/10.1023/A:1005153406421). This preserves the GQ, not necessarily the original coordinatized flock.

Consequently the clan can be taken to have coefficient triple $(t^{1/6},t^{1/2},a(t))$, with $a(0)=0$. Here $a$ already includes the normalization multiplier used in the original papers. The known normalized clan trace criterion ([Penttila–Storme, equation (2)](https://doi.org/10.1006/jcta.1997.2855)) is exactly
$$T\!\left(\frac{(t^{1/6}+u^{1/6})(a(t)+a(u))}{t+u}\right)=1\qquad(t\ne u),\tag{1}$$
where $T$ denotes the absolute trace to $\mathbb F_2$. Indeed, anisotropy of the difference of two clan matrices amounts to the trace-one condition on the product of the diagonal differences divided by the square of the off-diagonal difference; the middle coefficient is $\sqrt t$. No assumption concerning $a(t)$ being a power is made. We did not swap the two axes of the directed oval.

## 2. Linearization and the forced solutions

Put $F=\mathbb F_q$. Since $n$ is odd, $3\nmid(2^n-1)$, and 6 is coprime to $q-1$. Thus $x\mapsto x^6$ permutes the whole field. Substituting $t=x^6$, $u=y^6$ and $G(x)=a(x^6)$ gives
$$T\!\left(\frac{(x+y)(G(x)+G(y))}{x^6+y^6}\right)=1\quad(x\ne y),\qquad G(0)=0.\tag{2}$$
In these coordinates the candidate solution space is
$$G(x)=x^5+C^2x+Cx^3,\qquad C\in F.\tag{3}$$

**Fixed-coordinate theorem.** For each of the 63 degrees specified above, (3) is the entire set of functions satisfying (2).

To prove the inclusion that holds in every odd degree, write $s=x+y$, $p=xy$, $D=x^2+xy+y^2=s^2+p$. For distinct $x,y$, $sD\ne0$, since $x^6+y^6=s^2D^2\ne0$. Two field identities are
$$
\frac{(x+y)(x^5+y^5)}{x^6+y^6}=1+(p/D)^2+p/D,
\qquad
\frac{(x+y)(H_C(x)+H_C(y))}{x^6+y^6}=(C/D)^2+C/D,
$$
where $H_C(x)=C^2x+Cx^3$. The first follows by expanding $x^5+y^5=s(s^4+s^2p+p^2)$; the second uses $x^3+y^3=sD$. Taking traces gives respectively $1$ and $0$ since $T(1)=1$ and $T(w^2+w)=0$. Therefore $x^5$ is a particular solution, and solving (2) reduces to the kernel of its homogeneous binary-linear equations with $H(0)=0$. These equations contain every $H_C$.

The parameter $C$ is recoverable from the values on **any two distinct nonzero points**. Indeed $H_E(x)=0$ at $x\ne0$ iff $E=0$ or $E=x^2$. Equality of the functions for parameters $C,C'$ on two such points gives $E=C+C'=0$. Hence the forced kernel on any such set has binary dimension exactly $n$. The converse inclusion is what must be certified.

## 3. Local rigidity propagates to the entire field

Let $g$ generate $F^*$ and $S=\{0,1,g,\ldots,g^{L-1}\}$ with $3\le L\le q-1$. Impose the homogeneous equations from (2) on all unordered pairs inside $S$, taking $H(0)=0$. This finite system has $nL$ binary variables and $L(L+1)/2$ binary equations.

**Local-to-global lemma.** If this matrix has binary rank $n(L-1)$, its solutions on $S$ are exactly the restrictions of $H_C$, by the dimension and injection just proved. Let $H$ solve the system on the entire field and let $b\in F^*$. The function $H^{(b)}(x)=b^{-5}H(bx)$ on $S$ obeys the same homogeneous equations: the coefficient $(x+y)/(x^6+y^6)$ acquires the factor $b^{-5}$ under simultaneous scaling of its two arguments. Thus $H^{(b)}=H_C$ on $S$ for some $C$. Undoing the scaling, $H$ equals $H_{b^2 C}$ on $bS$. In particular this holds on every multiplicative translate $g^jS$. The windows $g^jS$ and $g^{j+1}S$ share at least two distinct nonzero elements, so their parameters agree. The windows cover $F^*$ because $g$ is primitive. Hence $H=H_C$ on all of $F$. This argument is valid even when $L$ is tiny relative to $q-1$; it does not assume $H$ is homogeneous or invariant under scaling.

The matrices in the supplied certificates attain rank $n(L-1)$ for every odd $3\le n\le127$. For the listed field choices $L=2n-1$ except that $n=5$ uses $L=10$. No optimality of $L$ and no rank assertion in untested fields are needed. For example, $n=127$ uses 253 nonzero points and zero, 32,131 variables, and rank 32,004; this determines $H$ at all $2^{127}$ field elements. The ranks, not an extrapolation of their pattern, supply the finite conclusion.

## 4. Back to the Payne GQ

In the original variable, (3) is
$$a(t)=t^{5/6}+C^2t^{1/6}+Ct^{1/2}.$$
It gives the same flock up to a cone-preserving projectivity as the standard Payne triple. In the cone parametrization $(X_1,X_2,X_3)=(v^2,vw,w^2)$, the canonical plane form at $t=x^6$ uses the binary quadratic expression $xv^2+x^3vw+x^5w^2$. The substitution $(v,w)\mapsto(v+Cw,w)$ changes only the last coefficient, to $x^5+C^2x+Cx^3$. It is induced by the invertible linear map $(X_1,X_2,X_3)\mapsto (X_1+C^2X_3,X_2+CX_3,X_3)$, fixes $X_0$, and preserves $X_1X_3=X_2^2$. Thus these fixed-coordinate triples are projectively equivalent to the Payne $P_1$ flock, whose GQ is the Payne GQ ([Penttila–Storme, §§1.1, 1.3](https://doi.org/10.1006/jcta.1997.2855)). It is the **GQ isomorphism** that persists through every initial recoordinatization. For $q=8$ the Payne and FTWKB geometries coincide, as noted in [Cherowitzo–O’Keefe–Penttila (2003), §2](https://doi.org/10.1515/advg.2003.002).

## 5. Independent computations and how to reproduce

Python 3.10+, standard library only. Run both, or use a specific certified $n$ as a positional argument. The first checker verifies the number-theoretic data, not just the rank:

    python3 verify_seed.py
    python3 verify_raw.py
    python3 verify_seed.py 127
    python3 verify_raw.py 127

* **Certificate data.** Each entry of `fields.json` supplies $n$, a monic binary polynomial as its coefficient bitmask (bit 0 is the constant term), the complete factorization of $2^n-1$ including multiplicity, and $L$. Its companion recursively certifies that every listed factor $p$ is prime by a residue of exact order $p-1$ modulo $p$ and a certified factorization of $p-1$, down to $2$. Such an order means that $p-1$ distinct invertible residues exist, proving primality. Field irreducibility and the exact order $2^n-1$ of the residue class of the polynomial variable are checked; no unverified external primitive-polynomial table is assumed.
* **First implementation.** Use $Z(x)=H(x)/x^5$ for nonzero $x$. A pair $x=g^{j+d},y=g^j$ has equation $T(vg^{5d}Z(x)+vZ(y))=0$ with $v=(1+g^d)/(1+g^{6d})$; pairing $x$ with zero gives $T(Z(x))=0$. The program builds the binary rows via the true absolute trace in the polynomial basis and performs exact elimination. It explicitly tests the $n$ basis gauges on every difference class, the rank-$n$ injection on two shared points, and the affine right side one for $G_0=x^5$. Simultaneous scaling of both labels permutes the gauge parameters, so testing the difference classes checks every seed pair.
* **Second implementation.** Use the reciprocal polynomial, shift-and-add field products, extended Euclidean inversion, and the actual unscaled $H$ values. For each original unordered pair, it recomputes directly the coefficient $(x+y)/(x^6+y^6)$ and eliminates binary rows in a different order. It uses the top-coefficient functional $\ell$ rather than $T$: the trace pairing is nondegenerate, so $\ell(z)=T(cz)$ for one fixed $c\ne0$. Replacing $T$ by $\ell$ therefore performs the same invertible variable scaling at every point; **only the rank**, not the identity of the kernel vectors in these coordinates, is compared. Under the field isomorphism the reciprocal variable corresponds to $g^{-1}$; its consecutive seed is a scalar translate of the original one read backwards. The implementations share certificate inputs but no field arithmetic or matrix generation code.

## 6. Prior results and limitations

* Payne's canonical solution and the relation between clans, flocks, ovals and GQs were known long before this computation. Penttila–Storme (1998), Theorems 5.1–5.2, classify the *oval* or the case where *both* coefficient functions are monomials. Their Conjecture 5.6 is exactly the missing arbitrary-second-function converse for the Segre case. Averaging an arbitrary solution down to the known monomial one would not establish its uniqueness; this is why we bound the entire kernel.
* [O’Keefe–Penttila (2000), pp. 185–186](https://doi.org/10.1023/A:1005153406421) give the translation-oval classification and explicitly distinguish the undetermined Segre case. Their [2002 automorphism-group characterization](https://doi.org/10.1006/eujc.2001.0550) assumes symmetry of the herd, not merely a single Segre member. This proof imposes no such symmetry.
* The classification of all quadratic-cone flocks through field order 71 was completed by [Monzillo–Penttila–Siciliano (2022)](https://arxiv.org/abs/2205.05344); it includes $q=8,32$, not $q\ge128$. See also the [$q=32$ computation of Brown et al.](https://msp.org/iig/2008/6-1/iig-v6-n1-p07-p.pdf). These small geometries are baseline cases, not newly discovered objects. The range beyond that complete small-order classification is odd $n=7,9,\ldots,127$. We did not find an earlier arbitrary-second-coefficient result covering the claimed larger range; a negative literature search is not a guarantee of priority.
* A forward-citation check on the 1998 DOI using Semantic Scholar and OpenCitations returned, among other results, [Bader–Ghinelli–Penttila on monomial flocks](https://doi.org/10.1006/eujc.2001.0503), [Bader–de Resmini on Kantor flocks in odd characteristic](https://doi.org/10.1016/S0012-365X(01)00381-8), [Penttila’s survey of oval configurations](https://doi.org/10.1007/s00022-003-1700-4), and [Cherowitzo–O’Keefe–Penttila on cyclic constructions](https://doi.org/10.1515/advg.2003.002). These are not arbitrary-completion classifications for one Segre herd member. Targeted searches also used “Segre–Bartocci/Payne herd”, “Payne flock subquadrangle” and the conjecture number; the exact derivation above does not depend on the exhaustiveness of those searches.
* This theorem is not a uniform proof at all odd $n$. A uniform proof of the seed rank, or another exhaustive argument for the remaining degrees, is missing. A few tested pair equations do **not** alone imply global uniqueness: the certified local rank, primitivity, homogeneous scaling law, and two-point parameter injection are all essential.
