# The exact strictness threshold in the Carlet–Thornburgh hierarchy

For scalar Boolean functions on \(\mathbb F_2^n\), write:
1. \(Q_n\): algebraic degree at most two;
2. \(PB_n\): partially-bent functions, equivalently affine extensions of a bent function in an even number of effective variables, up to adding an affine term;
3. \(RPB_n\): restrictions to an affine hyperplane of partially-bent functions in \(n+1\) variables, identified affinely with \(\mathbb F_2^n\);
4. \(P_n\): plateaued functions, whose nonzero Walsh coefficients have a common absolute value;
5. \(RP_n\): analogous hyperplane restrictions of plateaued functions in \(n+1\) variables;
6. \(All_n\): all Boolean functions.

We prove the following exact nesting. Subscripts \(n\) are omitted in the table.

| Dimension | Nesting |
|---|---|
| \(n\le2\) | \(Q=PB=RPB=P=RP=All\) |
| \(n=3\) | \(Q=PB=RPB=P=RP\subsetneq All\) |
| \(n=4\) | \(Q=PB=RPB=P\subsetneq RP\subsetneq All\) |
| \(n=5\) | \(Q=PB\subsetneq RPB=P\subsetneq RP\subsetneq All\) |
| \(n\ge6\) | \(Q\subsetneq PB\subsetneq RPB\subsetneq P\subsetneq RP\subsetneq All\) |

This corrects the claim of six distinct classes for all \(n\ge5\) in the abstract and final section of Carlet–Thornburgh, [ePrint 2026/386, 14 Nov. copy](https://opencryptology.org/2026/386/versions/20261114T034025Z.pdf). It does not dispute their main theorem about functions **all of whose** hyperplane restrictions are plateaued. We also determine the exact four- and five-variable restriction classes \(RP_4,RP_5\), and \(RPB_6\). These are special cases of the further questions in their §4 and conclusion, not a general classification of all admissible supports.

## 1. Fourier facts and the ordinary inclusions

On \(n\) variables, set \(W_f(u)=\sum_x(-1)^{f(x)+u\cdot x}\). Affine changes of coordinates and addition of an affine form preserve plateauedness, partial bentness and the restriction properties: lift the change to the chosen hyperplane by keeping the extra coordinate, and extend the added form independently of it. A restriction to any affine hyperplane can thus be taken on the slice with last coordinate zero.

If a function has a plateaued spectrum of amplitude \(\lambda>0\), Parseval gives \(\lambda^2\,|\mathrm{supp}(W)|=2^{2n}\). Hence \(\lambda\) is a power of two and at least \(2^{n/2}\). Bent means every Walsh coefficient is nonzero and its modulus is \(2^{n/2}\). Two \(n\)-variable functions \(f,h\) concatenated as the two slices of \(G\) have
\[
 W_G(u,b)=W_f(u)+(-1)^bW_h(u).
\]
Thus if \(G\) is plateaued of amplitude \(\lambda\), every Walsh modulus of its restriction \(f\) belongs to \(\{0,\lambda/2,\lambda\}\). For bent \(G\) both members on the right before averaging are nonzero with equal modulus; hence \(f\) has only one possible nonzero modulus and is near-bent of dimension \(n\), with support size \(2^{n-1}\).

Quadratic Boolean functions are partially bent: their alternating polar form has a radical on which the function is affine, and splitting off the radical leaves a nondegenerate alternating polar form. The associated nondegenerate quadratic function is bent, as follows either from the Walsh sum or its balanced derivatives. The degenerate zero-dimensional bent core means an affine function. Adding a free coordinate preserves partial bentness and plateauedness, so \(PB_n\subseteq RPB_n\) and \(P_n\subseteq RP_n\). Of course \(RP_n\subseteq All_n\). The next argument gives \(RPB_n\subseteq P_n\), completing the inclusions.

## 2. The odd core condition for a non-partially-bent restriction

The linear structures of \(f\) are the directions \(a\) such that \(D_a f(x)=f(x+a)+f(x)\) is constant. By Fourier transforming translation, this holds exactly when \(u\cdot a\) is constant on \(\mathrm{supp}(W_f)\). Thus the common annihilator of all support differences is the space of linear structures. Its codimension is the affine-span dimension \(d\) of the support; after subtracting an affine form carrying their constant derivatives and choosing a complement, the function is the affine/free extension of a \(d\)-variable reduced function. Its reduced Walsh support has full affine span, and the old support is an affine copy of it, with coefficients scaled by the free-coordinate factor.

Write a partially-bent extension \(G\) as a bent function on an even-dimensional quotient of dimension \(r\), pulled back by a linear quotient map with kernel \(K\), plus an affine term. Let \(H\) be the affine hyperplane of restriction. If its direction does not contain \(K\), the projection of \(H\) is the whole quotient; the restriction is partially bent. If the direction contains \(K\), the image is a hyperplane in the bent quotient; the restriction is an affine/free extension of a near-bent function in \(r-1\) variables by the Fourier slice identity. In particular it is plateaued. (For \(r=0\) there is only the first case.)

The near-bent quotient restriction has support size \(2^{r-2}\). If it has an extra linear structure, its support lies in an affine hyperplane of precisely that same size, hence equals that hyperplane. A plateaued function with affine Walsh support is partially bent: reduce by the linear structures as above, leaving a full-support constant-modulus transform, which by Parseval is bent. This would make the original restriction partially bent as well. It follows that **if \(f\in RPB_n\setminus PB_n\), its Walsh affine-span dimension \(d\) is odd**, and its reduced function is a non-partially-bent near-bent restriction of a bent function in \(d+1\) variables. Conversely, if such a reduced restriction extends to a bent function, its affine/free extension extends to a partially-bent function by adding the same free coordinates.

## 3. Exact small dimensions

We use the following elementary Walsh divisibility fact. If all coefficients of \(W_f\) are divisible by \(2^k\), \(2\le k\le n\), then \(\deg f\le n-k+1\): on every affine flat of dimension \(n-k+2\), Poisson summation writes the signed truth sum as a signed sum of coefficients divided by \(2^{k-2}\), hence a multiple of four. The restriction weight is therefore even. The parity of values on such flats is the corresponding order of derivative, so all these derivatives vanish. In particular, all plateaued functions on at most four variables are quadratic: for dimension four the possible amplitudes are \(4,8,16\), where amplitude 4 is bent of degree at most two, and divisibility handles the others; at dimension three amplitude is 4 or 8 and divisibility suffices. A partially-bent function on at most five variables is quadratic because its largest possible even bent core has dimension at most four (the degree bound for bent functions in dimension four is two).

For \(n=3\), the cubic \(x_1x_2x_3\), up to quadratic perturbations, need not directly have the same Walsh support as every cubic. But every three-variable function of degree three has an odd truth weight: it has nonzero full multilinear coefficient. Consequently every coefficient has modulus congruent to \(2\) modulo 4; by Parseval the Walsh coefficients cannot all have modulus 2. Since every possible nonzero Walsh modulus of a plateaued extension restriction is a power of two, such a cubic cannot extend. Thus \(RP_3=Q_3\). For \(n\le2\) all functions are quadratic and the six classes coincide.

For \(n=4,5\), any **nonplateaued** restriction of a plateaued extension must have both nonzero moduli \(\lambda/2,\lambda\). It is not a restriction of a bent extension. If \(\lambda\ge 2^n\), the presence of a coefficient of modulus \(\lambda\) is either impossible or forces all other coefficients zero by Parseval. Thus in both dimensions the only possible mixed moduli are \(\{4,8\}\) for \(n=4\) and \(\{8,16\}\) for \(n=5\) (for \(n=5\) the excluded minimum amplitude 8 is bent in dimension six). By the divisibility bound all candidate mixed restrictions have degree at most three. Also every five-variable plateaued function has degree at most three, and its possible amplitudes are 8, 16, 32.

For completeness we check the resulting finite sets directly, without a catalogue or assumption about unchecked EA classes. On the leading part of a degree-three Boolean function, an invertible linear change acts as on an exterior three-form, since its top squarefree coefficients are minors; repeats of a variable lower the degree. In four variables exterior three-forms identify, via the volume element and inverse transpose, with vectors, so their orbits have sizes 1 and 15, represented by 0 and \(123\). Here \(123\) stands for \(x_1x_2x_3\). In five variables, by duality they identify with alternating two-forms, whose only ranks are 0, 2 and 4. In a symplectic basis the representatives are \(0,123,123+145\), with orbit sizes \(1,155,868\): a rank-two nonzero form is determined by its two-dimensional support in the dual description over \(\mathbb F_2\), of which there are \((31\cdot30)/(3\cdot2)=155\); subtracting these and zero from \(2^{10}\) leaves 868. Affine terms can be omitted, since both extension and Walsh absolute supports are EA-invariant.

For each of the two top forms in four variables the verifier tests every one of the 64 possible homogeneous quadratic additions. For each of the three top forms in five variables it tests all 1,024 additions. A positive mixed restriction has an explicit certificate that uses just \(h(x)=f(x)+c\cdot x\) for some \(c\): test \(\{|W_f(u)+W_f(u+c)|,|W_f(u)-W_f(u+c)|\}\subseteq\{0,\lambda\}\) at all frequencies. Every mixed candidate passes. For each five-variable amplitude-8 plateaued candidate, some translate of its Walsh support is its complement, giving a bent extension by the same \(h\) construction; all candidates pass. For other amplitudes in dimension five the functions are partially bent already: amplitude 32 is affine, and amplitude 16 with degree at most two by divisibility is quadratic. This establishes:
* \(RP_4\) consists of the plateaued functions and exactly those with nonzero moduli \(\{4,8\}\); the counts are 2,048 plateaued and 26,880 nonplateaued extendable.
* \(RP_5\) consists of the plateaued functions and exactly those with nonzero moduli \(\{8,16\}\); the counts are 14,064,640 plateaued and 19,443,200 nonplateaued extendable.
* \(RPB_5=P_5\). For \(n=6\), \(RPB_6\) consists exactly of the six-variable bent functions and the six-variable plateaued functions with a nonzero linear structure. Indeed a non-partially-bent member must have odd reduced dimension \(d\le5\) by §2. Conversely, any six-variable plateaued function with a linear structure reduces to dimension at most five. For dimension at most four the reduced function is quadratic, and at dimension five §3 supplies a partially-bent extension. A partially-bent function without linear structures is itself bent. These observations give both directions.

Class counts multiply the numbers of positive normalized quadratic additions in each top orbit by that orbit size and by \(2^{n+1}\) for the unrestricted affine term; the verifier prints the individual contributions. These counts are not used in place of existence proofs.

## 4. Uniform strictness from dimension six

Each of the five proper inclusions has a witness at a minimal dimension and persists on adding free coordinates, for the following explicit reasons.

* **\(Q\subsetneq PB\):** the six-variable function \(b(x,y)=x\cdot y+y_1y_2y_3\) on two triples is bent (sum over \(x\) forces \(y\) at each frequency) and cubic. It stays cubic and partially bent with free coordinates.
* **\(PB\subsetneq RPB\):** \(f=123+14+25\) on five coordinates has modulus set \(\{0,8\}\), and \(h=f+x_3\) has the complementary Walsh support. Their concatenation is six-variable bent. This cubic is not partially bent in five variables. Its Walsh support remains non-affine when padded, so the extensions stay outside \(PB\).
* **\(RPB\subsetneq P\):** on two triples \(x,y\), take \(F(x,y)=x\cdot\phi(y)\) with the fibers of \(\phi\) given by
  \[
  \{0,1\}\mapsto0,\quad \{2,4\}\mapsto1,\quad
  \{3,6\}\mapsto2,\quad \{5,7\}\mapsto4 ,
  \]
  where numbers encode three binary coordinates. For a frequency \((a,b)\), the Walsh sum is \(8\sum_{y:\phi(y)=a}(-1)^{b\cdot y}\). It has modulus 16 exactly if \(a\) is an image point and \(b\) annihilates the difference of its two preimages. No affine equation of the form \(u\cdot a+v\cdot b=\kappa\) can hold throughout the support except the trivial one. Indeed, on each individual fiber slice, \(v\) would need to be a multiple of its difference; two distinct nonzero differences force \(v=0\). Then the four affinely independent \(a\)'s force \(u=0,\kappa=0\). Thus the support has affine-span dimension six but has only 16 points, so this is non-partially-bent and not in \(RPB\) by §2. Padding leaves the affine-span dimension six and the non-affine nature of the support intact.
* **\(P\subsetneq RP\):** \(123+14\) on four variables has mixed moduli \(\{0,4,8\}\), and pairing it with itself plus \(x_2\) gives a plateaued extension of amplitude 8. Independent free coordinates scale each nonzero Walsh coefficient by the same factor, preserving mixedness, and can be appended to the extension.
* **\(RP\subsetneq All\):** \(123\) in three variables has Walsh moduli 2 and 6, with ratio three, so it cannot extend to plateaued. Padding preserves this forbidden ratio.

Together with §3 these witnesses prove the exact table. They distinguish the endpoint correction from the general higher-dimensional questions, which remain outside our claims. The verifier independently computes the Walsh spectra of the displayed explicit witnesses, checks the entire finite part in §3, and rejects a false side-selection control.
