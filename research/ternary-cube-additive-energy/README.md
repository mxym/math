# The sharp additive-energy exponent for the ternary cube

For a nonempty subset $A$ of $\{0,1,2\}^d$, let $E(A)$ count ordered quadruples $(a,b,c,e)\in A^4$ with $a+b=c+e$. Addition is coordinatewise in the **integers**, not modulo 3. How small can the exponent $t$ in $E(A)\le |A|^t$ be if the same bound must hold in every dimension?

**Result.** The least exponent satisfies
$$
2.7207109973971711<t<2.7207109973971716.
$$
Its exact value is $t=4/q$, where the following system has a unique solution with $1.4702039297178894<q<1.4702039297178896$ and $1/4<z<1$:
$$
3z^{1-q/2}(1+z)=1+6z,\qquad
(4-q)\log(1+12z+6z^2)=4\log(1+6z).
$$

**What approaches equality?** No finite nonsingleton set attains equality. But the Hamming balls about the all-ones word, of radius $\lfloor\alpha d\rfloor$ with $\alpha=2z^{q/2}/(1+2z^{q/2})$, satisfy $\log E(A_d)/\log|A_d|\longrightarrow t$. Thus a sharp dimension-independent exponent can arise without a single nontrivial finite equality example.

**Proof idea.** [De Dios Pont, Greenfeld, Ivanisvili and Madrid](https://arxiv.org/pdf/2112.09352) reduced this problem to a three-coefficient Fourier inequality. They also computed the quartic, tested a symmetric profile, and proved that the full cube fails to maximize the exponent. The key remaining step here is to show that, at the critical norm, replacing the two endpoint coefficient masses by their average strictly increases the quartic unless they are equal. That leaves a single scalar variable. Two rational certificates isolate the critical crossing; an explicit count of coordinate types gives the asymptotically optimal ball construction.

* [Full proof and finite-set equality](PROOF.md)
* [Sources and scope of the prior-work search](SOURCES.md), including [Shao](https://doi.org/10.1017/prm.2024.126) and [Shao–Sun](https://arxiv.org/abs/2610.07490) on other ranges
* [Independent internal mathematical review](REVIEW.md) and [check outputs](CHECKS.txt)

Reproduce the two exact checks with `python3 -B -O verify.py` and `python3 -B -O independent.py` (Python 3, standard library). The checkers derive their logarithm enclosures from different convergent rational series.

AI-assisted research, independently checked by a second AI; not externally peer-reviewed or formally verified. No claim of bibliographic priority. The result is for one fixed alphabet and ordinary quadruple energy, not all alphabets or higher energies.
