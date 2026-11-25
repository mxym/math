# Exact generic hub-witness rank on shared-tensor periodic cycles

**Yongxian Zhang.** AI-assisted proof development and internal checks; no external peer review claimed.

Use the shared-tensor periodic model of [Gesmundo–Landsberg–Walter](https://arxiv.org/abs/1801.09106). On a cycle of length \(2s\), index both physical and virtual symbols by a hub \(0\) and \(r\) opposite pairs \(a,-a\), so \(q=2r+1\). Set
\[
 A_0=E_{00},\qquad A_a=E_{0,a}+c_aE_{-a,0}\quad(a\ne0),
\]
where the \(c_a\) are independent nonzero complex parameters. Write \(B_{2k}(r)\) for the number of cyclic token necklaces of length \(2k\) on signed symbols in which each index occurs equally often with positive and negative sign. Then for generic \(c_a\), the alternating rank of this particular witness is exactly
\[
 q^s-\sum_{k=1}^{\lfloor s/2\rfloor}\binom{s-1}{2k-1}B_{2k}(r).
\]
In particular its loss is \(O_s(q^{\lfloor s/2\rfloor})\). This is a lower bound for the maximal rank, not its general exact value. For \(s=6\) the witness defect is \(20r^3+9r\); the [perturbed hub](README.md) improves that twelve-cycle bound to \(30r^2-r\).

## Tokens and uniformizing the move weights

Sign-relabel the even word and use the odd word as input (the transpose of the row-input convention does not affect rank). A nonzero odd letter \(a\) at site \(x\in\{0,\ldots,s-1\}\) is a token. A trace term pairs it with its opposite original even letter at \(x\) or \(x-1\) modulo \(s\). After sign relabeling this is the same token either staying or moving left by one. Each such pairing is injective. Conversely any injective movement gives one trace term: its pairs are hub dimers, and all unmatched sites use the hub monomer. If all tokens move in the fully occupied case, this is a distinct trace term from all staying even if the output word coincides. For a non-full site set inconsistent pairings yield no terms. Cyclic token order is preserved under any injective movement, so the matrix splits by the entire necklace of nonzero letters.

Fix a necklace with \(n>0\) tokens, primitive label period \(\ell\mid n\), and ordered primitive labels \(a_j\) for \(j\in\mathbb Z/\ell\). A state consists of \(n\) occupied sites and an offset \(j\) giving the first label in increasing position order. A wrap from site 0 to site \(s-1\) advances the offset by 1. Factor out \(\prod_{\text{tokens }a}c_{-a}\), the product for staying. Each move has relative weight \(r_a=c_a/c_{-a}\). Choose a nonzero \(\beta\) with \(\beta^\ell=\prod_{j=0}^{\ell-1}r_{a_j}\). For state \(u\) of offset \(j\) put
\[
 g(u)=b_j\prod_{\substack{\text{token }a\\\text{at site }x}}(r_a/\beta)^x,\qquad
 b_{j+1}/b_j=(r_{a_j}/\beta)^{-s}.
\]
The \(b_j\) are consistent around the primitive period. Conjugation by the diagonal with entries \(g(u)\) multiplies each transfer coefficient from \(u\) to \(v\) by \(g(v)/g(u)\). A nonwrapped move contributes \((r_a/\beta)^{-1}\) to this factor, producing the uniform weight \(\beta\). A wrapped move has an additional \((r_a/\beta)^s\), canceled by the offset change. Thus all moves have weight \(\beta\) after conjugation.

## Twisted exterior power and exact defect

Fourier transform the offset so incrementing it acts by a primitive-period character value \(\omega\), ranging over the \(\ell\)-th roots of unity. Let \(S_\eta e_x=e_{x-1}\) for \(x>0\) and \(S_\eta e_0=\eta e_{s-1}\). The resulting block is
\[
 \bigwedge\nolimits^n(I+\beta S_\eta),\qquad \eta=(-1)^{n-1}\omega.
\]
Indeed, the exterior expansion chooses stay or move for each occupied site and removes collisions, and any wrapped token crosses the other \(n-1\) wedge factors upon sorting. The sign in \(\eta\) cancels that sign while supplying the phase \(\omega\). This works also for \(n=s\), where both trace alignments occur. The all-core \(n=0\) state contributes rank one.

The eigenvalues of \(S_\eta\) are the \(s\) distinct roots of \(\eta\). Thus \(I+\beta S_\eta\) has rank \(s\) except when \(\eta=(-1)^s\beta^{-s}\), in which case it has rank \(s-1\). Its exterior-power ranks are respectively \(\binom{s}{n}\) and \(\binom{s-1}{n}\). For an unbalanced necklace \((\beta^s)^\ell\) is a nonconstant Laurent monomial in the independent \(c_a\), so all blocks are generically full. In a balanced necklace, the primitive period is itself balanced and has even length, so take \(\beta=1\). There is exactly one eligible singular character \(\omega=(-1)^{s+n-1}\), in the character list even for odd \(s\). This gives defect \(\binom{s-1}{n-1}\) per balanced necklace and no defect elsewhere. The finitely many required nonvanishing conditions for any fixed \(q,s\) can hold simultaneously. For \(n=s\) the same formula gives one missing dimension per balanced necklace.

For explicit counting, Burnside's lemma gives
\[
 B_{2k}(r)=\frac1{2k}\sum_{d\mid k}\varphi(d)\,(2k/d)!
       \sum_{\alpha_1+\cdots+\alpha_r=k/d}
              \prod_{j=1}^r\frac{1}{(\alpha_j!)^2}.
\]
Indeed a rotation whose repetition factor is \(d\) fixes precisely words formed by repeating a length-\(2k/d\) word, which must itself be balanced, hence \(d\mid k\). The inner multinomial sum counts the fixed words by matched sign multiplicities. A balanced word uses at most \(k\) classes, so for fixed \(k\), \(B_{2k}(r)=O_k(r^k)\). For \(s=6\), the \(n=2,4\) mixed defects are \(5r\) and \(20r+60\binom r2\), and the \(n=6\) defects are \(4r+30r(r-1)+120\binom r3\), giving \(20r^3+9r\).

As a cross-check, direct modular trace ranks by signed multiset at \((q,s)=(3,2{:}6),(5,2{:}5),(7,2{:}4)\) agree with this defect contribution for every block. The proof works for every half-length and does not depend on those finite checks.
