# Tokareva's bent-derivative question in dimension eight

**Theorem (computer-assisted, relative to the published seven-variable cubic classification).** Let $H:\mathbb F_2^8\to\mathbb F_2$ be balanced, with algebraic degree at most three. For **each** nonzero $e$ such that $H(x+e)=H(x)$ for all $x$, there is a bent Boolean function $G:\mathbb F_2^8\to\mathbb F_2$ satisfying $G(x)+G(x+e)=H(x)$ for every $x$. The witness may depend on $e$.

The finite calculation supplies a witness for *every* balanced affine orbit, not merely selected families or randomly drawn functions. This is about a directional derivative of one bent function. It does not say that all degree-four functions in eight variables are sums of two bent functions, or that the derivative conjecture holds in higher dimensions.

## Proof

1. **Fix the direction.** Choose a linear isomorphism from $\mathbb F_2^7\times\mathbb F_2$ to the original space taking $(0,1)$ to $e$. In the new coordinates write $H(z,t)=h(z)$, which is independent of $t$ by periodicity. Invertible linear changes preserve degree; restricting to $t=0$ gives $\deg h\leq 3$. Since each quotient value occurs twice, $h$ has weight 64.
2. **Find an antiderivative.** For any Boolean $v$ on seven variables, let $F(z,t)=v(z)+t h(z)$. Its derivative in $(0,1)$ is $h$. Write $s(z)=(-1)^{v(z)}$ and $S_b=\{z:h(z)=b\}$. The unnormalized Walsh transform satisfies
   $$W_F(u,b)=\sum_{z,t}(-1)^{v(z)+t h(z)+u\cdot z+bt}
      =2\sum_{z\in S_b}s(z)(-1)^{u\cdot z}.$$
   Hence $F$ is bent exactly when both slice signings have all character sums of magnitude eight. Equivalently, $W_v$ and $W_{v+h}$ have complementary supports with nonzero values $\pm16$.
3. **Reduce to actual input-affine equivalence.** Gillot and Langevin give the 3,486 AGL$(7,2)$ orbits of $B(0,3,7)=\mathrm{RM}(3,7)$: these are actual functions, *not* a quotient by output affine forms. Balance is invariant under input-affine permutations. Direct evaluation of the 3,486 catalogue ANFs gives precisely 768 balanced representatives. If $h(z)=h_i(Az+c)$, then $F_i(Az+c,t)$ is bent, because every affine permutation preserves all Walsh magnitudes up to reindexing. Its derivative in $(0,1)$ is precisely $h(z)$; pulling back to the original eight coordinates proves the assertion for the originally specified $e$.
4. **Verify the finite claim.** For each of these 768 indices, the table supplies $v_i$. The verifier evaluates the actual eight-bit truth table of $F_i$ and checks the defining derivative on every input, then computes each of its 256 Walsh coefficients from its definition as 256 minus twice a Hamming distance. All 196,608 coefficients have magnitude 16. Coverage of the **catalogue** is checked explicitly; its completeness up to AGL equivalence is an external result of the cited classification, not inferred merely from a matching row count. No stabilizer sizes or reported spectra from the source are used.

Together with Tokareva's reported positive dimensions 4 and 6 and the explicit counterexamples in every even dimension at least 10 by Feng and coauthors, the first failing even dimension (in the usual range $n\ge4$) for the derivative statement is therefore 10.

## Reproduce (Python 3.10+, no third-party packages)

Run from this directory:

~~~sh
python3 verify.py --download
~~~

Or, to work offline, first save the [authors' B-0-3-7.dat](https://langevin.univ-tln.fr/project/agl7/data/B-0-3-7.dat) and use:

~~~sh
python3 verify.py --catalogue /path/to/B-0-3-7.dat
~~~

Expected output:

~~~text
verified pinned catalogue: 3486 cubic-or-lower AGL representatives
balanced representatives: 768; witnesses: 768
derivative identities checked: 196608; Walsh coefficients checked: 196608 (all +/-16)
~~~

**Data provenance and convention.** The authors' catalogue (776,843 bytes, SHA-256: 07ead6fb7809c4f249b3a6b6e4f895b5d1d43fbbc3606cccbe0c3bcb3fa75846) is fetched from its author-hosted URL or supplied by the reader; an unexpected version is rejected. No explicit redistribution license was found on the project page, data index, or in the file. This package therefore does not redistribute the original catalogue. Our certificates.tsv (SHA-256: 83b1bc2ee764a8f8f324aa4588f802f123fec832d6706ae31aabb924472ac49c) contains only zero-based ANF-record indices into that file, and our 128-bit lower-half witnesses written as 32 hexadecimal digits. Bit $j$ from the least significant end is the Boolean value at $z=j$; variables $a,\ldots,g$ correspond to bits $0,\ldots,6$ in $j$. The eighth variable is the most significant input bit. The upper-half truth table equals the lower half XOR the truth table of the source ANF.

**Catalogue metadata caveat.** For its last representative, the nonconstant affine function $h=a$, the pinned file reports the whole AGL group as its stabilizer. Its orbit actually consists of the $2(2^7-1)=254$ nonconstant affine functions, so its stabilizer has index 254. Using the reported stabilizer sizes makes the sum of orbit sizes $2^{64}-253$; correcting this one entry gives $2^{64}$. The proof uses the published orbit-representative classification and the ANFs only, never these stabilizer fields. The mass check is a consistency check, not an independent proof of classification.

## How the witnesses were found (not a verification assumption)

The two disjoint signings can be sought independently. For a 64-point slice $S$, put $s(z)=1-2c(z)$, $c(z)\in\{0,1\}$. For $J\subseteq[7]$, let $S_J=\{z\in S: z_j=1\ (j\in J)\}$, $n_J=|S_J|$ and $M_J=\sum_{z\in S_J}s(z)$. Expanding the product of $1-2z_j$ over the support of $u$ gives its character sum as $\sum_{J\subseteq\operatorname{supp}u}(-2)^{|J|}M_J$. Requiring every character sum to be 8 modulo 16 is equivalent, by subset Möbius inversion, to
$M_\emptyset\equiv8\bmod 16$ and $(-2)^{|J|} M_J\equiv0\bmod16$ for $1\le|J|\le3$. This congruence condition is exact: by Parseval the mean square over the 128 character sums is 64, and every integer congruent to 8 modulo 16 has square at least 64.

The $n_J$ are even for $|J|\le3$: the indicator of a slice is either $h$ or $1+h$, and its product with $\prod_{j\in J}z_j$ has degree at most six, hence even weight in seven variables. Thus the triple constraints are automatic. For $|J|\le2$ require
$$\sum_{z\in S_J}c(z)\equiv (n_J-8\,\mathbf 1_{J=\emptyset})/2 \pmod {2^{3-|J|}}.$$
We solved the 29 resulting parity constraints on 64 unknowns, sampled their binary affine solution space, and rejected candidates failing the remaining seven modulus-4 conditions or the single modulus-8 condition. Failure to find a witness would not prove nonexistence; every accepted one is checked by a separate exact verifier that uses neither the search nor its congruences.

## Scope and prior work

- N. N. Tokareva, [On the set of derivatives of a Boolean bent function (2016)](https://doi.org/10.17223/2226308X/9/14). The [one-page Russian text](https://www.mathnet.ru/php/getFT.phtml?jrnid=pdma&paperid=298&what=fullt) states the period condition and reports the full $n=4,6$ cases and partial checks at $n=8$. The short abstract does not spell out the period condition.
- A. Shaporenko, [Derivatives of bent functions in connection with the bent sum decomposition problem](https://doi.org/10.1007/s10623-022-01167-4), gives in particular the quadratic result in all applicable dimensions.
- V. Gillot and P. Langevin, [Classification of some cosets of the Reed-Muller code](https://doi.org/10.1007/s12095-023-00652-4), Cryptography and Communications 15 (2023), 1129–1137; [author-hosted paper](https://langevin.univ-tln.fr/project/agl7/BFA-paper2022.pdf) and [project table and data](https://langevin.univ-tln.fr/project/agl7/aglclass.html). This package relies on their classification and does not claim credit for it.
- V. N. Potapov, [Existence of balanced functions that are not derivative of bent functions](https://arxiv.org/abs/2309.04244), gives an asymptotic disproof. Y. Feng, H. Jiang, G. Li, T. Li and L. Tang, [A counterexample to Tokareva's conjecture on sums of two bent functions](https://arxiv.org/abs/2610.32239v1), give sum counterexamples in every even dimension at least eight, and derivative counterexamples in every even dimension at least ten.
- M. R. Kepes, A. Kercsó-Molnár and A. Viczián, [A family of symmetric counterexamples to the bent sum decomposition conjecture, v3](https://arxiv.org/html/2611.06744v3), §5, construct derivative counterexamples in dimensions $N=2^k+2$ for $k\ge3$, starting at ten. Their eight-variable counterexample (like that of Feng et al., whose arXiv submission listed only v1 as of 2026-11-27) concerns the **unrestricted bent-sum** question for functions of degree at most four. The positive result here is solely the **derivative** statement in dimension eight for balanced functions of degree at most three with a nonzero period.

We have not located an earlier complete positive eight-variable derivative proof in the checked sources (through 2026-11-27). That is a statement about the search, not a proof of priority or a claim of peer review.
