# Sources and scope

1. **Yuk-Kam Lau and Jie Wu**, *On the least quadratic non-residue*,
   International Journal of Number Theory 4 (2008), Theorem 1.
   Author preprint:
   https://hkumath.hku.hk/~imr/IMRPreprintSeries/2007/IMR2007-4.pdf

   For a nonprincipal Dirichlet character of cube-free modulus \(q\),
   their theorem bounds the least value outside \(\{0,1\}\) by
   \[
     q^{1/(4\sqrt e)+\varepsilon}
   \]
   up to an \(\varepsilon\)-dependent constant. This is the sole
   analytic estimate used here.

2. **Gary Miller**, *Riemann's hypothesis and tests for primality*,
   Journal of Computer and System Sciences 13 (1976), 300--317.

   The repeated-square gcd routine from a supplied group-order multiple
   is standard. Miller obtains deterministic polynomial time under ERH;
   the present theorem instead inserts an unconditional power-size
   character witness bound.

3. **Bartosz Źrałek**, *A deterministic version of Pollard's
   \(p-1\) algorithm*, Mathematics of Computation 79 (2010), 513--533,
   DOI 10.1090/S0025-5718-09-02262-5; preprint:
   https://arxiv.org/abs/0707.4102

   Section 3 explicitly uses
   \((\cdot/p)\), \((\cdot/q)\), and \((\cdot/pq)\) in the three cases
   \(v_2(p-1)>v_2(q-1)\), \(<\), and \(=\). This is the direct
   predecessor for the pair-separating character in the proof.

4. **Jacek Pomykała and Maciej Radziejewski**, *Integer factoring and
   compositeness witnesses*, conference manuscript:
   https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

   Their Algorithm 1 is a Miller--Rabin-type complete factoring
   procedure for squarefree inputs supplied with a multiple of
   \(\varphi(n)\). Sections 2--3 organize failure through least
   character nonresidues, and Lemma 3.4 quotes the Lau--Wu
   \(2/13\) corollary. The present note works directly with a multiple
   of \(\lambda(N)\), allows arbitrary prime multiplicities, and records
   the all-pairs output-sensitive bottleneck \(H(N)\). No assertion is
   made that the general witness framework is new.

5. Repository predecessor
   factor-known-exponent-burgess-bound, pinned at commit
   483828a8e4298ebc8519296f7d46c43aa3ffbc31.

   That note proves a first-split profile and the coarser complete bound
   based on
   \(\min\{\operatorname{rad}(N),(E+1)^2\}\). The result here replaces
   recursive first-split accounting by simultaneous pairwise refinement
   and obtains the smaller hidden bottleneck \(H(N)\).

The theorem assumes that \(E\) is supplied and that its bit length is
polynomial in the bit length of \(N\). It does not construct \(E\), does
not imply ordinary deterministic polynomial-time factoring, and makes
no conclusion about a concrete cryptographic instance or deployed
system. The consulted sources establish the ingredients and closely
related algorithms; no absolute priority claim is made for the exact
\(H(N)\) formulation.
