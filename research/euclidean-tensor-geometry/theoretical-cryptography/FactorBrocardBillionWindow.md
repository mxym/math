# A billion-index exact exclusion window for the Brocard equation

Research note, 28 November 2026. There are no integer solutions to \(n!+1=m^2\) with
\[
             10^{15}<n\le10^{15}+10^9.
\]
This is a finite result for exactly one billion new indices. It does not recheck smaller indices or imply the global conjecture. For comparison, [Epstein and Glickman's primary 2020 computation report](https://raw.githubusercontent.com/jhg023/brocard/master/README.md) records their prior search through \(10^{15}\) with no additional solutions. The present checker is independent of that older code and does not take its conclusion as a premise for the appended window. Modular quadratic-residue sieving is established; the contribution here is the particular completed interval with a reproducible arithmetic check.

## 1. One fast sweep per certified prime

Put \(B=10^{15}+10^9\), \(N=10^9\), and take an odd prime \(p>B\). For \(n=B-j\), \(0\le j<N\), set \(r=p-n\) and \(F=(r-1)!\pmod p\). Wilson's theorem gives
\[
 n!\,F=(-1)^r\pmod p,\qquad
 \chi_p(n!+1)=\chi_p\big(F(F+(-1)^r)\big),
 \tag{1}
\]
where \(\chi_p\) is the quadratic character including value zero. The second equality uses \(F\ne0\) and multiplication by the nonzero square \(F^2\). Start at \(r=p-B\); the next index in the decreasing scan has \(r+1\) and factorial residue \(rF\bmod p\). Thus every index is visited exactly once for this prime, without evaluating a factorial of size near \(10^{15}\). Discard only when the character in (1) is \(-1\); in particular a zero residue is **not** discarded. Each survivor set is intersected with the preceding survivors through an exact one-bit-per-index mask.

The [data file](factor_brocard_billion_window.json) lists the 31 primes that were used and recursive complete-order certificates. Starting from \(2\), for each candidate \(p\) the verifier proves the factorization of \(p-1\) into previously certified primes and checks that a specified unit modulo \(p\) has order exactly \(p-1\). A residue with that order supplies at least \(p-1\) units modulo \(p\), hence \(p\) is prime. All 203 non-base certificate entries in the transitive dependency closure are checked with exact integers.

## 2. Verified full run

The first stage, at \(p=1000001000000017\), leaves \(499989992\) entries. The second leaves \(250003158\). At the last four stages the remaining counts are \(5,3,1,0\), ending at the prime \(1000001000001131\). All 31 exact counts, and the inclusive upper endpoint plus the number of entries, are present in the data file. As there are no survivors, every candidate has a certified nonresidue obstruction. The full run used the recurrence in (1), early skipping of character tests on already excluded indices, and the exact modular reduction explained below.

The [Node.js verifier](verify_factor_brocard_billion_window.js) builds its scan engine in memory as standard WebAssembly. This is a local computation and requires no compiler, network or package. In the directory containing the two files, run:

- `node verify_factor_brocard_billion_window.js --full` to duplicate the full reported run; it uses about 125 MB for the mask and may take a substantial time.
- `node verify_factor_brocard_billion_window.js --full-integer` for an alternative exact reduction and character implementation over the same full range. This mode is slower; the recorded result above refers to `--full`.
- `node verify_factor_brocard_billion_window.js --quick` and `--quick-integer` for tests of wide intermediate products and a bitwise comparison on the last million indices. The independent oracle computes the direct \(n!\) via the reversed Wilson tail at the *lower* endpoint, then steps in increasing \(n\) and applies Euler's criterion to \(n!+1\) using exact BigInt power. These are sample checks, not another proof of all one billion indices.

## 3. Why both machine kernels are exact

For the main kernel, modular multiplication takes \(0\le a,b\le p\le2^{50}\), so all three inputs convert exactly to binary64. Let \(u=ab/p\). The two floating-point operations (multiplication and division) give a nonnegative approximation \(\tilde u\) with
\[
    |\tilde u-u|\le (2^{-52}+2^{-106})u < 1.
\]
The case of zero product is exact; every other operation is far from underflow and overflow. Therefore the estimate \(\lfloor\tilde u\rfloor\) differs by at most one from the exact quotient. WebAssembly's low-word integer multiplications and subtraction compute \(ab-\lfloor\tilde u\rfloor p\) modulo \(2^{64}\); the true residual is in \((-p,2p)\), so its signed interpretation is exactly that residual. One conditional addition and one conditional subtraction yield its unique representative in \([0,p)\). In particular the calculation does not decide any square test by a floating-point comparison. The quadratic character is then evaluated by the ordinary binary Jacobi algorithm, replacing the odd part via reciprocity and an integer remainder, with zero returned for a nonunit. For the certified prime denominator this is the Legendre symbol.

The integer-only kernel splits \(b\) into four 13-bit limbs and evaluates the product by Horner's rule, reducing modulo \(p\) between limbs. Before each reduction the sum of the two products is less than \(2^{64}\): the accumulated residue is below \(p\le2^{50}\), each limb is below \(2^{13}\), and \(a\le p\). Its quadratic-character step uses separate Jacobi computations on \(F\) and \(F+(-1)^r\), then multiplies the two signs. This version of binary Jacobi replaces the larger odd numerator by its difference with the denominator after applying reciprocity if a swap is needed and divides out powers of two at the next iteration. Both versions leave character zero in the mask. All index arithmetic and prime data inputs are exact in the specified range; the factorial loop is indexed by \(r\), and the bit count is below \(2^{31}\).
