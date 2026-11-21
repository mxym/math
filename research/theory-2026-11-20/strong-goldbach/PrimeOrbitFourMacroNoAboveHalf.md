# No four-macro fixed-seed terminal with a limiting weight above one half at near-smooth centers

In the setting of [the matched-pair theorem](PrimeOrbitFourMacroMatchedOffset.md), the entire W>1/2 sector is impossible. Thus, in a six-label, strongly connected, all-composite fixed-prime-seed orbit at near-smooth centers, if there are four macroscopic labels then **all four have upper limiting weight at most one half**. Precisely, near-smooth means that for a fixed finite set F of primes the positive even centers N satisfy log(N/N_F)=o(log N), where N_F is the full F-part. Macroscopic means having positive limit of log(x)/log(N) along the subsequence, after extraction of limits. The theorem does not close the four-macro W≤1/2 sector or solve Goldbach.

**A local multiplicative-congruence argument.** Suppose such a subsequence exists with W>1/2. We use only the following previously proved inputs. The two largest primes M>K have M/K→r in (0,∞), M=o(N), and the other four primes are o(K). The matched pairs are i↔M, j↔K, U↔V. The unique fixed seed p is among i,j,U,V and every other label tends to infinity. There is a fixed two-dimensional left eigenspace at eigenvalue one of the exponent matrix A, with matching equal Gale columns for i,M and j,K in distinct projective directions; no third column lies in either direction. These facts follow from [the four intermediates](PrimeOrbitFourMacroNearSmoothIntermediate.md), [the top-ratio theorem](PrimeOrbitFourMacroTwoLines.md), and [the matched-pair theorem](PrimeOrbitFourMacroMatchedOffset.md). Only the matching and finite positive ratio are used, not the nonzero cofactor offset.

For a mutual pair s↔X write N=s+X+h_s sX with positive even integer h_s (the complementary cofactor is odd, bigger than one, and congruent to one modulo s). Denote by h_i,h_j,h_0 the multipliers for i,M; j,K; U,V. Thus (N−i)(N−M)/(iM)=1+h_i N, and likewise for the other two pairs.

Choose a fixed integral left eigenrow annihilating the j,K Gale direction and positive at i,M. Its entries are D,D at i,M with D>0, zero at j,K, and −A_0,−B_0 at U,V with A_0,B_0>0: every nonzero left eigenrow has both signs and each sign support contains a directed cycle, hence at least two indices. As the row is a 1-eigenrow, factoring all complements gives the exact positive-rational identity

    (1+h_i N)^D = ((N−U)/U)^A_0 ((N−V)/V)^B_0.

All labels are units modulo N (an orbit label dividing N would create a loop and is not permitted here). Square the identity, so that replacing N−x with −x(1−N/x) introduces no sign. Expand to first order modulo N² in the localization with denominators prime to N. This gives

    2(D h_i U V+A_0 V+B_0 U) ≡ 0 (mod N).

Let n be the left side divided by N, a positive integer. Now h_i≤N/(iM), U,V=o(M), and U,V≤N. In fact

    n/U = 2D h_i V/N + 2A_0 V/(NU)+2B_0/N → 0,

and likewise n/V→0. Positivity and integrality imply U,V→∞. Reduce nN=2(D h_i UV+A_0 V+B_0 U) modulo U and V using N≡V mod U and N≡U mod V (the mutual pair U,V) and their coprimality. Then n≡2A_0 mod U and n≡2B_0 mod V. Since n=o(min(U,V)) and A_0,B_0 are fixed, eventually n=2A_0=2B_0. The defining identity for n now gives D h_i=A_0 h_0. Interchanging the two upper pairs similarly gives D' h_j=A'_0 h_0 for fixed positive integers D',A'_0.

In fact the multipliers coincide. With A_0=B_0 the exact product identity becomes (1+h_i N)^D=(1+h_0 N)^A_0. Dividing its logarithm by D h_i N=A_0 h_0 N gives equality of log(1+x)/x at x=h_i N and h_0 N. This function is strictly decreasing on the positive reals (for instance it is the integral from 0 to 1 of 1/(1+t x)). Thus h_i=h_0. Equally h_j=h_0; call the common value h.

Consequently iM=(N−i−M)/h and jK=(N−j−K)/h, whence j/i=(M/K)(N−j−K)/(N−i−M)→r in (0,∞). But U,V both tend to infinity and M,K are macroscopic, so the fixed seed p must equal i or j. The other parent must tend to infinity, contradicting this finite positive ratio. This requires no identification of which growing label is q.

For related exponent-digraph framework, see [Kelanemer (2026)](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460). The full argument was unavailable for comparison; no priority claim is made.
