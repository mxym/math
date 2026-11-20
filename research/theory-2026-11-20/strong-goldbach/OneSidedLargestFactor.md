# Peeling the largest factor in the only remaining signs

Use K(m)=Σ_{k|m}μ(k)min(0,log(k/√m)) and the symmetric rough identity above. Write an even squarefree m>1 here to mean **even Ω(m)**, not that m itself is even. If r=P⁺(m), b=m/r, T=√m/r=√(b/r), then there is the exact identity

    K(m) = −Λ(b) + 2 Σ_{d|b, d<T} μ(d)log(T/d).                      (1)

The empty sum is zero, and equality at an endpoint has zero weight. Indeed the contribution from divisors not containing r can be completed to Σ_{d|b} μ(d)log(d/√m)=−Λ(b), since b>1. In its omitted tail d>√m write d=b/e with e<T. Because μ(b)=−1, the sign becomes −μ(e) and log(d/√m)=log(T/e). Divisors containing r contribute a second identical truncated sum. Thus (1) follows without assuming any distribution theorem.

In particular, for Ω(m)≥4 and r≥√m one has **K=0**. For r<√m, if b has at most two distinct primes ≤T then **K≥0**, regardless of the total factor count. With zero such primes the sum is log T. With one it equals log of that prime. With two s,t≤T it is max(log(st/T),0), by direct expansion. Hence a negative K from any even Ω≥6 requires at least three of m's smaller prime factors to lie at or below √m/P⁺(m). This is an extra pointwise restriction on top of N^τ-roughness, bounded Ω, and the four-factor overlap formula. It does not imply that every m satisfying the restriction gives negative weight.

**The very unbalanced semiprime negative terms cost only O(τ) of the main scale.** Uniformly for fixed 0<τ≤1/4 and even N→∞,

    Σ_{r<s primes, r≤N^τ, rs<N} (log r) Λ(N−rs)
        ≪ τ N S(N) + o(NS(N)),                                        (2)

with constant independent of τ (in the limiting statement). For a proper prime power N−rs, the total after identifying factorizations of each m is N^(1/2+o(1)). When p=N−rs divides N, bound by N^o(1). For r∤N, put X=N/r≥N^(3/4). Sieve s≤X for both s and N−rs prime using the elementary dimension-two upper bound in [Ford, Thms. 2.4–2.5](https://ford126.web.illinois.edu/sieve2023.pdf). With W=N^0.01, the product of local factors is ≪S(N)h(r)/L², h(r)=(r−1)/(r−2) for r>2 (r=2 is omitted since N is even). The two classes collapse for primes dividing N; the class corresponding to N−rs is absent at r. The CRT error is O(W log(2W)); the exceptions when s≤W or N−rs≤W cost O(W+1) for each r. Thus after multiplying by Λ(p)≤L, summing with log r, and using Σ_{r≤N^τ}(log r)/r≪τL (h(r)≪1), one obtains (2). The accumulated sieve errors are N^(0.26+o(1)). This establishes rigorous one-sided control in that sector, not a sharp upper bound on semiprimes whose smaller factor has fixed positive logarithmic size.

At a fixed small τ, it is therefore only the remaining semiprime range and even composites with the three-factor constraint above that need be paid on the negative side; positive four-factor and higher-factor masses may instead be kept when seeking the sharp comparison. No upper bound smaller than NS(N) for the total negative mass is known from this note.

### Exact sign when three primes enter the cutoff

If exactly three primes in b are at most T, write their logarithms as a≤b'≤c
and put u=log T. The sum in (1) is f(u)−f(u−c), where
f(s)=max(0,min(s,a,b',a+b'−s)). When c≤u≤a+b', this difference is
a+b'+c−2u, since u−c≤a. When u≥max(c,a+b'), f(u)=0 and f(u−c) is
strictly positive precisely for c<u<a+b'+c. Together these show strict
negativity precisely for max(c,(a+b'+c)/2)<u<a+b'+c. This does not control
cases with four or more primes in b below T.

The restriction is nonvacuous: for m=3·5·7·11·13·17=255255, direct evaluation by
squaring the product inside the logarithm gives exp(2K(m))=83521/9845600625<1.
Thus even Ω alone is not a sign condition. This example is only pointwise and
does not estimate its correlation with Λ(N−m).
