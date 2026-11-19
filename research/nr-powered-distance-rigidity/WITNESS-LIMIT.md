# Why the threshold 18 is not simply a cutoff on runtime (separate note)

For each N≥19 the max-radius Fejér site test B in Part II is actually negative at some parameters. This does **not** give a nonregular configuration or counterexample to the conjecture.

In the limit s→∞, the ratio of the top terms of d_m(st²) and d_m(s) gives
\[
 B_\infty(t,\cos θ)=1+2\sum_{m=1}^{N-1}(1-m/N)t^{2k-m}\cos(mθ),\qquad k=N-1.
\]
Take θ=2π/N. At t=1 this is zero. Put w=exp(iθ). The polynomial \(\sum_{m=0}^{N-1}(1-m/N)z^m=(N-(N+1)z+z^{N+1})/[N(1-z)^2]\) has \(wS'(w)=2w/(1-w)^2=-1/(2\sin^2(\pi/N))\). Consequently
\[
 \partial_t B_\infty(1,\cos θ)=-2(N-1)+1/\sin^2(\pi/N)>0.
\]
Indeed \(\sin(\pi/N)<\pi/N\) and \(N^2/(N-1)\) increases for N≥2, with its value at N=19 equal to 361/18>2(22/7)^2. For t<1 sufficiently close to 1 the limit test is strictly negative, hence also B_N(t,s,cosθ)<0 for finite s sufficiently large. This only rules out this particular pointwise-positivity argument; one cannot infer anything about actual constancy for any collection of sites from this negative witness value.
