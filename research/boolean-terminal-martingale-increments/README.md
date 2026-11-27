# A maximum-increment bound for finite martingales

Let X_0,…,X_n be a martingale in [0,1] with deterministic initial value, μ=min(X_0,1−X_0), and v=E[X_n(1−X_n)]. For every a>0 with θ=1/4−(n+1)a²>0,

    Pr[max_i |X_i−X_(i−1)| ≥ a] ≥ max{0, θ μ−(1+2θ)v}.

For Boolean terminal value v=0. At a=1/sqrt(12(n+1)), the probability-times-threshold product is at least μ/(12 sqrt(3(n+1))). This gives the inverse-square-root bound with a constant independent of the initial mean, and includes an approximate-terminal version.

The proof conditions only on observable events and uses stopped variance after the first crossing of the midpoint. This is a probability result, with no analysis of a cryptographic protocol or construction of an adversarial procedure. Its Boolean case resolves the literal abstract formulation in AICR c/0030; a terminal hypothesis is essential.

See PROOF.md and SOURCES.md. Replay with sh replay.sh | diff -u RESULTS.txt -
