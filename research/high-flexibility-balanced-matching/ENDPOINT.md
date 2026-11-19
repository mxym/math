# Strict eventual balanced dominance for every partial flexibility budget

Yongxian Zhang. AI-assisted research draft, not externally peer-reviewed. Take the independent-edge sparse balanced bipartite market of Ameen, Sentenac and Yu (ASY), arXiv:2604.02295v2, §§1.1, 3. Each side has n agents; flexibility probabilities are b_L,b_R, and regular/regular, mixed, flexible/flexible edge probabilities are respectively 2α/n, (α+α_f)/n, 2α_f/n. As usual evaluate at sufficiently large n for each fixed rate. η is the limit, n→∞, of expected maximum matching size divided by n. Here α>0, 0<B<1 are fixed, B=b_L+b_R. OS is (B,0); TS is the **balanced** (B/2,B/2) allocation.

**Theorem.** For each such α,B there is a finite α₀(α,B) such that η_TS>η_OS whenever α_f>α₀. No claim of positivity at all finite α_f or of uniform thresholds over α,B.

**Proof.** Put q=1−B/2, p=1−B=2q−1, t=2αq and h(v)=v(1−log v), h(0)=0. ASY Propositions 3–4 (35)–(38) give consecutive limits of **unmatched** fractions, α_f→∞ after n→∞:

    U_OS = max_y [p exp(−ty/q)+h(y)−1],
    U_TS = max(0,max_y q[exp(−ty)+h(y)]−1),

where the original domain is (0,1]; continuity at zero allows [0,1]. If U_TS=0 use U_OS≥p exp(−2α)>0 (y=1). Otherwise choose a maximizer y of the bracketed TS expression. Its derivative is q[−t exp(−ty)−log y], which tends to +∞ as y↓0 and is negative at 1; thus 0<y<1. Set x=exp(−ty). Criticality gives y=exp(−tx). The same expression at x is also q[x+y+txy]−1, exactly its value at y. After interchanging x and y if necessary take y≥x; no uniqueness or symmetry of the fixed point is assumed.

At this y, subtract TS from the trial OS value. Since exp(−w)≥1−w with w=(1−q)ty/q and exp(−ty/q)=x exp(−w), the difference is at least

    p x (1−w) − qx + (1−q)(y+txy)
      = (1−q)(y−x) + (1−q)² txy/q > 0.

This proves the strict gap of limiting unmatched fractions, hence the reverse gap of matching rates for all sufficiently large α_f by ASY convergence. ∎

Prior boundary: ASY Theorem 4 gives this for B≥2−2e/3 and Theorem 5 for sufficiently small or sufficiently large α at each B. Their discussion after both results explicitly leaves the intermediate α regime at smaller B open. Their earlier proof evaluates the same trial point when the one-type fixed point is unique and uses exp(u)≥1+u; our additional step is the equal-value transposition of any two-cycle, allowing evaluation at the larger partner. Freund, Martin and Zhao (FMZ), arXiv:2404.04709v3, Theorem 3 gives an earlier small-α regime. ASY Theorems 2 and 3 also show why B=1 and α=0 are excluded. Neither this theorem nor its proof determines the global optimal split at all finite rates.
