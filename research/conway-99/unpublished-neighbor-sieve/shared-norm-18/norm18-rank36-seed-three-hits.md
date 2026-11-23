# Three short hit sets when norm 16 and U127 vanish

At rank 36, assume N16=U127=0. Every such graph must meet **each** of the three sets
```
{U228, U230, U337},    {U026, U226},    {U026, U230}.
```
Here U026 denotes the **unit** norm-26 species; raw G026 is not assumed zero. In particular this seven-type nonexistence (first cut) also allows U125. If U026 is absent, the other cuts require both U226 and U230.

For the three contrary cases the [exact native verifier](norm18_rank36_seed_three_hits.py) proves the following respective lower bounds on the same actual oriented N18:
```
14,275,638,990 N18 ≥ 441,845,165,853,000    ⇒ N18 ≥ 30,952,
        13,090 N18 ≥         404,031,180    ⇒ N18 ≥ 30,866,
        16,898 N18 ≥         585,281,984    ⇒ N18 ≥ 34,638.
```
All contradict the [root-seed graph bound](norm18-label-edge-cap.md) N18≤29,842 assuming only N16=U127=0. No other shell is silently turned off. Positive coefficients in the checker are actual mark lower bounds, nonnegative angular atoms or raw/unit populations, together with these previously established positive rows:

* First case: original Sidon tangents ('Ct',34) and ('Ct',48) in [the original rank-36 sieve](rank36_four_hit_sets.py), and the original rank-36 Fano zero equality.
* Second: [actual G121≤29,372](u226-global-pressure.md); no lower bound on an original or extension Y2 is used.
* Third: G121≤29,372 and the [positive-pair square capacity](active-square-eight-all.md) 2G226+3N16≤5544+3U127.

Neither the second nor the third scalar comparison needs N16=0, which is needed on its graph-upper side only. The shared factor 2402 converts each selected anisotropic unit count to its true global count. The assertions are conditional hit sets, not an elimination of rank 36.
 
The [support sieve](rank36_five_candidates.py) combines these three conditions with the earlier exact hit sets. It leaves 49 size-five supports passing the necessary tests, down from 51, and reproduces the larger-cardinality layers. No remaining profile is asserted to occur in a graph.
