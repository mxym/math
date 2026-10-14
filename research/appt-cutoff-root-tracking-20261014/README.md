# Quantitative APPT cutoff tracking and inverse-logarithmic expansion

Ordinary written proof in the existing APPT entropy programme,
Yongxian Zhang / South China University of Technology,14 October2026.
See [the manuscript](PAPER.md), [complete obligations](THEOREM_MAP.md),
[primary-source boundary](LITERATURE.md) and
[the new ordinary read record](MANUSCRIPT_REVIEW.json).

Fix m>=3, q=(m+1)/(m-1), t=q-1, kappa=1/log(3/q), D=mn,
L=logD, b=log(e t kappa) and U=logL+b. The actual eventual all-higher-order
APPT pole cutoff A_(m,n), defined without early-order monotonicity, obeys

    A_(m,n)=w_D+O_m(D^(-beta)), beta>0,
    (1/kappa)w_D+log(t w_D)-(w_D-1)log(1-1/w_D)=logD.

The model root is unique. A sufficient explicit beta is given in T1;
neither that rate nor a finite dimension threshold is asserted optimal.
Its first two inverse-logarithmic corrections are

    A_(m,n)=kappa(L-logL-b)+(kappa U+1/2)/L
       +[(kappa/2)U^2+(1/2-kappa)U+1/(6kappa)-1/2]/L^2
       +O_m((logL)^3/L^3).

The manuscript gives a rigorous recursive expansion at every fixed finite
order, including its remainder. The positive Lambert approximation
kappa V(D/(e t kappa)) differs by1/(2logD)+O(loglogD/(logD)^2).
No convergence or joint growing-m/truncation-order assertion is made.

For every fixed ell>=3, the exact scalar chord/pole crossing z_D tracks
the uniform physical upper cutoff: all actual m>=ell and every real
alpha>=z_D+D^(-beta), at large D, have the unique APPT/ASEP pole optimum.
An actual ell-by-n integer-rank APPT projection beats the pole at
z_D-D^(-beta). The latter's ASEP status is not established.

For fixed actual m, the complete APPT moment envelope on every continuous
critical-to-C logD interval is max{exact pole moment, exact scalar chord
maximum}, with relative error O(D^(-2beta)). The proof retains the exact
strict loss for arbitrarily small positive pole deficits, quantifies all
other physical spectra, controls integer-rank rounding, and covers every
higher real order. It does not classify exact finite transition optimizers.

The new PAPER285 plus map19 received a complete304-line initial ordinary
read and an exact final four-line/context clarification read, bound to final
bytes with literal reconstruction of the original read. Earlier
critical300/sharp240/finite-band249 reads keep their actual inherited
scope; the new read does not extend any original-paper or Lean audit.
This is internal AI-assisted scrutiny, not external human peer review or
historical priority certification.

The finite supporting program uses220-digit Decimal arithmetic plus
exact rational coefficient and derivative controls:

- 12 exact inverse-log coefficient controls and5 exact derivative cancellations;
- 25 actual m-by-10^exponent dimension cases, with m=3,4,5,8,12;
- 75 real-order slope/rank-rounding points and25 actual APPT lower controls;
- One smaller-D slope-margin failure is retained explicitly; all largest
  sampled cases meet that margin. No finite threshold is certified.

Windows standard, optimized Windows and WSL execute the same implementation,
not three independent mathematical proofs. Losses below working precision
may round to zero; exact equality is not inferred. The source correspondence
checker verifies declared bytes/read ranges/links, not the theorem itself.

```text
python3 check_tracking.py --out DIAGNOSTIC.wsl.json
python3 check_sources.py --out SOURCE_CHECK.json
```

[Source bindings](SOURCE_HASHES.json) and [source check](SOURCE_CHECK.json)
cover the final packet plus the actually used ordinary inputs.
[Windows](DIAGNOSTIC.windows.json), [optimized Windows](DIAGNOSTIC.windows-opt.json),
[WSL](DIAGNOSTIC.wsl.json) and [their semantic comparison](DIAGNOSTIC_COMPARISON.json)
retain the diagnostic range and the smaller-sample failure.

Known projection/inscribed-polytope and separability inputs keep their
attribution. All rights reserved for original material; retain third-party
notices. No funding. OpenAI AI assistants supported research and review;
author responsibility remains. [Author record](../../AUTHOR.md).
No new Lean execution/audit roots, complete major-conjecture count,
external message, aiXiv submission, Release, DOI or priority claim.
