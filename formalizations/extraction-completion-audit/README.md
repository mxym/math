# Independent completion endpoint audit (preliminary)

This new scope reviews the mature extensions at mathematical source commit
`aa1cd0c497a4a9963013ec6dde76a5ed296e2c61`. It is independent internal AI review,
not external human peer review or a first-discovery certificate. The complete
manuscript is not certified by this package.

`SCOPE.json` is the authoritative endpoint/definition/control classification.
`ROOTS.txt` lists selected terminal theorem declarations; `DEFINITIONS.txt`
explicitly binds the concrete protocol, CP, finite-target and loss definitions.
These list sizes describe audit inputs. Dependency closure sizes likewise do
not count mathematical research results and are never added to old scopes.

The old 39/91/235/444, 83/11 and 608 scopes, all their manifests, roots and
evidence are preserved. The fresh-build option removes only ordinary owned
`.lake/build` directories of the seven new completion packages in the current
isolated worktree. It refuses symlinked outputs and resolved paths outside this
worktree. Shared Mathlib and earlier package outputs are preserved.

## Current state

Only `CompletionVerification` has been ordinarily built. No final source
binding, positive full empty-kernel replay, or final forged-proof campaign has
yet been performed. The scope remains `PRELIMINARY` pending the actual reserved
finite-BE/fixed-error and Bell/discard endpoints. `reproduce.py` rejects a final
freeze or audit until the scope is `READY` and `pending_required` is empty.

## Reproduction after final mathematical freeze

1. In the isolated D-backed review worktree, integrate the notified frozen
   mathematical source commit. Update `SCOPE.json`, its three declaration lists,
   `Check.lean`, and `Audit.lean` with the actual added terminal declarations.
   Review their types and definitions, then mark the scope `READY`.
2. Run the mount/backing-image guard and `python3 reproduce.py --plan`.
   `--plan` only checks inventory; it is not mathematical verification.
3. Run `python3 reproduce.py --freeze-source` once. It verifies Lean 4.34.1,
   actual Git pins, unchanged tracked dependency sources, the historical
   Multinomial cache hashes, and exact mathematical file bytes at `source_head`.
   It binds recursive local Lean imports plus every local dependency config,
   all new audit code/config, and every tracked old audit input and evidence.
   Before a new binding, old tracked file names and exact Git blob bytes are
   checked against the initial independent-review commit `aa1cd0c497a4a9963013ec6dde76a5ed296e2c61`.
   `EXECUTION_INPUTS.json` separately binds the exact D-storage guard and the
   resolved D-backed Lean executable; those hashes are checked before execution.
4. Run `python3 reproduce.py --fresh` with output redirected to D storage. It
   calls the D guard, serializes through the shared build lock, freshly builds
   all new owned mathematical libraries, checks every selected type and axiom
   set, and replays their entire proof-and-definition dependency closure from a
   fresh empty environment with kernel trust level zero.
5. Each selected control changes only its theorem proof to `True.intro` and
   retains the original declaration type and universe parameters. The type
   dependencies and `True.intro` are first positively replayed; a separate fresh
   kernel must reject the forged declaration. This distinguishes proof rejection
   from a missing dependency or altered target type.
6. The driver rechecks all bindings and writes fresh `verification/completion-*`
   evidence and a summary. Inspect the exit code, axiom whitelist, one positive
   replay marker, every control marker, and the bound evidence hashes. A PASS
   certifies this scope only.

The only allowed axioms in mathematical closure are `propext`,
`Classical.choice`, and `Quot.sound`. Audit metaprograms are not mathematical
premises. The script rejects unsafe/partial dependencies in replayed closures
and forbidden proof tokens in imported local mathematical sources.

## Scope limits

The pure sharp profile is balanced dimensions only, with fixed local dimension
at least two. Reliability and eventual exactness keep their strict rank/rate
inequalities; the Gaussian endpoint keeps positive varentropy and the strict
entropy-limited local gap. The fidelity exponent covers every nonnegative rate,
including zero and rates at or above the local cap. These results concern an
intrinsic reserved family, not an unproved identification with the manuscript's
Schur implementation. Current Schur endpoints cover actual unclassified
Jucys--Murphy products and codimension-one asymptotics. General-rank sharp
moments/Young multiplicities/Weyl-hook constants and finite-gate Solovay--Kitaev
are outside the current claimed scope.
