# Quadratic orders: the original Main theorem

The literal theorem `Entry002.arithmeticSupply_mainTarget_proved : Entry002.MainTarget` closes the unchanged all-quadratic-order target. It proves uniformly bounded finite connected components for the bounded-step graph of actual irreducible elements of every positive-conductor order in a quadratic number field, with the original integral-basis and full planar-coordinate quantifiers. It also bounds injective finite walks and excludes an injective infinite bounded-step walk.

The proof uses the weaker Dirichlet-supply route. The original natural-density prime-ideal PNT and strong `PrincipalSplitPrimeSupplyTarget` remain open. This package does not give an effective algorithm for the bound, assert mathematical novelty, or claim journal or external human-referee endorsement.

## Read the result

- [Exact theorem and nonclaims](THEOREM.md)
- [Proof route and source map](PROOF_ROADMAP.md)
- [Reproduction and trust boundaries](VERIFICATION.md)
- [Source identity and attribution](PROVENANCE.md)
- [Existing licenses](LICENSE_NOTICE.md)
- [Independent evidence](audit/README.md)

The independent check freshly compiled 129 main-library modules and five external arithmetic bridges. The exact 995-module class-field source set was independently compiled in a separate audit and its completed source/output ledger rechecked before reuse here. An additional 113 official modules were freshly compiled for the main phase, and 457 for that independent class-field phase; other pinned official artifacts remained read-only cache inputs. This is not a full rebuild of Lean or mathlib.

The literal Main's 125,368-constant stored declaration closure was replayed into a genuinely empty Lean kernel at trust level zero. Its only logical axioms are `propext`, `Classical.choice`, and `Quot.sound`; their types and universe parameters match stock Lean. This result must be distinguished from source compilation and from inventorying compiler-generated auxiliary declarations. The full inventory contains seven partial compiler-generated helpers that are not proof roots and are unreachable from the accepted safe logical roots. See the final independent report for exact categories; no claim is made that every inventory entry is a safe kernel replay root.

The unconditional endpoint requires `import ArithmeticSupplyWeakMain`. Merely importing the mathlib-only umbrella `Entry002` does not expose the closed Main; its historical `verification.json` records that narrower scope. After the full verifier succeeds, use its fresh output and official overlay on `LEAN_PATH` to import the external bridge.

The combined Main-first inventory is 2,501 theorems, 412 definitions (seven partial runtime helpers) and 39 structural declarations. The 2,906 safe logical roots comprise 2,501 theorems and 405 safe definitions; the nonpartial stored closure has 126,696 constants. That traversal is separate from the literal-Main kernel replay.

See [release tooling revision 2](RELEASE_REVISION.md) for the final-copy review repairs and the separate completed-run artifact checker.

## Start verification

    python3 -B scripts/verify_integrity.py
    python3 -B scripts/test_release_integrity.py --output /outside/controls.json
    python3 -B scripts/verify.py --lean-bin /path/to/lean/bin --dependency-project /path/to/dependency-project --output /path/to/fresh-run

The public verifier accepts already provisioned pinned dependencies. It builds all 134 owned and all 995 class-field modules freshly into a new external directory before its declaration checks and literal-Main empty-kernel replay. It never uses old owned or class-field cache objects. Exact-reference official cache inputs are allowed and explicitly recorded; unavailable non-toolchain official artifacts are built from pinned sources. No automated download or network provisioning is claimed. See [VERIFICATION.md](VERIFICATION.md) for cost and the distinction between the completed independent audit and this new release wrapper.

The 1,256 retained `.lean` files include historical controls and reference projects, not 1,256 new Main-proof modules. All retain their original bytes. Historical author READMEs and comments are preserved, including earlier pending states; they do not override this scoped release report. The original 80/85-module source baselines were not edited or replaced by this derivative. Source-only preparation does not constitute publication.
