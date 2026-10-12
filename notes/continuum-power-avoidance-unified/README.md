# Large closed sets avoiding a continuum of power asymptotics

**Unified traditional manuscript, revision 2, 7 October 2026.**

Read the [14-page paper](continuum-avoidance.pdf), its unchanged [TeX source](source/continuum-avoidance.tex), and the [independent revision-closure review](review/REVISION2_CLOSURE.md). This public distribution preserves the reviewed PDF and mathematical source byte for byte. The author field remains blank; the release does not assign authorship or a new license.

## Result and exact scope

Fix a prescribed, nonempty countable family of positive configurations whose occupied dyadic logarithmic bins have eventually bounded gaps, separately for each configuration. For every epsilon between zero and one, the paper constructs a closed nowhere dense one-periodic set with measure strictly greater than 1 minus epsilon in every unit interval. After choosing that set, all positive real leading exponents, positive power remainder gains, translations, nonzero signed coefficients, finite error bounds, and eventual maps on configuration tails may vary. Every tail has infinitely many **distinct output values** outside the set. No continuity, measurability, or injectivity of the map is assumed.

The prescribed family comes **before** the choice of the avoiding set. A universal set for all possible configurations is not asserted. The compact corollary gives one compact subset of [0,1] that avoids every affine null geometric progression at every ratio in (0,1), with infinitely many distinct misses in every tail.

The manuscript gives the traditional proof in full, including the finite routing probability calculation, continuum representatives with boundary strata, the noncircular logarithmic schedule, measurable closed-center projection, open repair, and countable exhaustion. It also explains the precise limits of the endpoint obstructions. The [citation audit](evidence/citation-audit.txt) and [pinned research sources](evidence/research-source-retrieval.json) preserve prior-work attribution and comparison limits.

## Independent review and retained correction history

The [original end-to-end review](review/INDEPENDENT_REVIEW_V0.md) identified a genuine missing initial-window hypothesis in the isolated v0 Lemma 4.1. The final schedule already supplied that hypothesis, but the lemma statement required repair. Revision 2 imposes the standing conditions in Section 3:

- U >= 4 and U > |k|
- U >= s1*z1-k
- L >= max{2, ceil(2D)}

The revised probability lemmas explicitly inherit them. Three other changes clarify the exact quarter-width equality, the joint probability and atom-mass factor, and the closed-activation example's ambient exponent interval. The [exact source patch](revision/source.patch), [author-supplied correction record](revision/REVIEW.txt), and original [baseline TeX](revision/baseline/source/continuum-avoidance.tex) and [baseline PDF](revision/baseline/continuum-avoidance.pdf) remain available. The baseline is superseded and retains the identified omission.

The [closure review](review/REVISION2_CLOSURE.md) reports PASS with no remaining mathematical blocker or regression. It independently checked the traditional proof and complete revision rather than substituting a Lean PASS for paper reasoning. It checked hypothesis propagation, the exact diff and zero-fuzz replay, unchanged frozen proofs, and all 14 rendered pages. [Machine-readable results](review/REVISION2_CLOSURE.json) are included. Public review derivatives remove private delivery identifiers only, with their original report hashes recorded in [PROVENANCE.json](PROVENANCE.json).

This is independent AI-model review, not external human peer review, journal acceptance, or certification of originality or worldwide priority. Authorship and submission metadata remain for the rights holder to settle.

## Lean correspondence and genuine replay evidence

The unchanged [correspondence CSV](evidence/theorem-correspondence.csv), [JSON](evidence/theorem-correspondence.json), and [typeset appendix source](source/correspondence.tex) map **20 proof steps to 57 exact Lean declarations** with source paths, lines, and hashes. The inventory has 759 source-visible declarations. The module map has 65 source modules and 172 local import edges; it is a module-import map, not a kernel constant-dependency graph. Name/line correspondence alone does not prove the equivalence of English prose and a formal statement.

The two full Lean packages are kept in their own repository locations and are not duplicated here:

- [Geometric avoidance](../../formalizations/geometric-avoidance/README.md): [formal sources](../../formalizations/geometric-avoidance/ContinuumGeometric/), [independent evidence](../../formalizations/geometric-avoidance/evidence/independent/), and [trust/scope explanation](../../formalizations/geometric-avoidance/TRUST_AND_SCOPE.md)
- [Prescribed-family continuum remainder avoidance](../../formalizations/continuum-remainder-avoidance/README.md): [formal sources](../../formalizations/continuum-remainder-avoidance/project/), [verification instructions](../../formalizations/continuum-remainder-avoidance/VERIFICATION.md), and [independent audit](../../formalizations/continuum-remainder-avoidance/audit/independent/AUDIT_REPORT.md)

The stronger formalization includes 45 unchanged geometric modules, 18 remainder modules, and two aggregate modules. Its independently implemented [endpoint replay](../../formalizations/continuum-remainder-avoidance/audit/checks/ReplayClosure.lean) and [all-safe replay](../../formalizations/continuum-remainder-avoidance/audit/checks/ReplayAllSafeOwned.lean) use an empty, trust-zero environment. Their historical [endpoint log](../../formalizations/continuum-remainder-avoidance/audit/independent/logs/ReplayClosure.log) and [all-safe log](../../formalizations/continuum-remainder-avoidance/audit/independent/logs/ReplayAllSafeOwned.log) record 34,923 and 35,620 replayed declarations respectively. The latter is the closure of 1,445 safe owned declarations. Read that package's exact trust boundary and pinned environment before reproducing the replay.

The original submitted KernelReplay.lean was an import-only probe. It was not the actual empty-kernel replay. The original paper ZIP did not contain the later genuine replay programs and logs; those live in the formalization distributions linked above. Historical in-paper references to the source supplement describe that original delivery, not an assertion that omitted archives or independent replay files are embedded in this lean manuscript distribution. No new Lean build or kernel replay is claimed by this manuscript package's checks.

## Reproduce the manuscript checks

The standalone package needs Python 3 and GNU `patch`. It needs neither a private file service nor network access:

```sh
python3 -B run_checks.py
python3 -O -B run_checks.py
```

These commands verify the exact payload inventory, all file hashes and sizes, frozen revision anchors, independently regenerated diff and zero-fuzz patch replay, the original exact-rational early-window countercontrol and eight corrected endpoint cases, resolved source labels/citations, and consistency of the 20/57 correspondence with the source inventories. The original revision helper is archival; the wrapper runs it on a temporary copy. These commands write no package files, update no manifest, and fail closed on altered, missing, unlisted, symlinked, or malformed inputs. The supplied PDF's exact bytes are checked. A successful check is neither a proof of the infinite theorem nor a new independent mathematical review.

To check all 65 source hashes, all 759 declaration locations, and the 45 reused geometric modules against a full checkout containing both public formalizations:

```sh
python3 -B run_checks.py --repository-root ../..
python3 -O -B run_checks.py --repository-root ../..
```

Run these from this manuscript directory in the repository. For separately extracted public projects, pass both `--geometric-root PATH` and `--continuum-root PATH` instead. A requested comparison fails if the expected sources are missing or differ. With no source-root option, the report explicitly marks that comparison `NOT_RUN`.

To rebuild the paper in a temporary directory and compare every extracted text byte to the frozen 14-page PDF:

```sh
python3 -B run_checks.py --build-pdf
```

This additionally needs `pdflatex`, `pdftotext`, and standard TeX packages: geometry, amsmath, amssymb, amsthm, mathtools, lmodern, microtype, booktabs, longtable, array, xurl, and hyperref. If the installed TeX distribution has no prebuilt pdflatex format, the checker generates one from its installed latex.ltx with English hyphenation in the temporary build directory. It keeps generated TeX caches there as well. Three passes run with shell escape disabled; unresolved references, missing characters, and overfull boxes fail the check. To retain a build, add `--build-output NEW_DIRECTORY` outside this package. The directory must not already exist. PDF timestamps or engine metadata may change on rebuilding; the supplied reviewed PDF is never overwritten or re-signed.

The [completed local reproduction record](review/PUBLIC_REPRODUCTION.json) records two full runs, normal and Python `-O`, including both isolated PDF builds and the external formal-source comparisons.

[MANIFEST.json](MANIFEST.json) inventories this public payload. [SHA256SUMS](SHA256SUMS) also binds that manifest. Hashes are consistency records, not digital signatures or independent publisher authentication; retain an independently obtained release archive digest when authenticity matters. Generated reports, extracted caches, and rebuild outputs belong outside the sealed package.

## Provenance and rights

[PROVENANCE.json](PROVENANCE.json) records the precise revision-2 input archive (4,281,025 bytes, SHA-256 `73772896db3dabaa4fc38eb389bbef7d6f1d09b2fdffde2bf0c80b8da869a7d2`), unchanged supplied members, original review hashes, and external proof identities. The [original manifest](provenance/original-revision2-manifest.json) is retained as historical provenance; its omitted archive/build entries are not part of this public payload inventory. The entire original archive remains a separate source record and is not required by `run_checks.py`.

Read [NOTICE.md](NOTICE.md), the retained [collection notice](third_party_licenses/repository_NOTICE.md), and [upstream license](third_party_licenses/openai_math_LICENSE.txt). Existing upstream attribution and terms remain within their original scope. No new blanket license or author/institution attribution is added.
