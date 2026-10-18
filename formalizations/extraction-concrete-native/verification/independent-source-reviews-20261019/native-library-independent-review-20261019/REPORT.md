# Independent source review: concrete rational gate library

Status: **No substantive mathematical or interface defect found in the fixed sources listed below. Independent source review and existing author-evidence byte verification only; no new Lean/Lake invocation, fresh kernel replay, or negative controls.**

The reviewer is separate from the author of the new universality proofs. The earlier author's independent-review reports were not treated as evidence that these new proofs are correct. This report does not extend any frozen core, algorithm, raw/resource, or historical audit scope.

## Fixed objects and scope

| Object | Fixed Git object | Directly reviewed mathematical files |
|---|---|---|
| SU(2) universality mathematics | `68e1175648097b1ba240d9dffb718805aa22d699` | `RationalGateUniversality/Tori.lean`, `Euler.lean`, `Density.lean` |
| Universality author seal | `2afbc1694cae6209b4b010212e485ac98a8304ad` | 13 theorem/4 definition root selection, checks, inventory, import binding, report and actual copied log |
| Provider and Circle geometry | `d3c249ef46886ec80a31afecd8a4b0e0b7269f23` | `RationalGateProvider/Fifths.lean`, `SignedFifths.lean`, `GaussianAngle.lean`, `CircleDensity.lean`; 19+9 selected roots and check files |
| Concrete old dyadic interface | `fce6bf635f1bc100e26c8544517586c72dc228fc` | `RationalGateInterface/Library.lean`, `Check.lean`; six selected roots |

Package prefixes are respectively `formalizations/extraction-rational-gate-universality`, `formalizations/extraction-rational-gate-provider`, and `formalizations/extraction-rational-gate-interface`. All reads used fixed Git objects, rather than whichever parallel working-tree state happened to exist.

The reviewer also read the relevant older definitions/proofs in `CircuitRecursion/{FiniteNet,SpecialUnitaryNet,SU2Coordinates,QuaternionPlane,QuaternionOracles,PrecomputedNet}.lean`. Those establish the actual SU(2) normal form, quaternion coordinates, instruction-word convention, approximation interface, compactness, and finite-net connection. The review does not claim to re-read all 199 modules in the author import closure; their exact fixed blobs and SHA256 values, and the 42 configuration inputs, were independently byte-checked against the author's binding.

The manifest binds Git blob IDs and SHA256 values for every file in the three fixed package prefixes, the six additionally read older files, all 199 closure modules, all 42 configurations, the original author logs, and selected pinned Mathlib API source files. The shared Mathlib pin is `d13f23b723b8a846827a245b89c10fc7d3f11612`; Lean version recorded by the author is 4.34.1.

## Mathematical review

**Concrete groups and axes.** `rationalGate` constructs genuine members of the finite complex matrix SU(2), through the existing quaternion matrix `[[a,b],[-conj b,conj a]]` with norm-square sum one. Its four labels are Z(q), Z(q) inverse, X(q), X(q) inverse, with q=(3+4i)/5. The exact coordinate theorem matches the table used by the finite-state provider. The explicit label map swaps 0/1 and 2/3. `rationalGate_inverse` proves actual group inverse equality by matrix multiplication; it does not ask callers to certify the inverse relation.

`zTorus` and `xTorus` have the intended first rows `(z,0)` and `(Re z,i Im z)`. Their multiplication proofs establish actual Circle homomorphisms, including identity. `ext_first_row` is valid because the older SU(2) normal form fixes the lower row. The continuity proofs reduce the existing subtype topology to all four matrix entries. The locally installed `IsTopologicalGroup SU2` derives multiplication continuity from matrix multiplication and inverse continuity from matrix star. No discrete topology or extra topology is substituted.

**Zero-safe Euler factorization.** `su2_euler` takes only `U : SU2`. For first-row entries a,b, it uses the existing exact mass identity `norm(a)^2+norm(b)^2=1` and defines t with real/imaginary parts `norm(a),norm(b)`. It sets alpha=arg(a), beta=arg(-i b), s=exp((alpha+beta)/2), r=exp((alpha-beta)/2). The two proven first-row multiplication formulas then recover a and b. The pinned Mathlib `Complex.norm_mul_exp_arg_mul_I` is explicitly valid at zero and handles that case in its own proof. Thus a=0 or b=0 introduces neither division by a vanishing entry nor a missing case. A globally continuous choice of argument is unnecessary: only existence of three factors is asserted.

**Infinite order and Circle density.** The Gaussian-integer homomorphism modulo five sends i to 2, the numerator 3+4i to 1, and 5 to 0. For every positive natural n, equality of the nth powers of numerator and 5 would yield 1=0 in `ZMod 5`. Injectivity of the Gaussian-integer complex embedding and the nonzero denominator convert this into `q^n != 1`. The Circle wrapper has norm one. Its AddCircle preimage therefore has additive order zero. The pinned `AddCircle.denseRange_zsmul_iff` really has positive-circle-length and infinite-order hypotheses, both supplied here; the homeomorphism carries dense integer multiples to dense integer powers of q. There is no caller-supplied irrationality or Circle-density certificate.

**SU(2) density.** In `rationalGate_dense`, S is the algebraic subgroup generated by the actual four gate values and H is its topological closure. The exact identities for gate labels 0 and 2 put Z(q) and X(q) in H. For each axis, the preimage of H is closed by the proven continuity of that torus. Circle dense-power induction therefore puts every point of the corresponding torus in H, since its integer powers are carried into group powers by the proven homomorphism. The new ZXZ factorization and subgroup multiplication put every actual U in H. The final conversion from H=universe to `Dense (Subgroup.closure (Set.range rationalGate) : Set SU2)` matches the intended statement. The proof has no Euler, SU(2)-density, or coverage-certificate argument from a caller.

**Finite net.** `rationalGate_precomputedNet` instantiates the older `precomputedNet_exists` using the actual inverse labels and the just-proved density. Reading the older chain confirms that finite words represent the generated subgroup in the existing chronological convention; compactness supplies a uniform word-length bound, and a finite bounded-word enumeration supplies a table. The endpoint covers every SU(2) target within the existing operator-norm distance 1/576. The theorem is existential: neither a numeric L nor a discovery algorithm or generation-time bound is produced.

## Actual provider and interface review

The five-state transition table performs binary long division for fifths without division in `transition`, `next`, or `run`. Prepending each emitted digit to the retained earlier list gives the intended little-endian representation after p steps. The conserved identity is exact: `5*bitValue(bits)+remainder = initial.value*2^p`. Remainders are always below five, so quotient, remainder, and strict dyadic error theorems follow. Precision zero is included: the output list is empty and each target magnitude is below one. Negative values use an explicit sign with the same magnitude list; possible negative zero is harmless at this signed-value interface.

The program `entryBits i p` performs four actual finite-state coordinate queries, using exactly the coordinate sign/remainder table already equated to the concrete SU(2) matrix. It has no real/complex matrix argument and does not evaluate a noncomputable matrix. `dyadicEntry` materializes signed integer denotations from these lists. Its correctness theorem unfolds the old `CircuitRecursion.DyadicQApproximates` and the old dyadic denominator `2^p`, rather than introducing a weaker replacement property. All four coordinates and all natural precisions are covered. The actual author log also contains the four-label precision-four packet check marker.

The fixed objects reviewed here have no canonical native `WordPacket` output. They provide raw signed little-endian lists and an integer-valued denotational adapter. The fixed `dyadicEntry_correct` theorem proves mathematical value compatibility, not the cost of integer materialization. A later canonical native Word adapter requires its own actual data/value equality and action-bound review; its correctness is not implied merely by these six interface roots.

## Evidence recheck and limits

The original D: author logs were independently hashed against the fixed reports, including the universality log byte-for-byte against its committed `build.log`:

| Author run | Jobs | Actual log SHA256 |
|---|---:|---|
| Provider 19 roots | 3097 | `186571031cb991b35338733172bd368abe26a838fd099d4e32a9a91428511e4a` |
| Circle geometry 9 roots | 3111 | `b2acf7c6468e713134c0bb63b319cd5d124d0bfd9d22aea4263f94795a050adb` |
| Concrete interface 6 roots | 3864 | `6a48523b44cefd1279d858e64ac0d2de01e22b46ef24c74aee31c1a58293b877` |
| Universality 13 theorem/4 definition roots | 3883 | `5b493dc19a33f87d3672eb55d4b6e18d127edf56a31de957e0db46d48eabb8c4` |

The read-only recheck verifies the successful aggregate-build terminal records, actual printed axiom sets for all selected roots against the reports, source snapshots, owned inventory, universality sealed-file hashes, and the full recorded local import/configuration binding. Universality `Check.lean` explicitly requires the selected 13 theorem and four definition declaration kinds. Provider/interface source declarations and printed types were read directly; their check files primarily print types/axioms and the interface also executes small exact packets. The author's standard evidence permits only `propext`, `Classical.choice`, and `Quot.sound` for these roots (some roots use fewer). This review does not independently recreate their Lean environments or trust-zero audit.

The exact positive cost facts in these fixed sources are p transducer transitions in the abstract `Steps` relation, p magnitude bits per coordinate, denominator length p+1, and aggregate four-coordinate/shared-denominator length 5p+1 excluding signs. They do not account for all calls, four-vector construction, clocks/fuel/counters, denominator construction runtime, integer conversion, canonical normalization, memory allocation, indexing, native target/read costs, offline net discovery, or whole classical compiler bit time. No hidden caller-supplied runtime certificate appears in the reviewed endpoints; rather, these costs remain outside those endpoints.

No substantive correction is requested for the fixed objects. For subsequent claims, retain these distinctions: algebraic/topological universality; old dyadic semantic correctness; concrete bit-output volume; separately proved native representation/action bounds; complete machine time, which remains open. Source review plus hash validation does not become a new independent-kernel or hosted-CI scope.

## Reproduction and preservation

Run `python3 /mnt/d/math/tmp/extraction-resume-20261018/native-library-independent-review-20261019/recheck.py` in Ubuntu-22.04. It reads fixed Git objects and existing D-backed evidence, compares them to `MANIFEST.json`, and prints a compact result. It never invokes Lean, Lake, builds, Git mutation, or deletion. The manifest also binds this report's bytes.

Before creating these new small D: report files, `ensure_d_storage.py` confirmed `/mnt/lean-research-d` is the ext4 loop backed by `/mnt/d/math/wsl-data/lean-research-20261016.ext4`. All reviewer outputs remain under this new D: temporary review directory. No research source, old report, frozen input, shared cache, or Gaussian file was written or deleted. No cleanup/reset operation was run.

The parent-reported uncommitted `extraction-rational-gate-binary` successor and all later native numerical/encoding successors are outside this sealed report's fixed scope. They receive no correctness, cost, standard-build, or audit endorsement from this report.
