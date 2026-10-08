#!/usr/bin/env python3
"""Fail-closed complete sharp upper Main source-package guard.
Internal hashes are not signatures: externally authenticate the archive digest.
"""
from pathlib import Path
import hashlib,json,os,re,stat
ARCHIVE_PREFIX='formalizations/sharp-simplex-upper-bound'
METADATA={'format':2,'release_date':'2026-10-07','package':'sharp-simplex-upper-bound','scope':'Literal original Entry005.sharpMainGoal and MainTarget; upper only, separate lower project','base_patch_sha256':'9a0a33f57cc6a3f9f373040ae11fd98ade985bbd5712f31fca3b82f702b7a932','supplement_patch_sha256':'01dab955ed966f094eedb30de00a392af6615f8960114a8099187f7061a7a71e','archive_prefix':ARCHIVE_PREFIX}
SEAL_FILES=frozenset({'SOURCE_MANIFEST.json','SHA256SUMS'})
RUNTIME_DIRECTORIES=frozenset({'.git'})
DIGEST=re.compile(r'[0-9a-f]{64}\Z')
REQUIRED_INVENTORY_SHA256='6f497ae04220dd1fbd4fd9fa3cbc1e21ee6c7b60c1bfa7004c7435850f622039'
EXPECTED_FILES=frozenset([
  ".gitignore",
  "LICENSE_NOTICE.md",
  "PROOF_ROADMAP.md",
  "PROVENANCE.md",
  "README.md",
  "SHA256SUMS",
  "SOURCE_MANIFEST.json",
  "THEOREM.md",
  "VERIFICATION.md",
  "audit/README.md",
  "audit/checks/IndependentPublicAudit.lean",
  "audit/checks/KernelNegativeControl.lean",
  "audit/checks/LiteralPositiveControls.lean",
  "audit/checks/NegativeAbbreviationAsProof.lean",
  "audit/checks/NegativeConstantOmission.lean",
  "audit/checks/NegativeWrongQuantifier.lean",
  "audit/checks/OwnedInventory.lean",
  "audit/checks/ReplayAllSafeOwned.lean",
  "audit/checks/ReplayLiteralMain.lean",
  "audit/historical/replay_upper_main.original.py",
  "audit/independent/AUDIT_EVIDENCE_SHA256.json",
  "audit/independent/FINAL_PASS.json",
  "audit/independent/IndependentPublicAudit.log.gz",
  "audit/independent/IndependentPublicAudit.result.json",
  "audit/independent/KernelNegativeControl.log",
  "audit/independent/KernelNegativeControl.result.json",
  "audit/independent/LiteralPositiveControls.log",
  "audit/independent/LiteralPositiveControls.result.json",
  "audit/independent/NegativeAbbreviationAsProof.log",
  "audit/independent/NegativeAbbreviationAsProof.result.json",
  "audit/independent/NegativeConstantOmission.log",
  "audit/independent/NegativeConstantOmission.result.json",
  "audit/independent/NegativeWrongQuantifier.log",
  "audit/independent/NegativeWrongQuantifier.result.json",
  "audit/independent/OwnedInventory.log.gz",
  "audit/independent/OwnedInventory.result.json",
  "audit/independent/REPRODUCE.md",
  "audit/independent/ReplayAllSafeOwned.log",
  "audit/independent/ReplayAllSafeOwned.result.json",
  "audit/independent/ReplayLiteralMain.log",
  "audit/independent/ReplayLiteralMain.result.json",
  "audit/independent/TECHNICAL_REPORT.md",
  "audit/independent/build-progress-summary.json",
  "audit/independent/build-progress.json",
  "audit/independent/build.json",
  "audit/independent/environment.json",
  "audit/independent/fresh-regular-owned-outputs.json",
  "audit/independent/import-closure.json.gz",
  "audit/independent/independent-pins.json",
  "audit/independent/input-integrity.json",
  "audit/independent/main-owned-dependency-closure.json",
  "audit/independent/missing-dependencies.json",
  "audit/independent/missing-owned-imports.json",
  "audit/independent/original-definition-identities.json",
  "audit/independent/owned-declarations.json.gz",
  "audit/independent/owned-source-set.json",
  "audit/independent/ownership-summary.json",
  "audit/independent/post-audit-pins.json",
  "audit/independent/public-axioms.json.gz",
  "audit/independent/source-public-theorems.json",
  "audit/independent/unresolved-source-closure.json",
  "audit/mathematical/REVIEW.md",
  "audit/mathematical/exact_controls.py",
  "project/README.md",
  "project/evidence/ActualFiniteEnclosingRadialCap-compile.log",
  "project/evidence/ActualNormalizedDirectionalRoundness-compile.log",
  "project/evidence/FiniteRadialSupportScale-compile.log",
  "project/evidence/OriginalRadialScale-compile.log",
  "project/evidence/PolarSimplexConstruction-compile.log",
  "project/evidence/SharpMainRetentionAssembly-compile.log",
  "project/evidence/SharpUpperMain-compile.log",
  "project/evidence/VerifiedPyramidMomentBridge-compile.log",
  "project/evidence/additive141-signatures-and-axioms.txt",
  "project/evidence/incoming-compatible-source-build.json",
  "project/evidence/incoming-source-materialization.json",
  "project/evidence/independent-final-Main-verification.json",
  "project/evidence/portable-main-replay-verification.json",
  "project/evidence/replay-Entry005.ActualFiniteEnclosingCap.compile.log",
  "project/evidence/replay-Entry005.ActualFiniteEnclosingRadialCap.compile.log",
  "project/evidence/replay-Entry005.ActualNormalizedDirectionalRoundness.compile.log",
  "project/evidence/replay-Entry005.ActualSupportFirstVariationTest.compile.log",
  "project/evidence/replay-Entry005.CenteredAtomCorrection.compile.log",
  "project/evidence/replay-Entry005.ConditionalPyramidMomentBridge.compile.log",
  "project/evidence/replay-Entry005.FiniteHalfspaceCenteredCorrection.compile.log",
  "project/evidence/replay-Entry005.FiniteMinkowskiScaleGate.compile.log",
  "project/evidence/replay-Entry005.FiniteRadialSupportScale.compile.log",
  "project/evidence/replay-Entry005.MainTarget.compile.log",
  "project/evidence/replay-Entry005.OriginalRadialScale.compile.log",
  "project/evidence/replay-Entry005.PolarSimplexConstruction.compile.log",
  "project/evidence/replay-Entry005.ProjectionScaleAssembly.compile.log",
  "project/evidence/replay-Entry005.PyramidApproximationLimits.compile.log",
  "project/evidence/replay-Entry005.SameWitnessOriginalQBudget.compile.log",
  "project/evidence/replay-Entry005.SharpConstantGates.compile.log",
  "project/evidence/replay-Entry005.SharpMainRetentionAssembly.compile.log",
  "project/evidence/replay-Entry005.SharpUpperMain.compile.log",
  "project/evidence/replay-Entry005.SupportScaleCapAssembly.compile.log",
  "project/evidence/replay-Entry005.VerifiedPyramidMomentBridge.compile.log",
  "project/evidence/source-manifest.json",
  "project/evidence/upper-main-audit-verification.json",
  "project/evidence/upper-main-signatures-and-axioms.txt",
  "project/evidence/written-Main-Library-readback-verification.json",
  "project/formal/Entry005.lean",
  "project/formal/Entry005/ActualAssignmentAssembly.lean",
  "project/formal/Entry005/ActualBodyConeLaw.lean",
  "project/formal/Entry005/ActualBodyHorizontalMoment.lean",
  "project/formal/Entry005/ActualBodyJointConeInterface.lean",
  "project/formal/Entry005/ActualBodyPolarBoundary.lean",
  "project/formal/Entry005/ActualFiniteEnclosingCap.lean",
  "project/formal/Entry005/ActualFiniteEnclosingRadialCap.lean",
  "project/formal/Entry005/ActualNormalizedDirectionalRoundness.lean",
  "project/formal/Entry005/ActualPyramidAssignment.lean",
  "project/formal/Entry005/ActualPyramidDefect.lean",
  "project/formal/Entry005/ActualPyramidJointCone.lean",
  "project/formal/Entry005/ActualPyramidMoment.lean",
  "project/formal/Entry005/ActualSupportFirstVariationTest.lean",
  "project/formal/Entry005/AffineNormalization.lean",
  "project/formal/Entry005/AffinePyramid.lean",
  "project/formal/Entry005/AnchorCoordinates.lean",
  "project/formal/Entry005/AnchorSelection.lean",
  "project/formal/Entry005/AssignmentKernel.lean",
  "project/formal/Entry005/BallVolume.lean",
  "project/formal/Entry005/Cap.lean",
  "project/formal/Entry005/CenteredAtomCorrection.lean",
  "project/formal/Entry005/CentroidMaximumBound.lean",
  "project/formal/Entry005/ClippedAssignmentKernel.lean",
  "project/formal/Entry005/CompactBallConeLaw.lean",
  "project/formal/Entry005/CompactIidMomentContinuity.lean",
  "project/formal/Entry005/CompactProbabilitySubsequence.lean",
  "project/formal/Entry005/ConditionalPyramidMomentBridge.lean",
  "project/formal/Entry005/ConeLawFinite.lean",
  "project/formal/Entry005/ConeLawGeometry.lean",
  "project/formal/Entry005/Constants.lean",
  "project/formal/Entry005/CovarianceConditioning.lean",
  "project/formal/Entry005/DeterminantMoment.lean",
  "project/formal/Entry005/DeterminantWitness.lean",
  "project/formal/Entry005/EntryAffineInvariance.lean",
  "project/formal/Entry005/FacetRadialMass.lean",
  "project/formal/Entry005/FamilyWitness.lean",
  "project/formal/Entry005/FiniteBodyWeightedAssignment.lean",
  "project/formal/Entry005/FiniteDeterminantTupleInjection.lean",
  "project/formal/Entry005/FiniteHalfspaceCauchy.lean",
  "project/formal/Entry005/FiniteHalfspaceCenteredCorrection.lean",
  "project/formal/Entry005/FiniteHalfspaceConeLaw.lean",
  "project/formal/Entry005/FiniteHalfspaceFacets.lean",
  "project/formal/Entry005/FiniteHalfspaceHorizontalMoment.lean",
  "project/formal/Entry005/FiniteLawZonotopeMoment.lean",
  "project/formal/Entry005/FiniteMinkowskiScaleGate.lean",
  "project/formal/Entry005/FiniteRadialSupportScale.lean",
  "project/formal/Entry005/FirstMomentAssignment.lean",
  "project/formal/Entry005/GeometricEndpoint.lean",
  "project/formal/Entry005/HalfspaceApproximation.lean",
  "project/formal/Entry005/HalfspaceApproximationSequence.lean",
  "project/formal/Entry005/Handoff.lean",
  "project/formal/Entry005/HausdorffRetention.lean",
  "project/formal/Entry005/HyperplaneProjectionJacobian.lean",
  "project/formal/Entry005/IidAnchorAffineDeterminant.lean",
  "project/formal/Entry005/IidAnchorFirstMomentPositive.lean",
  "project/formal/Entry005/IidAnchorSpanningSupport.lean",
  "project/formal/Entry005/IidTransport.lean",
  "project/formal/Entry005/IidWeightedAnchorSelection.lean",
  "project/formal/Entry005/IntegratedWitness.lean",
  "project/formal/Entry005/IntrinsicLinearImageReuse.lean",
  "project/formal/Entry005/LargestCoordinate.lean",
  "project/formal/Entry005/MainTarget.lean",
  "project/formal/Entry005/MaximumOuterBall.lean",
  "project/formal/Entry005/OfficialProjectionDefinitions.lean",
  "project/formal/Entry005/OriginalRadialScale.lean",
  "project/formal/Entry005/PaperWitnessCombinatorics.lean",
  "project/formal/Entry005/PaperWitnessTransport.lean",
  "project/formal/Entry005/PolarSimplexConstruction.lean",
  "project/formal/Entry005/PrescribedSimplex.lean",
  "project/formal/Entry005/ProjectionAffineTransport.lean",
  "project/formal/Entry005/ProjectionBodyCovariance.lean",
  "project/formal/Entry005/ProjectionBodyDirections.lean",
  "project/formal/Entry005/ProjectionCap.lean",
  "project/formal/Entry005/ProjectionScaleAssembly.lean",
  "project/formal/Entry005/ProjectionVolumeSqueeze.lean",
  "project/formal/Entry005/PyramidApproximationLimits.lean",
  "project/formal/Entry005/PyramidContinuity.lean",
  "project/formal/Entry005/PyramidEntryDefect.lean",
  "project/formal/Entry005/PyramidFacetAreas.lean",
  "project/formal/Entry005/PyramidFormalization.lean",
  "project/formal/Entry005/PyramidHalfspaces.lean",
  "project/formal/Entry005/PyramidIidMomentReuse.lean",
  "project/formal/Entry005/PyramidLiftCoordinates.lean",
  "project/formal/Entry005/PyramidLiftedMoment.lean",
  "project/formal/Entry005/PyramidMomentDefect.lean",
  "project/formal/Entry005/PyramidProjectionBody.lean",
  "project/formal/Entry005/PyramidProjectionVolume.lean",
  "project/formal/Entry005/PyramidSideArea.lean",
  "project/formal/Entry005/PyramidSideFrame.lean",
  "project/formal/Entry005/PyramidVolume.lean",
  "project/formal/Entry005/PyramidZonotopeAlgebra.lean",
  "project/formal/Entry005/RadialConeVolume.lean",
  "project/formal/Entry005/RadialPowerIntegral.lean",
  "project/formal/Entry005/RegularSimplex.lean",
  "project/formal/Entry005/RoundAnchorChain.lean",
  "project/formal/Entry005/SameWitnessOriginalQBudget.lean",
  "project/formal/Entry005/SelectedAnchorHullRoundness.lean",
  "project/formal/Entry005/SelectedAnchorSimplex.lean",
  "project/formal/Entry005/SharpConstantGates.lean",
  "project/formal/Entry005/SharpMainRetentionAssembly.lean",
  "project/formal/Entry005/SharpNormalizationRadius.lean",
  "project/formal/Entry005/SharpUpperMain.lean",
  "project/formal/Entry005/SimplexVolumeInterface.lean",
  "project/formal/Entry005/StrongBallVolume.lean",
  "project/formal/Entry005/StrongGeometricEndpoint.lean",
  "project/formal/Entry005/StrongProjectionCap.lean",
  "project/formal/Entry005/SupportScaleCapAssembly.lean",
  "project/formal/Entry005/Targets.lean",
  "project/formal/Entry005/ThresholdGate.lean",
  "project/formal/Entry005/UnitBallAnchorChain.lean",
  "project/formal/Entry005/UnitBallDeterminant.lean",
  "project/formal/Entry005/VerifiedPyramidMomentBridge.lean",
  "project/formal/Entry005/WeightedAnchorSelection.lean",
  "project/formal/Entry005/WitnessAnchorChain.lean",
  "project/formal/Entry005/ZonotopeDeterminant.lean",
  "project/formal/Entry005/ZonotopeFormula.lean",
  "project/formal/Entry005/ZonotopeInjectionCombinatorics.lean",
  "project/formal/Entry005/ZonotopeVolume.lean",
  "project/formal/Mxym/StochasticRigidity.lean",
  "project/formal/OAI/Geometry/ProjectionVolume/Basic.lean",
  "project/formal/OAI/Geometry/ProjectionVolume/Brightness.lean",
  "project/formal/OAI/Geometry/ProjectionVolume/Model.lean",
  "project/formal/UpperMainAudit.lean",
  "project/formal/controls/AffinePyramidChecks.lean",
  "project/formal/controls/CentroidMaximumBoundChecks.lean",
  "project/formal/controls/EntryAffineInvarianceChecks.lean",
  "project/formal/controls/GeometricEndpointChecks.lean",
  "project/formal/controls/HausdorffChecks.lean",
  "project/formal/controls/InterfaceChecks.lean",
  "project/formal/controls/MaximumOuterBallChecks.lean",
  "project/formal/controls/PrescribedChecks.lean",
  "project/formal/controls/ProjectionAffineTransportChecks.lean",
  "project/formal/controls/RegularSimplexChecks.lean",
  "project/formal/controls/SharpNormalizationRadiusChecks.lean",
  "project/formal/controls/StrongGeometricEndpointChecks.lean",
  "project/formal/controls/StrongProjectionCapChecks.lean",
  "project/formal/controls/ThresholdChecks.lean",
  "project/formal/lake-manifest.json",
  "project/formal/lakefile.toml",
  "project/formal/lean-toolchain",
  "project/licenses/Original533OfficialSourceNotice.md",
  "project/licenses/UPSTREAM_NOTICE.md",
  "project/licenses/formal/OAI/LICENSE",
  "project/licenses/openai_math_LICENSE.txt",
  "project/proofs/CompleteSharpMainRadialProof.txt",
  "project/proofs/FrozenReports.sha256",
  "project/proofs/InspectedSources.sha256",
  "project/proofs/ReviewFindings.txt",
  "project/reviews/DirectionalRoundnessVerification.md",
  "project/reviews/ExactRadialSourceReview.txt",
  "project/reviews/FinalMainAudit.lean",
  "project/reviews/FinalMainAudit.log",
  "project/reviews/FinalMainExactSourceReview.txt",
  "project/reviews/FinalReviewFrozen.sha256",
  "project/reviews/FrozenSourceReview.sha256",
  "project/reviews/Independent-MainTargetCompile.log",
  "project/reviews/Independent-SharpMainRetentionAssemblyCompile.log",
  "project/reviews/Independent-SharpUpperMainCompile.log",
  "project/reviews/PolarSimplex-Audit.log",
  "project/reviews/PolarSimplex-LiteralTerminal.lean",
  "project/reviews/PolarSimplex-LiteralTerminal.log",
  "project/reviews/PolarSimplex-Manifest.json",
  "project/reviews/PolarSimplex-VerificationReport.md",
  "project/reviews/RadialScaleAudit.log",
  "project/scripts/make_readable_patch.py",
  "project/scripts/pins.json",
  "project/scripts/replay_upper_main.py",
  "project/scripts/source_inventory.py",
  "provenance/DEPENDENCY_PROVENANCE.json",
  "provenance/EXTERNAL_ARTIFACTS_REFERENCE.json.gz",
  "provenance/INPUT_COMPOSITION.json",
  "provenance/ORIGINAL_SOURCE_SHA256.json",
  "provenance/PUBLIC_DERIVATIVE_LEDGER.json",
  "provenance/REQUIRED_PAYLOAD_SHA256.json",
  "provenance/TOOLCHAIN_FILES_SHA256.json",
  "provenance/openai/LICENSE.OpenAI-math.Apache-2.0.txt",
  "provenance/openai/ModelImportOnly.patch",
  "provenance/openai/Provenance.json",
  "scripts/bootstrap.py",
  "scripts/make_archive.py",
  "scripts/release_integrity.py",
  "scripts/seal_release.py",
  "scripts/source_inventory.py",
  "scripts/test_release_integrity.py",
  "scripts/test_source_completeness.py",
  "scripts/verify.py",
  "scripts/verify_integrity.py",
  "third_party_licenses/Cli/LICENSE",
  "third_party_licenses/LeanSearchClient/LICENSE",
  "third_party_licenses/Qq/LICENSE",
  "third_party_licenses/SHA256SUMS",
  "third_party_licenses/aesop/LICENSE",
  "third_party_licenses/batteries/LICENSE",
  "third_party_licenses/importGraph/LICENSE",
  "third_party_licenses/importGraph/html-template/LICENSE_source",
  "third_party_licenses/lean4/LICENSE",
  "third_party_licenses/lean4/LICENSES",
  "third_party_licenses/mathlib/LICENSE",
  "third_party_licenses/openai_math_LICENSE.txt",
  "third_party_licenses/plausible/LICENSE",
  "third_party_licenses/proofwidgets/LICENSE",
  "third_party_licenses/repository_NOTICE.md"
])
class ReleaseIntegrityError(RuntimeError):
    """A frozen release is incomplete, inconsistent, or unexpectedly modified."""


def require(condition, message):
    if not condition:
        raise ReleaseIntegrityError('RELEASE_INTEGRITY: ' + message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def file_sha256(path):
    return sha256(Path(path).read_bytes())


def reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: ' + str(key))
        result[key] = value
    return result


def json_value(data, label):
    try:
        return json.loads(data.decode('utf-8'), object_pairs_hook=reject_duplicate_keys,
                          parse_constant=lambda value: require(False, 'nonfinite JSON: ' + value))
    except (ValueError, UnicodeError, RecursionError) as error:
        raise ReleaseIntegrityError('RELEASE_INTEGRITY: malformed JSON: ' + label) from error


def canonical_path(name):
    require(type(name) is str and bool(name), 'invalid member name')
    require(not any(ord(c) < 32 or ord(c) == 127 for c in name) and '\\' not in name,
            'noncanonical member path: ' + repr(name))
    path = Path(name)
    require(not path.is_absolute() and all(part not in ('', '.', '..') for part in name.split('/')),
            'unsafe member path: ' + repr(name))
    require(path.as_posix() == name, 'noncanonical member path: ' + repr(name))
    return name


def digest_map(value, label):
    require(type(value) is dict, label + ' must be an object')
    for name, digest in value.items():
        canonical_path(name)
        require(type(digest) is str and DIGEST.fullmatch(digest) is not None,
                'invalid SHA-256 digest in ' + label + ': ' + name)
    return value


def expected_directories():
    return {parent.as_posix() for name in EXPECTED_FILES
            for parent in Path(name).parents if parent != Path('.')}


def actual_payload_files(root):
    """Reject unexpected directories too, and never follow a source symlink."""
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), 'source root must be a real directory')
    files = set()
    directories = expected_directories()
    def visit(directory):
        for entry in directory.iterdir():
            relative = canonical_path(entry.relative_to(root).as_posix())
            mode = entry.lstat().st_mode
            require(not stat.S_ISLNK(mode), 'source/runtime symlink forbidden: ' + relative)
            if relative in RUNTIME_DIRECTORIES:
                require(stat.S_ISDIR(mode), 'runtime exclusion must be a real directory: ' + relative)
                continue
            if stat.S_ISDIR(mode):
                require(relative in directories, 'unexpected source directory: ' + relative)
                visit(entry)
            else:
                require(stat.S_ISREG(mode), 'non-regular source member: ' + relative)
                files.add(relative)
    visit(root)
    return files


def read_regular_bytes(path):
    """Use no-follow on the final component when the platform supports it."""
    flags = os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0) | getattr(os, 'O_BINARY', 0)
    descriptor = os.open(path, flags)
    with os.fdopen(descriptor, 'rb') as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), 'not a regular file: ' + str(path))
        return stream.read()


def read_payload(root, sealed=True):
    root = Path(root)
    expected = EXPECTED_FILES if sealed else EXPECTED_FILES - SEAL_FILES
    actual = actual_payload_files(root)
    require(actual == expected,
            'payload inventory differs; missing=' + repr(sorted(expected - actual)) +
            '; unlisted=' + repr(sorted(actual - expected)))
    snapshot = {name: read_regular_bytes(root / name) for name in sorted(expected)}
    require(actual_payload_files(root) == expected, 'payload inventory changed during read')
    return snapshot


def validate_frozen_payload(snapshot):
    inventory_name='provenance/REQUIRED_PAYLOAD_SHA256.json'
    require(sha256(snapshot[inventory_name])==REQUIRED_INVENTORY_SHA256,'immutable required-inventory identity differs')
    required=digest_map(json_value(snapshot[inventory_name],'required inventory'),'required inventory')
    excluded=SEAL_FILES|{inventory_name,'scripts/release_integrity.py'}
    require(set(required)==EXPECTED_FILES-excluded,'immutable required-inventory coverage differs')
    for name,digest in required.items():require(sha256(snapshot[name])==digest,'immutable required payload differs: '+name)
    original=digest_map(json_value(snapshot['provenance/ORIGINAL_SOURCE_SHA256.json'],'original identity'),'original identity')
    require(len(original)==204 and all(n.startswith('project/') for n in original),'original composed source inventory differs')
    ledger=json_value(snapshot['provenance/PUBLIC_DERIVATIVE_LEDGER.json'],'derivative ledger')
    require(type(ledger) is list,'derivative ledger schema differs')
    changes={}
    for row in ledger:
        require(type(row) is dict and set(row)=={'origin','public','original_sha256','public_sha256','change'},'derivative row schema differs')
        name=canonical_path(row['public']);require(name not in changes,'duplicate derivative path')
        for k in ['original_sha256','public_sha256']:require(type(row[k]) is str and DIGEST.fullmatch(row[k]) is not None,'invalid derivative digest')
        require(name in snapshot and sha256(snapshot[name])==row['public_sha256'],'derivative identity differs: '+name)
        changes[name]=row
    for name,digest in original.items():
        if name in changes:require(changes[name]['original_sha256']==digest,'original derivative linkage differs')
        else:require(name in snapshot and sha256(snapshot[name])==digest,'original byte identity differs: '+name)
        require(not name.endswith('.lean') or name not in changes,'delivered Lean source changed: '+name)
    proof_names=[n for n in original if n.endswith('.lean') and (n.startswith(('project/formal/Entry005/','project/formal/Mxym/','project/formal/OAI/')) or n=='project/formal/Entry005.lean')]
    require(len(proof_names)==123 and not any(n in changes for n in proof_names),'mathematical sources not exactly frozen')
    module_hashes={n[len('project/formal/'):-5].replace('/','.'):original[n] for n in proof_names}
    source_set=json_value(snapshot['audit/independent/owned-source-set.json'],'source-set identity')
    require(module_hashes==source_set['module_sha256'],'source-set module hashes differ')
    compact=json.dumps(dict(sorted(module_hashes.items())),separators=(',',':')).encode()
    require(sha256(compact)=='36f41bf0bc292a93c5e45ce71b8483be82661f0e67f8326650850b3b1906497a','composed mathematical source-set identity differs')
    require(module_hashes['Entry005.SelectedAnchorHullRoundness']=='edfca1a3ae33a55278773cc6c7784acbb355570b3072afe9a70c158b95813fd4','exact missing-source supplement differs')
    license_hashes={n:sha256(b) for n,b in snapshot.items() if n.startswith('third_party_licenses/') and n!='third_party_licenses/SHA256SUMS'}
    license_hashes['provenance/DEPENDENCY_PROVENANCE.json']=sha256(snapshot['provenance/DEPENDENCY_PROVENANCE.json'])
    require(snapshot['third_party_licenses/SHA256SUMS']==checksum_bytes(license_hashes),'license checksum coverage differs')

def checksum_bytes(hashes):
    return ''.join(digest + '  ' + name + '\n' for name, digest in sorted(hashes.items())).encode('utf-8')


def manifest_bytes(snapshot):
    manifest = dict(METADATA)
    manifest['sha256'] = {name: sha256(data) for name, data in sorted(snapshot.items()) if name not in SEAL_FILES}
    return (json.dumps(manifest, indent=2, ensure_ascii=False) + '\n').encode('utf-8')


def validated_snapshot(root):
    """Return checked bytes, so an archive never rereads unchecked replacements.

    This is an integrity guard for a quiescent source tree, not an adversarial
    filesystem sandbox or a signature/authenticity verifier.
    """
    try:
        snapshot = read_payload(root)
        manifest = json_value(snapshot['SOURCE_MANIFEST.json'], 'SOURCE_MANIFEST.json')
        require(type(manifest) is dict and set(manifest) == set(METADATA) | {'sha256'}, 'manifest schema differs')
        for key, expected in METADATA.items():
            require(type(manifest[key]) is type(expected) and manifest[key] == expected,
                    'manifest metadata differs: ' + key)
        hashes = digest_map(manifest['sha256'], 'manifest sha256')
        covered = EXPECTED_FILES - SEAL_FILES
        require(set(hashes) == covered, 'manifest coverage differs; missing=' + repr(sorted(covered - set(hashes))) +
                '; extra=' + repr(sorted(set(hashes) - covered)))
        for name, digest in hashes.items():
            require(sha256(snapshot[name]) == digest, 'member digest differs: ' + name)
        validate_frozen_payload(snapshot)
        checksum_hashes = dict(hashes)
        checksum_hashes['SOURCE_MANIFEST.json'] = sha256(snapshot['SOURCE_MANIFEST.json'])
        require(snapshot['SHA256SUMS'] == checksum_bytes(checksum_hashes),
                'SHA256SUMS bytes or complete cross-coverage differ')
        return snapshot
    except OSError as error:
        raise ReleaseIntegrityError('RELEASE_INTEGRITY: filesystem read failed: ' + str(error)) from error


def validate_release(root):
    return sorted(validated_snapshot(root))
