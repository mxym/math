#!/usr/bin/env python3
"""Fail-closed public source-package guard, derived from audited release tooling.
Internal hashes are not signatures. Authenticate the archive digest externally.
"""
from pathlib import Path
import hashlib,json,os,re,stat
SOURCE_ARCHIVE_SHA256='85f444c30899ea9a5b76b7cb912ca10165f5c2302714d5ee199e033a69fd8074'
ARCHIVE_PREFIX='formalizations/simplex-truncation-sharpness'
METADATA={'format':2,'release_date':'2026-10-07','package':'simplex-truncation-sharpness','scope':'Literal Entry005.truncationSharpnessGoal; upper sharpMainGoal remains open','source_archive_sha256':SOURCE_ARCHIVE_SHA256,'archive_prefix':ARCHIVE_PREFIX}
SEAL_FILES=frozenset({'SOURCE_MANIFEST.json','SHA256SUMS'})
# Builds and caches must live outside this sealed source tree. Only .git is ignored.
RUNTIME_DIRECTORIES=frozenset({'.git'})
DIGEST=re.compile(r'[0-9a-f]{64}\Z')
REQUIRED_INVENTORY_SHA256='99697fa68bd9e0fda2a4b7db360f22b5f5260b911c7812ac831050985675a9b5'
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
  "audit/checks/NegativeFormulaOmission.lean",
  "audit/checks/NegativeMainSubstitution.lean",
  "audit/checks/OwnedInventory.lean",
  "audit/checks/ReplayAllSafeOwned.lean",
  "audit/independent/FINAL_PASS.json",
  "audit/independent/KernelNegativeControl.log",
  "audit/independent/LiteralPositiveControls.log",
  "audit/independent/NegativeFormulaOmission.log",
  "audit/independent/NegativeMainSubstitution.log",
  "audit/independent/ReplayAllSafeOwned.log",
  "audit/independent/SEMANTIC_REVIEW.md",
  "audit/independent/TECHNICAL_REPORT.md",
  "audit/independent/build.json",
  "audit/independent/empty-kernel-replay.json",
  "audit/independent/exact-rational-controls.json",
  "audit/independent/fresh-output-resolution.json",
  "audit/independent/import-closure.json.gz",
  "audit/independent/independent-pins.json",
  "audit/independent/independent-verification.json",
  "audit/independent/inherited-byte-identity.json",
  "audit/independent/manifest-provenance.json",
  "audit/independent/openai-upstream-fetch.json",
  "audit/independent/owned-declarations.json.gz",
  "audit/independent/ownership-summary.json",
  "audit/independent/public850-axioms.json.gz",
  "audit/independent/source-public-theorems.json",
  "audit/independent/targets-upstream-fetch.json",
  "audit/predecessor/FINITE_GEOMETRY_REVIEW.md",
  "audit/predecessor/INDEPENDENT_AUDIT_REPORT.md",
  "audit/predecessor/SAME_WITNESS_REVIEW.md",
  "project/BUNDLE_MANIFEST.json",
  "project/FACET_GEOMETRY_REPORT.md",
  "project/README.md",
  "project/SHARPNESS_PROOF.md",
  "project/SOURCE_FILES_SHA256.json",
  "project/TECHNICAL_REPORT.md",
  "project/TRUNCATION_DETERMINANT_REPORT.md",
  "project/VERIFICATION_SUMMARY.json",
  "project/coverage.json",
  "project/formal/AffineAudit.lean",
  "project/formal/AffineStatements.lean",
  "project/formal/AllStatements.lean",
  "project/formal/Audit.lean",
  "project/formal/Entry005.lean",
  "project/formal/Entry005/ActualAssignmentAssembly.lean",
  "project/formal/Entry005/ActualBodyConeLaw.lean",
  "project/formal/Entry005/ActualBodyHorizontalMoment.lean",
  "project/formal/Entry005/ActualBodyJointConeInterface.lean",
  "project/formal/Entry005/ActualBodyPolarBoundary.lean",
  "project/formal/Entry005/ActualPyramidAssignment.lean",
  "project/formal/Entry005/ActualPyramidDefect.lean",
  "project/formal/Entry005/ActualPyramidJointCone.lean",
  "project/formal/Entry005/ActualPyramidMoment.lean",
  "project/formal/Entry005/AffineNormalization.lean",
  "project/formal/Entry005/AffinePyramid.lean",
  "project/formal/Entry005/AnchorCoordinates.lean",
  "project/formal/Entry005/AnchorSelection.lean",
  "project/formal/Entry005/AssignmentKernel.lean",
  "project/formal/Entry005/BallVolume.lean",
  "project/formal/Entry005/Cap.lean",
  "project/formal/Entry005/CentroidMaximumBound.lean",
  "project/formal/Entry005/ClippedAssignmentKernel.lean",
  "project/formal/Entry005/CompactBallConeLaw.lean",
  "project/formal/Entry005/CompactIidMomentContinuity.lean",
  "project/formal/Entry005/CompactProbabilitySubsequence.lean",
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
  "project/formal/Entry005/FiniteHalfspaceConeLaw.lean",
  "project/formal/Entry005/FiniteHalfspaceFacets.lean",
  "project/formal/Entry005/FiniteHalfspaceHorizontalMoment.lean",
  "project/formal/Entry005/FiniteLawZonotopeMoment.lean",
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
  "project/formal/Entry005/MaximumOuterBall.lean",
  "project/formal/Entry005/OfficialProjectionDefinitions.lean",
  "project/formal/Entry005/PaperWitnessCombinatorics.lean",
  "project/formal/Entry005/PaperWitnessTransport.lean",
  "project/formal/Entry005/PrescribedSimplex.lean",
  "project/formal/Entry005/ProjectionAffineTransport.lean",
  "project/formal/Entry005/ProjectionBodyCovariance.lean",
  "project/formal/Entry005/ProjectionBodyDirections.lean",
  "project/formal/Entry005/ProjectionCap.lean",
  "project/formal/Entry005/ProjectionVolumeSqueeze.lean",
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
  "project/formal/Entry005/SelectedAnchorSimplex.lean",
  "project/formal/Entry005/SharpNormalizationRadius.lean",
  "project/formal/Entry005/SimplexVolumeInterface.lean",
  "project/formal/Entry005/StrongBallVolume.lean",
  "project/formal/Entry005/StrongGeometricEndpoint.lean",
  "project/formal/Entry005/StrongProjectionCap.lean",
  "project/formal/Entry005/Targets.lean",
  "project/formal/Entry005/ThresholdGate.lean",
  "project/formal/Entry005/TruncationActualDefect.lean",
  "project/formal/Entry005/TruncationCenteredHalfspaces.lean",
  "project/formal/Entry005/TruncationCentroid.lean",
  "project/formal/Entry005/TruncationConvexDeterminant.lean",
  "project/formal/Entry005/TruncationCoordinateFacets.lean",
  "project/formal/Entry005/TruncationDefinitions.lean",
  "project/formal/Entry005/TruncationFacetDeterminants.lean",
  "project/formal/Entry005/TruncationFacetFormula.lean",
  "project/formal/Entry005/TruncationFacetGeometry.lean",
  "project/formal/Entry005/TruncationFacetTranslation.lean",
  "project/formal/Entry005/TruncationFacetVectors.lean",
  "project/formal/Entry005/TruncationFormalization.lean",
  "project/formal/Entry005/TruncationGeometry.lean",
  "project/formal/Entry005/TruncationMaximum.lean",
  "project/formal/Entry005/TruncationPower.lean",
  "project/formal/Entry005/TruncationProjection.lean",
  "project/formal/Entry005/TruncationRationalDefect.lean",
  "project/formal/Entry005/TruncationScalarCancellation.lean",
  "project/formal/Entry005/TruncationSharpness.lean",
  "project/formal/Entry005/TruncationSharpnessAssembly.lean",
  "project/formal/Entry005/TruncationSimplexActualVolume.lean",
  "project/formal/Entry005/TruncationSimplexVolume.lean",
  "project/formal/Entry005/TruncationVolume.lean",
  "project/formal/Entry005/UnitBallAnchorChain.lean",
  "project/formal/Entry005/UnitBallDeterminant.lean",
  "project/formal/Entry005/WeightedAnchorSelection.lean",
  "project/formal/Entry005/WitnessAnchorChain.lean",
  "project/formal/Entry005/ZonotopeDeterminant.lean",
  "project/formal/Entry005/ZonotopeFormula.lean",
  "project/formal/Entry005/ZonotopeInjectionCombinatorics.lean",
  "project/formal/Entry005/ZonotopeVolume.lean",
  "project/formal/GeometricAudit.lean",
  "project/formal/GeometricStatements.lean",
  "project/formal/GeometricUpstream.lean",
  "project/formal/KernelInventory.lean",
  "project/formal/Mxym/StochasticRigidity.lean",
  "project/formal/NewAudit.lean",
  "project/formal/NewStatements.lean",
  "project/formal/OAI/Geometry/ProjectionVolume/Basic.lean",
  "project/formal/OAI/Geometry/ProjectionVolume/Brightness.lean",
  "project/formal/OAI/Geometry/ProjectionVolume/Model.lean",
  "project/formal/OwnedClosure.lean",
  "project/formal/OwnedDeclarations.lean",
  "project/formal/PrescribedUpstream.lean",
  "project/formal/PyramidAllStatements.lean",
  "project/formal/PyramidFinalAudit.lean",
  "project/formal/PyramidFocusedAudit.lean",
  "project/formal/PyramidOwnedClosure.lean",
  "project/formal/PyramidOwnedDeclarations.lean",
  "project/formal/PyramidPublicDeclarations.lean",
  "project/formal/ScalarAudit.lean",
  "project/formal/Upstream.lean",
  "project/formal/audit/truncation-all-statements.lean",
  "project/formal/audit/truncation-determinants-owned.lean",
  "project/formal/audit/truncation-facet-owned.lean",
  "project/formal/audit/truncation-facets.lean",
  "project/formal/audit/truncation-owned.lean",
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
  "project/formal/scripts/check_pins.py",
  "project/formal/scripts/clean_owned_build.py",
  "project/formal/scripts/clean_pyramid_build.py",
  "project/formal/scripts/mathlib-modules.txt",
  "project/inherited-pyramid-checkpoint/README.md",
  "project/inherited-pyramid-checkpoint/TECHNICAL_REPORT.md",
  "project/inherited-pyramid-checkpoint/coverage.json",
  "project/logs/pyramid-clean-714-statements.log",
  "project/logs/pyramid-clean-82-statements.log",
  "project/logs/pyramid-clean-build-release.log",
  "project/logs/pyramid-clean-owned-closure.log",
  "project/logs/pyramid-clean-owned-declarations.log",
  "project/logs/pyramid-clean-public-declarations.log",
  "project/logs/pyramid-control-AffinePyramidChecks.log",
  "project/logs/pyramid-control-CentroidMaximumBoundChecks.log",
  "project/logs/pyramid-control-EntryAffineInvarianceChecks.log",
  "project/logs/pyramid-control-GeometricEndpointChecks.log",
  "project/logs/pyramid-control-HausdorffChecks.log",
  "project/logs/pyramid-control-InterfaceChecks.log",
  "project/logs/pyramid-control-MaximumOuterBallChecks.log",
  "project/logs/pyramid-control-PrescribedChecks.log",
  "project/logs/pyramid-control-ProjectionAffineTransportChecks.log",
  "project/logs/pyramid-control-RegularSimplexChecks.log",
  "project/logs/pyramid-control-SharpNormalizationRadiusChecks.log",
  "project/logs/pyramid-control-StrongGeometricEndpointChecks.log",
  "project/logs/pyramid-control-StrongProjectionCapChecks.log",
  "project/logs/pyramid-control-ThresholdChecks.log",
  "project/logs/pyramid-guard-controls-optimized.log",
  "project/logs/pyramid-guard-controls.log",
  "project/logs/pyramid-pins-optimized.log",
  "project/logs/pyramid-pins.log",
  "project/logs/pyramid-verification.json",
  "project/logs/pyramid-verify-release.log",
  "project/logs/truncation-all-statements-axioms.log",
  "project/logs/truncation-clean-build.log",
  "project/logs/truncation-convex-determinant-verification.json",
  "project/logs/truncation-determinant-clean-build.log",
  "project/logs/truncation-determinant-owned-axioms.log",
  "project/logs/truncation-determinant-verification.json",
  "project/logs/truncation-facet-27-signatures-axioms.log",
  "project/logs/truncation-facet-clean-build.log",
  "project/logs/truncation-facet-owned-axioms.log",
  "project/logs/truncation-facet-provenance.json",
  "project/logs/truncation-facet-verification.json",
  "project/logs/truncation-owned-closure.log",
  "project/logs/truncation-pins-optimized.log",
  "project/logs/truncation-pins.log",
  "project/logs/truncation-power-verification.json",
  "project/logs/truncation-verification.json",
  "project/scripts/bootstrap.sh",
  "project/scripts/freeze_truncation.py",
  "project/scripts/make_truncation_coverage.py",
  "project/scripts/package_pyramid.py",
  "project/scripts/replay_text_bundle.py",
  "project/scripts/test_pyramid_audits.py",
  "project/scripts/verify_pyramid.py",
  "project/scripts/verify_truncation.py",
  "project/sources/HISTORICAL_INITIAL_INSPECTION.md",
  "project/sources/PYRAMID_UPSTREAM_REUSE.md",
  "project/sources/UPSTREAM_NOTICE.md",
  "project/sources/all-public-theorems-by-module.json",
  "project/sources/all-public-theorems.json",
  "project/sources/arbitrary-cache-extract-manifest.json",
  "project/sources/arbitrary-missing-cache-modules.json",
  "project/sources/cache-extract-manifest.json",
  "project/sources/coverage-frozen147.json",
  "project/sources/current-mxym-lean/README.md",
  "project/sources/current-mxym-lean/Targets.lean",
  "project/sources/current-mxym-lean/lake-manifest.json",
  "project/sources/current-mxym-lean/lakefile.toml",
  "project/sources/current-mxym-lean/lean-toolchain",
  "project/sources/current-mxym-pin-provenance.json",
  "project/sources/current-repository-inspection.json",
  "project/sources/delivery-lineage.json",
  "project/sources/entry005-v2-paper.md",
  "project/sources/frozen-147-source-hashes.json",
  "project/sources/frozen-147-theorems.json",
  "project/sources/inherited-pyramid-provenance.json",
  "project/sources/new-pyramid-source-hashes.json",
  "project/sources/openai-math/AffineBrightness.lean",
  "project/sources/openai-math/AffineCovariance.lean",
  "project/sources/openai-math/Basic.lean",
  "project/sources/openai-math/Brightness.lean",
  "project/sources/openai-math/Model.lean",
  "project/sources/openai-math/PrismVolume.lean",
  "project/sources/openai-math/README.md",
  "project/sources/openai-math/SimplexVolume.lean",
  "project/sources/openai-math/lake-manifest.json",
  "project/sources/openai-math/lakefile.lean",
  "project/sources/openai-math/lean-toolchain",
  "project/sources/openai-projection-source-inventory.json",
  "project/sources/openai-repository-inspection.json",
  "project/sources/openai_math_LICENSE.txt",
  "project/sources/owner-iid-helper-exact-body-check.json",
  "project/sources/owner-iid-helper-provenance.json",
  "project/sources/owner-joint-interface-hashes.json",
  "project/sources/owner-unchanged-source-hashes.json",
  "project/sources/proof.tex",
  "project/sources/provenance.json",
  "project/sources/published-note-README.md",
  "project/sources/pyramid-82-manifest.json",
  "project/sources/pyramid-82-verified.patch",
  "project/sources/pyramid-all-public-theorems.json",
  "project/sources/pyramid-provenance.json",
  "project/sources/pyramid-theorems-by-module.json",
  "project/sources/sharp-stability-proof.tex",
  "project/sources/truncation-facet-provenance.json",
  "project/sources/truncation-final-claims.json",
  "project/sources/truncation-proof.tex",
  "project/sources/truncation-public-by-module.json",
  "project/sources/truncation-public-theorems.json",
  "project/sources/truncation-source-hashes.json",
  "project/truncation-over-frozen-pyramid.patch",
  "provenance/DEPENDENCY_PROVENANCE.json",
  "provenance/EXTERNAL_ARTIFACTS_REFERENCE.json.gz",
  "provenance/INPUT_ARCHIVE.json",
  "provenance/ORIGINAL_SOURCE_SHA256.json",
  "provenance/PUBLIC_DERIVATIVE_LEDGER.json",
  "provenance/REQUIRED_PAYLOAD_SHA256.json",
  "provenance/TOOLCHAIN_FILES_SHA256.json",
  "scripts/bootstrap.py",
  "scripts/exact_rational_controls.original.py",
  "scripts/exact_rational_controls.py",
  "scripts/make_archive.py",
  "scripts/release_integrity.py",
  "scripts/seal_release.py",
  "scripts/source_inventory.py",
  "scripts/test_release_integrity.py",
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
    for name,digest in required.items():
        require(sha256(snapshot[name])==digest,'immutable required payload differs: '+name)
    original=digest_map(json_value(snapshot['provenance/ORIGINAL_SOURCE_SHA256.json'],'original identity'),'original identity')
    require(len(original)==290 and all(n.startswith('project/') for n in original),'original source inventory differs')
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
        if name in changes:
            require(changes[name]['original_sha256']==digest,'original derivative linkage differs')
        else:require(name in snapshot and sha256(snapshot[name])==digest,'original byte identity differs: '+name)
    require({n for n in original if n in changes}=={'project/sources/delivery-lineage.json','project/sources/pyramid-provenance.json'},'unexpected original-source changes')
    proof_names=[n for n in original if n.endswith('.lean') and (n.startswith(('project/formal/Entry005/','project/formal/Mxym/','project/formal/OAI/')) or n=='project/formal/Entry005.lean')]
    require(len(proof_names)==125 and not any(n in changes for n in proof_names),'mathematical sources not exactly frozen')
    bundle=json_value(snapshot['project/BUNDLE_MANIFEST.json'],'original input manifest')
    require(type(bundle) is dict and type(bundle.get('files')) is list and len(bundle['files'])==289,'original input manifest schema/count differs')
    names=[]
    for row in bundle['files']:
        name='project/'+canonical_path(row['path']);names.append(name)
        require(name in original and original[name]==row['sha256'],'input manifest identity differs')
    require(len(set(names))==289 and set(names)==set(original)-{'project/BUNDLE_MANIFEST.json'},'input manifest coverage differs')
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
