#!/usr/bin/env python3
"""Fail-closed integrity validation shared by build and source-archive commands.
Internal hashes detect damage against the declared frozen package. Authenticity
still requires an independently trusted archive digest or repository commit.
"""
from pathlib import Path
import hashlib
import json
import re

SOURCE_ARCHIVE_SHA256 = '747386b02dbd12ae6f7b763d79fdb1e9bd70ca1e195e1b84d943cb0bcff82cb5'
METADATA = {
    'format': 1,
    'release_date': '2026-10-07',
    'scope': 'Full original affine-geometric MainTarget',
    'source_archive_sha256': SOURCE_ARCHIVE_SHA256,
}
# Only these top-level generated/VCS directories are outside the source payload.
RUNTIME_DIRECTORIES = frozenset({'.lake', 'vendor', 'replay-evidence', '.git'})
DIGEST = re.compile(r'[0-9a-f]{64}\Z')

ORIGINAL_INVENTORY_SHA256 = '5b45965560db62aafbae3c5e9e17434935d52a568abce3131e64fc40c81c7501'
PRESERVED_WRAPPER_LEDGER_SHA256 = '323eae91edc7d4abc329aba11d442fff4094dcdb4fa2a92cdd42b484b0d4d349'
ORIGINAL_INPUT_FILES = frozenset([
    "ContinuumGeometric.lean",
    "ContinuumGeometric/Activation.lean",
    "ContinuumGeometric/BoundedGrid.lean",
    "ContinuumGeometric/CandidateBounds.lean",
    "ContinuumGeometric/ClosedProjection.lean",
    "ContinuumGeometric/ClosedRepair.lean",
    "ContinuumGeometric/CoefficientCover.lean",
    "ContinuumGeometric/CountableExhaustion.lean",
    "ContinuumGeometric/EntropySchedule.lean",
    "ContinuumGeometric/FiniteRoutingProbability.lean",
    "ContinuumGeometric/GeometricParameters.lean",
    "ContinuumGeometric/GeometryChain.lean",
    "ContinuumGeometric/GridCutBridge.lean",
    "ContinuumGeometric/Interfaces.lean",
    "ContinuumGeometric/LineSignBound.lean",
    "ContinuumGeometric/LocalSignatures.lean",
    "ContinuumGeometric/MainProof.lean",
    "ContinuumGeometric/NoDefaultProbability.lean",
    "ContinuumGeometric/PeriodicRepair.lean",
    "ContinuumGeometric/Planar.lean",
    "ContinuumGeometric/RoutingActiveGeometry.lean",
    "ContinuumGeometric/RoutingAssembly.lean",
    "ContinuumGeometric/RoutingCenterAtoms.lean",
    "ContinuumGeometric/RoutingChoices.lean",
    "ContinuumGeometric/RoutingEntropy.lean",
    "ContinuumGeometric/RoutingFactorization.lean",
    "ContinuumGeometric/RoutingGeometry.lean",
    "ContinuumGeometric/RoutingGlobalGrid.lean",
    "ContinuumGeometric/RoutingInterfaces.lean",
    "ContinuumGeometric/RoutingLocalHit.lean",
    "ContinuumGeometric/RoutingLocalProbability.lean",
    "ContinuumGeometric/RoutingMeasure.lean",
    "ContinuumGeometric/RoutingModel.lean",
    "ContinuumGeometric/RoutingPreorder.lean",
    "ContinuumGeometric/RoutingProbability.lean",
    "ContinuumGeometric/RoutingSchedule.lean",
    "ContinuumGeometric/RoutingSeparation.lean",
    "ContinuumGeometric/RoutingStableGeometry.lean",
    "ContinuumGeometric/RoutingStableMeasure.lean",
    "ContinuumGeometric/RoutingStableProbability.lean",
    "ContinuumGeometric/RoutingTemplate.lean",
    "ContinuumGeometric/RoutingTreeBounds.lean",
    "ContinuumGeometric/ShiftedActivation.lean",
    "ContinuumGeometric/SignFiberCount.lean",
    "ContinuumGeometric/Target.lean",
    "ContinuumGeometric/ZeroErrorBuffer.lean",
    "PublicTheorems.json",
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain"
])

class ReleaseIntegrityError(RuntimeError):
    pass

def require(condition, message):
    if not condition:
        raise ReleaseIntegrityError('RELEASE_INTEGRITY: ' + message)

def file_sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()

def reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: ' + str(key))
        result[key] = value
    return result

def canonical_path(name):
    require(isinstance(name, str) and bool(name), 'invalid member name')
    require('\\' not in name and '\x00' not in name and '\n' not in name and '\r' not in name,
            'noncanonical member path: ' + repr(name))
    path = Path(name)
    require(not path.is_absolute() and all(part not in ('', '.', '..') for part in name.split('/')),
            'unsafe member path: ' + repr(name))
    require(path.as_posix() == name, 'noncanonical member path: ' + repr(name))
    return name

def actual_payload_files(root):
    files = set()
    def visit(directory):
        for entry in directory.iterdir():
            relative = entry.relative_to(root).as_posix()
            if directory == root and entry.name in RUNTIME_DIRECTORIES:
                require(entry.is_dir(), 'runtime exclusion must be a directory: ' + relative)
                continue
            require(not entry.is_symlink(), 'source symlink forbidden: ' + relative)
            if entry.is_dir():
                visit(entry)
            else:
                require(entry.is_file(), 'non-regular source member: ' + relative)
                files.add(relative)
    visit(root)
    return files

def validate_release(root):
    """Return the exact distributable file list after all checks succeed."""
    root = Path(root).resolve()
    for name in ('SOURCE_MANIFEST.json', 'SHA256SUMS'):
        path = root / name
        require(path.is_file() and not path.is_symlink(), 'missing or non-regular required file: ' + name)
    actual = actual_payload_files(root)
    require(actual == EXPECTED_FILES,
            'payload inventory differs; missing=' + repr(sorted(EXPECTED_FILES - actual)) +
            '; unlisted=' + repr(sorted(actual - EXPECTED_FILES)))
    try:
        manifest = json.loads((root / 'SOURCE_MANIFEST.json').read_text(encoding='utf-8'),
                              object_pairs_hook=reject_duplicate_keys)
    except (ValueError, UnicodeError) as error:
        raise ReleaseIntegrityError('RELEASE_INTEGRITY: malformed manifest JSON') from error
    require(isinstance(manifest, dict) and set(manifest) == set(METADATA) | {'sha256'},
            'manifest schema differs')
    for key, expected in METADATA.items():
        require(type(manifest[key]) is type(expected) and manifest[key] == expected,
                'manifest metadata differs: ' + key)
    hashes = manifest['sha256']
    require(isinstance(hashes, dict), 'manifest sha256 must be an object')
    for name, digest in hashes.items():
        canonical_path(name)
        require(isinstance(digest, str) and DIGEST.fullmatch(digest) is not None,
                'invalid SHA-256 digest: ' + name)
    covered = EXPECTED_FILES - {'SOURCE_MANIFEST.json', 'SHA256SUMS'}
    require(set(hashes) == covered,
            'manifest coverage differs; missing=' + repr(sorted(covered - set(hashes))) +
            '; extra=' + repr(sorted(set(hashes) - covered)))
    for name, digest in hashes.items():
        require(file_sha256(root / name) == digest, 'member digest differs: ' + name)
    # Preserve the audited mathematical inputs even if the outer release
    # manifest/checksums were regenerated. These records are immutable in v2.
    original_path = root / 'provenance/ORIGINAL_SOURCE_SHA256.json'
    require(file_sha256(original_path) == ORIGINAL_INVENTORY_SHA256,
            'immutable original-source inventory identity differs')
    original = json.loads(original_path.read_text(encoding='utf-8'),
                          object_pairs_hook=reject_duplicate_keys)
    require(isinstance(original, dict) and set(original) == ORIGINAL_INPUT_FILES,
            'immutable original-source inventory coverage differs')
    for name, digest in original.items():
        require(file_sha256(root / name) == digest, 'immutable source/pin differs: ' + name)
    wrapper_path = root / 'provenance/CHECK_WRAPPER_PROVENANCE.json'
    require(file_sha256(wrapper_path) == PRESERVED_WRAPPER_LEDGER_SHA256,
            'preserved statement/check wrapper ledger identity differs')
    wrappers = json.loads(wrapper_path.read_text(encoding='utf-8'),
                          object_pairs_hook=reject_duplicate_keys)
    require(isinstance(wrappers, list) and len(wrappers) == 5,
            'preserved wrapper ledger coverage differs')
    for wrapper in wrappers:
        name = canonical_path(wrapper['public'])
        require(name in EXPECTED_FILES and file_sha256(root / name) == wrapper['public_sha256'],
                'preserved statement/check wrapper differs: ' + name)
    checksum_hashes = dict(hashes)
    checksum_hashes['SOURCE_MANIFEST.json'] = file_sha256(root / 'SOURCE_MANIFEST.json')
    expected_checksums = ''.join(digest + '  ' + name + '\n'
                                 for name, digest in sorted(checksum_hashes.items())).encode('utf-8')
    require((root / 'SHA256SUMS').read_bytes() == expected_checksums,
            'SHA256SUMS bytes or complete cross-coverage differ')
    return sorted(EXPECTED_FILES)

# The exact versioned payload inventory is embedded independently of manifest
# entries. A removed wrapper cannot disappear from both the manifest and disk.
# This inventory is maintained when explicitly re-freezing a new release.
EXPECTED_FILES = frozenset([
    ".gitignore",
    "ATTRIBUTION.md",
    "CHANGE_LEDGER.md",
    "CI.md",
    "ContinuumGeometric.lean",
    "ContinuumGeometric/Activation.lean",
    "ContinuumGeometric/BoundedGrid.lean",
    "ContinuumGeometric/CandidateBounds.lean",
    "ContinuumGeometric/ClosedProjection.lean",
    "ContinuumGeometric/ClosedRepair.lean",
    "ContinuumGeometric/CoefficientCover.lean",
    "ContinuumGeometric/CountableExhaustion.lean",
    "ContinuumGeometric/EntropySchedule.lean",
    "ContinuumGeometric/FiniteRoutingProbability.lean",
    "ContinuumGeometric/GeometricParameters.lean",
    "ContinuumGeometric/GeometryChain.lean",
    "ContinuumGeometric/GridCutBridge.lean",
    "ContinuumGeometric/Interfaces.lean",
    "ContinuumGeometric/LineSignBound.lean",
    "ContinuumGeometric/LocalSignatures.lean",
    "ContinuumGeometric/MainProof.lean",
    "ContinuumGeometric/NoDefaultProbability.lean",
    "ContinuumGeometric/PeriodicRepair.lean",
    "ContinuumGeometric/Planar.lean",
    "ContinuumGeometric/RoutingActiveGeometry.lean",
    "ContinuumGeometric/RoutingAssembly.lean",
    "ContinuumGeometric/RoutingCenterAtoms.lean",
    "ContinuumGeometric/RoutingChoices.lean",
    "ContinuumGeometric/RoutingEntropy.lean",
    "ContinuumGeometric/RoutingFactorization.lean",
    "ContinuumGeometric/RoutingGeometry.lean",
    "ContinuumGeometric/RoutingGlobalGrid.lean",
    "ContinuumGeometric/RoutingInterfaces.lean",
    "ContinuumGeometric/RoutingLocalHit.lean",
    "ContinuumGeometric/RoutingLocalProbability.lean",
    "ContinuumGeometric/RoutingMeasure.lean",
    "ContinuumGeometric/RoutingModel.lean",
    "ContinuumGeometric/RoutingPreorder.lean",
    "ContinuumGeometric/RoutingProbability.lean",
    "ContinuumGeometric/RoutingSchedule.lean",
    "ContinuumGeometric/RoutingSeparation.lean",
    "ContinuumGeometric/RoutingStableGeometry.lean",
    "ContinuumGeometric/RoutingStableMeasure.lean",
    "ContinuumGeometric/RoutingStableProbability.lean",
    "ContinuumGeometric/RoutingTemplate.lean",
    "ContinuumGeometric/RoutingTreeBounds.lean",
    "ContinuumGeometric/ShiftedActivation.lean",
    "ContinuumGeometric/SignFiberCount.lean",
    "ContinuumGeometric/Target.lean",
    "ContinuumGeometric/ZeroErrorBuffer.lean",
    "DEPENDENCIES.md",
    "DEPENDENCY_PROVENANCE.json",
    "NOTICE.md",
    "PROOF_ROADMAP.md",
    "PublicTheorems.json",
    "README.md",
    "SHA256SUMS",
    "SOURCE_MANIFEST.json",
    "THEOREM_MAP.md",
    "TRUST_AND_SCOPE.md",
    "checks/ClosureAudit.lean",
    "checks/ExactMain.lean",
    "checks/IndependentBoundaryFacts.lean",
    "checks/PublicAxioms.lean",
    "checks/ReplayClosure.lean",
    "checks/negative/DropBoundaryZero.lean",
    "checks/negative/HostileClosedActivation.lean",
    "checks/negative/HostileDefaultReadOmission.lean",
    "checks/negative/HostileDuplicateOwn.lean",
    "checks/negative/HostileDuplicateTerminal.lean",
    "checks/negative/HostileMissingGap.lean",
    "checks/negative/HostileReverseRefinement.lean",
    "checks/negative/HostileRightBoundary.lean",
    "checks/negative/HostileRootAbsolutePosition.lean",
    "checks/negative/HostileRootNegativeCoefficient.lean",
    "checks/negative/HostileRootPZero.lean",
    "checks/negative/HostileRootPositionFreeEntropy.lean",
    "checks/negative/HostileRootSmallExceptional.lean",
    "checks/negative/HostileRootWrapEndpoint.lean",
    "checks/negative/HostileZeroActivation.lean",
    "checks/negative/IgnoreSignCrossing.lean",
    "checks/negative/assign_grid_boundary_to_left_cell.lean",
    "checks/negative/drop_open_window_loss.lean",
    "checks/negative/expected.json",
    "checks/negative/include_left_boundary.lean",
    "checks/negative/log_the_zero_center_boundary.lean",
    "checks/negative/omit_coefficient_shift.lean",
    "checks/negative/strict_buffer_budget_without_positive_p.lean",
    "checks/positive/APIProbe.lean",
    "checks/positive/ArrangementAudit.lean",
    "checks/positive/Audit.lean",
    "checks/positive/BoundaryControls.lean",
    "checks/positive/GridBoundaryControls.lean",
    "checks/positive/LocalBoundaryControls.lean",
    "checks/positive/MainTargetProbe.lean",
    "checks/positive/ProjectionBoundaryControls.lean",
    "checks/positive/geometry_evidence_ActiveAxiomAudit.lean",
    "checks/positive/geometry_evidence_AxiomAudit.lean",
    "checks/positive/geometry_evidence_CandidateAxiomAudit.lean",
    "checks/positive/geometry_evidence_PositiveControls.lean",
    "checks/positive/geometry_evidence_PreorderAxiomAudit.lean",
    "checks/positive/probability_evidence_ProbabilityAudit.lean",
    "checks/positive/probability_evidence_center_atom_evidence_CenterAtomAudit.lean",
    "checks/positive/probability_evidence_measure_evidence_MeasureAudit.lean",
    "checks/positive/probability_evidence_no_default_evidence_NoDefaultAudit.lean",
    "checks/positive/probability_evidence_probability_controls_ProbabilityControls.lean",
    "checks/positive/repair_evidence_BoundaryAudit.lean",
    "checks/positive/repair_evidence_RootAssemblyAudit.lean",
    "checks/positive/repair_evidence_StableBoundaryAudit.lean",
    "ci/geometric-avoidance.yml.proposed",
    "evidence/independent/ACTUAL_MODULE_SOURCE_ARTIFACT_HASHES.json",
    "evidence/independent/AUDIT_REPORT.txt",
    "evidence/independent/BUILD_NORMAL_OPTIMIZED_EQUALITY.json",
    "evidence/independent/COMPLETE_STORED_PROOF_GRAPH.json.gz",
    "evidence/independent/CONTROLS_NORMAL_OPTIMIZED_EQUALITY.json",
    "evidence/independent/INVENTORY_GUARD_CONTROL.json",
    "evidence/independent/LEAN_PYTHON_CLOSURE_EQUALITY.json",
    "evidence/independent/MAIN_OWNED_CLOSURE.json",
    "evidence/independent/MAIN_PROOF_CLOSURE.json",
    "evidence/independent/MAIN_PUBLIC_DEPENDENCIES.json",
    "evidence/independent/OWNED_INVENTORY.json",
    "evidence/independent/OWNED_MODULES.json",
    "evidence/independent/PUBLIC_ROOT_SUMMARY.json",
    "evidence/independent/REAL_LEBESGUE_PROVENANCE.json",
    "evidence/independent/SEMANTIC_CHECK_MANIFEST.json",
    "evidence/independent/SEMANTIC_EXACT_CHECKS.json",
    "evidence/independent/SEMANTIC_REVIEW.txt",
    "evidence/independent/SEMANTIC_SOURCE_REFERENCES.json",
    "evidence/independent/SOURCE_INSPECTION.json",
    "evidence/independent/VERIFICATION.json",
    "evidence/independent/logs/Audit.log",
    "evidence/independent/logs/ClosureAudit.log",
    "evidence/independent/logs/ExactMain.log",
    "evidence/independent/logs/FastClosureAudit.log",
    "evidence/independent/logs/IndependentBoundaryFacts.log",
    "evidence/independent/logs/ReplayClosure.log",
    "evidence/independent/logs/pins.json",
    "evidence/release/BUILD.json",
    "evidence/release/CONTROLS.json",
    "evidence/release/FINAL_REPLAY.json",
    "evidence/release/INDEPENDENT_BUILD_COMPARISON.json",
    "evidence/release/OWNED_BUILD_SHA256.json",
    "evidence/release/PUBLIC_ROOT_SUMMARIES.json",
    "evidence/release/REPLAY_INPUT_MANIFEST.json",
    "evidence/release/VERIFICATION.json",
    "evidence/release/logs/ClosureAudit.log",
    "evidence/release/logs/ExactMain.log",
    "evidence/release/logs/IndependentBoundaryFacts.log",
    "evidence/release/logs/PublicAxioms.log",
    "evidence/release/logs/ReplayClosure.log",
    "evidence/release/logs/ownership-injection-rejection.log",
    "evidence/release/logs/semantic-normal.log",
    "evidence/release/logs/semantic-optimized.log",
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain",
    "provenance/CHECK_WRAPPER_PROVENANCE.json",
    "provenance/CI_VALIDATION.json",
    "provenance/ORIGINAL_SOURCE_SHA256.json",
    "provenance/PACKAGING_GUARD_CONTROLS.json",
    "provenance/PACKAGING_REPAIR.json",
    "provenance/PROOF_BYTE_COMPARISON.json",
    "provenance/PUBLIC_DERIVATIVE_LEDGER.json",
    "provenance/TOOLCHAIN_FILES_SHA256.json",
    "scripts/make_archive.py",
    "scripts/release_integrity.py",
    "scripts/reproduce.py",
    "scripts/semantic_exact_checks.py",
    "scripts/test_release_integrity.py",
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
