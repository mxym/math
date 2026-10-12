#!/usr/bin/env python3
"""Fail-closed, assertion-free validation of the frozen continuum source release.

Adapted from the audited geometric-avoidance v2 packaging guard. Internal hashes
are not signatures: authenticity needs a trusted external digest or commit.
No Lean, network, dependencies, generated build data, or subprocess is executed.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import stat

SOURCE_ARCHIVE_SHA256 = 'b8fb480b8888321b864cf3c58a81cad3dfc223cc837071b940be58a93cca0e51'
ARCHIVE_PREFIX = 'formalizations/continuum-remainder-avoidance'
METADATA = {
    'format': 2,
    'release_date': '2026-10-07',
    'package': 'continuum-remainder-avoidance',
    'scope': 'Full ContinuumRemainder.ContinuumPowerTarget',
    'source_archive_sha256': SOURCE_ARCHIVE_SHA256,
    'archive_prefix': ARCHIVE_PREFIX,
}
SEAL_FILES = frozenset({'SOURCE_MANIFEST.json', 'SHA256SUMS'})
# Only these exact real directories are excluded; no other cache is ignored.
# Their contents are neither validated nor distributed.
RUNTIME_DIRECTORIES = frozenset({'.git', 'project/.lake', 'vendor', 'replay-evidence'})
DIGEST = re.compile(r'[0-9a-f]{64}\Z')
DERIVATIVE_LEDGER_SHA256 = 'd245f46210c9ee70cb9368d7dc0791592eedd3a23cfa5b1d3e55c11b0fc55f92'

FROZEN_METADATA_SHA256 = {
    "audit/independent/pins.json": "797c616885a5151f9910ac4e92544116e677fb3fc6363887ae35c6426311d4e4",
    "provenance/DEPENDENCY_PROVENANCE.json": "e652ec0d12158764e8f3cfd4fadca22984c1d6371664fc5bd0e1c35f9d61077a",
    "provenance/INPUT_ARCHIVE.json": "ccd09700e8df745e056dae6cbf2e6dd9983536459d2d0b36e2487a6a4acf21b9",
    "provenance/ORIGINAL_SOURCE_SHA256.json": "e32c9dacf5fcf2088edaf6a3a32fe74dbb21edb87449165e982bf952c1e832b3",
    "provenance/TOOLCHAIN_FILES_SHA256.json": "5ce0ade313b607222e8409a5bcbf1a7c2161ea1ef7ef5ba11edd11f8a45779e8",
    "submitted-evidence/MANIFEST.json": "521428348fb113864c6af3d010156ca18f91d97bdc9fac4bdadaf6da2af01fa4",
    "submitted-evidence/source-freeze.json": "48841d7974245af1cf7de677580ecec934ed6310bbbb21f2456cbe6b77081e71",
    "third_party_licenses/Cli/LICENSE": "f7e95706807e931782b6efd9a9d2789508a52423ad67b56ee7e5e324362d4aac",
    "third_party_licenses/LeanSearchClient/LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    "third_party_licenses/Qq/LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    "third_party_licenses/SHA256SUMS": "dbe057b2c131f769e176f12843902877ce60a3856914fb9143ad70e6543f8226",
    "third_party_licenses/aesop/LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    "third_party_licenses/batteries/LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    "third_party_licenses/importGraph/LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    "third_party_licenses/importGraph/html-template/LICENSE_source": "49110e6ed9990dbd0869c66bdae2882a9e74776094a12e87f25067979e777502",
    "third_party_licenses/lean4/LICENSE": "8b28515ffffc5c0fe2807d8ae3735b00b324d9b7ce807dd63ff6ac8922fbce7e",
    "third_party_licenses/lean4/LICENSES": "00cce2ac071f63d470a287438a7c6bbc4334706be244384e9af4fc9ead11cdce",
    "third_party_licenses/mathlib/LICENSE": "b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1",
    "third_party_licenses/openai_math_LICENSE.txt": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    "third_party_licenses/plausible/LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    "third_party_licenses/proofwidgets/LICENSE": "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4",
    "third_party_licenses/repository_NOTICE.md": "1f1d6f4638d99535bb113dce6efb142ea9404f669d135f624c927f8d78386542"
}

ORIGINAL_INPUT_FILES = frozenset([
    "audit/controls/base-negative/DropBoundaryZero.lean",
    "audit/controls/base-negative/HostileClosedActivation.lean",
    "audit/controls/base-negative/HostileDefaultReadOmission.lean",
    "audit/controls/base-negative/HostileDuplicateOwn.lean",
    "audit/controls/base-negative/HostileDuplicateTerminal.lean",
    "audit/controls/base-negative/HostileMissingGap.lean",
    "audit/controls/base-negative/HostileReverseRefinement.lean",
    "audit/controls/base-negative/HostileRightBoundary.lean",
    "audit/controls/base-negative/HostileRootAbsolutePosition.lean",
    "audit/controls/base-negative/HostileRootNegativeCoefficient.lean",
    "audit/controls/base-negative/HostileRootPZero.lean",
    "audit/controls/base-negative/HostileRootPositionFreeEntropy.lean",
    "audit/controls/base-negative/HostileRootSmallExceptional.lean",
    "audit/controls/base-negative/HostileRootWrapEndpoint.lean",
    "audit/controls/base-negative/HostileZeroActivation.lean",
    "audit/controls/base-negative/IgnoreSignCrossing.lean",
    "audit/controls/base-negative/assign_grid_boundary_to_left_cell.lean",
    "audit/controls/base-negative/drop_open_window_loss.lean",
    "audit/controls/base-negative/expected.json",
    "audit/controls/base-negative/include_left_boundary.lean",
    "audit/controls/base-negative/log_the_zero_center_boundary.lean",
    "audit/controls/base-negative/omit_coefficient_shift.lean",
    "audit/controls/base-negative/strict_buffer_budget_without_positive_p.lean",
    "audit/controls/base-positive/APIProbe.lean",
    "audit/controls/base-positive/ArrangementAudit.lean",
    "audit/controls/base-positive/Audit.lean",
    "audit/controls/base-positive/BoundaryControls.lean",
    "audit/controls/base-positive/GridBoundaryControls.lean",
    "audit/controls/base-positive/LocalBoundaryControls.lean",
    "audit/controls/base-positive/MainTargetProbe.lean",
    "audit/controls/base-positive/ProjectionBoundaryControls.lean",
    "audit/controls/base-positive/geometry_evidence_ActiveAxiomAudit.lean",
    "audit/controls/base-positive/geometry_evidence_AxiomAudit.lean",
    "audit/controls/base-positive/geometry_evidence_CandidateAxiomAudit.lean",
    "audit/controls/base-positive/geometry_evidence_PositiveControls.lean",
    "audit/controls/base-positive/geometry_evidence_PreorderAxiomAudit.lean",
    "audit/controls/base-positive/probability_evidence_ProbabilityAudit.lean",
    "audit/controls/base-positive/probability_evidence_center_atom_evidence_CenterAtomAudit.lean",
    "audit/controls/base-positive/probability_evidence_measure_evidence_MeasureAudit.lean",
    "audit/controls/base-positive/probability_evidence_no_default_evidence_NoDefaultAudit.lean",
    "audit/controls/base-positive/probability_evidence_probability_controls_ProbabilityControls.lean",
    "audit/controls/base-positive/repair_evidence_BoundaryAudit.lean",
    "audit/controls/base-positive/repair_evidence_RootAssemblyAudit.lean",
    "audit/controls/base-positive/repair_evidence_StableBoundaryAudit.lean",
    "audit/controls/submitted-negative/ClosedActivationLowerEndpoint.lean",
    "audit/controls/submitted-negative/ClosedActivationUpperEndpoint.lean",
    "audit/controls/submitted-negative/DroppedExponentUpperBound.lean",
    "audit/controls/submitted-negative/DroppedNonnegativeOutputShift.lean",
    "audit/controls/submitted-negative/SingleBufferErrorEndpoint.lean",
    "audit/controls/submitted-negative/ZeroRemainderRate.lean",
    "project/APIProbe.lean",
    "project/ArrangementAudit.lean",
    "project/Audit.lean",
    "project/BoundaryControls.lean",
    "project/ContinuumGeometric.lean",
    "project/ContinuumGeometric/Activation.lean",
    "project/ContinuumGeometric/BoundedGrid.lean",
    "project/ContinuumGeometric/CandidateBounds.lean",
    "project/ContinuumGeometric/ClosedProjection.lean",
    "project/ContinuumGeometric/ClosedRepair.lean",
    "project/ContinuumGeometric/CoefficientCover.lean",
    "project/ContinuumGeometric/CountableExhaustion.lean",
    "project/ContinuumGeometric/EntropySchedule.lean",
    "project/ContinuumGeometric/FiniteRoutingProbability.lean",
    "project/ContinuumGeometric/GeometricParameters.lean",
    "project/ContinuumGeometric/GeometryChain.lean",
    "project/ContinuumGeometric/GridCutBridge.lean",
    "project/ContinuumGeometric/Interfaces.lean",
    "project/ContinuumGeometric/LineSignBound.lean",
    "project/ContinuumGeometric/LocalSignatures.lean",
    "project/ContinuumGeometric/MainProof.lean",
    "project/ContinuumGeometric/NoDefaultProbability.lean",
    "project/ContinuumGeometric/PeriodicRepair.lean",
    "project/ContinuumGeometric/Planar.lean",
    "project/ContinuumGeometric/RoutingActiveGeometry.lean",
    "project/ContinuumGeometric/RoutingAssembly.lean",
    "project/ContinuumGeometric/RoutingCenterAtoms.lean",
    "project/ContinuumGeometric/RoutingChoices.lean",
    "project/ContinuumGeometric/RoutingEntropy.lean",
    "project/ContinuumGeometric/RoutingFactorization.lean",
    "project/ContinuumGeometric/RoutingGeometry.lean",
    "project/ContinuumGeometric/RoutingGlobalGrid.lean",
    "project/ContinuumGeometric/RoutingInterfaces.lean",
    "project/ContinuumGeometric/RoutingLocalHit.lean",
    "project/ContinuumGeometric/RoutingLocalProbability.lean",
    "project/ContinuumGeometric/RoutingMeasure.lean",
    "project/ContinuumGeometric/RoutingModel.lean",
    "project/ContinuumGeometric/RoutingPreorder.lean",
    "project/ContinuumGeometric/RoutingProbability.lean",
    "project/ContinuumGeometric/RoutingSchedule.lean",
    "project/ContinuumGeometric/RoutingSeparation.lean",
    "project/ContinuumGeometric/RoutingStableGeometry.lean",
    "project/ContinuumGeometric/RoutingStableMeasure.lean",
    "project/ContinuumGeometric/RoutingStableProbability.lean",
    "project/ContinuumGeometric/RoutingTemplate.lean",
    "project/ContinuumGeometric/RoutingTreeBounds.lean",
    "project/ContinuumGeometric/ShiftedActivation.lean",
    "project/ContinuumGeometric/SignFiberCount.lean",
    "project/ContinuumGeometric/Target.lean",
    "project/ContinuumGeometric/ZeroErrorBuffer.lean",
    "project/ContinuumRemainder.lean",
    "project/ContinuumRemainder/Counting.lean",
    "project/ContinuumRemainder/DistinctMisses.lean",
    "project/ContinuumRemainder/ErrorDomination.lean",
    "project/ContinuumRemainder/ErrorSchedule.lean",
    "project/ContinuumRemainder/Exhaustion.lean",
    "project/ContinuumRemainder/FinalProof.lean",
    "project/ContinuumRemainder/LogGeometry.lean",
    "project/ContinuumRemainder/LogRouting.lean",
    "project/ContinuumRemainder/LogRoutingProbability.lean",
    "project/ContinuumRemainder/LogSignatures.lean",
    "project/ContinuumRemainder/RobustAssembly.lean",
    "project/ContinuumRemainder/RobustRepair.lean",
    "project/ContinuumRemainder/SampleLocalProbability.lean",
    "project/ContinuumRemainder/SampleSchedule.lean",
    "project/ContinuumRemainder/SampleStableProbability.lean",
    "project/ContinuumRemainder/Sampling.lean",
    "project/ContinuumRemainder/Specification.lean",
    "project/ContinuumRemainder/TopologyConclusion.lean",
    "project/GridBoundaryControls.lean",
    "project/LocalBoundaryControls.lean",
    "project/MainTargetProbe.lean",
    "project/ProjectionBoundaryControls.lean",
    "project/PublicTheorems.json",
    "project/candidate_bounds_scratch/AxiomAudit.lean",
    "project/candidate_bounds_scratch/PreorderAxiomAudit.lean",
    "project/candidate_bounds_scratch/PreorderChecks.lean",
    "project/geometry_evidence/ActiveAxiomAudit.lean",
    "project/geometry_evidence/AxiomAudit.lean",
    "project/geometry_evidence/CandidateAxiomAudit.lean",
    "project/geometry_evidence/HostileClosedActivation.lean",
    "project/geometry_evidence/HostileDefaultReadOmission.lean",
    "project/geometry_evidence/HostileDuplicateOwn.lean",
    "project/geometry_evidence/HostileDuplicateTerminal.lean",
    "project/geometry_evidence/HostileMissingGap.lean",
    "project/geometry_evidence/HostileReverseRefinement.lean",
    "project/geometry_evidence/HostileRightBoundary.lean",
    "project/geometry_evidence/HostileZeroActivation.lean",
    "project/geometry_evidence/PositiveControls.lean",
    "project/geometry_evidence/PreorderAxiomAudit.lean",
    "project/grid_geometry_scratch/AxiomAudit.lean",
    "project/lake-manifest.json",
    "project/lakefile.toml",
    "project/lean-toolchain",
    "project/probability_evidence/ProbabilityAudit.lean",
    "project/probability_evidence/center_atom_evidence/CenterAtomAudit.lean",
    "project/probability_evidence/measure_evidence/MeasureAudit.lean",
    "project/probability_evidence/no_default_evidence/NoDefaultAudit.lean",
    "project/probability_evidence/probability_controls/ProbabilityControls.lean",
    "project/remainder_evidence/ExhaustionAudit.lean",
    "project/remainder_evidence/SampleStableAudit.lean",
    "project/repair_evidence/BoundaryAudit.lean",
    "project/repair_evidence/HostileRootAbsolutePosition.lean",
    "project/repair_evidence/HostileRootNegativeCoefficient.lean",
    "project/repair_evidence/HostileRootPZero.lean",
    "project/repair_evidence/HostileRootPositionFreeEntropy.lean",
    "project/repair_evidence/HostileRootSmallExceptional.lean",
    "project/repair_evidence/HostileRootWrapEndpoint.lean",
    "project/repair_evidence/RobustErrorCountercontrols.lean",
    "project/repair_evidence/RobustErrorEvidence.lean",
    "project/repair_evidence/RootAssemblyAudit.lean",
    "project/repair_evidence/StableBoundaryAudit.lean",
    "project/sampling_evidence/FinalTargetAudit.lean",
    "project/sampling_evidence/SamplingAudit.lean",
    "submitted-evidence/ExpandedTargetProbe.lean",
    "submitted-evidence/KernelReplay.lean",
    "submitted-evidence/MANIFEST.json",
    "submitted-evidence/WRITTEN_PROOF.txt",
    "submitted-evidence/base-source-comparison.json",
    "submitted-evidence/kernel-trust-zero-fresh.log",
    "submitted-evidence/kernel-trust-zero.log",
    "submitted-evidence/normal-pass/axioms.log",
    "submitted-evidence/normal-pass/build.log",
    "submitted-evidence/normal-pass/remainder_evidence-ExhaustionAudit.log",
    "submitted-evidence/normal-pass/remainder_evidence-SampleStableAudit.log",
    "submitted-evidence/normal-pass/repair_evidence-RobustErrorCountercontrols.log",
    "submitted-evidence/normal-pass/repair_evidence-RobustErrorEvidence.log",
    "submitted-evidence/normal-pass/report.json",
    "submitted-evidence/normal-pass/sampling_evidence-FinalTargetAudit.log",
    "submitted-evidence/normal-pass/sampling_evidence-SamplingAudit.log",
    "submitted-evidence/optimized-pass/axioms.log",
    "submitted-evidence/optimized-pass/build.log",
    "submitted-evidence/optimized-pass/remainder_evidence-ExhaustionAudit.log",
    "submitted-evidence/optimized-pass/remainder_evidence-SampleStableAudit.log",
    "submitted-evidence/optimized-pass/repair_evidence-RobustErrorCountercontrols.log",
    "submitted-evidence/optimized-pass/repair_evidence-RobustErrorEvidence.log",
    "submitted-evidence/optimized-pass/report.json",
    "submitted-evidence/optimized-pass/sampling_evidence-FinalTargetAudit.log",
    "submitted-evidence/optimized-pass/sampling_evidence-SamplingAudit.log",
    "submitted-evidence/source-freeze.json"
])

EXPECTED_FILES = frozenset([
    ".gitignore",
    "LICENSE_NOTICE.md",
    "PROOF_ROADMAP.md",
    "PROVENANCE.md",
    "README.md",
    "SHA256SUMS",
    "SOURCE_MANIFEST.json",
    "THEOREM.md",
    "VERIFICATION.md",
    "audit/checks/AllPublicAxioms.lean",
    "audit/checks/ClosureAudit.lean",
    "audit/checks/ExactMain.lean",
    "audit/checks/ReplayAllSafeOwned.lean",
    "audit/checks/ReplayClosure.lean",
    "audit/checks/SemanticProbe.lean",
    "audit/controls/base-negative/DropBoundaryZero.lean",
    "audit/controls/base-negative/HostileClosedActivation.lean",
    "audit/controls/base-negative/HostileDefaultReadOmission.lean",
    "audit/controls/base-negative/HostileDuplicateOwn.lean",
    "audit/controls/base-negative/HostileDuplicateTerminal.lean",
    "audit/controls/base-negative/HostileMissingGap.lean",
    "audit/controls/base-negative/HostileReverseRefinement.lean",
    "audit/controls/base-negative/HostileRightBoundary.lean",
    "audit/controls/base-negative/HostileRootAbsolutePosition.lean",
    "audit/controls/base-negative/HostileRootNegativeCoefficient.lean",
    "audit/controls/base-negative/HostileRootPZero.lean",
    "audit/controls/base-negative/HostileRootPositionFreeEntropy.lean",
    "audit/controls/base-negative/HostileRootSmallExceptional.lean",
    "audit/controls/base-negative/HostileRootWrapEndpoint.lean",
    "audit/controls/base-negative/HostileZeroActivation.lean",
    "audit/controls/base-negative/IgnoreSignCrossing.lean",
    "audit/controls/base-negative/assign_grid_boundary_to_left_cell.lean",
    "audit/controls/base-negative/drop_open_window_loss.lean",
    "audit/controls/base-negative/expected.json",
    "audit/controls/base-negative/include_left_boundary.lean",
    "audit/controls/base-negative/log_the_zero_center_boundary.lean",
    "audit/controls/base-negative/omit_coefficient_shift.lean",
    "audit/controls/base-negative/strict_buffer_budget_without_positive_p.lean",
    "audit/controls/base-positive/APIProbe.lean",
    "audit/controls/base-positive/ArrangementAudit.lean",
    "audit/controls/base-positive/Audit.lean",
    "audit/controls/base-positive/BoundaryControls.lean",
    "audit/controls/base-positive/GridBoundaryControls.lean",
    "audit/controls/base-positive/LocalBoundaryControls.lean",
    "audit/controls/base-positive/MainTargetProbe.lean",
    "audit/controls/base-positive/ProjectionBoundaryControls.lean",
    "audit/controls/base-positive/geometry_evidence_ActiveAxiomAudit.lean",
    "audit/controls/base-positive/geometry_evidence_AxiomAudit.lean",
    "audit/controls/base-positive/geometry_evidence_CandidateAxiomAudit.lean",
    "audit/controls/base-positive/geometry_evidence_PositiveControls.lean",
    "audit/controls/base-positive/geometry_evidence_PreorderAxiomAudit.lean",
    "audit/controls/base-positive/probability_evidence_ProbabilityAudit.lean",
    "audit/controls/base-positive/probability_evidence_center_atom_evidence_CenterAtomAudit.lean",
    "audit/controls/base-positive/probability_evidence_measure_evidence_MeasureAudit.lean",
    "audit/controls/base-positive/probability_evidence_no_default_evidence_NoDefaultAudit.lean",
    "audit/controls/base-positive/probability_evidence_probability_controls_ProbabilityControls.lean",
    "audit/controls/base-positive/repair_evidence_BoundaryAudit.lean",
    "audit/controls/base-positive/repair_evidence_RootAssemblyAudit.lean",
    "audit/controls/base-positive/repair_evidence_StableBoundaryAudit.lean",
    "audit/controls/independent/FinalNonvacuity.lean",
    "audit/controls/independent/HypothesisMutations.lean",
    "audit/controls/independent/SemanticControls.lean",
    "audit/controls/independent/UniversalFamilyControl.lean",
    "audit/controls/independent/negative/AlphaZeroCost.lean",
    "audit/controls/independent/negative/ClosedLowerActivation.lean",
    "audit/controls/independent/negative/ClosedUpperActivation.lean",
    "audit/controls/independent/negative/ConstantDistinctValues.lean",
    "audit/controls/independent/negative/EmptyLogSyndetic.lean",
    "audit/controls/independent/negative/OuterClosedEndpoint.lean",
    "audit/controls/submitted-negative/ClosedActivationLowerEndpoint.lean",
    "audit/controls/submitted-negative/ClosedActivationUpperEndpoint.lean",
    "audit/controls/submitted-negative/DroppedExponentUpperBound.lean",
    "audit/controls/submitted-negative/DroppedNonnegativeOutputShift.lean",
    "audit/controls/submitted-negative/SingleBufferErrorEndpoint.lean",
    "audit/controls/submitted-negative/ZeroRemainderRate.lean",
    "audit/independent/ACTUAL_MODULE_SOURCE_ARTIFACT_HASHES.json",
    "audit/independent/AUDIT_REPORT.md",
    "audit/independent/BOUNDARY_AUDIT_REPORT.txt",
    "audit/independent/FAST_CLOSURE_SUMMARY.json.gz",
    "audit/independent/FAST_OWNED_INVENTORY.json.gz",
    "audit/independent/FAST_PROOF_GRAPH.json.gz",
    "audit/independent/FINAL_AUDIT.json",
    "audit/independent/INDEPENDENT_PUBLIC_NAMES.json",
    "audit/independent/OWNED_MODULES.json",
    "audit/independent/PRODUCTION_GUARD_CONTROL.json",
    "audit/independent/REBUILD_AND_CONTROL_VERIFICATION.json",
    "audit/independent/SEMANTIC_REVIEW.md",
    "audit/independent/SOURCE_INSPECTION.json",
    "audit/independent/logs/AllPublicAxioms.log",
    "audit/independent/logs/ExactMain.log",
    "audit/independent/logs/FastClosureAudit.log",
    "audit/independent/logs/ReplayAllSafeOwned.log",
    "audit/independent/logs/ReplayClosure.log",
    "audit/independent/logs/SemanticProbe.log",
    "audit/independent/pins.json",
    "project/APIProbe.lean",
    "project/ArrangementAudit.lean",
    "project/Audit.lean",
    "project/BoundaryControls.lean",
    "project/ContinuumGeometric.lean",
    "project/ContinuumGeometric/Activation.lean",
    "project/ContinuumGeometric/BoundedGrid.lean",
    "project/ContinuumGeometric/CandidateBounds.lean",
    "project/ContinuumGeometric/ClosedProjection.lean",
    "project/ContinuumGeometric/ClosedRepair.lean",
    "project/ContinuumGeometric/CoefficientCover.lean",
    "project/ContinuumGeometric/CountableExhaustion.lean",
    "project/ContinuumGeometric/EntropySchedule.lean",
    "project/ContinuumGeometric/FiniteRoutingProbability.lean",
    "project/ContinuumGeometric/GeometricParameters.lean",
    "project/ContinuumGeometric/GeometryChain.lean",
    "project/ContinuumGeometric/GridCutBridge.lean",
    "project/ContinuumGeometric/Interfaces.lean",
    "project/ContinuumGeometric/LineSignBound.lean",
    "project/ContinuumGeometric/LocalSignatures.lean",
    "project/ContinuumGeometric/MainProof.lean",
    "project/ContinuumGeometric/NoDefaultProbability.lean",
    "project/ContinuumGeometric/PeriodicRepair.lean",
    "project/ContinuumGeometric/Planar.lean",
    "project/ContinuumGeometric/RoutingActiveGeometry.lean",
    "project/ContinuumGeometric/RoutingAssembly.lean",
    "project/ContinuumGeometric/RoutingCenterAtoms.lean",
    "project/ContinuumGeometric/RoutingChoices.lean",
    "project/ContinuumGeometric/RoutingEntropy.lean",
    "project/ContinuumGeometric/RoutingFactorization.lean",
    "project/ContinuumGeometric/RoutingGeometry.lean",
    "project/ContinuumGeometric/RoutingGlobalGrid.lean",
    "project/ContinuumGeometric/RoutingInterfaces.lean",
    "project/ContinuumGeometric/RoutingLocalHit.lean",
    "project/ContinuumGeometric/RoutingLocalProbability.lean",
    "project/ContinuumGeometric/RoutingMeasure.lean",
    "project/ContinuumGeometric/RoutingModel.lean",
    "project/ContinuumGeometric/RoutingPreorder.lean",
    "project/ContinuumGeometric/RoutingProbability.lean",
    "project/ContinuumGeometric/RoutingSchedule.lean",
    "project/ContinuumGeometric/RoutingSeparation.lean",
    "project/ContinuumGeometric/RoutingStableGeometry.lean",
    "project/ContinuumGeometric/RoutingStableMeasure.lean",
    "project/ContinuumGeometric/RoutingStableProbability.lean",
    "project/ContinuumGeometric/RoutingTemplate.lean",
    "project/ContinuumGeometric/RoutingTreeBounds.lean",
    "project/ContinuumGeometric/ShiftedActivation.lean",
    "project/ContinuumGeometric/SignFiberCount.lean",
    "project/ContinuumGeometric/Target.lean",
    "project/ContinuumGeometric/ZeroErrorBuffer.lean",
    "project/ContinuumRemainder.lean",
    "project/ContinuumRemainder/Counting.lean",
    "project/ContinuumRemainder/DistinctMisses.lean",
    "project/ContinuumRemainder/ErrorDomination.lean",
    "project/ContinuumRemainder/ErrorSchedule.lean",
    "project/ContinuumRemainder/Exhaustion.lean",
    "project/ContinuumRemainder/FinalProof.lean",
    "project/ContinuumRemainder/LogGeometry.lean",
    "project/ContinuumRemainder/LogRouting.lean",
    "project/ContinuumRemainder/LogRoutingProbability.lean",
    "project/ContinuumRemainder/LogSignatures.lean",
    "project/ContinuumRemainder/RobustAssembly.lean",
    "project/ContinuumRemainder/RobustRepair.lean",
    "project/ContinuumRemainder/SampleLocalProbability.lean",
    "project/ContinuumRemainder/SampleSchedule.lean",
    "project/ContinuumRemainder/SampleStableProbability.lean",
    "project/ContinuumRemainder/Sampling.lean",
    "project/ContinuumRemainder/Specification.lean",
    "project/ContinuumRemainder/TopologyConclusion.lean",
    "project/GridBoundaryControls.lean",
    "project/LocalBoundaryControls.lean",
    "project/MainTargetProbe.lean",
    "project/ProjectionBoundaryControls.lean",
    "project/PublicTheorems.json",
    "project/candidate_bounds_scratch/AxiomAudit.lean",
    "project/candidate_bounds_scratch/PreorderAxiomAudit.lean",
    "project/candidate_bounds_scratch/PreorderChecks.lean",
    "project/geometry_evidence/ActiveAxiomAudit.lean",
    "project/geometry_evidence/AxiomAudit.lean",
    "project/geometry_evidence/CandidateAxiomAudit.lean",
    "project/geometry_evidence/HostileClosedActivation.lean",
    "project/geometry_evidence/HostileDefaultReadOmission.lean",
    "project/geometry_evidence/HostileDuplicateOwn.lean",
    "project/geometry_evidence/HostileDuplicateTerminal.lean",
    "project/geometry_evidence/HostileMissingGap.lean",
    "project/geometry_evidence/HostileReverseRefinement.lean",
    "project/geometry_evidence/HostileRightBoundary.lean",
    "project/geometry_evidence/HostileZeroActivation.lean",
    "project/geometry_evidence/PositiveControls.lean",
    "project/geometry_evidence/PreorderAxiomAudit.lean",
    "project/grid_geometry_scratch/AxiomAudit.lean",
    "project/lake-manifest.json",
    "project/lakefile.toml",
    "project/lean-toolchain",
    "project/probability_evidence/ProbabilityAudit.lean",
    "project/probability_evidence/center_atom_evidence/CenterAtomAudit.lean",
    "project/probability_evidence/measure_evidence/MeasureAudit.lean",
    "project/probability_evidence/no_default_evidence/NoDefaultAudit.lean",
    "project/probability_evidence/probability_controls/ProbabilityControls.lean",
    "project/remainder_evidence/ExhaustionAudit.lean",
    "project/remainder_evidence/SampleStableAudit.lean",
    "project/repair_evidence/BoundaryAudit.lean",
    "project/repair_evidence/HostileRootAbsolutePosition.lean",
    "project/repair_evidence/HostileRootNegativeCoefficient.lean",
    "project/repair_evidence/HostileRootPZero.lean",
    "project/repair_evidence/HostileRootPositionFreeEntropy.lean",
    "project/repair_evidence/HostileRootSmallExceptional.lean",
    "project/repair_evidence/HostileRootWrapEndpoint.lean",
    "project/repair_evidence/RobustErrorCountercontrols.lean",
    "project/repair_evidence/RobustErrorEvidence.lean",
    "project/repair_evidence/RootAssemblyAudit.lean",
    "project/repair_evidence/StableBoundaryAudit.lean",
    "project/sampling_evidence/FinalTargetAudit.lean",
    "project/sampling_evidence/SamplingAudit.lean",
    "provenance/DEPENDENCY_PROVENANCE.json",
    "provenance/INPUT_ARCHIVE.json",
    "provenance/ORIGINAL_SOURCE_SHA256.json",
    "provenance/PUBLIC_DERIVATIVE_LEDGER.json",
    "provenance/TOOLCHAIN_FILES_SHA256.json",
    "scripts/make_archive.py",
    "scripts/release_integrity.py",
    "scripts/seal_release.py",
    "scripts/semantic_exact_checks.py",
    "scripts/test_release_integrity.py",
    "scripts/verify.py",
    "scripts/verify_integrity.py",
    "submitted-evidence/ExpandedTargetProbe.lean",
    "submitted-evidence/KernelReplay.lean",
    "submitted-evidence/MANIFEST.json",
    "submitted-evidence/README.original.txt",
    "submitted-evidence/WRITTEN_PROOF.txt",
    "submitted-evidence/base-source-comparison.json",
    "submitted-evidence/historical/CONTINUATION_CONTRACT.md",
    "submitted-evidence/historical/DEPENDENCIES.md",
    "submitted-evidence/kernel-replay-record.json",
    "submitted-evidence/kernel-trust-zero-fresh.log",
    "submitted-evidence/kernel-trust-zero.log",
    "submitted-evidence/normal-pass/axioms.log",
    "submitted-evidence/normal-pass/build.log",
    "submitted-evidence/normal-pass/negative-ClosedActivationLowerEndpoint.log",
    "submitted-evidence/normal-pass/negative-ClosedActivationUpperEndpoint.log",
    "submitted-evidence/normal-pass/negative-DroppedExponentUpperBound.log",
    "submitted-evidence/normal-pass/negative-DroppedNonnegativeOutputShift.log",
    "submitted-evidence/normal-pass/negative-SingleBufferErrorEndpoint.log",
    "submitted-evidence/normal-pass/negative-ZeroRemainderRate.log",
    "submitted-evidence/normal-pass/remainder_evidence-ExhaustionAudit.log",
    "submitted-evidence/normal-pass/remainder_evidence-SampleStableAudit.log",
    "submitted-evidence/normal-pass/repair_evidence-RobustErrorCountercontrols.log",
    "submitted-evidence/normal-pass/repair_evidence-RobustErrorEvidence.log",
    "submitted-evidence/normal-pass/report.json",
    "submitted-evidence/normal-pass/sampling_evidence-FinalTargetAudit.log",
    "submitted-evidence/normal-pass/sampling_evidence-SamplingAudit.log",
    "submitted-evidence/optimized-pass/axioms.log",
    "submitted-evidence/optimized-pass/build.log",
    "submitted-evidence/optimized-pass/negative-ClosedActivationLowerEndpoint.log",
    "submitted-evidence/optimized-pass/negative-ClosedActivationUpperEndpoint.log",
    "submitted-evidence/optimized-pass/negative-DroppedExponentUpperBound.log",
    "submitted-evidence/optimized-pass/negative-DroppedNonnegativeOutputShift.log",
    "submitted-evidence/optimized-pass/negative-SingleBufferErrorEndpoint.log",
    "submitted-evidence/optimized-pass/negative-ZeroRemainderRate.log",
    "submitted-evidence/optimized-pass/remainder_evidence-ExhaustionAudit.log",
    "submitted-evidence/optimized-pass/remainder_evidence-SampleStableAudit.log",
    "submitted-evidence/optimized-pass/repair_evidence-RobustErrorCountercontrols.log",
    "submitted-evidence/optimized-pass/repair_evidence-RobustErrorEvidence.log",
    "submitted-evidence/optimized-pass/report.json",
    "submitted-evidence/optimized-pass/sampling_evidence-FinalTargetAudit.log",
    "submitted-evidence/optimized-pass/sampling_evidence-SamplingAudit.log",
    "submitted-evidence/source-freeze.json",
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
    """Independent anchors survive attempted regeneration of the outer seal."""
    for name, digest in FROZEN_METADATA_SHA256.items():
        require(name in snapshot and sha256(snapshot[name]) == digest,
                'immutable metadata/license identity differs: ' + name)
    original = digest_map(json_value(snapshot['provenance/ORIGINAL_SOURCE_SHA256.json'],
                                      'original-source inventory'), 'original-source inventory')
    require(set(original) == ORIGINAL_INPUT_FILES, 'immutable original-source coverage differs')
    for name, digest in original.items():
        require(name in snapshot and sha256(snapshot[name]) == digest,
                'immutable submitted source/pin/evidence differs: ' + name)
    require(len([name for name in original if name.startswith('project/') and name.endswith('.lean')]) == 110,
            'submitted Lean-source count differs')
    freeze = digest_map(json_value(snapshot['submitted-evidence/source-freeze.json'],
                                   'submitted source-freeze'), 'submitted source-freeze')
    for name, digest in freeze.items():
        require(name in original and original[name] == digest, 'source-freeze binding differs: ' + name)
    require(type(DERIVATIVE_LEDGER_SHA256) is str and DIGEST.fullmatch(DERIVATIVE_LEDGER_SHA256) is not None,
            'final derivative ledger has not been explicitly bound by the maintainer')
    ledger_bytes = snapshot['provenance/PUBLIC_DERIVATIVE_LEDGER.json']
    require(sha256(ledger_bytes) == DERIVATIVE_LEDGER_SHA256, 'immutable public derivative ledger identity differs')
    ledger = json_value(ledger_bytes, 'public derivative ledger')
    require(type(ledger) is list and bool(ledger), 'public derivative ledger must be nonempty')
    seen = set()
    for row in ledger:
        require(type(row) is dict and set(row) == {'origin', 'original_sha256', 'public', 'public_sha256', 'change'},
                'public derivative ledger row schema differs')
        name = canonical_path(row['public'])
        require(name not in seen, 'duplicate public derivative target: ' + name)
        seen.add(name)
        require(type(row['origin']) is str and bool(row['origin']) and
                type(row['change']) is str and bool(row['change']), 'invalid derivative origin/change: ' + name)
        for field in ('original_sha256', 'public_sha256'):
            require(type(row[field]) is str and DIGEST.fullmatch(row[field]) is not None,
                    'invalid derivative digest: ' + name)
        require(name in snapshot and sha256(snapshot[name]) == row['public_sha256'],
                'preserved public derivative differs: ' + name)
        if row['change'] == 'byte-identical':
            require(row['original_sha256'] == row['public_sha256'], 'false byte-identical ledger claim: ' + name)
        if name in original:
            require(row['original_sha256'] == original[name] == row['public_sha256'],
                    'source provenance and derivative ledger disagree: ' + name)
    require(ORIGINAL_INPUT_FILES <= seen, 'derivative ledger omits immutable original inputs')
    required_derivatives = {name for name in EXPECTED_FILES
                            if name.startswith(('audit/checks/', 'audit/controls/', 'audit/independent/'))}
    require(required_derivatives <= seen, 'derivative ledger omits audit input/evidence: ' +
            repr(sorted(required_derivatives - seen)))
    license_hashes = {name: digest for name, digest in FROZEN_METADATA_SHA256.items()
                      if name.startswith('third_party_licenses/') and name != 'third_party_licenses/SHA256SUMS'}
    license_hashes['provenance/DEPENDENCY_PROVENANCE.json'] = FROZEN_METADATA_SHA256['provenance/DEPENDENCY_PROVENANCE.json']
    require(snapshot['third_party_licenses/SHA256SUMS'] == checksum_bytes(license_hashes),
            'license checksum coverage/path differs')


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
