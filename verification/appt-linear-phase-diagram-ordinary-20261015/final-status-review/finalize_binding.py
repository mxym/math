"""Emit a private final binding only; candidate/root files remain unmodified."""
from pathlib import Path
import datetime as dt
import hashlib
import json

HERE = Path(__file__).resolve().parent
RUN = HERE/'metadata-runs/20261015T140738.980442Z'
STAGE = HERE.parent/'phase-diagram-publication'

def digest(path):
    data = path.read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def dump(name, value):
    target = HERE/name
    assert not target.exists(), 'Never overwrite a prior final report or binding.'
    target.write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')

def main():
    checked = json.loads((RUN/'RESULT.json').read_text())
    assert checked['status'] == checked['decision'] == 'PASS'
    manifest = json.loads((HERE/'stage-inputs/FINAL_CANDIDATE_INPUTS.json').read_text())
    assert digest(STAGE/'FINAL_CANDIDATE_INPUTS.json') == digest(HERE/'stage-inputs/FINAL_CANDIDATE_INPUTS.json')
    for rel, info in checked['candidate_files'].items():
        if rel in ('README.md', 'README.en.md', 'RESEARCH.md'):
            current = STAGE/'index-candidates'/rel
        else:
            name, dest = next((name, dest) for name, dest in manifest['new_projects'].items() if rel.startswith(dest+'/'))
            current = STAGE/'public-sources'/name/rel[len(dest)+1:]
        assert digest(current) == info, rel
    now = dt.datetime.now(dt.timezone.utc).isoformat()
    correction = json.loads((HERE/'FIRST_FAILURE_RECORD_CORRECTION.json').read_text())
    assert correction['correct_value'] is None
    report = {'status': 'PASS', 'decision': 'PASS', 'utc': now,
              'kind': 'New independent final source/status/README/index binding only, following four already completed exact-source ordinary mathematical reads.',
              'source_base': checked['source_base'], 'candidate_manifest': checked['input_manifest'],
              'candidate_file_count': 248, 'immutable_owner_files': 50,
              'current_public_independent_durable_files': 186, 'only_excluded_runtime_cache_count': 15,
              'three_exact_changed_rows': checked['three_index_changes'],
              'mathematical_source_versions': checked['four_math_sources_unchanged'],
              'four_prior_mathematical_decisions': checked['four_separate_math_reports'],
              'current_prose_complete_reads': ['research/appt-linear-phase-diagram-20261015/README.md',
                     'research/appt-linear-phase-diagram-20261015/STATUS.md',
                     'verification/appt-linear-phase-diagram-ordinary-20261015/README.md',
                     'research/appt-linear-phase-diagram-20261015/REVIEW.md'],
              'indices_actual_read_scope': 'All three changed rows and complete exact diffs/context; every other original index byte and URL occurrence preserved mechanically. No new review of all unrelated older mathematics.',
              'mathematical_read_in_this_binding_step': False, 'mathematical_controls_reexecuted': False,
              'scope_accuracy': ['Complete scalar allc>0/r>=0 diagram and full tied argmax classes',
                     'Rational unique cstar enclosure and nondegenerate mixed/triple phase follow exact four reviewed sources',
                     'Original fixed-positive-c finite-r S matrix window, m->infinity and integern>=m, original complex all-global-unitary APPT',
                     'Full scalar-distance/J/actual-peak losses, ties, alternation and physical attainment retained',
                     'No one-sided selection at shrinking gap, L2 interior peak formula, simultaneousc->0 physical theorem or unrestricted all-order rigidity added',
                     'Earlier small-c/threshold source URL retained; previous value and S proofs not claimed new',
                     'Author interval replay distinct from independent helper and from Lean'],
              'actual_metadata_execution': {'run': RUN.relative_to(HERE).as_posix(), 'result': digest(RUN/'RESULT.json'),
                     'checker': digest(RUN/'verify_candidate.py'), 'candidate_files': 248, 'owner_git_objects': 50,
                     'independent_durable_files': 186, 'canonical_paths': 426, 'anchors': 22},
              'retained_failures': {'parent_preflight': 'Original real staged-directory rejection plus original source/trace copied in stage-inputs; not a reviewer execution.',
                     'reviewer_first_comparison': 'Actual initial stdin equality failure and same-source reproduction, because15 explicit interpreter caches were not excluded.',
                     'same_source_reproduction': 'metadata-runs/20261015T140339.715815Z',
                     'metadata_record_correction': {'path': 'FIRST_FAILURE_RECORD_CORRECTION.json', **digest(HERE/'FIRST_FAILURE_RECORD_CORRECTION.json'),
                         'effect': 'Unverified original-tool-ID placeholder corrected to null; old record/harness preserved and not valid provenance. Actual assertion/source/returncode unaffected.'},
                     'original_mathematical_failures': 'All original durable old replay/control/negative records retained byte-identically; no new mathematical replay.'},
              'self_binding_link': checked['pending_self_binding_installation'],
              'publication_layout_transport_plot_Lean_or_new_mathematics_certified': False,
              'candidate_or_root_mutated': False,
              'full_report': {'path': 'FINAL_STATUS_REVIEW.md', **digest(HERE/'FINAL_STATUS_REVIEW.md')}}
    dump('FINAL_STATUS_REVIEW.json', report)
    stage_files = {p.relative_to(HERE/'stage-inputs').as_posix(): digest(p) for p in sorted((HERE/'stage-inputs').rglob('*')) if p.is_file()}
    binding = {'status': 'PASS', 'decision': 'PASS', 'utc': now,
               'kind': 'Exact final metadata/source/status/README/index binding by an independent internal AI agent; no new mathematics/control/Lean execution.',
               'source_base': checked['source_base'], 'candidate_manifest': checked['input_manifest'],
               'bound_candidate_file_count': 248, 'bound_candidate_files': checked['candidate_files'],
               'stage_receipt_and_script_bytes_only': stage_files,
               'stage_scripts_not_executed_or_semantically_approved_for_mutations': ['preflight.py', 'integrate.py', 'commit.py', 'transport.py', 'push.py', 'sync_origin.py'],
               'immutable_owner_source_commit': checked['owner_source_commit'], 'immutable_owner_file_count': 50,
               'four_exact_mathematical_source_hashes': checked['four_math_sources_unchanged'],
               'four_previously_completed_mathematical_reads': checked['four_separate_math_reports'],
               'current_prose_range_checked_against_those_reports': True,
               'three_index_bindings': checked['three_index_changes'],
               'public_independent_copy': {'durable_files_byte_identical': 186,
                    'original_private_total_files': 201,
                    'only_excluded_generated_interpreter_bytecode_files': checked['excluded_private_interpreter_caches'],
                    'all_sources_results_reports_ZIPs_and_failures_retained': True},
               'navigation': {'canonical_paths_checked': 426, 'fragments_checked': 22,
                    'existing_staged_directory_links_supported': True,
                    'pending_self_binding_installation_and_readback': checked['pending_self_binding_installation']},
               'reports': {'FINAL_STATUS_REVIEW.md': digest(HERE/'FINAL_STATUS_REVIEW.md'),
                           'FINAL_STATUS_REVIEW.json': digest(HERE/'FINAL_STATUS_REVIEW.json'),
                           'FIRST_FAILURE_RECORD_CORRECTION.json': digest(HERE/'FIRST_FAILURE_RECORD_CORRECTION.json')},
               'independent_metadata_run': {'path': RUN.relative_to(HERE).as_posix(), 'RESULT.json': digest(RUN/'RESULT.json'),
                    'program': digest(RUN/'verify_candidate.py')},
               'same_binding_may_be_installed_by_root_at': ['research/appt-linear-phase-diagram-20261015/FINAL_STATUS_BINDING.json',
                     'verification/appt-linear-phase-diagram-ordinary-20261015/FINAL_STATUS_BINDING.json'],
               'no_candidate_file_was_written_by_reviewer': True,
               'self_reference_exclusions': ['This FINAL_STATUS_BINDING.json itself and its future identical installed copies',
                    'The new final review output directory subsequently copied into evidence; it was not part of the248 candidate inputs. Its two reports are separately hash-bound above.',
                    'Future generated transport/integration/readback receipts and files created after this binding'],
               'limits': ['Previously reviewed mathematical scopes are unchanged; no fresh proof review or numeric/certificate/Lean rerun',
                    'No S5/X/laterS6 or new mathematical scope automatically covered',
                    'No new interval engine, complete all-order rigidity, finite exact optimizer, human peer review, priority or major count',
                    'No future layout/copy/commit/push/plot or original Lean audit guarantee'],
               'actual_output_location': str(HERE),
               'earlier_real_metadata_failures_and_null_record_correction_retained': True}
    dump('FINAL_STATUS_BINDING.json', binding)
    print(json.dumps({'status': 'PASS', 'decision': 'PASS', 'binding': digest(HERE/'FINAL_STATUS_BINDING.json'),
                      'FINAL_STATUS_REVIEW.md': digest(HERE/'FINAL_STATUS_REVIEW.md'),
                      'FINAL_STATUS_REVIEW.json': digest(HERE/'FINAL_STATUS_REVIEW.json'),
                      'candidate_files_mutated': False}, indent=2))

if __name__ == '__main__':
    main()
