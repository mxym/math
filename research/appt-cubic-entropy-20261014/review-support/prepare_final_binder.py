from pathlib import Path
p=Path('/mnt/d/math/tmp/appt-cubic-entropy-20261014/independent-review')
s=(p/'bind_review.py').read_text()
def replace_once(old,new):
    global s
    assert s.count(old)==1,(old,s.count(old))
    s=s.replace(old,new)
replace_once("assert sha(source/'PAPER.md')==initial_hash\nassert sha(source/'THEOREM_MAP.md')=='345a73ef453836b9d57137b2bfc1995f16c3662b483074527df4ea43f2e1a1fb'",'''final_hash='a2e940d320950c258d2aed13bb5afa81ea3bc41efa74acc09dca703d0a817449'
assert sha(source/'PAPER.md')==final_hash
paper_final=(source/'PAPER.md').read_bytes()
new_status=b'Ordinary written proof, 14 October 2026. Independently reviewed. All orders are fixed'
old_status=b'Private research draft, 14 October 2026. Unreviewed. All orders below are fixed'
assert paper_final.count(new_status)==1
assert hashlib.sha256(paper_final.replace(new_status,old_status)).hexdigest()==initial_hash
assert sha(source/'INITIAL_THEOREM_MAP.md')=='345a73ef453836b9d57137b2bfc1995f16c3662b483074527df4ea43f2e1a1fb'
assert sha(source/'THEOREM_MAP.md')=='50dd9a5c171e0efcd65848f5c6e9fca3065d31f9c99b38382ca70d7c0484c693'
map_final=(source/'THEOREM_MAP.md').read_bytes()
map_reversed=map_final.replace(b'14 October2026. This map preceded the manuscript. C0-C4 now have a complete\\nordinary written proof and independent mathematical review; no Lean claim.',b'14 October2026. Private active research map; unreviewed, no README or Lean claim.')
map_reversed=map_reversed.replace(b'C2/C3 are now proved with the complete actual upper. Atalpha2 the full\\ndelta_crit=1/4. Foralpha<2 the unrestricted graph formula is retained;\\none positive anomaly is insufficient already atalpha1. Existing growingm first-nonzero laws,',b'Candidates C2/C3 are not yet proved. Atalpha2 the one-positive trial gives\\ndelta_crit=1/4, but a complete actual upper is required. Foralpha<2 one\\nexception is not presumed sufficient. Existing growingm first-nonzero laws,')
assert hashlib.sha256(map_reversed).hexdigest()==sha(source/'INITIAL_THEOREM_MAP.md')
''')
replace_once("'THEOREM_MAP.md':{'actual_read_ranges':[[1,18]],'total_lines':18,'sha256':sha(source/'THEOREM_MAP.md')}","'INITIAL_THEOREM_MAP.md':{'actual_read_ranges':[[1,18]],'total_lines':18,'sha256':sha(source/'INITIAL_THEOREM_MAP.md')}")
replace_once("'mathematical_line_changes_from_initial':[],'binding':'Final file has identical bytes/hash to fully read initial file.'","'mathematical_line_changes_from_initial':[],'actual_nonmathematical_changed_lines':[[3,3]],'actual_delta_context_read':[[1,6]],'binding':'Reversing the sole disclosed status line restores the exact SHA256 of the fully read initial file; no second complete final reread claimed.'")
replace_once("(out/'REVIEW.json').write_text(json.dumps(record,indent=2)+'\\n')",'''record['coverage']['THEOREM_MAP.md']={'actual_read_ranges':[[1,19]],'total_lines':19,'sha256':sha(source/'THEOREM_MAP.md'),'delta':'Initial line3 status split into final lines3-4; initial lines14-16 replaced by final15-17 outcome description. Reverse substitutions restore the exact initial-map hash. The C0-C4 target rows are unchanged.'}
record['coverage']['README.md']={'actual_read_ranges':[[1,36]],'total_lines':36,'sha256':sha(source/'README.md'),'result':'PASS: fixed-order ordinary result and finite-versus-asymptotic limits disclosed; no formal or broad major-conjecture claim.'}
record['coverage']['LITERATURE.md']={'actual_read_ranges':[[1,46]],'total_lines':46,'sha256':sha(source/'LITERATURE.md'),'result':'PASS for bounded screen/provenance statements, not priority certification.'}
record['supplemental_primary_reading']=[
 {'url':'https://arxiv.org/abs/2608.03390','scope':'Metadata/abstract and version history; v2 18 September 2026 verified.'},
 {'url':'https://arxiv.org/html/2608.03390v2','actual_rendered_context_read':[[862,954]],'scope':'Includes Theorem6.10 polytope entropy domain; not a complete paper audit.'},
 {'url':'https://arxiv.org/abs/2609.18568','scope':'Metadata/abstract and version history; v1 16 September 2026 verified.'},
 {'url':'https://arxiv.org/html/2609.18568v1','actual_rendered_context_read':[[286,373]],'scope':'Includes Section3 outer-polytope entropy statement; not a complete qubit-proof review.'},
 {'url':'https://arxiv.org/abs/2609.06617','scope':'Metadata/abstract and version history; v1 6 September 2026 verified. Ky Fan partial-transpose graph optimization domain only; no full paper audit.'}]
record['source_bindings']={n:sha(source/n) for n in ['PAPER.md','INITIAL_PAPER.md','THEOREM_MAP.md','INITIAL_THEOREM_MAP.md','README.md','LITERATURE.md','check_cubic.py','FINITE_CONTROLS.json']}
record['binding_guard_event']={'event':'Initial helper rejected the changed final PAPER hash before any review output was written. The author had meanwhile disclosed one status edit. The final helper independently reverses that single byte substitution to validate all mathematical bytes against the reviewed initial source.','mathematical_control_failure':False}
(out/'BINDING_GUARD_EVENT.json').write_text(json.dumps(record['binding_guard_event'],indent=2)+'\\n')
(out/'REVIEW.json').write_text(json.dumps(record,indent=2)+'\\n')''')
replace_once("- THEOREM_MAP.md: complete 1-18, SHA256 `{sha(source/'THEOREM_MAP.md')}`.\n- PAPER.md remains byte-identical to the fully read initial manuscript. No\n  mathematical line changed, and no second complete final reread is claimed.","- INITIAL_THEOREM_MAP.md: complete 1-18, SHA256 `{sha(source/'INITIAL_THEOREM_MAP.md')}`.\n- Final PAPER.md changes only the disclosed nonmathematical status at line3.\n  Its final SHA256 is `{sha(source/'PAPER.md')}`. Reversing that sole change\n  restores the exact initial hash. No mathematical line changed, and no\n  second complete final reread is claimed. Delta context 1-6 was read.\n- Final THEOREM_MAP.md: complete 1-19, SHA256 `{sha(source/'THEOREM_MAP.md')}`.\n  Only status and outcome descriptions changed. Its target rows are intact,\n  and reversing the disclosed edits restores the exact initial-map hash.\n- README.md: complete 1-36; LITERATURE.md: complete 1-46. Both supplementary\n  sources were checked separately and are bound in REVIEW.json.")
replace_once("No Lean execution, audit expansion, catalog edit, commit, submission,\npublication, or external novelty claim was performed by this reviewer.","The supplemental literature metadata were independently checked against the\nprimary arXiv sources: AAW v2 (18 September 2026), Tran v1 (16 September\n2026), Jiang/Qiu/Yu v1 (6 September 2026). Actual contextual reads were AAW\nrendered 862-954 and Tran rendered 286-373, plus metadata/abstracts. Their\ndisclosed domains agree with the bounded literature screen. This is not a\nfull paper audit or an originality certificate.\n\nThe initial binding helper safely rejected the newly changed status bytes\nbefore writing any review output. The final helper validated the declared\nbyte deltas explicitly; this was not a mathematical control failure.\n\nNo Lean execution, audit expansion, catalog edit, commit, submission,\npublication, or external novelty claim was performed by this reviewer.")
(p/'bind_review_final.py').write_text(s)
print('Final binder written with explicit reverse-hash gates.')