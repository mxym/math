from pathlib import Path
import datetime,json
from review_helpers import *
out=Path(__file__).resolve().parent
records=[]
def reject(name,call):
    try:call()
    except AssertionError as e:records.append({'name':name,'rejected':True,'exception':'AssertionError','message':str(e)})
    else:raise RuntimeError('Accepted false metadata '+name)
row={'sha256':sha(b'original paper'),'bytes':14}
exact_hash(b'original paper',row)
reject('one_byte_paper_change',lambda:exact_hash(b'original Paper',row))
old='# Index\n[old](https://example.test/unchanged#anchor)\nOld six-class row\n'
new=old+'S7 and S8 row\nS9 and Rglob row\n'
require_old_text_preserved(old,new)
oldphase='| phase | [existing](research/appt-linear-phase-diagram-20261015/README.md) |\n'
newphase='| phase and slices | [existing](research/appt-linear-phase-diagram-20261015/README.md); [new](research/appt-coexistence-orientation-20261015/README.md) |\n'
require_old_text_preserved(old+oldphase,old+newphase+'S7 row\nS9/Rglob row\n',allow_phase_row_update=True)
reject('old_url_changed',lambda:require_old_text_preserved(old,new.replace('/unchanged','/changed')))
reject('old_six_class_text_deleted',lambda:require_old_text_preserved(old,new.replace('Old six-class row\n','')))
text='# Canonical heading\n\n<a id="explicit-anchor"></a>\n## Canonical heading\n'
require_anchor(text,'canonical-heading');require_anchor(text,'canonical-heading-1');require_anchor(text,'explicit-anchor')
reject('broken_fragment',lambda:require_anchor(text,'nonexistent-anchor'))
reject('repository_escape',lambda:local_target('README.md','../../private/STATE.json'))
reject('S8_quantum_window_promoted',lambda:reject_scope_label('S8','physical c->infinity'))
reject('S9_promoted_to_fixed_m',lambda:reject_scope_label('S9','fixed-m extension'))
reject('benchmark_limit_omitted',lambda:reject_scope_label('Rglob','benchmark all fixed D'))
(out/'HELPER_NEGATIVE_CONTROLS.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'purpose':'Metadata helper diagnostics only; not final batch decision or mathematical checks','positive_controls':'Literal hash, exactly two inserted rows, explicitly whitelisted phase-row update, duplicate/explicit anchors accepted','helper_source_sha256':sha((out/'review_helpers.py').read_bytes()),'control_source_sha256':sha(Path(__file__).read_bytes()),'actual_expected_assertion_failures':records,'unexpected_failures':[]},indent=2)+'\n')
print(json.dumps({'expected_metadata_negative_failures':len(records),'unexpected_failures':0,'final_pass_signed':False}))
