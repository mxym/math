"""Validate the explicit repository path base of identical project-root bindings."""
from pathlib import Path
import json,sys,hashlib
source=Path(sys.argv[1]);binding=json.loads(source.read_bytes())
base=Path(__file__).resolve().parent
prefix='verification/appt-spectral-closeout-ordinary-20261015/final-status-review/'
for field,name in [('review_report','FINAL_STATUS_REVIEW.md'),('review_decision','FINAL_STATUS_REVIEW.json')]:
    item=binding[field]
    assert item.get('path_base')=='repository_root',('missing explicit repository-root path base',field,item)
    assert item.get('repository_path')==prefix+name,('wrong repository-relative report target',field,item)
    assert item['sha256']==hashlib.sha256((base/name).read_bytes()).hexdigest(),('wrong bound report hash',field)
print(json.dumps({'status':'PASS','binding_repository_paths':'Explicit repository_root targets for both report and decision; consistent for all four project-root copies'}))
