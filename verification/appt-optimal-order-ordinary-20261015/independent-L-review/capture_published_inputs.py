#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess,difflib
root=Path(__file__).resolve().parent
repo='/home/mxym/math-appt-multiscale-20261013'
commit='5522928ae7e8b1960dedb790d7f3506f3b1f5f0b'
projects={'I':('appt-entropy-onset-envelope-20261015','226e122ef2eb536f71091a15ce6a8965e0a1bea4a51af4055b33b8c9d4f1234d'),
          'J':('appt-critical-order-transition-20261015','eabb141f940c6e0bf1b2edd0b1030ffc9156a1d9d7a73d3ef8912e2f4fbd0a7c'),
          'K':('appt-coupled-order-window-20261015','1de40761542d4f482841a285d84e874633b87a14e1f89baf26edd8302303024a')}
def sha(x):return hashlib.sha256(x).hexdigest()
result={'source_commit':commit,'kind':'read-only published dependency byte comparison','targets':{}}
for key,(project,finalhash) in projects.items():
    dest=root/'snapshot/published-inputs'/key;dest.mkdir(parents=True,exist_ok=True)
    data={}
    for name in ('PAPER.md','FINAL_STATUS.diff','FINAL_STATUS_BINDING.json','REVIEW.md','REVIEW.json'):
        raw=subprocess.run(['git','show',commit+':research/'+project+'/'+name],cwd=repo,capture_output=True,check=True).stdout
        (dest/name).write_bytes(raw);data[name]=raw
    old=(root/'snapshot/dependencies'/(key+'-PAPER.md')).read_bytes()
    binding=json.loads(data['FINAL_STATUS_BINDING.json'])
    assert sha(data['PAPER.md'])==finalhash==binding['final_paper_sha256']
    assert sha(old)==binding['reviewed_paper_sha256']
    assert binding['status']=='PASS'
    expected=''.join(difflib.unified_diff(old.decode().splitlines(keepends=True),
                    data['PAPER.md'].decode().splitlines(keepends=True),
                    fromfile=key+'/reviewed/PAPER.md',tofile=key+'/final/PAPER.md')).encode()
    assert expected==data['FINAL_STATUS.diff']
    result['targets'][key]={'project':project,'reviewed_mathematical_sha256':sha(old),
            'published_paper_sha256':finalhash,'whole_status_diff_matches':True,
            'files':{n:sha(raw) for n,raw in data.items()}}
(root/'PUBLISHED_INPUT_COMPARISON.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
