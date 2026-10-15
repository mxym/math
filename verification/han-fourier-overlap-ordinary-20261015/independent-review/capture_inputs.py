"""Private immutable-commit snapshot; never execute or edit author code."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,subprocess

HERE=Path(__file__).resolve().parent
REPO=Path('/home/mxym/math-breadth-tcs-20261015')
PREFIX='research/breadth-tcs-20261015/phase-2/han-q31-review-v1'
COMMIT='d83f9be16b9e4fb00437ca59fa79316b9de80960'
manifest={'captured_utc':datetime.now(timezone.utc).isoformat(),'commit':COMMIT,'files':{},
    'private_review_only':True,'author_controls_executed':False}
paths=subprocess.run(['git','-C',str(REPO),'ls-tree','-r','--name-only',COMMIT,PREFIX],
    check=True,stdout=subprocess.PIPE).stdout.decode().splitlines()
for name in paths:
    data=subprocess.run(['git','-C',str(REPO),'show',COMMIT+':'+name],check=True,stdout=subprocess.PIPE).stdout
    assert (REPO/name).read_bytes()==data,name
    relative=Path(name).relative_to(PREFIX)
    target=HERE/'snapshot'/relative
    target.parent.mkdir(parents=True,exist_ok=True)
    if target.exists():assert target.read_bytes()==data
    else:target.write_bytes(data)
    manifest['files'][relative.as_posix()]={'sha256':hashlib.sha256(data).hexdigest(),
        'bytes':len(data),'lines':len(data.splitlines()),'source':name}
assert manifest['files']['HAN_QUESTION_3_1_NEGATIVE_ANSWER.md']['sha256']=='0250c4792fdecbf5e14b4ea1300253329e7385d8593a4044efafa0a2767cb1ef'
(HERE/'INPUT_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(manifest))
