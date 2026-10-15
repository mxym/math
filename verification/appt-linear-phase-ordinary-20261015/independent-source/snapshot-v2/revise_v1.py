"""Keep the actual initial manuscript and the independent scope finding."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil,difflib
p=Path(__file__).resolve().parent
f=p/'PAPER.md';before=f.read_bytes()
expected='b270516f97cf719b2e64d4738d328d09d84ac133d8c44cc1620fd1126733e263'
if hashlib.sha256(before).hexdigest()!=expected:raise RuntimeError('Not the frozen v1')
h=p/'author-versions'/'v1-before-alpha-domain-finding'
h.mkdir(parents=True,exist_ok=False)
shutil.copyfile(f,h/'PAPER.md')
old=before.decode()
new=old.replace('D=mn, y_i=D lambda_i with eigenvalues in decreasing order, and set',
 'D=mn and y_i=D lambda_i with eigenvalues in decreasing order. For real\norders alpha>1 set')
new=new.replace('h is strictly increasing in L, so the optimized value as a function of L\n',
 'h has strictly positive derivative in L: a\'(L)=4/[3(2-L)^2]>0 and\n'+
 'dh/da=(2a+1)/(2sqrt(a^2+a))-1>0, since (2a+1)^2-4(a^2+a)=1.\n'+
 'Thus the optimized value as a function of L\n')
if old==new or new.count('For real\norders alpha>1 set')!=1:raise RuntimeError('Missing source revision')
f.write_text(new)
finding={'utc':datetime.now(timezone.utc).isoformat(),
 'kind':'actual independent full-read source-domain finding, preserved before correction',
 'finding':'Section 1 omitted alpha>1 before E=log(max M)/(alpha-1); that identity is false as written at 0<alpha<1. All linear-order targets eventually have alpha>1.',
 'counterexample':'For 0<alpha<1 the concave power moment is maximized by the maximally mixed state with value 1. A nonuniform actual APPT pole has a strictly positive entropy deficit, so max entropy deficit cannot be log(max moment)/(alpha-1)=0.',
 'secondary_clarification':'Explicit positive h derivative now substantiates the Schur-complement argument; strict monotonicity alone was not used as an implication of nonzero derivative.',
 'before_sha256':expected,'after_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),
 'affected_scope':'definition domain and an explicit local derivative; no extension of the mathematical targets',
 'author_control_run_before_finding':False,'v1_independent_complete_read':'finding, not a mathematical PASS'}
(h/'FINDING.json').write_text(json.dumps(finding,indent=2)+'\n')
(p/'V1_TO_V2.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='v1/PAPER.md',tofile='v2/PAPER.md')))
log=p/'RESEARCH_LOG.md'
text=log.read_text().replace('argument,+and','argument,\nand')
text+='\nIndependent reader found the missing alpha>1 definition domain before any\nauthor control run. The exact v1, full finding and source diff are retained\nin author-versions and V1_TO_V2.diff; v2 corrects that domain and spells\nout the positive optimizer derivative used in the Hessian calculation.\n'
log.write_text(text)
print(json.dumps(finding))
