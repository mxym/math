from pathlib import Path
import hashlib,json
stage=Path(__file__).parent
p=stage/'derive_coefficients.py'
raw=p.read_bytes();saved=stage/'INITIAL_DERIVE_COEFFICIENTS.py'
if saved.exists():raise RuntimeError('Do not overwrite initial test')
saved.write_bytes(raw)
old='assert s.series(r,u,0,3).removeO().expand()==rs'
new='assert s.cancel(s.series(r,u,0,3).removeO()-rs)==0'
if raw.decode().count(old)!=1:raise RuntimeError('Unexpected comparison anchor')
p.write_text(raw.decode().replace(old,new))
(stage/'INITIAL_EXPLORATORY_FAILURE.json').write_text(json.dumps({
 'initial_script_sha256':hashlib.sha256(raw).hexdigest(),'result':'AssertionError at line27',
 'cause':'Structural equality of expanded and factored SymPy expressions instead of algebraic zero comparison',
 'correction':'Use exact algebraic cancellation for the already symbolic rational expansion',
 'manuscript_math_changes':0,'raw_initial_script_retained':True},indent=2)+'\n')
print('Initial symbolic-test failure retained; comparison corrected.')
