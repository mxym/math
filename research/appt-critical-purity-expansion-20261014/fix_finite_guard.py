from pathlib import Path
import hashlib,json
stage=Path(__file__).parent
p=stage/'check_expansion.py';raw=p.read_bytes();saved=stage/'INITIAL_CHECK_EXPANSION.py'
if saved.exists():raise RuntimeError('Do not overwrite initial finite guard')
saved.write_bytes(raw)
s=raw.decode().replace('a fixed-z calculation misses exactly one unit.','a fixed-z calculation misses exactly four units.')
if s.count('assert missing==1')!=1:raise RuntimeError('Unexpected guard')
p.write_text(s.replace('assert missing==1','assert missing==4'))
(stage/'INITIAL_FINITE_GUARD_FAILURE.json').write_text(json.dumps({
 'initial_script_sha256':hashlib.sha256(raw).hexdigest(),'result':'AssertionError at line55 after all48 candidate rows computed',
 'cause':'Author finite guard used 1 for the displacement contribution at a=5/4; the D^2 purity coefficient contribution is4 (the different scalar-crossing contribution is1)',
 'corrected_guard':'4*(7/2-2*5/4)^2=4','manuscript_second_coefficient':7,
 'manuscript_mathematical_changes':0,'raw_initial_script_retained':True},indent=2)+'\n')
print('Initial incorrect finite guard retained; corrected to exact4, manuscript unchanged.')
