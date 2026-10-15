from pathlib import Path
import hashlib,json
out=Path('/mnt/d/math/tmp/research-resume-20261015/independent-phase-diagram-final-binding-review-20261015')
snap=out/'candidate-snapshot'
old=out.parent/'independent-critical-boundary-review-20261015'
new=snap/'verification/appt-linear-phase-diagram-ordinary-20261015/independent-source'
oldfiles={p.relative_to(old).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in old.rglob('*') if p.is_file()}
newfiles={p.relative_to(new).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in new.rglob('*') if p.is_file()}
print('independent old',len(oldfiles),'new',len(newfiles))
print('missing',sorted(oldfiles.keys()-newfiles.keys()),'extra',sorted(newfiles.keys()-oldfiles.keys()))
print('changed',[r for r in oldfiles.keys() & newfiles.keys() if oldfiles[r]!=newfiles[r]])
assert oldfiles==newfiles
project=snap/'research/appt-linear-phase-diagram-20261015'
for rel,h in [('LAST_MIXED_BOUNDARY.md','6e4f77e2bbecbc5e71f426925d444e8e1a9b69d2ffebcbef88badc1f4e87f0a0'),('NO_ISLANDS.md','f7509ff124d76f12855a55705f317c51133c8e1a93fcadc7f230bebd91b8ad16'),('CRITICAL_UNIQUENESS_CERTIFICATE.md','be76b90de9277fab91c1f676f8de7619c2d58a5b79cf65cf06839d7ce8e7637e'),('GLOBAL_MIXED_PHASE.md','5712392f1e74b9c1d1999bacb42cf21f0d0fac3c3cd963954774972dd487c4cb')]:
 assert hashlib.sha256((project/'author-snapshot'/rel).read_bytes()).hexdigest()==h
for name in ['README.md','STATUS.md']:
 print('TOP',name,hashlib.sha256((project/name).read_bytes()).hexdigest())
print('canonical diff files')
for p in (out/'stage-inputs').glob('*.candidate.diff'):print(p.name,p.read_text())
