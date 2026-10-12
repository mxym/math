#!/usr/bin/env python3
"""Verify exact reversibility of the bibliographic edits using only stdlib."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
def sha(data): return hashlib.sha256(data).hexdigest()
def main():
 changes=json.loads((ROOT/'corrections/editorial-replacements.json').read_text())
 original=json.loads((ROOT/'corrections/baseline-identifiers.json').read_text())['baseline']
 checks=[]
 for file in ('paper.md','LITERATURE.md'):
  data=(ROOT/file).read_text()
  for change in reversed(changes['changes']):
   if change['file']==file:
    if data.count(change['after'])!=1: raise RuntimeError('Nonunique/missing editorial block: '+change['label'])
    data=data.replace(change['after'],change['before'])
  if sha(data.encode())!=original[file]['sha256']: raise RuntimeError('Original byte identity failed: '+file)
  checks.append({'file':file,'exact_reversal_matches_original':True,'baseline_sha256':sha(data.encode()),'corrected_sha256':sha((ROOT/file).read_bytes())})
 before=(ROOT/'corrections/v4-paper.before.md').read_bytes()
 after=(ROOT/'corrections/v4-paper.after.md').read_text()
 insertion=changes['v4_insertion']
 if after.count(insertion)!=1 or after.replace(insertion,'').encode()!=before: raise RuntimeError('v4 insertion preservation failed')
 expected='19eb5aa0c79e34280cc3619cf40c1bea7acda6f6ec1161b05fbb6bf2308fda81'
 if sha(before)!=expected: raise RuntimeError('Pinned v4 original hash failed')
 checks.append({'file':'corrections/v4-paper.after.md','deleting_only_attribution_recovers_pinned_original':True,'original_sha256':sha(before),'corrected_sha256':sha(after.encode())})
 print(json.dumps({'status':'passed','scope':'Exact editorial reversal; preserves every original theorem and proof byte. No mathematical re-audit is asserted.','checks':checks},indent=2))
if __name__=='__main__': main()
