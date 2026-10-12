#!/usr/bin/env python3
"""Verify the exact reviewed source and its three approved status-only edits; read-only."""
import hashlib,json,pathlib,re,sys
p=pathlib.Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
m=json.loads((p/'REVIEW_PROVENANCE.json').read_text());changes=json.loads((p/'editorial-status-changes.json').read_text())['changes']
public=(p/'manuscript.tex').read_bytes();certificate=(p/'audits/exact-source-signoff.txt').read_bytes()
if H(public)!=m['public_source_sha256']:raise SystemExit('Public source hash mismatch')
if H(certificate)!=m['independent_certificate_sha256']:raise SystemExit('Certificate hash mismatch')
if len(changes)!=3:raise SystemExit('Exactly three approved status edits are required')
s=public.decode();original=s
for row in changes:
    if original.count(row['public'])!=1:raise SystemExit('Public status span missing or repeated: '+row['location'])
    original=original.replace(row['public'],row['reviewed'],1)
if H(original.encode())!=m['reviewed_source_sha256']:raise SystemExit('Reconstructed reviewed source hash mismatch')
if m['reviewed_source_sha256'].encode()not in certificate or b'Verdict: PASS.'not in certificate:raise SystemExit('Certificate does not identify the expected passed source')
pattern=r'\\begin\{(theorem|lemma|proposition|corollary|assumption|proof)\}(.*?)\\end\{\1\}'
a=re.findall(pattern,original,re.S);b=re.findall(pattern,s,re.S)
if a!=b or len(a)!=m['mathematical_environment_count']:raise SystemExit('Mathematical environment mismatch')
if H(json.dumps(a,ensure_ascii=False,separators=(',',':')).encode())!=m['mathematical_environments_sha256']:raise SystemExit('Canonical mathematical environment digest mismatch')
print('PASS: exact reviewed source reconstructed; certificate unchanged; all '+str(len(a))+' mathematical environments byte-identical.')
print('Scope: compact-data second/third activity coefficients only; no Gaussian, matched-layer, or unit-amplitude extension.')
