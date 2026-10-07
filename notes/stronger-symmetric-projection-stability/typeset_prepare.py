#!/usr/bin/env python3
"""Format-only amsmath fix: place display tags outside aligned sub-environments."""
from pathlib import Path
import re,sys
p=Path(sys.argv[1]);s=p.read_text();count=0
def relocate(m):
 global count
 body=m.group(1);tags=re.findall(r'\\tag\{[^{}]+\}',body)
 if not tags:return m.group(0)
 if len(tags)!=1:raise RuntimeError('Ambiguous multiple tags in aligned environment')
 count+=1
 return '\\begin{aligned}'+body.replace(tags[0],'')+'\\end{aligned}\n'+tags[0]
s=re.sub(r'\\begin\{aligned\}(.*?)\\end\{aligned\}',relocate,s,flags=re.S)
s=re.sub(r'\\texttt\{([0-9a-f]{40,64})\}',lambda m:'\\nolinkurl{'+m.group(1)+'}',s)
pat=r'\\\[\s*(P=\\frac3d p.*?w=\\frac1d.*?remaining axis\}\.\s*)\\\]'
def wrap(m):
 body=m.group(1).replace(',\\qquad',',\\\\')
 return '\\[\\begin{gathered}\n'+body+'\\end{gathered}\\]'
s,n=re.subn(pat,wrap,s,flags=re.S)
if n!=1:raise RuntimeError('Expected one three-clause probability display, found '+str(n))
p.write_text(s)
print('Relocated '+str(count)+' display tags outside aligned environments; mathematical tokens unchanged.')
