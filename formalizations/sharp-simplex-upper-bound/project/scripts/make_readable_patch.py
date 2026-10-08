#!/usr/bin/env python3
"""Create an exact new-file Git patch of this complete source-only increment."""
from pathlib import Path
import argparse,hashlib,json

ROOT=Path(__file__).resolve().parent.parent

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    options=parser.parse_args()
    target=options.output.resolve()
    if target==ROOT or ROOT in target.parents:
        raise ValueError('Patch output must be outside the source tree')
    chunks=[];entries=[];line=1
    for source in sorted(ROOT.rglob('*')):
        if not source.is_file():continue
        if source.is_symlink():raise ValueError('Symlink in source release: '+str(source))
        data=source.read_bytes();text=data.decode('utf-8')
        if '\x00' in text:raise ValueError('Binary input: '+str(source))
        relative=source.relative_to(ROOT).as_posix();path=ROOT.name+'/'+relative
        if any(c not in 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_./' for c in path):
            raise ValueError('Unexpected patch pathname: '+path)
        blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        content=text.split('\n') if text else []
        final_lf=text.endswith('\n')
        if final_lf:content.pop()
        header=f'diff --git a/{path} b/{path}\nnew file mode 100644\nindex 0000000..{blob[:7]}\n'
        if content:
            header+=f'--- /dev/null\n+++ b/{path}\n@@ -0,0 +1,{len(content)} @@\n'
        body=''
        for i,item in enumerate(content):
            body+='+'+item+'\n'
            if i==len(content)-1 and not final_lf:
                body+='\\ No newline at end of file\n'
        piece=header+body
        entries.append({'file':relative,'patch_start_line':line,
            'patch_end_line':line+piece.count('\n')-1,'source_bytes':len(data),
            'source_sha256':hashlib.sha256(data).hexdigest()})
        chunks.append(piece);line+=piece.count('\n')
    payload=''.join(chunks).encode('utf-8');target.write_bytes(payload)
    index={'patch_file':target.name,'bytes':len(payload),'lines':payload.count(b'\n'),
           'sha256':hashlib.sha256(payload).hexdigest(),'files':entries}
    target.with_suffix('.index.json').write_text(json.dumps(index,indent=2)+'\n')
    print(json.dumps({k:v for k,v in index.items() if k!='files'}|{'files':len(entries)},indent=2))

if __name__=='__main__':main()
