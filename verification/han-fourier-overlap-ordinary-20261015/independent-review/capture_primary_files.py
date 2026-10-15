"""Privately copy declared primary evidence; distinguish author downloads from our reads."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,subprocess

HERE=Path(__file__).resolve().parent
data=json.loads((HERE/'snapshot/HAN_Q31_TARGET_AND_SOURCE_MAP.json').read_text())
out={'captured_utc':datetime.now(timezone.utc).isoformat(),
     'files_downloaded_by':'author, reused locally with exact hashes',
     'independent_official_metadata_and_selected_fulltext_reads':'recorded separately in literature review',
     'files':{}}
dest=HERE/'primary-evidence';dest.mkdir(exist_ok=True)
for item in data['primary_sources']:
    source=Path(item['file_in_aux_only']);raw=source.read_bytes()
    assert len(raw)==item['bytes'] and hashlib.sha256(raw).hexdigest()==item['sha256'],str(source)
    target=dest/source.name
    if target.exists():assert target.read_bytes()==raw
    else:target.write_bytes(raw)
    record={'source':str(source),'declared_url':item['url'],'bytes':len(raw),
        'sha256':hashlib.sha256(raw).hexdigest(),'author_declared_read_scope':item['actual_read_scope']}
    if source.suffix=='.pdf':
        txt=target.with_suffix('.txt')
        subprocess.run(['pdftotext','-layout',str(target),str(txt)],check=True)
        record['reviewer_generated_text']={'file':txt.name,'sha256':hashlib.sha256(txt.read_bytes()).hexdigest(),
            'lines':len(txt.read_bytes().splitlines())}
    out['files'][target.name]=record
(HERE/'PRIMARY_SOURCE_FILES.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'copied_files':len(out['files']),'PDF_text_extraction':'pdftotext -layout',
    'source_hashes_match_author_map':True,'fresh_native_download_claimed':False}))
