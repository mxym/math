from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import urllib.request

aux=Path('/mnt/d/math/tmp/breadth-tcs-20261015')
out=aux/'primary-bytes'
out.mkdir(exist_ok=True)
sources={
    'order-compression-author.pdf':'https://www2.cs.uregina.ca/~zilles/darnstaedtDSZ13.pdf',
    'partial-concepts-author.pdf':'https://www.cs.tau.ac.il/~nogaa/PDFS/PCC.pdf',
    'floyd-warmuth-author.pdf':'https://mwarmuth.bitbucket.io/pubs/J30.pdf',
}
records=[]
for name,url in sources.items():
    file=out/name
    if file.exists():
        raise FileExistsError(str(file))
    try:
        data=urllib.request.urlopen(url,timeout=25).read()
        if not data.startswith(b'%PDF'):
            raise ValueError('Response is not a PDF')
        file.write_bytes(data)
        textfile=file.with_suffix('.txt')
        subprocess.run(['pdftotext','-layout',str(file),str(textfile)],check=True)
        records.append({'url':url,'private_file':name,'bytes':len(data),
            'sha256':hashlib.sha256(data).hexdigest(),
            'text_sha256':hashlib.sha256(textfile.read_bytes()).hexdigest(),
            'fetched_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'read_scope':'Download and extraction alone are not a complete read. Exact bounded scopes recorded after reading.'})
    except Exception as exc:
        records.append({'url':url,'error':str(exc)})
(aux/'RESUMED_SOURCE_FETCHES.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records,indent=2))
