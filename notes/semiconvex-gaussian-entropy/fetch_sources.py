#!/usr/bin/env python3
"""Download only the public pinned sources listed in sources.json; verify bytes."""
import argparse,hashlib,json,pathlib,urllib.request

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--destination',default='source-cache')
    parser.add_argument('--offline',action='store_true',help='Verify existing bytes without downloads')
    args=parser.parse_args()
    manifest=json.loads(pathlib.Path(__file__).with_name('sources.json').read_text())
    destination=pathlib.Path(args.destination)
    destination.mkdir(parents=True,exist_ok=True)
    for item in manifest['files']:
        target=destination/item['cache_name']
        if not args.offline:
            request=urllib.request.Request(item['url'],headers={'User-Agent':'reproducible-math-proof-note'})
            with urllib.request.urlopen(request,timeout=60) as response:
                data=response.read()
            if hashlib.sha256(data).hexdigest()!=item['sha256']:
                raise RuntimeError('Downloaded source hash mismatch: '+item['cache_name'])
            target.write_bytes(data)
        data=target.read_bytes()
        if len(data)!=item['bytes'] or hashlib.sha256(data).hexdigest()!=item['sha256']:
            raise RuntimeError('Source hash or size mismatch: '+item['cache_name'])
        print('VERIFIED '+item['cache_name'])
    print('PASS: all pinned public sources matched exact SHA-256 hashes')

if __name__=='__main__':
    main()
