#!/usr/bin/env python3
"""Anonymous public-download SHA256 and DataCite registration verification."""
import json, hashlib, urllib.request, urllib.error, concurrent.futures, argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parent
if not __debug__:raise SystemExit('Run without -O or -OO; verification requires enabled checks')

def get(url):
 accept='application/vnd.inveniordm.v1+json' if '/api/records/' in url and not url.endswith('/content') else '*/*'
 req=urllib.request.Request(url,headers={'Accept':accept,'User-Agent':'mxym-math-public-archive-audit/1.0'})
 with urllib.request.urlopen(req,timeout=60) as r:return r.read(),r.geturl()

def check(item):
 raw,_=get('https://zenodo.org/api/records/'+item['id']);record=json.loads(raw)
 assert record['is_published'] and record['pids']['doi']['identifier']==item['doi']
 assert record['access']['record']=='public' and record['access']['files']=='public'
 assert set(record['files']['entries'])=={x['name'] for x in item['uploads']}
 rights=record['metadata']['rights'];assert len(rights)==1 and not rights[0].get('id') and rights[0]['title']['en']=='Existing licenses preserved; otherwise all rights reserved'
 author=record['metadata']['creators'][0]['person_or_org'];assert author['family_name']=='Zhang' and {'identifier':'0009-0000-3864-3536','scheme':'orcid'} in author['identifiers']
 results=[]
 for x in item['uploads']:
  data,_=get(record['files']['entries'][x['name']]['links']['content']);digest=hashlib.sha256(data).hexdigest()
  assert digest==x['sha256'] and len(data)==x['bytes']
  results.append({'name':x['name'],'bytes':len(data),'sha256':digest})
 doi={'identifier':item['doi'],'registration_status':'not-confirmed'}
 try:
  data,_=get('https://api.datacite.org/dois/'+item['doi']);info=json.loads(data)['data']['attributes']
  assert info['doi'].lower()==item['doi'].lower() and info['state']=='findable'
  doi.update(registration_status='findable',datacite_url=info['url'],registered=info.get('registered'))
 except urllib.error.HTTPError as e:doi['http_status']=e.code
 return {'key':item['key'],'id':item['id'],'status':'PASS','rights_verified':True,'anonymous_downloads':results,'doi':doi,'concept_doi':record['parent']['pids']['doi']['identifier']}

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--fresh',action='store_true',help='Ignore cached checks and download every published attachment again.')
 args=parser.parse_args()
 state=json.loads((ROOT/'PUBLICATION_STATE.json').read_text());items=[x for x in state['records'].values() if x['status']=='published']
 path=ROOT/'PUBLIC_DOWNLOAD_AUDIT.json';old=json.loads(path.read_text()) if path.exists() and not args.fresh else {'records':[]};records={x['key']:x for x in old['records']}
 pending=[x for x in items if x['key'] not in records or records[x['key']]['doi']['registration_status']!='findable' or not records[x['key']].get('rights_verified')]
 with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
  jobs={ex.submit(check,x):x for x in pending}
  for f in concurrent.futures.as_completed(jobs):
   x=f.result();records[x['key']]=x;print('PUBLIC_PASS',x['key'],x['doi']['registration_status'],flush=True)
   path.write_text(json.dumps({'status':'PASS','scope':'Anonymous record/creator/rights access and exact public-file SHA256; DOI registration checked separately. Not mathematical verification.','records':list(records.values())},indent=2)+'\n')
 print('PUBLIC_AUDIT_COMPLETE',len(records),flush=True)
if __name__=='__main__':main()
