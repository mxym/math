"""The same four-way hit at ranks 38 and 40; exact native graph-chart replay."""
import json
from pathlib import Path
from original_site_populations import calc
def check(rank,cert):
 o,w,c,g,u,ub,red=calc(rank,[],export=True)
 tab={str(k):v for k,v in ub.items()}
 tab.update({'S':w((1,23))-99*o-7*w((0,14)),'444':w((4,44)),'Y1':c((0,14))})
 for h in {20,24,125,127}:tab['abs'+str(h)]=(-1)*u[divmod(h,100)]
 den,terms=cert;assert den>0 and len(terms)==len(dict(terms))
 assert {k for k,a in terms if k.startswith('abs')}=={'abs20','abs24','abs125','abs127'}
 z=den*o
 for k,a in terms:
  assert type(a) is int and a>0
  z+=a*tab[k]
 assert not any(red(z))
 print('Rank',rank,'must hit 020,024,125 or 127; constant',den,'and',len(terms),'positive terms.')
if __name__=='__main__':
 t=json.loads(Path(__file__).with_name('ranks38-40-four-way-hit.json').read_text())
 for r in (38,40):check(r,t[str(r)])
