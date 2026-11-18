"""Load the original Heidelberg SMAPO facet lists; no catalog is redistributed here."""
import argparse,hashlib,itertools,json,pathlib,re,string,urllib.request
URL="https://comopt.ifi.uni-heidelberg.de/software/SMAPO/cut/swcut_{}"
SPECS={
 5:(2,"830c83c51d0eabd6d2cccc87bee515f36bdb511afe8f04e6e88f7f8b37f5e699"),
 6:(3,"b3b03399f23a7b8fadfe512fee3a72a955971a7e567568deabff24d0da2a9374"),
 7:(11,"0207726c7ea6bddcb96257214d0b93d49c380e85cf4ff1131c241d98b1abeb64"),
 8:(147,"ff1b1ea2cc9670d00b0296b28bb96326f5334419fe140f5fac0689e55e1b08b0")}
def require(b,msg):
 if not b:raise ValueError(msg)
def arguments():
 p=argparse.ArgumentParser(description=__doc__)
 group=p.add_mutually_exclusive_group(required=True)
 group.add_argument('--source-dir',type=pathlib.Path,help='directory containing unmodified SMAPO swcut_5 to swcut_8')
 group.add_argument('--download',action='store_true',help='read the four official HTTPS endpoints')
 return p.parse_args()
def load(n,args):
 if args.source_dir is not None:
  with (args.source_dir/f'swcut_{n}').open('rb') as h:data=h.read(1000001)
 else:
  with urllib.request.urlopen(URL.format(n),timeout=30) as h:data=h.read(1000001)
 require(len(data)<=1000000,'oversized input')
 lines=[s.strip() for s in data.decode('ascii').splitlines() if s.strip()]
 E=[''.join(e) for e in itertools.combinations(string.ascii_uppercase[:n],2)]
 require(len(lines)>=5 and re.fullmatch(r'DIM\s*=\s*'+str(len(E)),lines[0]) and
     lines[1]=='INDEX' and lines[2].split()==E and lines[3]=='INEQUALITIES_SECTION' and
     lines[-1]=='END',(n,'format/columns'))
 D={}
 for line in lines[4:-1]:
  m=re.fullmatch(r'\(\s*(\d+)\s*\)\s+((?:[+-]?\d+\s+)+)<=\s*0',line)
  require(m is not None,(n,'row syntax',line[:50]))
  i=int(m[1]);a=list(map(int,m[2].split()))
  require(i==len(D)+1 and len(a)==len(E),(n,'row number/length'));D[str(i)]=a
 expected,sha=SPECS[n];require(len(D)==expected,(n,'row count'))
 canonical=(json.dumps(D,separators=(',',':'))+'\n').encode('ascii')
 require(hashlib.sha256(canonical).hexdigest()==sha,(n,'coefficient digest'))
 return D
if __name__=='__main__':
 args=arguments()
 for n in SPECS:print(n,len(load(n,args)),'rows match canonical SHA-256',SPECS[n][1])
