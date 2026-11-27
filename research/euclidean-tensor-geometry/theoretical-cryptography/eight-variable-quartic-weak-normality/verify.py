#!/usr/bin/env python3
"""Reproduce the certificate from three named local source files in an isolated temporary directory."""
import argparse, hashlib, os, pathlib, platform, resource, shutil, subprocess, sys, tempfile
if not __debug__: raise SystemExit("Assertions are integral to this checker; do not use -O.")
here=pathlib.Path(__file__).resolve().parent
PINS=['fc58fe0b3b11b67056ebb5f49c58aea8b338edb8d9cda9313d15494850dc7c80','6dd6570fc71bf535c6a7ebe4e1733e01d3efa5c72812e01ec9e296fe1aa8c0eb','2b403fc9fd57a72b8587f3f06e3e2f93fed044db4f22bdc2fdc9ef2a5c9a3885']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,d,out=None,check=True):
 env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1'
 if out:
  with (d/out).open('w') as f:return subprocess.run(cmd,cwd=d,check=check,stdout=f,env=env)
 return subprocess.run(cmd,cwd=d,check=check,env=env)
def sanity():
 # Nonparallel Walsh pair phase checks, every u and every side; this checks more than absolute values.
 bits=lambda n: n.bit_count()%2
 signs=[1-2*(bits(x&5)^int((x&11)==11)^int((x&12)==12)) for x in range(16)]
 W=[sum(s*(-1)**bits(x&u) for x,s in enumerate(signs)) for u in range(16)]
 for a in range(1,16):
  P=a&-a
  for u in range(16):
   for b in (0,1):
    direct=sum(signs[x]*(-1)**bits(u&(x^(b*P))) for x in range(16) if bits(x&a)==b)
    assert 2*direct==(-1)**(b*bits(u&P))*(W[u]+(-1)**b*W[u^a])
 # Fourier defect square constraint allows exactly one triple of moment parameters.
 cases=[]
 for z in range(4):
  for n6 in range(64):
   for n4 in range(64-n6):
    mm=63-n6-n4
    if 6+6*n6+4*n4-2*mm==0 and 36+36*n6+16*n4+4*mm==64*(6+2*z):
     cases.append((z,n6,n4))
 assert cases==[(3,15,0)]
 # A vectorial 4->2 bent map does exist, so the output parity argument must not exclude it.
 # Bilinear multiplication in F4, encoded x0+x1*t, t^2=t+1.
 def mul(x,y):
  a,b=x&1,x>>1;c,d=y&1,y>>1
  return (a*c^b*d) | ((a*d^b*c^b*d)<<1)
 for lam in [1,2,3]:
  ws=[sum((-1)**(bits(lam&mul(v&3,v>>2))^bits(u&v)) for v in range(16)) for u in range(16)]
  assert {abs(w) for w in ws}=={4}
 assert all((16+4*(7-2*i))%8==4 for i in range(8))
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('abnormal7',type=pathlib.Path);ap.add_argument('header7',type=pathlib.Path);ap.add_argument('header8',type=pathlib.Path)
 ap.add_argument('--keep',type=pathlib.Path,help='create this new directory and retain derived certificates and binaries')
 args=ap.parse_args();raw=[p.resolve() for p in (args.abnormal7,args.header7,args.header8)]
 for p,h in zip(raw,PINS):
  if sha(p)!=h:sys.exit('input SHA-256 mismatch: '+str(p))
 sanity()
 with tempfile.TemporaryDirectory() as tmp:
  d=pathlib.Path(tmp) if args.keep is None else args.keep.resolve()
  if args.keep is not None:d.mkdir()
  run(['g++','-O3','-std=c++17',here/'headers.cpp','-o',d/'heads'],d)
  run(['g++','-O3','-std=c++17',here/'independent.cpp','-o',d/'alt'],d)
  run([sys.executable,here/'spectrum.py',*raw[:2]],d,'spectrum.txt')
  run([d/'heads',*raw[1:]],d,'headers.txt')
  run([sys.executable,here/'histogram.py'],d,'histograms.txt')
  run([sys.executable,here/'join.py',d],d,'joined.txt')
  records=(d/'spectrum.txt').read_text().splitlines()[1:]
  counts=[int(r.split(';')[1].strip()) for r in records];assert sum(counts)==39952 and sum(counts[:4])==894
  assert len((d/'headers.txt').read_text().splitlines())==999
  header130=(d/'headers.txt').read_text().splitlines()[131].split();assert header130==['130','0','3'*255]
  run([d/'alt',d],d)
  # Negative control: known-bad intermediate certificate must not be accepted.
  resource.setrlimit(resource.RLIMIT_CORE,(0,0))
  with tempfile.TemporaryDirectory(dir=d) as neg:
   bad=pathlib.Path(neg)
   for name in ('histograms.txt','spectrum.txt','headers.txt'):
    shutil.copyfile(d/name,bad/name)
   def control():return subprocess.run([d/'alt',bad],stdout=subprocess.DEVNULL,stderr=subprocess.PIPE)
   assert control().returncode==0  # same directory AND all three tables, positive baseline
   table=bad/'histograms.txt';before=table.read_bytes()
   after=before.replace(b'32640',b'32641',1)
   assert len(before)==len(after) and sum(x!=y for x,y in zip(before,after))==1
   table.write_bytes(after)
   assert all(sha(bad/f)==sha(d/f) for f in ('spectrum.txt','headers.txt'))
   p=control();assert p.returncode!=0 and b'x.s[j]==stoi(t[25+j])' in p.stderr
   print('Negative control: unchanged copy exit 0; one histogram byte changed; exit',p.returncode,'at the aggregate-bin equality assertion.')
  print('39952 abnormal records: 39058 E, 894 O; 14 absolute Walsh types.')
  print('998 x 255 restriction signatures agree in both implementations; head 130 has type 3 on all 255 normals.')
  print((d/'joined.txt').read_text(),end='')
  for name in ('spectrum.txt','headers.txt','histograms.txt','joined.txt'):print(sha(d/name),name)
  print('PASS: all arithmetic checks, phase and dimension controls, corrupted histogram rejected.')
if __name__=='__main__':main()
