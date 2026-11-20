from pathlib import Path
import subprocess,gzip,tempfile
p=Path(__file__).resolve().parent
with tempfile.TemporaryDirectory()as tmp:
 t=Path(tmp)
 for s in ['enumerate','verify']:
  subprocess.run(['c++','-O3','-std=c++17',str(p/(s+'.cpp')),'-o',str(t/s)],check=True)
 subprocess.run([str(t/'enumerate')],cwd=t,check=True)
 with gzip.open(p/'bounds.txt.gz','rb')as f,(t/'bounds.txt').open('wb')as o:
  while b:=f.read(1<<20):o.write(b)
 subprocess.run([str(t/'verify'),str(t/'orient.dat'),str(t/'bounds.txt')],check=True)
