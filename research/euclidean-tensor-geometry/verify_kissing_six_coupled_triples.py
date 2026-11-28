#!/usr/bin/env python3
"""Rebuild the exact trivariate polynomial, then test its four Gram domains with Node."""
import sys,json,base64,zlib,itertools,math,hashlib,pathlib,subprocess
from fractions import Fraction as Q

def require(x,msg):
 if not x:raise ValueError(msg)
def read(s):return json.loads(zlib.decompress(base64.b64decode(s)))
def compile_row(row,J,tcoeff):
 q,d,th,use3,rows=row;N=6;Q2=q*(q-1)//2;Q3=q*(q-1)*(q-2)//6
 require(73<=q<=76 and 0<=d<=10 and use3==1,'witness dimensions')
 SCALE=10**8
 F,aa,X,Y=[[[Q(int(l),10**24)for l,h in row]for row in read(J[n])]for n in ('dense_0_0.txt','dense_sos1.txt','dense_sos2_1.txt','dense_sos2_2.txt')]
 from collections import defaultdict
 def con(c):return {0:c}
 def plus(*ps):
  R=defaultdict(Q)
  for p in ps:
   for i,v in p.items():R[i]+=v
  return dict(R)
 def sc(p,c):return {i:c*v for i,v in p.items()}
 def mul(p,q):
  R=defaultdict(Q)
  for i,v in p.items():
   for j,w in q.items():R[i+j]+=v*w
  return dict(R)
 def prod(*p):
  out=con(1)
  for s in p:out=mul(out,s)
  return out
 def pw(p,n):return prod(*([p]*n))
 def poly1D(P):
  return plus(*(sc(pw(a,i),v)for i,v in enumerate(P)if v))
 def perm(P,l):
  R={}
  for e,v in P.items():
   i=e%64;j=e//64%64;k=e//4096
   ex=(i,j,k);R[ex[l%3]+64*ex[(l+1)%3]+4096*ex[(l+2)%3]]=v
  return R
 def cyclic(p):return sc(plus(*(perm(p,i)for i in range(3))),Q(1,3))
 a={1:1};b={64:1};c={4096:1};one=con(1)
 ch=[one,a]
 for i in range(1,14):ch.append(plus(sc(mul(a,ch[-1]),2),sc(ch[-2],-1)))
 gp=[one,a]
 for j in range(1,35):gp.append(plus(sc(mul(a,gp[-1]),Q(2*j+4,j+4)),sc(gp[-2],Q(-j,j+4))))
 def che(x):return plus(*(sc(p,v)for p,v in zip(ch,x)))
 w=plus(c,sc(mul(a,b),-1));ab=prod(plus(one,sc(pw(a,2),-1)),plus(one,sc(pw(b,2),-1)));qq=[one,w]
 for k in range(1,d):qq.append(plus(sc(mul(w,qq[-1]),Q(2*k+N-3,k+N-3)),sc(mul(ab,qq[-2]),Q(-k,k+N-3))))
 def chegram(M):return plus(*(sc(mul(ch[i],ch[j]),v)for i,row in enumerate(M)for j,v in enumerate(row)))
 r2=plus(chegram(X),prod(plus(one,a),plus(con(Q(1,2)),sc(a,-1)),chegram(Y)))
 r3={}
 for i,j,k,v in read(tcoeff):
  for e in itertools.permutations((i,j,k)):r3[e[0]+64*e[1]+4096*e[2]]=Q(int(v),10**26)
 out=defaultdict(Q);budget=0;total=0
 for lam,data in rows:
  lam=Q(lam,SCALE);require(lam>=0,'negative dual multiplier');typ=data[0]
  if typ=='P':
   require(1<=data[1]<=28,'harmonic degree');P=cyclic(sc(gp[data[1]],-(q-1)));B=1
  elif typ=='H':
   k,u=data[1:];require(0<=k<=d and len(u)==d+1-k,'Gram factor dimensions');u=[Q(v,SCALE)for v in u];f=che(u);ff=perm(f,2);P=cyclic(plus(sc(prod(qq[k],f,ff),q-2),prod(pw(plus(one,sc(pw(a,2),-1)),k),f,f),sc(f,2*sum(u))if k==0 else {}));P=sc(P,-(q-1));B=sum(u)**2 if k==0 else 0
  else:
   require(typ=='T' and len(data[1])==13,'four-point tangent width');z=[Q(v,SCALE)for v in data[1]];fv=[2*sum(z[i]*F[i][j]for i in range(13))for j in range(13)]
   P=plus(sc(cyclic(plus(r2,poly1D(fv[2:]))),Q2),sc(r3,use3*Q3))
   zn=sum(map(abs,z));eps=Q(2,10**24);err=eps*(zn**2+2*zn*(1+q+11*Q2)+221*Q2+q)+Q3*Q(2,10**23)
   B=Q(7699,100)-q-q*aa[0][0]-fv[0]-q*fv[1]+sum(x*y for x,y in zip(z,fv))/2+err;total+=lam
  for e,w in P.items():out[e]+=lam*w
  budget+=lam*B
 out[0]-=budget
 
 den=math.lcm(*(v.denominator for v in out.values()if v))
 r=[[e%64,e//64%64,e//4096,str(int(v*den))]for e,v in sorted(out.items())if v]
 # The RHS Q_2*m/3 for the stratum and chosen integer threshold is added in the Bernstein checker.
 return base64.b64encode(zlib.compress(json.dumps([str(den),r],separators=(',',':')).encode(),9)).decode()
def run(data,previous,js,selected=()):
 require(len(data['source_sha256'])==45 and len(read(data['triangle_coefficients']))==352,'wrong source inventory')
 valid={v for row,ans in data['witnesses'] for v in (str(row[0]),str(row[0])+':'+row[2])}
 require(set(selected)<=valid,'unknown row selector')
 for row,ans in data['witnesses']:
  q,d,t,flag,rows=row
  if selected and not any(s in (str(q),str(q)+':'+t)for s in selected):continue
  th=Q(t);inp=compile_row(row,previous,data['triangle_coefficients'])
  subprocess.run(['node',str(js),str(q),str(th.numerator),str(th.denominator),str(ans),'0','1','2','3'],input=inp,text=True,check=True)
  print('PASS',q,'points: at least',ans,'pairs above',t,flush=True)
def main():
 root=pathlib.Path(__file__).resolve().parent
 raw=(root/'kissing-six-coupled-triple-data.json').read_bytes();old=(root/'kissing-six-near-contact-certificate.json').read_bytes()
 require(hashlib.sha256(raw).hexdigest()=='82075fc3b2bec58e21b15c3c7455b28e975932cc51fd4c94352e9faf0fd581be','different coupled data')
 require(hashlib.sha256(old).hexdigest()=='fbfbef5bfac609d60185c7f923f23584fce1423ae0b4bfadcff33681aa8543b0','different pair data')
 run(json.loads(raw),json.loads(old)['matrices'],root/'verify-kissing-coupled-bernstein.js',sys.argv[1:])
if __name__=='__main__':main()
