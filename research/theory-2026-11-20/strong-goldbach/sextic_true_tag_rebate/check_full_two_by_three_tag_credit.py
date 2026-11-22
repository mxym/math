from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

# Reuse the preceding exact third difference, variable linear bounds,
# finite-rank harmonic densities, and base outward interval cube.
three = Path(__file__).resolve().with_name("check_three_by_three_tag_credit.py")
raw = three.read_bytes()
if sha256(raw).hexdigest() != (
    "10f98e5c3f1ce9cca510553c394c8b3afdabbaaffcef29fb041e1b0c0ff1ff9d"
):
    raise ArithmeticError("different three-by-three checker")
prefix, sep, cpp = raw.decode().partition('\ntext += r"""')
if not sep or cpp.count("\nint main(){") != 1:
    raise ArithmeticError("ambiguous reused wrapper")
env = {"__file__": str(three)}
exec(compile(prefix, str(three), "exec"), env)
text = env["text"] + cpp.split("\nint main(){")[0]

text += r"""

I positive2(I T){
 I V=0;
 for(int k=7;k<=11;k+=2){
  if(T.r <(k*af).l)continue;
  int il=max(k*A,idxlo(T.l)), ir=max(k*A,idxhi(T.r));
  I d=range(taildens[k],il,ir);
  I z=T/k;
  I amp=1056*I(1<<(k-3))*powI(z,2)+80640*I(1<<(k-5))*powI(z,4);
  V=V+d*amp;
 }
 return I(0,V.r);
}
int main(){
 constexpr int ns=160,step=70,st=30,end=800;
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants();prep_b(800);rank_dens();
 struct Cell {int i,j; I vol, mean, pos, sq;};
 vector<Cell> cells;
 for(int i=st;i<end;i+=step)for(int j=i;j<end;j+=step){
   int iu=min(end,i+step),ju=min(end,j+step);
   I u=I(i,iu)/P,v=I(j,ju)/P,T=1-u-v;
   mark3=0;prep_g(1,u,v);
   // Negative rank-three geometry holds analytically on the whole bank.
   I m=mean(1,u,v,ns),pos=positive2(T),sq=mean2(1,u,v,0,ns);
   if(i+j<650&&iu>50&&ju>50){
     prep_b(1630);
     I mw=neg(mean(1,u,v,ns));
     m=m+I(0,max(0.0,mw.r));
     prep_b(800);
   }
   I vol=I(iu-i)*I(ju-j)/I(P*P)/(i==j?2:1);
   cells.push_back({i,j,vol,m,pos,sq});
 }
 I allvol=0,allsum=0,negsum=0;
 int seen=0,negc=0,nr=0;
 double minimum=1e100;
 for(int i=st;i<end;i+=step)for(int j=i;j<end;j+=step)for(int l=j;l<end;l+=step){
   int iu=min(end,i+step),ju=min(end,j+step),lu=min(end,l+step),sup=iu+ju+lu;
   I u=I(i,iu)/P,v=I(j,ju)/P,w=I(l,lu)/P;
   mark3=w;prep_g(2,u,v);
   auto p=beta(sup);
   I k=p.first,U=p.second;
   int d=(10000000-1000*(i+j+l+sup))/10000;
   if(d<=0)abort();
   I bs=mean2(2,u,v,d,ns);
   int rep=i==l?6:(i==j||j==l?2:1);
   I vol=I(iu-i)*I(ju-j)*I(lu-l)/I((double)P*P*P)/rep;
   for(const auto& C:cells){
      I lower=I(d)*neg(k*C.mean+(U-k)*C.pos)-I(0,cap_sqrt(U*I(575)/80*C.sq*bs));
      I allweight=vol*C.vol;
      minimum=min(minimum,lower.l);
      if(lower.l<0){negsum=negsum+allweight*I(lower.l);negc++;}
      allvol=allvol+allweight;allsum=allsum+allweight*I(lower.l);seen++;
   }
   nr++;
 }
 printf("full two-three: %zu x %d, %d cells, global min %.4f, negative cells %d negative both %.8f, angle5 %.12g, lower %.14g\n",
        cells.size(),nr,seen,minimum,negc,(2*negsum).l,allvol.l,(2*allsum).l);
 if(cells.size()!=66||nr!=286||seen!=18876||negc!=7150||
    (2*allsum).l<=(I(883)/10000).r)abort();
}
"""

with tempfile.TemporaryDirectory(prefix="sextic-full-two-by-three-") as run:
    src = Path(run, "proof.cpp")
    out = Path(run, "proof")
    src.write_text(text)
    subprocess.run(
        ["c++", "-O3", "-std=c++17", "-ffp-contract=off", "-fno-fast-math",
         str(src), "-o", str(out)], check=True
    )
    subprocess.run([str(out)], check=True)
