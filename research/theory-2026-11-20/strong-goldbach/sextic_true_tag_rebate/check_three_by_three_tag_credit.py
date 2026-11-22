from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

# Reuse only the audited interval/g3 setup, not either preceding chamber.
base = Path(__file__).resolve().with_name("check_two_by_three_tag_credit.py")
raw = base.read_bytes()
if sha256(raw).hexdigest() != (
    "e8a65208294b8cdd20e766a3960f2c539e91f47a04ff3d81f0c0bf1ccc9a845d"
):
    raise ArithmeticError("different two-by-three checker")
setup, sep, remainder = raw.decode().partition('\ntext += r"""')
if not sep or remainder.count("int main(){") != 1:
    raise ArithmeticError("ambiguous setup boundary")
env = {"__file__": str(base)}
exec(compile(setup, str(base), "exec"), env)
text = env["text"]

text += r"""
double cap_sqrt(I r) {
 if(r.r<0)abort();
 const double s=up(up(sqrt(r.r)));
 if((I(s)*I(s)).l<r.r)abort();
 return s;
}
I log1p_01(I t, bool upper){
 I y=t/(2+t), yy=sq(y), val=0, z=y;
 for(int j=0;j<14;j++,z=z*yy) val=val+2*z/(2*j+1);
 if(upper)val=val+2*z/(29*(1-yy));
 return val;
}
pair<I,I> beta(int up_sum){
 if(up_sum<=1780)return {I(549)/80,I(575)/80};
 I D=I(4980-up_sum)/P, s=D/af;
 I lr=log1p_01(s-2,false); // computes log(1+(s-2))=log(s-1), for t ≤2
 I cap=0, wid=(s-3)/128;
 for(int j=1;j<=128;j++){
    I t=j*wid;
    cap=cap+log1p_01(t,true)/(2+t)*wid;
 }
 return {(2*lr)/D,(2*(1+cap))/D};
}
I jdens[13][P+10], jp[P+10], taildens[13][15][P+10];
void rank_dens(){
 for(int j=1;j<=12;j++){
  for(int i=0;i<=P+1;i++){
   if(i<j*A)jdens[j][i]=0;
   else {
    I x=I(i,i+1)/P;
    if(j==1)jdens[j][i]=1/x;
    else jdens[j][i]=I(jp[i-A].l,jp[i-A+1].r)/x;
   }
   taildens[j][0][i]=jdens[j][i];
  }
  sparse(taildens[j],P+1);
  jp[0]=0;
  for(int i=0;i<=P+1;i++)jp[i+1]=jp[i]+jdens[j][i]/P;
 }
}
I positive3(I T){
 I V=0;
 for(int k=6;k<=12;k+=2){
  if(T.r <(k*af).l)continue;
  int il=max(k*A,idxlo(T.l)), ir=max(k*A,idxhi(T.r));
  I d=range(taildens[k],il,ir);
  I z=T/k;
  I amp=1056*I(1<<(k-2))*z+80640*I(1<<(k-4))*powI(z,3);
  V=V+d*amp;
 }
 return I(0,V.r);
}
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants();
 constexpr int ns=100,step=80,st=30,end=800;
 prep_b(800);rank_dens();
 struct Cell {int i,j,l,s,rep,d; I mean, mass, pos, k,U, sq;};
 vector<Cell> cells;
 for(int i=st;i<end;i+=step)for(int j=i;j<end;j+=step)for(int l=j;l<end;l+=step){
   int iu=min(end,i+step),ju=min(end,j+step),lu=min(end,l+step),sup=iu+ju+lu;
   I u=I(i,iu)/P,v=I(j,ju)/P,w=I(l,lu)/P,T=1-u-v-w;
   mark3=w; prep_g(2,u,v);
   I m=mean(2,u,v,ns), mass=rr(0,T), pos=positive3(T);
   int d=max(1,int((-m.r-m.l)/(mass.r+mass.l)));
   auto p=beta(sup);
   I s2=mean2(2,u,v,d,ns);
   int rep=i==l?6:(i==j||j==l?2:1);
   cells.push_back({i,j,l,sup,rep,d,m,mass,pos,p.first,p.second,s2});
  }
 I allvol=0,allsum=0;
 int seen=0;
 double minimum=1e100;
 for(size_t ii=0;ii<cells.size();ii++)for(size_t jj=ii;jj<cells.size();jj++){
   const auto& a=cells[ii]; const auto& b=cells[jj];
   I negL=neg(b.k*a.mean+(b.U-b.k)*a.pos);
   I negR=neg(a.k*b.mean+(a.U-a.k)*b.pos);
   I totalmass(0,min((b.U*a.mass).r,(a.U*b.mass).r));
   I sqerr(0,cap_sqrt(a.U*b.U*a.sq*b.sq));
   I lower=b.d*negL+a.d*negR-a.d*b.d*totalmass-sqerr;
   if(lower.l<=770000)abort();
   minimum=min(minimum,lower.l);
   auto volume=[&](const Cell &c){return I(min(end,c.i+step)-c.i)*I(min(end,c.j+step)-c.j)*I(min(end,c.l+step)-c.l)/I((double)P*P*P)/c.rep;};
   I vol=(ii==jj?1:2)*volume(a)*volume(b);
   allvol=allvol+vol;allsum=allsum+vol*I(lower.l);seen++;
 }
 printf("three-by-three: %zu triples, %d cell pairs, min %.7f, angle6 %.12g, lower %.14g\n",
        cells.size(),seen,minimum,allvol.l,allsum.l);
 if(cells.size()!=220||seen!=24310||allsum.l<=(I(37104)/1000000).r)abort();
}
"""
with tempfile.TemporaryDirectory(prefix="sextic-three-by-three-") as run:
    src = Path(run, "proof.cpp")
    out = Path(run, "proof")
    src.write_text(text)
    subprocess.run(
        ["c++", "-O3", "-std=c++17", "-ffp-contract=off", "-fno-fast-math",
         str(src), "-o", str(out)], check=True
    )
    subprocess.run([str(out)], check=True)
