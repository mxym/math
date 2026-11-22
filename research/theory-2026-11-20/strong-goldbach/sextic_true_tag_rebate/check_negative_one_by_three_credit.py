from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

# Reuse only the audited interval/g3 setup, not either preceding chamber.
here = Path(__file__).resolve().parent
base = here / "check_two_by_three_tag_credit.py"
if sha256((here / "check_three_by_three_tag_credit.py").read_bytes()).hexdigest() != (
    "10f98e5c3f1ce9cca510553c394c8b3afdabbaaffcef29fb041e1b0c0ff1ff9d"
):
    raise ArithmeticError("different three-by-three checker")
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
I sumB(I T,int l,int u){
 I V=0;
 for(int k=l;k<=u;k++){
  if(T.r <(k*af).l)continue;
  V=V+range(taildens[k],max(k*A,idxlo(T.l)),max(k*A,idxhi(T.r)));
 }
 return V;
}
I pos4one(I t,int divs){
 I T=1-t,spanT=T-3*af,V=0;
 for(int i=0;i<divs;i++)for(int j=i;j<divs;j++){
   int zz[4]={0,i,j,divs};
   I q=sq(t);
   for(int k=0;k<3;k++){
      int i1=zz[k],i2=zz[k+1];
      I gap=I(max(0,i2-i1-(k>0)),min(divs,i2-i1+(k<2)))/divs;
      q=q+sq(af+spanT*gap);
   }
   int rep=i==j?2:1;
   V=V+fplus(528-1680*q)/rep;
 }
 return V*sq(spanT/divs)/6;
}
I defr(I T,int k,int d,int divs){
 I V=0,spanT=T-k*af;
 int n=k-1;
 auto eval=[&](int i,int j,int l,int rep){
    int a[5]={0,i,j,l,divs};
    a[k]=divs;
    I pr=1,qs=I(8)/100*(1-T);
    double maxw=0;
    for(int p=0;p<k;p++){
       int i1=a[p],i2=a[p+1];
       I gap=I(max(0,i2-i1-(p>0)),min(divs,i2-i1+(p<n)))/divs;
       I ang=af+spanT*gap;
       pr=pr*ang;
       qs=qs+sq(ang);
       maxw=max(maxw,ang.l);
    }
    I base;
    if(k==2)base=(10080*I(maxw)-1056/I(maxw))*pr;
    else if(k==3)base=40320*pr;
    else base=80640*I(pr.l)/I(cap_sqrt(qs));
    I part=I(0,fplus(d-base).r);
    return part/(pr*rep);
 };
 if(k==2)for(int i=0;i<divs;i++)V=V+eval(i,0,0,1);
 if(k==3)for(int i=0;i<divs;i++)for(int j=i;j<divs;j++)V=V+eval(i,j,0,i==j?2:1);
 if(k==4)for(int i=0;i<divs;i++)for(int j=i;j<divs;j++)for(int l=j;l<divs;l++)
   V=V+eval(i,j,l,i==l?6:(i==j||j==l?2:1));
 return V*powI(spanT/divs,n)/fac(k);
}

int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants();prep_b(800);rank_dens();
 I MY=0,UX=(I(575)/80)*(I(77)/1000)*(I(154)/10),MX=0,UY=0;
 I mXneg=0,phiY=0,credit=0;
 int cells=0;
 for(int i=30;i<800;i+=2){
   int iu=min(800,i+2);I t=I(i,iu)/P,T=1-t;
   I high=0;
   for(int k=8;k<=12;k+=2){
    if(T.r <(k*af).l)continue;
    I d=range(taildens[k],max(k*A,idxlo(T.l)),max(k*A,idxhi(T.r)));
    I z=T/k;
    I amp=1056*I(1<<(k-5))*powI(z,3)+80640*I(1<<(k-7))*powI(z,5);
    high=high+amp*d;
   }
   I vol=I(iu-i)/P;
   MX=MX+high*vol;
   mark3=0;prep_g(0,t,0);
   int which[2]={1,2};
   I pos12=at0/T+integral(2,which,0,T,t,0,0,720,3)/2+pos4one(t,35);
   mXneg=mXneg+vol*fplus(pos12-mean(0,t,0,720)-I(0,high.r));
 }
 double p4max=0,p5max=0;
 for(int i=0;i<10000;i++){
   I z=I(i,i+1)/P,q=I(64)/P+z;
   const double s=cap_sqrt(q);
   I c4=fplus(1680*q-528)*z*powI(1-z,2)/4;
   I c5=fplus(10080*I(s)-1056/I(s))*z*powI(1-z,3)/27;
   p4max=max(p4max,c4.r);p5max=max(p5max,c5.r);
 }
 if(!(p4max<11.8 && p5max<15.4))abort();
 const int st=30,end=800,step=40;
 static I boxdef[261][35][5]; // indexed by T's lower rational 0..1 and its width <= .012
 static bool done[261][35]={};
 for(int i=st;i<end;i+=step)for(int j=i;j<end;j+=step)for(int l=j;l<end;l+=step){
   ++cells;
   int iu=min(end,i+step),ju=min(end,j+step),lu=min(end,l+step),sup=iu+ju+lu;
   I u=I(i,iu)/P,v=I(j,ju)/P,w=I(l,lu)/P,T=1-u-v-w;
   I pos=positive3(T)/2; 
   auto p=beta(sup);
   int rep=i==l?6:(i==j||j==l?2:1);
   I vol=I(iu-i)*I(ju-j)*I(lu-l)/I((double)P*P*P)/rep;
   MY=MY+pos*vol;
   double aAmp=0;
   for(int k=6;k<=12;k+=2){
    if(T.r <(k*af).l)continue;
    I z=T/k, amp=1056*I(1<<(k-3))*z+80640*I(1<<(k-5))*powI(z,3);
    aAmp=max(aAmp,amp.r);
   }
   UY=UY+p.second*vol*I(aAmp);
   phiY=phiY+vol*p.first;
   int aa=P-sup,q=sup-i-j-l;
   int fi=(aa-7600)/10, fj=q/5;
   if((aa-7600)%10 || q%5 || fi<0||fi>=261||fj<0||fj>=35)abort();
   const int ds[5]={125,150,175,200,225};
   if(!done[fi][fj]){
       I TT=I(aa,aa+q)/P;
       for(int h=0;h<5;h++){
         int d=ds[h];
         I val=d*sumB(TT,5,12);
         for(int k=2;k<=4;k++)val=val+defr(TT,k,d,52);
         boxdef[fi][fj][h]=val;
       }
       done[fi][fj]=true;
   }
   double best=0;
   for(int h=0;h<5;h++){
      I cc=ds[h]*mXneg*p.first-UX*boxdef[fi][fj][h];
      best=max(best,cc.l);
   }
   credit=credit+vol*I(best);
 }
 I debit=2*(MY*UX+MX*UY);
 credit=2*credit;
 I net=credit-debit;
 if(!(cells==1540 && credit.l>.05863 && debit.r<.0444 && net.l>.01432))abort();
 printf("cells %d; p4 %.12g p5 %.12g; mXneg %.12g PhiY %.12g; MY %.12g UY %.12g MX %.12g UX %.12g; debit %.12g credit %.12g net %.12g\n",
      cells,p4max,p5max,mXneg.l,phiY.l,MY.r,UY.r,MX.r,UX.r,debit.r,credit.l,net.l);
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
