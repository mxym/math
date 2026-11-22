"""Actual whole-three-tag ledger and outward ordinary/prime inputs."""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

ul,ua,h,m=map(F,(".55006","7.736",".002527",".350"))
B=F("1.228")*F(".344")-F(".091")+ul*(F(".01701")+F(".16921"))
B+=(F(".852")+F(".52844"))*h+ua*F(".009042")+F(".007445")*m
self_cost=ul*(m+h)+ua*h
mj=list(map(F,(".01933",".00345",".000534",".000078",".0000114")))
uj=list(map(F,(".373","1.232","12.850","8.679","35.095")))
C=F(".1212")*m+ul*sum(mj)/2+sum(min(u*h,ua*a)/2 for a,u in zip(mj,uj))
total=2*B+self_cost+2*C
if not total<F("1.340"):
    raise ArithmeticError("literal union cost")
print("True union rational cost:",float(total),flush=True)

base=Path(__file__).resolve().with_name("check_negative_one_by_three_credit.py")
raw=base.read_bytes()
if sha256(raw).hexdigest()!="7b86a6db2d004f76a016b6e71cb7cfe0a75a92c66358e420c02ea0bbbe7fd4e3":
    raise ArithmeticError("different audited tag-3 inputs")
prefix,sep,cpp=raw.decode().partition('\ntext += r"""')
if not sep or cpp.count("\nint main(){")!=1:
    raise ArithmeticError("ambiguous audited boundary")
env={"__file__":str(base)}
exec(compile(prefix,str(base),"exec"),env)
text=env["text"]+cpp.split("\nint main(){")[0]
text += r"""
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants();prep_b(800);rank_dens();
 I MY=0,UX=I(400)/111,MX=0,UY=0;
 I mXneg=1,phiY=0,credit=0,signedY=0;
 int cells=0;
 const int st=30,end=800,step=40;
 static I boxdef[261][35][14]; // indexed by T's lower rational 0..1 and its width <= .012
 static bool done[261][35]={};
 for(int i=st;i<end;i+=step)for(int j=i;j<end;j+=step)for(int l=j;l<end;l+=step){
   ++cells;
   int iu=min(end,i+step),ju=min(end,j+step),lu=min(end,l+step),sup=iu+ju+lu;
   I u=I(i,iu)/P,v=I(j,ju)/P,w=I(l,lu)/P,T=1-u-v-w;
   I pos=positive3(T)/2; 
   auto p=beta(sup);
   int rep=i==l?6:(i==j||j==l?2:1);
   I vol=I(iu-i)*I(ju-j)*I(lu-l)/I((double)P*P*P)/rep;
   mark3=w;prep_g(2,u,v);
   signedY=signedY+vol*mean(2,u,v,400);
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
   const int ds[14]={125,175,225,275,325,375,425,475,525,575,625,675,725,775};
   if(!done[fi][fj]){
       I TT=I(aa,aa+q)/P;
       for(int h=0;h<14;h++){
         int d=ds[h];
         I r4=fplus(d-(1680*sq(TT)-528)*TT)/TT;
         I val=d*sumB(TT,5,12)+r4;
         for(int k=2;k<=4;k++)val=val+defr(TT,k,d,52);
         boxdef[fi][fj][h]=val;
       }
       done[fi][fj]=true;
   }
   double best=0;
   for(int h=0;h<14;h++){
      I cc=ds[h]*mXneg*p.first-UX*boxdef[fi][fj][h];
      best=max(best,cc.l);
   }
   credit=credit+vol*I(best);
 }
 I debit=2*(MY*UX+MX*UY);
 credit=2*credit;
 I net=credit-debit;
 if(!(cells==1540 && signedY.l>-.344 && MY.r<.002527 && net.l>.18308))abort();
 printf("complete true tag-3 model [%.12g,%.12g], high absolute %.12g, positive prime gain %.12g, high prime debit %.12g, one-orientation prime rebate %.12g\n",
 signedY.l,signedY.r,MY.r,credit.l/2,debit.r/2,net.l/2);
}

"""
with tempfile.TemporaryDirectory(prefix="sextic-whole-three-tag-") as run:
    src = Path(run, "proof.cpp")
    out = Path(run, "proof")
    src.write_text(text)
    subprocess.run(
        ["c++", "-O3", "-std=c++17", "-ffp-contract=off", "-fno-fast-math",
         str(src), "-o", str(out)], check=True
    )
    subprocess.run([str(out)], check=True)
