"""Outward check of the entire positive nonsemiprime one-by-three debit."""
from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

base = Path(__file__).resolve().with_name("check_negative_one_by_three_credit.py")
raw = base.read_bytes()
if sha256(raw).hexdigest() != (
    "7b86a6db2d004f76a016b6e71cb7cfe0a75a92c66358e420c02ea0bbbe7fd4e3"
):
    raise ArithmeticError("different audited three-tag inputs")
prefix, sep, cpp = raw.decode().partition('\ntext += r"""')
if not sep or cpp.count("\nint main(){") != 1:
    raise ArithmeticError("ambiguous prior C++ boundary")
env = {"__file__": str(base)}
exec(compile(prefix, str(base), "exec"), env)
text = env["text"] + cpp.split("\nint main(){")[0]

text += r"""
I g1tight(I t,I x){
    if(x.l>=.5)return 0;
    if((x+t).r<=.5){
      I z=HALF-x-t/2,q=sq(z),v=sq(t)/12,v4=sq(sq(t))/80;
      return z*(176*(q+3*v)-672*(sq(q)+10*q*v+5*v4));
    }
    I v=0;
    for(int j=0;j<50;j++){
      I u=x+t*I(j,j+1)/50, h=fplus(HALF-u);
      I q1=I(h.l),q2=I(h.r);
      I k1=q1*powI(q1,2)*(176-672*sq(q1)), k2=q2*powI(q2,2)*(176-672*sq(q2));
      double lo=min(k1.l,k2.l),hi=max(k1.r,k2.r);
      I c=I(11)/70;
      double w=cap_sqrt(c), wl=dw(dw(sqrt(c.l)));
      if((I(wl)*I(wl)).r>c.l)abort();
      if(h.l<=w&&h.r>=wl)hi=max(hi,(I(w)*c*(176-672*c)).r);
      v=v+I(lo,hi)/50;
    }
    return v;
}
void prep_gtight(I t){
 at0=g1tight(t,0);
 for(int i=0;i<=P/2;i++)profile[0][i]=g1tight(t,I(i,i+1)/P);
 sparse(profile,P/2);
}
I UshortF(int Dnum){
  I D=I(Dnum)/P;
  if(Dnum<=2400)return 2/D;
  if(Dnum>=4000) return UshortF(3999);
  I s=D/af;
  I cap=0,wid=(s-3)/192;
  for(int j=1;j<=192;j++){
      I t=j*wid;
      // supremum of log(1+t)/(2+t) is at t approximately 2.59, so monotone for t≤2.
      I y=t/(2+t), y2=sq(y), v=0,z=y;
      for(int k=0;k<20;k++,z=z*y2)v=v+2*z/(2*k+1);
      v=v+2*z/(41*(1-y2));
      cap=cap+v/(2+t)*wid;
  }
  return 2*(1+cap)/D;
}
int main(){
 sieve_constants();prep_b(800);rank_dens();
 I m3=0,m4=0,mh=0,mY=0,mYhi=0,U=0,U123=0,U1234=0,Usplit=0;
 I u3=0,u4=0;
 int cells=0;
 int which[2]={1,2};
 for(int i=30;i<800;i+=2){
    int iu=min(800,i+2);I t=I(i,iu)/P,T=1-t;
    I vol=I(iu-i)/P;
    mark3=0;prep_gtight(t);
    m3=m3+vol*integral(2,which,0,T,t,0,0,720,3)/2;
    m4=m4+vol*pos4one(t,60);
    u3=u3+fplus(at0)*vol*(I(575)/80);
    u4=u4+fplus(528-1680*(sq(t)+sq(T)/3))*powI(T/3,3)*vol*(I(575)/80);
    for(int k=8;k<=12;k+=2){
      if(T.r <(k*af).l)continue;
      I den=range(taildens[k],max(k*A,idxlo(T.l)),max(k*A,idxhi(T.r)));
      I z=T/k;
      mh=mh+vol*(1056*I(1<<(k-5))*powI(z,3)+80640*I(1<<(k-7))*powI(z,5))*den;
    }
 }
 const int st=30,end=800,step=40;
 for(int i=st;i<end;i+=step)for(int j=i;j<end;j+=step)for(int l=j;l<end;l+=step){
   ++cells;
   int iu=min(end,i+step),ju=min(end,j+step),lu=min(end,l+step),sup=iu+ju+lu;
   I t=I(i,iu)/P,v=I(j,ju)/P,w=I(l,lu)/P,T=1-t-v-w;
   I qs=sq(t)+sq(v)+sq(w);
   auto b=beta(sup);
   int rep=i==l?6:(i==j||j==l?2:1);
   I vol=I(iu-i)*I(ju-j)*I(lu-l)/I((double)P*P*P)/rep;
   double caps[13]={0},below[5]={0};
   I D=I(4980-sup)/P;
   I floor=D/3;
   caps[1]=max(0.,(T*(1680*(qs+sq(T))-528)).r);
   for(int zi=0;zi<500;zi++){
     I tau=I(500+zi,501+zi)/1000;
     I z=T*tau;
     if((T-z).r<af.l)continue;
     I q=qs+(sq(tau)+sq(1-tau))*sq(T);
     double sqr=cap_sqrt(q);
     double cap=(fplus(10080*I(sqr)-1056/I(sqr))*sq(T)*tau*(1-tau)).r;
     caps[2]=max(caps[2],cap);
     if((T* (1-tau)-floor).l<=0)below[2]=max(below[2],cap);
   }
   caps[3]=(40320*powI(T/3,3)).r;
   below[3]=(40320*floor*sq(T-floor)/4).r;
   caps[4]=(1056*T/2+80640*I(cap_sqrt(8))*powI(T/4,4)/T).r;
   below[4]=(2112*floor+80640*I(cap_sqrt(8))*floor*powI((T-floor)/3,3)/T).r;
   for(int k=6;k<=12;k+=2){
    if(T.r <(k*af).l)continue;
    I z=T/k, amp=1056*I(1<<(k-3))*z+80640*I(1<<(k-5))*powI(z,3);
    caps[k]=amp.r;
   }
   double m=0,m123=0,m1234=0;
   for(int k=1;k<=12;k++)if(T.r >=(k*af).l){
     m=max(m,caps[k]);if(k<=3)m123=max(m123,caps[k]);if(k<=4)m1234=max(m1234,caps[k]);
     I den=range(taildens[k],max(k*A,idxlo(T.l)),max(k*A,idxhi(T.r)));
     mY=mY+I(caps[k])*den*vol;if(k>=5)mYhi=mYhi+I(caps[k])*den*vol;
   }
   double mb=0;
   for(int k=1;k<=4;k++)mb=max(mb,below[k]);
   if(mb>m1234)mb=m1234;
   auto fa=UshortF(4980-sup);
   I u0=2/D, split=I(m1234)*u0+I(mb)*fplus(fa-u0);
   Usplit=Usplit+vol*I(min((b.second*I(m1234)).r,split.r));
   U=U+b.second*vol*I(m);U123=U123+b.second*vol*I(m123);U1234=U1234+b.second*vol*I(m1234);
 }
 I debit=2*((m3+m4)*Usplit+(u3+u4)*mYhi+mh*U);
 printf("cells %d; mX34 %.12g UX34 %.12g mXh %.12g; UYlow %.12g mYh %.12g UY %.12g; bilateral debit %.12g\n",
   cells,(m3+m4).r,(u3+u4).r,mh.r,Usplit.r,mYhi.r,U.r,debit.r);
 if(!(cells==1540 && (m3+m4).r<.16881 && (u3+u4).r<1.493 && mh.r<.000081 &&
       Usplit.r<.55006 && mYhi.r<.002527 && U.r<7.736 && debit.r<.1945))abort();
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
