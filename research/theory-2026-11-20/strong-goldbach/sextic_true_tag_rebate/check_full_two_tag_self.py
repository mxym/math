"""Outward lower on the full original actual two-tag self-pair."""
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

a = Q(2, 25)
def F(t):
    z = Q(1,2)-t
    return 44*z**4-112*z**6
if (F(0)-2*F(a)+F(2*a))/a**2 != -Q(5723854,390625):
    raise ArithmeticError("literal rank-three maximum")
base = Path(__file__).resolve().with_name("check_full_two_by_three_tag_credit.py")
raw = base.read_bytes()
if sha256(raw).hexdigest() != "7b1dbcf90742104c386e93c109bfe542c09eb131fa6c904be213e069c95f6c29":
    raise ArithmeticError("different audited two-tag inputs")
prefix, sep, cpp = raw.decode().partition('\ntext += r"""')
if not sep or cpp.count("\nint main(){") != 1:
    raise ArithmeticError("ambiguous two-tag helper boundary")
env = {"__file__": str(base)}
exec(compile(prefix, str(base), "exec"), env)
text = env["text"] + cpp.split("\nint main(){")[0]

text += r"""
int main(){
 constexpr int st=30,end=800,step=60,ns=96;
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants();prep_b(800);rank_dens();
 I ma=0, Mh=0,Ul=0,Ua=0, mhRank[3],uRank[3];
 struct D {int d,s,rep; I vol,m,ms,ua; bool good;}; vector<D> bank;
 for(int i=st;i<end;i+=step)for(int j=i;j<end;j+=step){
   int iu=min(end,i+step),ju=min(end,j+step),sup=iu+ju;
   I u=I(i,iu)/P,v=I(j,ju)/P,T=1-u-v;
   int r=i==j?2:1;
   I vol=I(iu-i)*I(ju-j)/I(P*P)/r; ma=ma+vol;
   bool good=i+j>=650||iu<=50||ju<=50;
   mark3=0;prep_g(1,u,v);
   I md=rr(0,T),m=0,ss=0;
   int d=0;
   if(good){
      m=mean(1,u,v,ns);
      d=max(1,int((-m.l-m.r)/(md.l+md.r)));
      ss=mean2(1,u,v,d,ns);
   }
   I qs=sq(u)+sq(v);
   double cap=max( (40320*powI(T/4,4)).r,(2112*sq(T/5)+80640*I(cap_sqrt(10))*powI(T/5,5)/T).r);
   cap=max(cap,at0.ab());
   for(int zi=0;zi<1000;zi++){
     I th=I(zi,zi+1)/1000,z=T*th;
     I qq=qs+sq(z)+sq(T-z);
     cap=max(cap,(fplus(1680*qq-528)*sq(T)*th*(1-th)).r);
     qq=qs+sq(z)+sq(T-z); // for rank5, remaining two squares ≤ (T-z)^2.
     double w=cap_sqrt(qq);
     cap=max(cap,(fplus(10080*I(w)-1056/I(w))*z*sq((T-z)/2)).r);
   }
   double ca=cap;
   for(int k=7;k<=11;k+=2){
     if(T.r<(k*af).l)continue;
     I w=T/k,z=1056*I(1<<(k-4))*sq(w)+80640*I(1<<(k-6))*powI(w,4);
     I den=range(taildens[k],max(k*A,idxlo(T.l)),max(k*A,idxhi(T.r)));
     ca=max(ca,z.r);
     Mh=Mh+vol*z*den; mhRank[(k-7)/2]=mhRank[(k-7)/2]+vol*z*den; uRank[(k-7)/2]=uRank[(k-7)/2]+vol*z*(I(575)/80);
   }
   I U=I(575)/80;
   Ul=Ul+vol*U*I(cap);Ua=Ua+vol*U*I(ca);
   bank.push_back({d,sup,r,vol,m,ss,U*md,good});
 }
 if(ma.l>(I(77)/1000*I(77)/1000/2).r || ma.r<(I(77)/1000*I(77)/1000/2).l)abort();
 I score=0,U=I(575)/80,k=I(549)/80;
 int nn=0;
 for(size_t i=0;i<bank.size();i++)for(size_t j=i;j<bank.size();j++){
   const auto &a=bank[i],&b=bank[j];
   if(!a.good||!b.good)continue;
   I lo=k*(a.d*fplus(neg(b.m))+b.d*fplus(neg(a.m)))
        -a.d*b.d*I(0,min(a.ua.r,b.ua.r))-I(0,cap_sqrt(U*U*a.ms*b.ms));
   if(lo.l<=0)continue;
   score=score+(i==j?1:2)*a.vol*b.vol*I(lo.l);
   nn++;
 }
 I high=0;
 for(int i=0;i<3;i++)for(int j=0;j<3;j++)high=high+I(min((uRank[i]*mhRank[j]).r,(uRank[j]*mhRank[i]).r));
 I debt=2*Mh*Ul+high;
 printf("m ranks %.12g %.12g %.12g; U ranks %.12g %.12g %.12g high %.12g\n",
 mhRank[0].r,mhRank[1].r,mhRank[2].r,uRank[0].r,uRank[1].r,uRank[2].r,high.r);
 printf("bins %zu area %.12g total pos %d lower %.12g, m_hi %.12g Ulo %.12g Uall %.12g debit %.12g full closed %.12g\n",
 bank.size(),ma.r,nn,score.l,Mh.r,Ul.r,Ua.r,debt.r,(score-debt).l);
 if(!(bank.size()==91 && nn==1891 && score.l>.196699 && debt.r<.009287 && (score-debt).l>.187412))abort();
}
"""
with tempfile.TemporaryDirectory(prefix="sextic-full-two-tag-self-") as run:
    src = Path(run, "proof.cpp")
    out = Path(run, "proof")
    src.write_text(text)
    subprocess.run(
        ["c++", "-O3", "-std=c++17", "-ffp-contract=off", "-fno-fast-math",
         str(src), "-o", str(out)], check=True
    )
    subprocess.run([str(out)], check=True)
