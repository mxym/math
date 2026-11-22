"""Exact outward certificate on the entire original 1 x 2 chamber."""
from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile
base=Path(__file__).resolve().with_name("check_full_one_by_one.py")
raw=base.read_bytes()
if sha256(raw).hexdigest()!="3c2328333a931defbb7f1ddf3f0a62ed18d1b2b9e48aa922ee83a4153c4ca9c6":
    raise ArithmeticError("different audited direct atom")
prefix,sep,cpp=raw.decode().partition('\ntext+=r"""')
if not sep or cpp.count("\nstruct Cell")!=1:
    raise ArithmeticError("ambiguous previous direct-atom helper boundary")
env={"__file__":str(base)}
exec(compile(prefix,str(base),"exec"),env)
helpers=cpp.split("\nstruct Cell")[0]
if helpers.count("i<=7000")!=1:
    raise ArithmeticError("different actual affine range")
text=env["text"]+helpers.replace("i<=7000","i<=8000")

text += r"""
struct XCell {int l,u; I w,z,pos,neg,cp,cn; vector<I> g;};
struct YCell {int l1,l2,u1,u2,s,lev; I w,neg,cap; vector<I> g; I g0;};
int lev(int il,int iu){
  return min(5000+il/2,(40000-6*iu)/7)-4;
}
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants(); prep_b(800); all_ranks(); lin_sieve(); rough2_den();
 const int DT=5,DS=5, DY=40;
 vector<XCell> X;
 I Ux=0,Uxh=0,mXh=0,mxr[3],uxr[3],myr[3],uyr[3];
 for(int i=30;i<800;i+=DT){
   int iu=min(800,i+DT);
   I t=I(i,iu)/P,T=1-t,w=I(iu-i)/P;
   prep_gc(t);
   I p=0,n=0,cp=0,cn=I(154)/10;
   vector<I> g;
   for(int si=0;si<P/2;si+=DS)g.push_back(fplus(range(profile,si,si+DS-1)));
   X.push_back({i,iu,w,fplus(at0),p,n,cp,cn,g});
   double cap=(I(154)/10).r,hcap=0;
   for(int k=8;k<=12;k+=2){
      if(T.r<(k*af).l)continue;
      I z=T/k,p0=1056*I(1<<(k-5))*powI(z,3)+80640*I(1<<(k-7))*powI(z,5);
      hcap=max(hcap,p0.r);
      mXh=mXh+w*p0*psm(k,T); mxr[(k-8)/2]=mxr[(k-8)/2]+w*p0*psm(k,T); uxr[(k-8)/2]=uxr[(k-8)/2]+w*(I(575)/80)*p0;
   }
   Uxh=Uxh+w*(I(575)/80)*I(hcap);
   Ux=Ux+w*(I(575)/80)*I(max(cap,hcap));
 }
 vector<YCell> Y;
 I Mh=0, Ul=0,mYlow=0;
 for(int i=30;i<800;i+=DY)for(int j=i;j<800;j+=DY){
   int iu=min(i+DY,800),ju=min(j+DY,800),h=iu+ju;
   I u=I(i,iu)/P,v=I(j,ju)/P,T=1-u-v;
   I w=I(iu-i)*I(ju-j)/I(P*P)/(i==j?2:1);
   mark3=0;prep_g(1,u,v);
   vector<I> g;
   for(int si=0;si<P/2;si+=DS)g.push_back(range(profile,si,si+DS-1));
   I g0=at0;
   I mm=mean(1,u,v,800),mh=0;
   for(int k=7;k<=11;k+=2){
     if(T.r<(k*af).l)continue;
     I z=T/k;
     I p0=1056*I(1<<(k-4))*sq(z)+80640*I(1<<(k-6))*powI(z,4);
     mh=mh+p0*psm(k,T);
     myr[(k-7)/2]=myr[(k-7)/2]+w*p0*psm(k,T);
     uyr[(k-7)/2]=uyr[(k-7)/2]+w*(I(575)/80)*p0;
   }
   Mh=Mh+w*mh;
   I m=neg(mm)+I(-mh.r,mh.r);
   if(i+j<650 && iu>50 && ju>50){
      prep_b(1630);
      I mw=fplus(neg(mean(1,u,v,800)));
      m=m-I(0,mw.r);
      prep_b(800);
   }
   m=fplus(m);mYlow=mYlow+w*m;
   I qs=sq(u)+sq(v);
   double cap=max((40320*powI(T/4,4)).r,(2112*sq(T/5)+80640*I(cap_sqrt(10))*powI(T/5,5)/T).r);
   cap=max(cap,g0.ab());
   for(int zi=0;zi<1000;zi++){
      I th=I(zi,zi+1)/1000,z=T*th;
      I qq=qs+sq(z)+sq(T-z);
      cap=max(cap,(fplus(1680*qq-528)*sq(T)*th*(1-th)).r);
      double r=cap_sqrt(qq);
      cap=max(cap,(fplus(10080*I(r)-1056/I(r))*z*sq((T-z)/2)).r);
   }
   Ul=Ul+w*(I(575)/80)*I(cap);
   Y.push_back({i,j,iu,ju,h,max(lev(i,iu),lev(j,ju)),w,m,I(cap),g,g0});
 }
 vector<I> pe,po;
 for(int lo=0;lo<P/2;lo+=DS){
   I e=0,o=0;
   for(int j=1;j<=6;j++){
     if(lo<j*A)continue;
     I V=range(j_dens[j],lo,lo+DS-1);
     if(j%2)o=o+V;else e=e+V;
   }
   pe.push_back(fplus(e));po.push_back(fplus(o));
 }
 auto mid=[](I v){return v.l*.5+v.r*.5;};
 auto dir=[&](const XCell& a,const YCell& b){
    int D0=b.lev-a.u;
    if(D0<800)abort();
    I cn=neg(ufn[D0]*a.z),cost=0;
    for(int l=800;l<P/2;l+=DS){
       int idx=l/DS,h=l+DS;
       int de=b.lev-a.u-h;
       const I e=pe[idx],o=po[idx],g=a.g[idx],ab=aff[a.u+b.s+h],ws=I(DS)/P*g;
       I dn=de>0?lfn[de]*o:I(0);
       const I aa=b.cap*ab;
       if(de>0 && mid(b.neg)*mid(ufn[de])<aa.r)dn=dn-e*ufn[de];
       else cost=cost+ws*e*aa;
       cn=cn+ws*dn;
    }
    return b.neg*cn-cost;
 };
 I ans=0;
 int nc=0;
 for(const auto& x:X)for(const auto& y:Y){
    I r=dir(x,y),v=x.w*y.w;
    ans=ans+r*v;
    if(r.l>0)nc++;
 }
 I hi=0;
 for(int i=0;i<3;i++)for(int j=0;j<3;j++)
   hi=hi+I(min((uxr[i]*myr[j]).r,(uyr[j]*mxr[i]).r));
 I xlo=I(154)/10*I(575)/80*I(77)/1000;
 I rest=2*(Mh*xlo+hi),net=2*ans-rest;
 printf("X=%zu Y=%zu positive %d; mYneg %.12g %.12g mYh %.12g Ux %.12g Ul %.12g; paired both gross %.12g tail %.12g net %.12g\n",X.size(),Y.size(),nc,mYlow.l,mYlow.r,Mh.r,Ux.r,Ul.r,(2*ans).l,rest.r,net.l);
 if(!(X.size()==154 && Y.size()==210 && nc==23243 && (2*ans).l>.5876248 &&
       rest.r<.014238 && net.l>.5733869))abort();
}

"""
with tempfile.TemporaryDirectory(prefix='sextic-full-one-two-') as d:
    src=Path(d)/'proof.cpp'; out=Path(d)/'proof'
    src.write_text(text)
    subprocess.run(['c++','-O3','-std=c++17','-ffp-contract=off','-fno-fast-math',str(src),'-o',str(out)],check=True)
    subprocess.run([str(out)],check=True)
