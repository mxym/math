"""Outward full one-by-one certificate, including actual high-rank charge."""
from hashlib import sha256
from pathlib import Path
import subprocess, tempfile
here=Path(__file__).resolve().parent
base=here/'check_negative_one_by_three_credit.py'
raw=base.read_bytes()
if sha256(raw).hexdigest()!='7b86a6db2d004f76a016b6e71cb7cfe0a75a92c66358e420c02ea0bbbe7fd4e3':
    raise ArithmeticError('different audited input')
prefix, sep, cpp=raw.decode().partition('\ntext += r"""')
if not sep or cpp.count('\nint main(){')!=1:
    raise ArithmeticError('ambiguous preceding checker boundary')
env={'__file__':str(base)}
exec(compile(prefix,str(base),'exec'),env)
text=env['text']+cpp.split('\nint main(){')[0]
text+=r"""
I valueF(I x){
 I h=fplus(HALF-x), h2=sq(h);
 return sq(h2)*(44-112*h2);
}
I profile_cell(I t,I s){
 if(s.l>=.5)return 0;
 double cc=.5*t.l+.5*t.r, zz=.5*s.l+.5*s.r;
 I c=I(cc),z=I(zz);
 I gc=(valueF(z)-valueF(z+c))/c;
 I ds=(fp(z+c)-fp(z))/c;
 I dt=(fp(z+c)-gc)/c;
 I ht=I(up(max(cc-t.l,t.r-cc))), hs=I(up(max(zz-s.l,s.r-zz)));
 // The Hessian is an average of phi'' with factors v^0,v^1,v^2, so the full
 // two-variable Taylor remainder is bounded by 1200*(hs+ht)^2.
 I err=hs*I(ds.ab())+ht*I(dt.ab())+1200*sq(ht+hs);
 return fplus(I(dw(gc.l-err.r),up(gc.r+err.r)));
}
void prep_gc(I t){
 at0=profile_cell(t,0);
 for(int i=0;i<=P/2;i++)profile[0][i]=profile_cell(t,I(i,i+1)/P);
 sparse(profile,P/2);
}
I sw[6301], sv[6301], ufn[6301], lfn[6301];
void lin_sieve(){
  const int D=800; // parameter grid s=j/D; actual exponent j/P
  for (int j=0;j<=6300;j++){
    if(j<=2*D)sw[j]=0;
    if(j<=3*D)sv[j]=2;
    if(j>2*D){
       const int l=j-1-D,r=j-D;
       sw[j]=sw[j-1]+I(sv[l].l,sv[r].r)/I(l,r);
    }
    if(j>3*D){
       const int l=j-1-D,r=j-D;
       sv[j]=sv[j-1]+I(sw[l].l,sw[r].r)/I(l,r);
    }
    if(j>0){
       ufn[j]=j<D ? I(2)/(I(j)/P) :sv[j]/(I(j)/P);
       lfn[j]=sw[j]/(I(j)/P);
    }
  }
  ufn[0]=I(1e80);lfn[0]=0;
  if((lfn[3200]-I(549)/80).l<0 || (I(575)/80-ufn[3200]).l<0)abort();
}
using i128 = __int128_t;
const int rk=20000,rn=6*rk+10000;
const long long mx=1000000000000LL;
long long rh[rn+1],rl[rn+1];
i128 rid[rn+1];
I aff[P+1];
long long invceil(long long n,long long d){return (n+d-1)/d;}
void rough2_den(){
  for(int j=0;j<=rk;j++)rh[j]=rl[j]=mx;
  for(long long j=rk;j<rn;j++){
     long long c=invceil(2*(j+1-rk)*rh[j-rk],j*j);
     long long e=2*(j-rk)*rl[j+1-rk]/((j+1)*(j+1));
     rl[j+1]=max(0LL,rl[j]-c);
     rh[j+1]=max(0LL,rh[j]-e);
     if(rl[j+1]>rh[j+1])abort();
  }
  for(long long j=0;j<rn;j++)rid[j+1]=rid[j]+(2*j+1)*i128(rl[j+1]);
  for(int i=0;i<=7000;i++){
    // In units of a=.08, use lower integral endpoint floor(K*.499*(1-i/P)/a).
    const int j=(long long)rk*499*(P-i)/(1000*800);
    if(j<=0 || j>rn)abort();
    const I lower=I(dw((double(rid[j])/double(2LL*rk*rk))/double(mx)));
    aff[i]=1/(sq(af)*lower);
  }
}
I j_dens[13][15][P+10], jp0[P+10];
void all_ranks(){
 for(int j=1;j<=12;j++){
  for(int i=0;i<=P+1;i++){
    if(i<j*A)j_dens[j][0][i]=0;
    else {
       I x=I(i,i+1)/P;
       if(j==1)j_dens[j][0][i]=1/x;
       else j_dens[j][0][i]=I(jp0[i-A].l,jp0[i-A+1].r)/x;
    }
  }
  sparse(j_dens[j],P+1);
  jp0[0]=0;
  for(int i=0;i<=P+1;i++)jp0[i+1]=jp0[i]+j_dens[j][0][i]/P;
 }
}
I psm(int j,I T){
 if(T.r<(j*af).l)return 0;
 I a=range(j_dens[j],max(j*A,idxlo(T.l)),max(j*A,idxhi(T.r)));
 return I(T.l<(j*af).r?0:a.l,a.r);
}
struct Cell {int l,u,lev; I p,n,cp,cn,z; vector<I> g;};
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 const int DT=2, DS=5; // both axes: multiples of 1/P
 sieve_constants(); prep_b(800); all_ranks();
 lin_sieve(); rough2_den();
 vector<Cell> bank;
 int wh[2]={1,2};
 I HP=0, PP=0, NN=0, Ulow=0,Uhigh=0, amargo=0;
 for(int i=30;i<800;i+=DT){
  int iu=min(i+DT,800);
  const I t=I(i,iu)/P,T=1-t,w=I(iu-i)/P;
  prep_gc(t);
  I p=at0/T+integral(2,wh,0,T,t,0,0,1440,3)/2+pos4one(t,96);
  p=fplus(p);
  I h=0,cheavy=0;
  for(int k=8;k<=12;k+=2){
   auto amp=1056*I(1<<(k-5))*powI(T/k,3)+80640*I(1<<(k-7))*powI(T/k,5);
   if(T.r<(k*af).l)continue;
   h=h+amp*psm(k,T);
   cheavy=I(max(cheavy.r,amp.r));
  }
  // true one-integer signed mean of the entire profile; use |m(H_h)|≤h.
  I mm=mean(0,t,0,1440);
  I n=fplus(p-mm+I(-h.r,h.r));
  I qc=fplus(528-1680*(sq(t)+sq(T)/3))*powI(T/3,3);
  I cp=I(max(at0.r,qc.r));
  I cn=I(154)/10;
  const int lev=min(5000+i/2,(40000-6*iu)/7)-4;
  if(lev<4990 || lev>5263)abort();
  vector<I> g;
  for(int si=0;si<P/2;si+=DS)g.push_back(fplus(range(profile,si,si+DS-1)));
  bank.push_back({i,iu,lev,p,n,cp,cn,fplus(at0),g});
  HP=HP+w*h; PP=PP+w*p; NN=NN+w*n;
  Ulow=Ulow+w*(I(575)/80)*I(max(cp.r,cn.r));
  Uhigh=Uhigh+w*(I(575)/80)*cheavy;
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
 auto dir=[&](const Cell& a,const Cell& b){
    int D0=a.lev-b.u;
    if(D0<800)abort();
    I cpos=lfn[D0]*b.z, cneg=neg(ufn[D0]*b.z), cost=0;
    auto mid=[](I v){return v.l*.5+v.r*.5;};
    for(int l=0;l<P/2;l+=DS){
       int idx=l/DS,h=l+DS;
       if(l<A)continue;
       int de=a.lev-b.u-h;
       const I tp=pe[idx],to=po[idx],g=b.g[idx],ab=aff[a.u+b.u+h], ws=I(DS)/P*g;
       I dp=de>0?lfn[de]*tp:I(0),dn=de>0?lfn[de]*to:I(0);
       const I ap=a.cp*ab, an=a.cn*ab;
       if(de>0 && mid(a.p)*mid(ufn[de])<ap.r) dp=dp-to*ufn[de];
       else cost=cost+ws*to*ap;
       if(de>0 && mid(a.n)*mid(ufn[de])<an.r) dn=dn-tp*ufn[de];
       else cost=cost+ws*tp*an;
       cpos=cpos+ws*dp;cneg=cneg+ws*dn;
    }
    return a.p*cpos+a.n*cneg-cost;
 };
 I ans=0,basic=0,early=0;
 for(auto& x:bank)for(auto& y:bank){
    I a=dir(x,y),b=dir(y,x);
    I w=I(x.u-x.l)*I(y.u-y.l)/(I(P)*P);
    ans=ans+I(max(a.l,b.l))*w;
    basic=basic+a*w;
    if(x.u<=260&&y.u<=260)early=early+I(max(a.l,b.l))*w;
 }
 I tails=(2*Ulow+Uhigh)*HP;
 I lower=ans-tails;
 if(bank.size()!=385 || tails.r>=.0039181 || lower.l<=.07050) abort();
 printf("inputs %zu/%d, P %.8f %.8f, N %.8f %.8f, m_h %.8f, U_l %.8f, U_h %.8f\n",
      bank.size(),DS,PP.l,PP.r,NN.l,NN.r,HP.r,Ulow.r,Uhigh.r);
 printf("one-direction %.12f full lower %.12f early %.12f tails %.12f remainder %.12f\n",basic.l,ans.l,early.l,tails.r,lower.l);
}
"""
with tempfile.TemporaryDirectory(prefix='strong-one-one-') as d:
    src=Path(d)/'proof.cpp'; out=Path(d)/'proof'
    src.write_text(text)
    subprocess.run(['c++','-O3','-std=c++17','-ffp-contract=off','-fno-fast-math',str(src),'-o',str(out)],check=True)
    subprocess.run([str(out)],check=True)
