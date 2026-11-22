from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

# Reuse the exact outward intervals and the audited one-arm densities.
base = Path(__file__).resolve().with_name("check_one_by_two_tag_credit.cpp")
raw = base.read_bytes()
if sha256(raw).hexdigest() != (
    "6dcdfea4141f79d656baefed4f2d386d3fe45c58486c0fbba1546c58949f7463"
):
    raise ArithmeticError("different base checker")

text = raw.decode()
if text.count("\nint main(){") != 1:
    raise ArithmeticError("ambiguous checker entry point")
text = text.split("\nint main(){")[0]

text += r"""
I polyF(double t){
 const I z=fplus(I(.5)-t),z2=sq(z);
 return sq(z2)*(44-112*z2);
}
I upper1(int lev){
 if(lev>=3200)return (I(575)/1000)/af;
 I D=I(lev)/P;
 if(lev<=2400)return 2/D;
 I s=D/af, v=s-3;
 return (2/D)*(1+sq(v)/4);
}
I lower1(int lev){
 if(lev>=3200)return (I(549)/1000)/af;
 if(lev<=1600)return 0;
 I D=I(lev)/P, T=1-(2*af)/D, a=0;
 for(int i=0;i<10;i++)a=a+powI(T,2*i+1)/(2*i+1);
 return 4*a/D;
}
const int K=10000;
const long long scale=10000000000000LL;
long long lo[40001],hi[40001];
__int128 cs[40001];
void rho2(){
 for(int i=0;i<=K;i++)lo[i]=hi[i]=scale;
 for(int i=K;i<4*K;i++){
  const long long a=i*i,b=1LL*(i+1)*(i+1);
  lo[i+1]=max(0LL,lo[i]-(2LL*(i+1-K)*hi[i-K]+a-1)/a);
  hi[i+1]=max(0LL,hi[i]-(2LL*(i-K)*lo[i+1-K])/b);
  if(lo[i+1]>hi[i+1])abort();
 }
 for(int i=0;i<4*K;i++)cs[i+1]=cs[i]+(2LL*i+1)*(__int128)lo[i+1];
}
I bound2(int h,int j,int b){
 int z=(1LL*K*499*(P-b-h-j))/(1000*800);
 if(z<=0||z>4*K)abort();
 I G=box((double)cs[z],(double)cs[z])/(2LL*K*K)/I(scale);
 return 1/(sq(af)*G);
}
I source(int lo,int hi,int withPNT){
 I res=0;
 for(int k=lo;k<hi;k++){
  I t=I(k,k+1)/P;
  I z=I(1)-I(polyF(t.r).l,polyF(t.l).r);
  I den=withPNT?t*(1-t):t;
  res=res+z/(den*P);
 }
 return res;
}
I volume(int i,int j,int step){
 // sqrt-free clipped rectangle (u+v>.065), with extra 1/2 for equal bins
 const long long x=650-i-j;
 const long long z=max(0LL,x),t=max(0LL,x-step),u=max(0LL,x-2*step);
 long long twice_area=2LL*step*step -(z*z-2*t*t+u*u);
 if(twice_area<0)abort();
 return I(twice_area)/(2LL*P*P)/(i==j?2:1);
}
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants();rho2();prep_b(800);
 constexpr int dp=10,beta=1251;
 static_assert((800-60)%dp==0);
 const I mZ=source(800,beta,1),m0=source(800,beta,0);
 int count=0;
 I V=0,full=0,ma0=0,mt0=0,signedUpper=0;
 double largest=0,smallest=1e10;
 for(int i=60;i+dp<=800;i+=dp)for(int j=i;j+dp<=800;j+=dp){
    const I vv=volume(i,j,dp);if(vv.r<=0 || i+j+2*dp<=650)continue;
    I u=I(i,i+dp)/P,v=I(j,j+dp)/P;
    prep_g(1,u,v);
    const int hi=i+j+2*dp;
    const int stop=4990-hi-450;
    I M=fplus(neg(at0))*upper1(4990-hi), T=0;
    I L1=at0*lower1(4990-hi), LT=0;
    if(at0.r>=0)abort();
    for(int k=800;k<5000;k++){
       const I e=fplus((pf[0][k]-pf[1][k])/2), o=fplus((pf[0][k]+pf[1][k])/2);
       const I g=profile[0][k],gp=fplus(g),gm=fplus(neg(g));
       if(k+1<=stop){
          const int D=4990-hi-k-1;
          const I U=upper1(D), K0=lower1(D);
          M=M+((U*o-K0*e)*gp+(U*e-K0*o)*gm)/P;
          L1=L1+((U*e-K0*o)*gp+(U*o-K0*e)*gm)/P;
       }else{
          I C2=bound2(hi,k+1,beta);
          T=T+C2*(o*gp+e*gm)/P;
          LT=LT+C2*(e*gp+o*gm)/P;
       }
    }
    const I C=M*mZ+T*m0;
    largest=max(largest,C.r);
    smallest=min(smallest,C.r);
    full=full+vv*C; signedUpper=signedUpper+vv*(L1*mZ+LT*m0);V=V+vv;ma0=ma0+vv*M*mZ;mt0=mt0+vv*T*m0;
    count++;
 }
 printf("E2-source %.8f %.8f, boxes %d area %.14f max/min %.8f %.8f main %.10f tail %.10f bilateral %.12f, upper %.12f\n",
       mZ.r,m0.r,count,V.r,largest,smallest,(2*ma0).r,(2*mt0).r,(2*full).r,(2*signedUpper).r);
 if(count!=2073 || (2*full).r>=(I(385)/1000).l ||
       (2*signedUpper).r>=neg(I(90)/1000).l)abort();
}
"""

with tempfile.TemporaryDirectory(prefix="sextic-medium-adverse-") as run:
    src = Path(run, "proof.cpp")
    out = Path(run, "proof")
    src.write_text(text)
    subprocess.run(
        ["c++", "-O3", "-std=c++17", "-ffp-contract=off", "-fno-fast-math",
         str(src), "-o", str(out)], check=True
    )
    subprocess.run([str(out)], check=True)
