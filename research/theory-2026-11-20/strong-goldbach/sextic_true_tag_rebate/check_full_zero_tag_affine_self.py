from fractions import Fraction as Q
from hashlib import sha256
from math import factorial
from pathlib import Path
import subprocess
import tempfile

# Euler--Maclaurin with alternating remainder, plus lower log 2 by atanh.
n = 256
log2 = sum((Q(2, (2*j+1)*3**(2*j+1)) for j in range(40)), Q(0))
gamma_hi = sum((Q(1,i) for i in range(1,n+1)),Q(0))-8*log2-Q(1,2*n)+Q(1,12*n*n)
t = 2*gamma_hi
if not 0 < t < 2:
    raise ArithmeticError("exponential tail range")
exp_hi = sum((t**j/factorial(j) for j in range(41)),Q(0)) + t**41/factorial(41)/(1-Q(2,42))
if not 1/exp_hi > Q(3152,10000):
    raise ArithmeticError("exp(-2 gamma) inequality")

# Reuse only the audited ordinary/one-arm and augmented Selberg routines.
base = Path(__file__).resolve().with_name("check_small_semiprime_three_tag.py")
raw = base.read_bytes()
if sha256(raw).hexdigest() != "27d2df301617567e940c97f26eb7c5e82a2c9c31d6ea333f873b1b6f11b1716e":
    raise ArithmeticError("different base checker")
setup, sep, part = raw.decode().partition('\ntext += r"""')
prior, sep2, body = part.partition('\nint main(){')
if not sep or not sep2 or body.count('int main(){'):
    raise ArithmeticError("ambiguous base checker boundary")
env = {"__file__": str(base)}
exec(compile(setup, str(base), "exec"),env)
text = env["text"]+prior
text += r"""
const int JQ=10000, JL=7*JQ;
const long long FS=10000000000000LL;
long long flo[JL+2], fhi[JL+2];
__int128 cL[JL+2],cU[JL+2];
I fMoment[125005];
long long ceillong(long long num,long long den){return (num+den-1)/den;}
void g2_cdf(){
 for(int j=0;j<=JQ;j++)flo[j]=fhi[j]=FS;
 for(long long j=JQ;j<JL;j++){
   flo[j+1]=max(0LL,flo[j]-ceillong(2*(j+1-JQ)*fhi[j-JQ],j*j));
   fhi[j+1]=max(0LL,fhi[j]-2*(j-JQ)*flo[j+1-JQ]/((j+1)*(j+1)));
   if(flo[j+1]>fhi[j+1])abort();
 }
 for(int j=0;j<JL;j++){
   cL[j+1]=cL[j]+(2*j+1)*(__int128)flo[j+1];
   cU[j+1]=cU[j]+(2*j+1)*(__int128)fhi[j];
 }
}
I Graw(int j,bool lower){
 if(j<=0||j>JL)abort();
 double v=(double)(lower?cL[j]:cU[j]);
 return box(v,v)/I(2LL*JQ*JQ)/I(FS);
}
void f2_integral(){
 // lower integral for exp(-2 gamma)*s^2*f_2(s).
 const int betaHi=42670,vStop=62660;
 for(int i=betaHi;i<125001;i++){
   I addon;
   if(i<vStop) {
     int q=(i+2-JQ)/2;  // upward (i+1-JQ)/2
     addon=(I(2)*I(i)/JQ)/Graw(q,false)/JQ;
   } else {
     // F_2(s-1)>=1.
     addon=(I(3152)/10000)*(I(2*i+1)/I(1LL*JQ*JQ));
   }
   fMoment[i+1]=fMoment[i]+addon;
 }
}
I lowerD(int maxSum){
 // physical support exponent .999*(1-s0^+-s1^+); round ratio downward.
 int j=(999LL*(P-maxSum)*JQ)/(1000*A);
 if(j<=42670)return 0;
 I x=I(j)/JQ;
 return fMoment[j]/(sq(x)*sq(af));
}
I upperD(int maxSum){
 // actual Selberg floor D_small^2 < fibre length.
 int j=(499LL*(P-maxSum)*JQ)/(1000*A);
 return 1/(Graw(j,true)*sq(af));
}
I polybox(int l,int h){
 I t=I(l,h)/P;
 return I(polyF(t.r).l,polyF(t.l).r);
}
struct Group{int hi;I e,o,w,profile;};
I estimatePi(){
 I total=upper1(4990);
 for(int j=800;j<5000;j++){
   I e=fplus((pf[0][j]-pf[1][j])/2),o=fplus((pf[0][j]+pf[1][j])/2);
   I g=polybox(j,j+1);
   I plus=bound2(j+1,0,0)*e*g;
   int D=4990-j-1;
   if(D>0){
     I cand=(upper1(D)*e-lower1(D)*o)*g;
     if(cand.r<plus.r)plus=cand;
   }
   total=total+I(plus.r)/P;
 }
 return total;
}
I roughQcoeff(){
 I total=lower1(4990);
 for(int j=800;j<4989;j++){
   I e=fplus((pf[0][j]-pf[1][j])/2),o=fplus((pf[0][j]+pf[1][j])/2);
   I g=polybox(j,j+1);
   int D=4990-j-1;
   total=total+g*(lower1(D)*e-upper1(D)*o)/P;
 }
 return total;
}
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants();rho2();prep_b(800);g2_cdf();f2_integral();
 const int step=1;
 vector<Group> zz={{0,1,0,1,1}};
 for(int j=800;j<4999;j+=step){
   int h=min(4999,j+step);
   I BP=rr(0,I(j,h)/P),BN=rr(1,I(j,h)/P);
   zz.push_back({h,fplus((BP-BN)/2),fplus((BP+BN)/2),I(h-j)/P,polybox(j,h)});
 }
 static I dcL[P+1],dcU[P+1];
 for(int j=0;j<=9998;j++) {
   dcL[j]=lowerD(j);
   dcU[j]=upperD(j);
 }
 I lb=0;
 for(size_t ii=0;ii<zz.size();ii++)for(size_t jj=ii;jj<zz.size();jj++){
   auto &a=zz[ii];auto &b=zz[jj]; int s=a.hi+b.hi;
   I pos=a.e*b.e+a.o*b.o, neg=a.e*b.o+a.o*b.e;
   I V=(ii==jj?1:2)*a.w*b.w*a.profile*b.profile;
   lb=lb+V*(dcL[s]*pos-dcU[s]*neg);
 }
 I C0=upperD(0);
 I caperr=I(2)*I(44)*I(1<<24)*powI(I(1)/10000,4)*C0;
 I pi=estimatePi();
 I raw=lb-caperr;
 I qm=roughQcoeff();
 I qcap=I(44)*I(2*(1<<12))*powI(I(11)/10000,4)*C0;
 I qloss=fplus(I(2000)/499-qm)*I(1701)/100000+qcap;
 I net=raw-2*pi-2*qloss;
 printf("Q ordinary coeff [%.12f,%.12f], cap %.12g cross loss %.12f\n",qm.l,qm.r,qcap.r,qloss.r);
 if(!(zz.size()==4200 && raw.l>9.585 && caperr.r<.00000729 &&
      pi.r<3.95872 && qm.l>3.01957 && qcap.r<.00002605 &&
      C0.r<49.353 && qloss.r<.016840 && net.l>1.633))abort();
 printf("boxes %zu raw lower %.12f cap error %.12g, prime upper %.12f, net lower %.12f\n",
        zz.size(),raw.l,caperr.r,pi.r,net.l);
}

"""
with tempfile.TemporaryDirectory(prefix="goldbach-full-zero-tag-") as p:
    src = Path(p)/"check.cpp"
    exe = Path(p)/"check"
    src.write_text(text)
    subprocess.run(["g++","-O3","-fno-fast-math","-ffp-contract=off",str(src),"-o",str(exe)],check=True)
    subprocess.run([str(exe)],check=True)
