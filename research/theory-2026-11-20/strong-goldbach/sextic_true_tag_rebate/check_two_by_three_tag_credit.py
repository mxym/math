from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

# Reuse the previously audited interval arithmetic and occupied-class cubature.
base = Path(__file__).resolve().with_name("check_one_by_two_tag_credit.cpp")
raw = base.read_bytes()
if sha256(raw).hexdigest() != (
    "6dcdfea4141f79d656baefed4f2d386d3fe45c58486c0fbba1546c58949f7463"
):
    raise ArithmeticError("different one-by-two checker")

text = raw.decode()
if text.count("\nint main(){") != 1:
    raise ArithmeticError("ambiguous checker entry point")
text = text.split("\nint main(){")[0]

def literal(old, new, count=1):
    global text
    if text.count(old) != count:
        raise ArithmeticError("ambiguous checker substitution: " + old)
    text = text.replace(old, new)

literal("const int P=10000;", "const int P=10000;\nI mark3;")
literal("int idxlo(double x){", r"""
I cubic3(I h) {
 // Pointwise profile -F'''(s)=1056 h-13440 h^3, h=(.5-s)_+.
 const I hp=I(h.l), hq=I(h.r);
 const I f1=hp*(1056-13440*sq(hp)), f2=hq*(1056-13440*sq(hq));
 const I crit=I(11)/420; // critical h^2
 double top=max(f1.r,f2.r);
 if(sq(hp).l<=crit.r && sq(hq).r>=crit.l) {
   const I critical_h=box(.1618,.1620);
   if(sq(I(critical_h.l)).r>=crit.l || sq(I(critical_h.r)).l<=crit.r)abort();
   top=max(top,(704*critical_h).r);
 }
 return I(min(f1.l,f2.l),top);
}
I g3(I u,I v,I w,I x) {
 const I s=u+v+w;
 if((x+s).r>.5)return cubic3(fplus(HALF-I(x.l,(x+s).r)));
 const I h=fplus(HALF-(x+s/2));
 const I sig=(sq(u)+sq(v)+sq(w))/12;
 return cubic3(h)-40320*h*sig;
}
int idxlo(double x){""")
literal("mode==0 ? g1(t,0):g2(t,u,0)",
        "mode==0 ? g1(t,0):mode==1?g2(t,u,0):g3(t,u,mark3,0)")
literal("mode==0 ? g1(t,x) :g2(t,u,x)",
        "mode==0 ? g1(t,x):mode==1?g2(t,u,x):g3(t,u,mark3,x)")
literal("I T=I(1)-t-u,V=0;", "I T=I(1)-t-u-mark3,V=0;", count=2)

text += r"""
double cap_sqrt(I r) {
 if(r.r<0)abort();
 const double s=up(up(sqrt(r.r)));
 if((I(s)*I(s)).l<r.r)abort();
 return s;
}
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants();
 constexpr int ns=160,dq=40;
 prep_b(800);
 const I k=(I(549)/1000)/af,U=(I(575)/1000)/af;
 struct Left {int i,j; I mean, sq, positive;};
 vector<Left> bank;
 for(int i=60;i+dq<=800;i+=dq)for(int j=i;j+dq<=800;j+=dq){
   if(i+j<=650)continue;
   const I u=I(i,i+dq)/P,v=I(j,j+dq)/P;
   mark3=0;
   prep_g(1,u,v);
   const I m=mean(1,u,v,ns), s=mean2(1,u,v,0,ns);
   const I mass=rr(0,1-u-v);
   bank.push_back({i,j,m,s,I(0,cap_sqrt(s*mass))});
 }
 I total=0,volume=0;
 int nright=0,count=0;
 double min_cell=1e20;
 for(int i=60;i+dq<=800;i+=dq)for(int j=i;j+dq<=800;j+=dq)
  for(int l=j;l+dq<=800;l+=dq){
    if(i+j<=650||i+j+l+3*dq>1760)continue;
    nright++;
    const I u=I(i,i+dq)/P,v=I(j,j+dq)/P,w=I(l,l+dq)/P;
    mark3=w;
    prep_g(2,u,v);
    const int d=(10000000-2000*(i+j+l+3*dq/2))/10000;
    if(d<=0)abort();
    const I bs=mean2(2,u,v,d,ns);
    for(const auto &L:bank){
       const I benefit=I(d)*(-1*k*L.mean-(U-k)*L.positive);
       const I lower=benefit-I(0,cap_sqrt(U*U*L.sq*bs));
       if(lower.l<=100)abort(); // every cell, not a chosen positive subsample
       const int rep=(L.i==L.j?2:1)*(i==l?6:(i==j||j==l?2:1));
       const I w=powI(I(dq)/P,5)/rep;
       volume=volume+w;
       total=total+w*I(lower.l);
       count++;
       min_cell=min(min_cell,lower.l);
    }
 }
 const I bilateral=2*total;
 printf("two-by-three: %zu x %d = %d boxes, min %.9f, volume %.12g, bilateral lower %.13g\n",
        bank.size(),nright,count,min_cell,volume.l,bilateral.l);
 if(bank.size()!=115||nright!=349||count!=40135||
    bilateral.l<=(I(395335)/10000000).r)abort();
}
"""
with tempfile.TemporaryDirectory(prefix="sextic-two-by-three-") as run:
    src = Path(run, "proof.cpp")
    out = Path(run, "proof")
    src.write_text(text)
    subprocess.run(
        ["c++", "-O3", "-std=c++17", "-ffp-contract=off", "-fno-fast-math",
         str(src), "-o", str(out)], check=True
    )
    subprocess.run([str(out)], check=True)
