from hashlib import sha256
from pathlib import Path
import subprocess
import tempfile

p = Path(__file__).resolve().with_name("check_full_zero_tag_affine_self.py")
raw = p.read_bytes()
if sha256(raw).hexdigest() != "848d4efd005f6ad5e222ff1bf4bd6967f67a66398ecd28a8ff15308b0f926a98":
    raise ArithmeticError("different full zero-tag checker")
head, sep, tail = raw.decode().partition('\ntext += r"""')
before, sep2, body = tail.partition('\nint main(){')
body, sep3, _ = body.partition('\n"""')
if not sep or not sep2 or not sep3:
    raise ArithmeticError("ambiguous exact old checker boundaries")
env = {"__file__": str(p)}
exec(compile(head,str(p),"exec"),env)
text = env["text"] + before
text += r"""
I AA[125005],BB[125005]; // u^2 exp(-2 gamma) times F_2, f_2
const int AL=53577, AH=53578, BL=42664, BH=42665;
I Ghalf(int i){ // enclose G(i/(2JQ)) using both adjacent grid points
    return I(Graw(i/2,true).l,Graw((i+1)/2,false).r);
}
void exactDHR(){
    // The only table input: α is in (AL,AH)/JQ, β in (BL,BH)/JQ.
    for(int j=2;j<=AL;j++){
       I x=I(j)/JQ;
       AA[j]=sq(x)/Ghalf(j);
    }
    // u²F_2(u) increases, F_2(u) decreases. This handles the unknown
    // α within its single grid cell without applying a wrong differential branch.
    AA[AH]=I(AA[AL].l,(sq(I(AH)/JQ)/Ghalf(AL)).r);
    for(int j=BL;j<125001;j++){
       int k=j-JQ;
       I c=I(2)*I(j,j+1)/I(1LL*JQ*JQ);
       I inc;
       if(j==BL) inc=I(0,(c/Ghalf(k)).r); // β in this cell; derivative is 0 before it
       else if(k+1<=AL) inc=c/I(Ghalf(k).l,Ghalf(k+1).r);
       else inc=c*I(AA[k].l,AA[k+1].r)/sq(I(k,k+1)/JQ);
       BB[j+1]=BB[j]+inc;
       if(j>=AH) AA[j+1]=AA[j]+c*I(BB[k].l,BB[k+1].r)/sq(I(k,k+1)/JQ);
    }
}
I lowerExact(int maxSum){
    int j=999LL*(P-maxSum)*JQ/(1000*A);
    if(j<BH) return 0;
    return fplus(BB[j]/(sq(I(j)/JQ)*sq(af)));
}
I upperExact(int maxSum){
    I capped=upperD(maxSum);
    int j=999LL*(P-maxSum)*JQ/(1000*A);
    if(j<AH)return capped; // Selberg valid for every remaining fixed positive ratio
    I candidate=AA[j]/(sq(I(j)/JQ)*sq(af));
    return candidate.r<capped.r?candidate:capped;
}
"""
for old,new in (
    ("sieve_constants();rho2();prep_b(800);g2_cdf();f2_integral();",
     "sieve_constants();rho2();prep_b(800);g2_cdf();exactDHR();"),
    ("dcL[j]=lowerD(j);","dcL[j]=lowerExact(j);"),
    ("dcU[j]=upperD(j);","dcU[j]=upperExact(j);"),
):
    if body.count(old)!=1:
        raise ArithmeticError("ambiguous sieve substitution")
    body=body.replace(old,new)
cut = body.index(" I pi=estimatePi();")
text+="\nint main(){"+body[:cut]+r"""
 const I raw=lb-caperr;
 const I net=raw-2*(I(3729964)/1000000+I(16840)/1000000);
 if(!(zz.size()==4200 && caperr.r<.00000729 && raw.l>11.745 && net.l>4.251))abort();
 printf("boxes %zu raw lower %.12f cap error %.12g; complete lower %.12f\n",
        zz.size(),raw.l,caperr.r,net.l);
}
"""
with tempfile.TemporaryDirectory(prefix="goldbach-exact-dhr-zero-") as d:
    src=Path(d)/"check.cpp"
    exe=Path(d)/"check"
    src.write_text(text)
    subprocess.run(["g++","-O3","-fno-fast-math","-ffp-contract=off",str(src),"-o",str(exe)],check=True)
    subprocess.run([str(exe)],check=True)
