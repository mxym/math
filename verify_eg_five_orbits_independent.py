#!/usr/bin/env python3
"""Independent five-layer audit. SymPy HNF indexes cells; determinantal divisors test membership."""
from itertools import combinations,permutations,product
from math import gcd
from functools import lru_cache
from json import loads
from base64 import b85decode
from zlib import decompress
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form
data=loads(decompress(b85decode("c$~FdS+d<G5dHTmT=|x&0O?NIipwiWW$%#$4LzI&^q%89$Je@abLg1{`JW#@fBqHnubATbEBy8M&wq}`#}~hTAD@4P<+D7On3lMt<#GIuad|IsTV6{H%eL&x_IoJ=$KY^`3%@z#o(CPj<KrNDS4Iy@w_Kl&&&1)FCyE(j`F`olb<A_&J^xm}c=UMCyh+YGMYAca3!qNd$e>XhIplF`Z+VsbsR}00-ej|4MH53wtQuJscQ%bny`h;1AU$V^%bLVAFK$;pk(l}zilF78L5);Qn`Dx!kO;JpU7@VCs^kT*VAN`<F3lwTxO63=C3a&05!o!w!8M#!U(H~{Oj3^>CfPb9*|(kL=K0p1V&%vQK>TY8F)bWMZvMt3V^!5!oUjpj(rRPHq}CRsp4Oh1Yi-CSALIUAbWTXY<b<s02bu9P$w$WW8fsEAjE6RsedGdwk4v+5h}z^J<$N6`ikCy2Aa@~{Rud_P<3F37S<bULwTj|dEU1K@B+QOth)okGu1rWl{WS4ceqs{HDnrtUT`!z<X<^CnJ@7iz-NC-zBF1TVtR!J^BIe)J5@W)Rah+3>pl0@eW39Ht_#+GO*v;XG)aTU76JxHDBk;smQQlPvZB!6lj(x33d8aB0+MqM^@0!s=+PssRZII*cl=Q#_Q*fz9MbWUOT!qrQ2LO#vj3>55d4kg*n$0W}5~Hlaminn0O*N#yy>fVQIVM=BhAvIGrqTg64Qa9}K2{}i%As=JR?aI77D%kIjZJLqKo?1PL(PfRg^~!5?$TCa=2nJy|8b3^EzG3Y<`l(hP;Ca1rEyQUSgGnQk)dwAcJff0pg^drj$2joQL=VT7ROE_iHX#xO@S9llTj{~Fwx5i!k`e!<Pp6|%sd)E2Xj}O{5W9dwrzz}m8+rOk*Wdb+9bqYc_Q~M++jMEG6XrIWAfS~sHRrgwT1{z&3Bt~i7!p1O8dc^)mW^PZjDFYSS3&I`xh~D9-Gf&obQ_%dx@A84t^F-*atwC;i#QlxG}h*l#6v!#kaT8=x^<snxjP4WRdL^dUT`gd0s*JGvlDKfE4q7=H@m0XkIO}6w^`tc7(?E&Yx;Il%e`fCZC5J$t+2o1R&RY=)yuXc>pUdd5KNTMSl=IGu`#c=1rzpu4FND(6QZ_FSYr$srex0Jf9L$Ec=_Ddb1@{U^)f0sb|S1DNxQ2X@HKY<8&^2r&{u=TFMh#uynX}&lWJnLX<#w>HN?UUKE?V-DX~A-vdT^;)zWhq#0`ajtWD?@Lgg`#4GLl(z7-zDSoPMhVo-$8C&(Hg%xnn;2A5mD!3Z62lQaPEs9ScMC2d<S6`&*2v9*b7O>;DY*hSz&vBkwh&H_XLByq7hlCA;4z;;Ka;zzJL+$g@a=Iefc8cYdqltWI_hLAF8g76PYMEBiXp3AfEz?5~VM9NnH?A&i^p=w@>7JSM`m;|Dbu^?~oit>`F+DqEIEMtA8P$E4Y0NWm{rQQvv>q3XE94NXf`5Y5<a`nNM;h+;+w8N=^*_;4|3V{urX`zTN&59lbh`eWsX9}wI=^ogbjH4mv)9rbHrpw;HP6`iyMYzcJWvs0b{`z$r-u=D-`_omPRIT&ASxB0ns%z3e4q?Ju7V$^qRp`ewor#ub3I47iyYV3H3?u@n1L%C>Bw7`!La%T=A;|TzP*h~T~yCFEz4@-s66)iob1dN)bOfuhZ2H8VWMV+Rq}4DWNf~*JT;9HSM!WWTP@aPR5<TC884!5m}j2|S!%Ai(Xl$+t7;b8l29&6HgK3ErBiRH6pDxB)9uCxKD|a8oY16jtv3ni-6M})+;WB{FT{1(E3xN3<Ga@24=ZvJQ8|}#gqjt%!xDB)hAPhouG5ij1_)`c&QXTJN2}_dWk7V&kn4sE81ge$C}hTYPr<~B3VgGt+M5%+j7~Z|m(_01CaC26oq?9St8sKc>RF4z+~`&qM=(L3`VNjUjD3=i55rwWM2PXWd9`C7bu72TyybUW>Q3iWTqtPgOX8XBio&g{rPJ`D-@G2e%PC|5&+fwm>8QXv(apoFS*lzD+j4HHmq=_d;!Qrp(;PQYN*)mgnwUPAqG-(FMI7=6E1z_w>sk3+HThMkot5t)pI0u^V}W=|tJ^G_<l60<&G2}dwU&UM?yQvx{f$f&Jex9AL<itq5T{M`I>7#LKT=O7y+~6DU}+SArlZbNM~^g$9@7!SXgjlpmTgYJd4a!CA+f>Tvbcp~*kGE_rQ!Q6KJ{kVY#>eUr7^lK^kd|Z!nH5z%YnT@vV^*mP_Lq>c9LPRw`lcjyAiWPmi;ot3*IWHaqv0;!G@HfQUcuIU6K9*otH~y7!L$zBt5`!nF$wkQVBxedmoBTn$0L!P6tTqnH1={7Wpo_cJfL2MDPEvOZ8X7*o&Tox9&5A$K|g4=CMATp?;2}AQft$i}>hOWiS@pB99(5p*km;+=X1eh5Y=#ruA?T1;-Hyo`WMW9J&}WIJj67rIlbiHdLn5y#dqC;8_)a54M(r$d;+#7LmGPT?$h_g14Ud_|+DikHNJ)yQOzlkM{l(%Ln^@CIF0X?X3ukVC~4vk@D&)hDcC1LfF#7SYK%udL3+*isfO4X-D7&HXY$S+AB;k!B({G1J$9v1K6_&LF9HF=YVdVuFIV%VV7&Lx>eoYE9O_rq^>kuX%W<76|#1jSWBhsw#<b-(*tdSS~{fJGsH!T;dHh~+<U7mQL+Zj@6@VH9@Yaj8=ND9_}ioQnxJ~9-bQ4Q*AWKrxXZuF$-H-+^$Sbkxp8(;lBTyj+~K<o)9GP#VS4?y87)Lx%(R*-F7+n1f2}yyw?+5b7l}lTT5I_IVa;a3lLbky%lc+Fq}kp3j{`73UsFsx5{F`wvcFDCy=DvFo%nsT+cyPx(SMtNrvr1Fow{LAdL0oq=BAjJLnwAjF-CfnGaD$G;~n^~0lRRQUG(mXYYtBTs2sxbm6w3&gyz8bIE^2=dPyh!bnXsTT`WNCJLdRX9`QDh#eEUx4ztwCIOnyYyU<*vn)8=gZpu%t4z1t7mc}OjCNF92bQ3T)=F}6=C;Sp;2|nEkc>hO``vZY(CYaH6sXObue~W4ia(KULngzOfl{>Z5L3=V#qbp3JUpipx@CY|~)RX7NQx{KHJGs+S#*>sN%`R&2CuoXJyVh^q>{Pmy?MU6w(K9_wX~KPZngpgvYML|*0DsEqzv$=_&Yk;Ixn%CHf!&=-Ehp4|%j60qm)Qk~ds`NN-)UJJa%nGN(h*B;;llSj^~r|M3#?;ISP>-OB`@Qev9RiNJOkDzPb0J#z&7cZWg3V@B&PL=^@i$mQ%q~)n?Ko&0P+hCL-kT<YiBh4&`<UMljFJHan~CzI(EzCn6)Swv*kWZxmWVf>->RbZNFqy@6kN5SLCs)8hp*^4wfCwy`Gw6Q)R#b>Qxq%wtN0`-eePmc5UU|XbiUzu4qb6!rxivHzs9-RxSQICj~2Q@_HfCaT*>Pb_y2Jsli33TTz0;Wiaqz9HySS4ZtM>&fLn3I0hy?ZgmE323!gtG=hj&OQ^_8sG;QCV|g%8=9n|WrUDJdZC*PEifg5of6x=#K;qdP@KGT&cE^^xgQ$fzN7a^FR%@4A(@1H2hj#n)Lm5!sbW1t`2}*J1jt6Rn5ix8X$k2XJd$85DyKeGj>TMAqao3ODisu{ThhY{Gcz)*4_S4&qg=g@y*iDnOO~2pA9>K!zV&5j!jO>ATnj1!_=hzh$Gm^lr8XHZg>N<U8X>+!ROLu5f>y<lZitukh+p*%mi-9Zq?%Lx(*}(au9tag~Rh^i46Hs-dS%PnCp*llk|K!D#TO`VG83E8%YzGis2uR-35C+n70%BTtc5nis79X;eeF}R(s^<t?0BHmuPU)`!IFsFve}DW3aOKs0")))
E=list(combinations(range(5),2)); V=tuple(range(5))
def shapes():
    total=0; orbit=set()
    for mask in range(1<<len(E)):
        used=[e for j,e in enumerate(E) if mask>>j&1];parts=[{v} for v in V]
        for a,b in used:
            U=next(u for u in parts if a in u);W=next(u for u in parts if b in u)
            if U!=W:parts.remove(W);U.update(W)
        if len(parts)>1:continue
        for k in range(len(V)//2+1):
            for extra in combinations(used,k):
                if len(set(sum((list(e) for e in extra),[])))!=2*k:continue
                mult={e:(e in used)+(e in extra) for e in E}
                deg=[sum(m for e,m in mult.items() if i in e) for i in V]
                for loops in product(*[(0,) if d>=3 else tuple(range(3-d,3)) for d in deg]):
                    g=[x+y for x,y in zip(deg,loops)]
                    if any((loops[i]*loops[j] or min(g[i],g[j])>3) for i,j in used):continue
                    total+=1
                    orbit.add(min(''.join(map(str,[loops[i] for i in r]+[mult[tuple(sorted((r[i],r[j])))] for i,j in E])) for r in permutations(V)))
    assert total==4405 and orbit==data.keys()
def arrowdata(name):
    n=0;arr=[];avoid=[];relations=[];tree=[];used=[]
    def gen():
        nonlocal n
        n+=1;return (n,1)
    def arc(i,j,z,invol=False):
        t=len(arr);arr.append((i,j,z,t if invol else t+1))
        if not invol:arr.append((j,i,(z[0],-z[1]),t))
    # Greedy tree decided by enumerating earlier paths, not by the author's component union.
    for (i,j),cnt in zip(E,map(int,name[len(V):])):
        if not cnt:continue
        reach={i}
        for _ in V:
            reach|={a for e in tree if set(e)&reach for a in e}
        v=gen() if j in reach else (0,0)
        if v==(0,0):tree.append((i,j))
        arc(i,j,v)
        if cnt==2:
            w=gen();arc(i,j,w);avoid.append([w,(v[0],-v[1])])
    for i,x in enumerate(map(int,name[:len(V)])):
        if x:
            g=gen();arc(i,i,g,x==1);avoid.append([(g[0],x)])
            if x==1:relations.append([(g[0],2)])
    def expand(z):
        a=[0]*n
        for i,b in z:
            if i:a[i-1]+=b
        return tuple(a)
    return n,[(i,j,expand([z]),k)for i,j,z,k in arr],tuple(map(expand,avoid)),tuple(map(expand,relations))
@lru_cache(None)
def key(R,n):
    if not R:return ()
    M=hermite_normal_form(Matrix(R).T).T
    return tuple(tuple(int(x)for x in row)for row in M.tolist())
@lru_cache(None)
def rank_index(R,n):
    # gcd of all maximal minors is the index in the common rational saturation.
    if not R:return (0,1)
    A=Matrix(R);r=A.rank();z=0
    for I in combinations(range(len(R)),r):
        for J in combinations(range(n),r):z=gcd(z,int(A.extract(I,J).det()))
    return (r,z)
def has(R,v,n):
    return rank_index(R+(v,),n)==rank_index(R,n)
def walk(ar,w,n):
    assert len(w) in (4,8,16) and all(0<=j<len(ar)for j in w)
    z=(0,)*n;slots=[[] for j in V];D=set()
    for i,j in enumerate(w):
        a,b,v,rev=ar[j];nextj=w[(i+1)%len(w)]
        assert ar[nextj][0]==b and nextj!=rev
        for y in slots[a]:D.add(tuple(t-u for t,u in zip(z,y)))
        slots[a].append(z);z=tuple(t+u for t,u in zip(z,v))
    return z,D
def audit(name,src):
    n,ar,avoid,base=arrowdata(name)
    tab={key(tuple(tuple(v)for v in loads(k)),n):w for k,w in src.items()}
    assert len(tab)==len(src)
    active=set();done={};stats=[0,0]
    def rec(R):
        if R in done:return done[R]
        assert R not in active;active.add(R)
        assert R in tab and not any(has(R,f,n)for f in avoid)
        w,D=walk(ar,tab[R],n);assert has(R,w,n);dpt=0
        for d in D:
            assert not has(R,d,n)
            child=key(R+(d,),n);assert child!=R
            if any(has(child,f,n)for f in avoid):stats[0]+=1
            else:stats[1]+=1;dpt=max(dpt,1+rec(child))
        done[R]=dpt;active.remove(R);return dpt
    h=rec(key(base,n));assert set(done)==set(tab)
    return len(done),h,*stats
def sharp():
    name='000010111111100';n,A,_,_=arrowdata(name);M=16*(1+33+33**2)+1;w=(2,66,2178,M)
    assert M%2 and n==4
    direct=[0,7,8,3,4,11,6,1,4,14,5,2,9,10,14,5]
    zero=lambda v:not any(v[:3]) and v[3]%2==0
    t,D=walk(A,direct,n);assert zero(t) and all(not zero(v)for v in D)
    assert all(sum(x*y for x,y in zip(v,w))%(2*M)for v in D)
    def rooted(length):
        out=[]
        def visit(arcnums,v,origin):
            if len(arcnums)==length:
                if v==origin and A[arcnums[-1]][3]!=arcnums[0]:out.append(arcnums)
                return
            for j,(i,k,_,rev) in enumerate(A):
                if v==i and (not arcnums or arcnums[-1]!=rev):visit(arcnums+[j],k,origin)
        for i in V:visit([],i,i)
        return out
    for size,expected in [(4,24),(8,264)]:
        words=rooted(size);assert len(words)==expected
        for r in words:
            t,D=walk(A,r,n)
            assert not zero(t) or any(zero(v)for v in D)
    # Direct simple walks in smallest certified cyclic lift.
    sh={i:[]for i in V}
    for a,b,v,_ in A:
        shift=sum(t*u for t,u in zip(v,w))%(2*M)
        assert (b,shift)not in sh[a];sh[a].append((b,shift))
    assert all(len(sh[i])==3 for i in V)
    for root in V:
        def dfs(i,g,vis,md):
            for j,step in sh[i]:
                y=(j,(g+step)%(2*M))
                if y==(root,0) and md in (4,8):raise AssertionError
                if md<8 and y not in vis:dfs(*y,vis|{y},md+1)
        dfs(root,0,{(root,0)},1)
if __name__=='__main__':
    shapes();res=[audit(n,x)for n,x in data.items()]
    assert sum(x[0]for x in res)==378 and max(x[1]for x in res)==5
    sharp();print('PASS 4405/62 shapes, 378 cells, depth five; invoked terminal/recursive collisions:',sum(x[2]for x in res),sum(x[3]for x in res))
