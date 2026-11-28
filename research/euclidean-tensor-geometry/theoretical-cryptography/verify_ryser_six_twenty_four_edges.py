#!/usr/bin/env python3
"""Exact proof checks for the rank-six 24-edge lower bound.

Requires the preceding verify_ryser_six_twenty_three_edges.py in this directory.
No floating-point optimizer is used in this verifier.
"""
from base64 import b85decode
from zlib import decompress
from json import loads
from collections import Counter
from itertools import combinations
from math import comb
from verify_ryser_six_twenty_three_edges import integer_partitions, require
from heapq import heappush, heappop


def transports(n,a,b):
    R=len(a);C=len(b);src=R+C;sink=src+1;sz=sink+1
    G=[[] for i in range(sz)]
    cell={}; floors={}
    def add(u,v,cap,c):
        i=len(G[u]);j=len(G[v])
        G[u].append([v,cap,c,j]);G[v].append([u,0,-c,i])
        return (u,i)
    r=list(a);s=list(b);value=0
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            lo=max(0,x+y-n+9)
            hi=(0 if x==y==2 else min(x,y)-1)
            if lo>hi:return None
            r[i]-=lo;s[j]-=lo
            value+=comb(lo,2)
            floors[i,j]=lo
            cell[i,j]=[add(i,R+j,1,h) for h in range(lo,hi)]
    if min(r+s)<0:return None
    for i,x in enumerate(r):add(src,i,x,0)
    for j,y in enumerate(s):add(R+j,sink,y,0)
    ps=[0]*sz
    for count in range(sum(r)):
        prev=[None]*sz;d=[10**6]*sz;d[src]=0;heap=[(0,src)]
        while heap:
            t,u=heappop(heap)
            if t!=d[u]:continue
            for i,(v,cap,wt,inv) in enumerate(G[u]):
                if cap<=0:continue
                z=t+wt+ps[u]-ps[v]
                if z<d[v]:
                    d[v]=z;prev[v]=(u,i);heappush(heap,(z,v))
        if prev[sink] is None:
            reached={i for i,x in enumerate(d) if x<10**6}
            require(src in reached and sink not in reached, ('not a cut',a,b))
            require(all(not cap or v in reached for u in reached for v,cap,c,j in G[u]), ('cut arc',a,b))
            return None
        for i in range(sz):
            if d[i]<10**6:ps[i]+=d[i]
        x=sink
        while x!=src:
            r,i=prev[x]
            v,cap,w,j=G[r][i];G[r][i][1]-=1;G[x][j][1]+=1
            value+=w;x=r
    true={z:floors[z]+sum(1-G[u][t][1] for u,t in arcs) for z,arcs in cell.items()}
    require(tuple(sum(true[i,j] for j in range(C)) for i in range(R))==a, ('row',a,b))
    require(tuple(sum(true[i,j] for i in range(R)) for j in range(C))==b, ('column',a,b))
    require(value==sum(comb(w,2) for w in true.values()), ('objective',a,b))
    # Verify independently there is no negative-cost residual cycle. Equal
    # margins ensure any improvement decomposes into such cycles.
    d=[0]*sz
    for turn in range(sz):
        change=False
        for u in range(sz):
            for v,cap,w,k in G[u]:
                if cap>0 and d[v]>d[u]+w:
                    d[v]=d[u]+w;change=True
        if not change:break
    require(not change, ('negative residual cycle',a,b))
    return value

def compute(n):
    pats=sorted((sum(comb(x,2) for x in p),2*p.count(2),sum(x for x in p if x>=4),p)
        for k in range(6,n//2+1) for p in integer_partitions(n,k,2,n-15)
        if sum(p[-2:])<=n-9)
    K=len(pats);target=comb(n,2)
    B={}
    for i,x in enumerate(pats):
        for j,y in enumerate(pats[:i+1]):
            B[i,j]=transports(n,x[-1],y[-1])
    count=0;best=-100000
    valid=0; feasible=[]
    SMAX=pats[-1][0]
    def process(t,d2,h,s,b,l):
        nonlocal count,valid,best
        if s+l*SMAX<target:return
        if not l:
            if h<3*n:return
            count+=1
            valid+=1
            v=2*(s-target)-b
            best=max(best,v)
            if v>=0:feasible.append((v,s,b,tuple(pats[i][-1] for i in t)))
            return
        for i in range(t[-1] if t else 0,K):
            w,a,k,p=pats[i]
            if d2+a>n:continue
            bb=[B[i,j] for j in t]
            if any(x is None for x in bb):continue
            process(t+(i,),d2+a,h+k,s+w,b+sum(bb),l-1)
    process((),0,0,0,0,6)
    pool=sorted(feasible,reverse=True)
    require((K,count,best,len(pool))==(80,229202,13,576), (K,count,best,len(pool)))
    print("transport profiles:", K,count,best,len(pool),flush=True)
    return pool

# This encodes JSON rows [profile, denominator, claimed_lower_numerator,
# lambda_equalities, negative_eta_inequalities]. No code is encoded.
DUAL_TABLE = (
    "c-rk<3v%K*5WJ96CHVvFSyH+GH8$BS#(*`Nza(45)~f^sJAr=l?dkda{QR7T`{VXCynHtf<G-($^}C<%ufrAm?(6%j+jaO1!"
    "~HQ1+pj;K|Ak>(AM>#HqV3DE&%4|t{(t=Z<sb3!FJ#W{=kV*s-PZ;B+1K{7csxGFAq?n)f0qJIBH`rm)HhhvF?jj@$*=EsV!"
    "mwu?&o*uBfh*zar4ISz3BOmcz%BS+P4e)-6?e#m}i@dhX4N!@1JKJ;x33@o=;&grZ7l4phGZF5jcN8$X4(hfuJEeo+*rgNsE"
    "9fd_9X5o5E1m5?(UMd$okWICSyGAh!MPlmia;EJ)ARf7*VThdB}$$Nyi?yWe4r;<sC#oZNEi`OHnyjxv2C=ry$KVP6vm;9@a"
    "}!ksfq&kQ+U1_Y({aP`Y0%N~v@-ZF4ZVGv~}-3qE%L3(m>c{*E@lRwH<kd+$nGZg;qgsDj4keH5u7b}&kWF8io$~IT#e~dk0"
    "?g=x|F(<6z(t=ft$;eG+6~i8EQeK>8^@>?T0p2J$l;$W6l@22_>0nz#_C?=8N3e*`*C}HZ^XSCbL~g!3-LzdZoO|v+uZH?y{"
    "5;<*x@X7ihfXAzPE7P8!JeJ;>|{SId`IC9CT}cv91U>5cg(_jdW3rXL*pP((N5As#MTQqHU`bwOk#@LWsM~tsTSelip%Jbx&"
    "(Ev9k@vnHD>fMvP}n#&(-WXOT3Yn4^=bjO78T48m+bnq#{r8%>G%ZC4~WgboKHW@B9i#3=>RLz^Md_+(L}tqI|q!devK4*aO"
    "m;jflx%mXV3b1LZJH9X8;^=YO_OjW0Xy|HUDfNUO$kz5RE@_8&5g98VrbhQzh<pvh9o(qW}_^;@f~L-o@?sC!@#9XU?ST4ST"
    "|%Uk@&Oj0Tf7K44PxSzc+FnA0*Xpq9>5M*%{N~P5j*5VzC%WjCsE-nHgB0KeD$69_x#vUs2L&bY5dJl<vPFs#dY7)b(f9Qe`"
    "U7R+mbRV3QqmwJ&CkU>8Qt%t$(Io1mfZ7Cs_Ixum!<;*-cY<KlK%lKJ#y}7-N>gSogm<Pk&;mW5nj?L-($q5#IKr+{XVirNM"
    "@@&k<}5+tkR#xbX=g5MNR3fMTBOIW)db@xP@`7E=HM(A)L2KZq7Gd~|BChV6e}V@=rCvXIb+WMXQ<O5-i$qa>cBH!;r^%v8$"
    "!%gtO=AhWg>OHH<x2p87V?Ji^h!m2|Lbx%%G1Mq()!nQ;^0~?_@<5gS*fr$YQ}!uL&7RF3m)e(fD>DF?mg_Th|vr@-u49+y>"
    "o|4z7q~PonzW$!oUNDohOCNi~g*)1WD|xSbk1C&+r$rO>FyQOwW%H8tuYwS*?z9El8G4$GBsb6D5F)_CS*#ixekCA0*|P8U<"
    "c<aBc9ZN*VzyJN8*_pXWyNIX&o1-<;}TQu$^$mU9ra6Ae3Z3;z~1`f8ZDDz|ta2d^quF%Ng-8N$`&rG&Z>efKbLxxspWP0xk"
    "ct3Kh&gO1+nNVDx=7JnT=!_rxJ`GUOJVciUlW$*;+D|5Uj6L5zRlY6t*!ydUt~X#}fx31h0COu1tRdnq=cs!<ppH+MlPoUCf"
    "d#%jJe=4>ciFBkd!6FCNmc}^+Op)urre#lgISPqvoetJlm_xu2^_0frcc-IvSp{2EyD{jcVWGb(AtFc81nVAa-Xrw*Pm9to}"
    "T@rF=<pPGTOQ2aL;^3lo`(ke_tlgtsxCQdQ#*J&e6(hmbmBn{JLcea`u!%Q<ZY6LorvSM1CSADz#OGqvE~~8w~bUh1FsaKR}"
    "BrsZaVG^jK*%-IROIkZL~2I7BYL!4fH_YwP0>+%dxUpW#YuoqSwz`A?m6P!DfbLV(pT?Goa$F-5E^?qiDnV~R)h%lXnyK7kg"
    "cE9V$f<mzD7H`74CA5lnmPE>K+GiZ|(w3cd4&!BPhUzg!xw!KxZq6>#$QBOtpR9m>LHFeRO71C3&{LKo}jSj)UgkaQ!V6BT4"
    "g5+&5MIg8PhZ)LdD@}2?5VH4`TMfS|=ImX^f)pWArm|7V^yuD?wgYB?)xtavU$oR?vs(DKezTvza6R@o+~)LLP3rk^!|s0FP"
    "y>A^sn^}tr|4|~A+OP4U+f+&K1PjRmZ~QXNMv!P<sT!HU;ZWwu$Q;^LQulgciBVZhd}1!*7I3gTWE9{IcwYRj{_q|)DqUXNn"
    "T@l|5|u&n&CMD_3pZqC}7k{IXL^M6LN5(HtM3N;Xy?o51A(_8ETcUw-bbnscPQT-t*@_$^9>9CnEF<K;wq+>(X8pJ;!aZmQc"
    "?DZ(d?i!N$Om7YUwdBVjmaET~(^UcK_dDP-%6DVa;hbL!Sa?v_HcB!e=)!9Lx>i`~vk-agE}^U}9JM-yPwskHPxs|ps;F2x8"
    "{WEi@-O>0OuGcydTZWCFVBqa_dTXrtU0PN4I6C-)cD=-v(+;>mnVNW0&U;jpZ0i7`;BWCbXLqF$zO$T@yp)k_`p|7$;X*}F4"
    "XbWA1r0e8Jw_6@+39$a{PP70x@TrE<J(p>tX(YkeuFeBrgrqCvXso<+5FybYv3E9_sx;dw7Y`cFmBMQ<^(|#r#OaDSIh;zjV"
    "{U`YzVXfAs(?UPy$bY}V#|~rnFmXO`f3Ev5d*Odc+Z5oe=qOf;WP-7A{qO4mW?&Moy|y?=NjXJ@I=kRP<OgY>+oF-yw~Arq#"
    "?}}uP!N)MQGSsnslzk*wiJjQX}fz<m~oyIPf-w*>h_<tNz?KwjXp2F@5%nz7V@6INE@xLvpZNOH3`ouSt4z?_8D_z^#IhTm_"
    "}WfMbLf?+K;lZyN<&tPpgeEauQl*q6?0({AY0x7F39&nOk2Um?jegVC2Y6paE#=!dzZhShL}3Q^c-YV=#v=)B_E2#l)w^I36"
    "v^siMF?>DI8n8On4VWLu)7#j)`%kK#;7biyFI5C>ETLf1<ajcl<q#+j~Tw324!&CQEPhN78p?SaEfZlC(*jBcs<4`$uG-*wr"
    "XkJV+aD-E7H2us3mz{ZbM&=n`hfldLZPP>Rz3G-3fl@8L1SF?Mx5=EeDIIEpB3Fzr0maA{<10wm(SeNq73(*MD$HA*)iM|lU"
    "BKFO6^!Px8Y&|kUjpjuW%_y<fh?fK_9KlhVv!O}uL{*`KV>q!bP6uj-#3+XpE<r1XE`!)-UJfohQ)bLhQlh7Z94z#g4o7&T~"
    "b=9BdmDJQuBpnQk`!HD3v}0RHzEA+}G77;+q3KPwj8ZO@sHWA4MBT$i&QR{Gs&83B(I%v1>VYB$s-T7m-GF6X7|TqqG#Gd!D"
    "bJDpl7~OfFMeP|Ex0ie+T>yL-j5XWTou%%POm%_*62m%5vF3V-rZS8ArS-SK5I;ef-mKb>4#EjkFQ4+opEp=C9evkcLdzstX"
    "qe;O0cmBr+QBw+wb2Cn$gWeJ(;5|?dJHIf=H(%tk0fzhC1BuglpMyq>vWm8>p5I)sjBS{nC$l%VuP>mdz^l#BwXkiWq7Bi)%"
    "+56?6XH3e|>>w?DIN!`f3qX7GryIw|Gq_w=fATtsv*0k*_tRdu__KQ*Y6+TL^K~`*>mMG0<?e}v@#QuyCT>F$dS>^yp{2Abp"
    "Eka{eJ_W(Y1aE^HNAh3`gk|#b6cI=-<{_-g>Eu+K#O+Ux~pneqdDr+FBoJAt1Y$KMpJT4CT8o~QVSzfOC5g+5(-9_cpkdMGr"
    "gw100O27n2vqhU9TCrDGKEoLur`ms}XdB4t-yfTH!r51JT$E?}viudjlOaGod4v8XN8n^`?43YH%Kuy{X=t>h?`_)Xvbkp;d"
    "Q1{A{VIj%i?CkPt<7tF7fYSbfZ1WvVKDUv|~8a2yXBDM?*AJS!`%O6pJ_fI!mbnSJ&=f!KOjm#AvVRSrzhJg&+c?X)*VDBsD"
    "L;1LvY*Txz}xW=B~t&bLBSY?MMityY*_AJ)Lb7NftvqF)o%eD{2*c=qO4%OtMva{+XuQCGYm=%hsxw2bdp{TJ!5vVj~i;yiY"
    "E6LY(aFT#OA>rxp2mOp>M)9-@6@OYVzXDezcRaao4Pyjtig(K9=1?eylkci;9SI>8<ZdI$udzewqfYL^LFMOcxpHxNoK_}<8"
    "Z^Sf9I;oXgj$(bj<qDtk>O(NlN%^OIeX7bkZJ={+iC*_>d+cfXnYYh-&8pWOd_=PMr%Y78*}USPt<eQ^3`kR+hE!~2}}o$S-"
    "PZCI@GIT_o?kOO>J{UpnXhYIFw0@-6Z0cez8qrRHij#IS=gBUw(B;i>0xOS#z*7hxGj+3zFU-?=;(pm^R>}tv1?(>NeU0GeE"
    "wt+@3lhZ2(!^Le{ooY1w5!z<dZ8k<RpK5jmmLA!?;V{NifarONVC8pvW+zt^V5Dv!1ZRd6zbxgmmImyBH<D~}&pi4KIY=$6Z"
    "f$~$5v4!YbLDoLvGO=t*(G8b*356LUJ`9Kk2a(OZD=_-x76D+IH)HSVv#?qAvf-{yr74`X)kXy){Jrd)Iq*3*xZH7Oi+Q+o+"
    "l(rz6#T?5@kC>h2SR4tgvga`bpW_a$=ysg9D?fB|5rfLMC3qC6tyN9uDPT>jl_$YkXc21`*gP=SG;1vTi)7?>E!I$DsRwI$U"
    "RPCnf^7xnw@S63SaK@6fMaIvS?*pFa6RgoJRcF{2LnwrIT!G&tPN)FI?&nV_9~j3*7K&Q3Ug7aE9MR1ivQd5c2c8tytAf}ED"
    "LX^m;Ch?HHB&m"
)

def low_exception_types(pool):
    C=Counter()
    for F,S,B,P in pool:
        A=23-2*sum(p.count(2) for p in P)
        for L in range(min(F,2)+1):
            for l3 in range(L+1):
                t=S-253-L-l3
                if t<0 or t%3:continue
                h=t//3
                if h<=A//2+(0,2,4)[L]:
                    C[L,A,h,l3]+=1
                    require(max(p.count(2) for p in P)<=3, ('four 2s in a part',P))
    expected={(1,1,2,1):1,
              (2,3,5,2):12, (2,3,5,1):8, (2,3,5,0):4,
              (2,1,4,2):28, (2,1,4,1):10, (2,1,4,0):1,
              (2,1,3,0):3, (2,5,5,2):2}
    require(dict(C)==expected, C)
    print("small-exception shape checks:", str(sorted(C.items())),flush=True)

def coupled_check(pool):
    table={tuple(tuple(row) for row in P):(den,num,X,Z)
           for P,den,num,X,Z in loads(decompress(b85decode(DUAL_TABLE)))}
    require(len(table)==156, len(table))
    R=[];seen=set()
    for F,S,B,P in pool:
        if F<3:continue
        require(all(len(g)==6 for g in P), ('not balanced',P))
        A=23-2*sum(p.count(2) for p in P)
        require(A in (1,3), ('A count',A))
        seen.add(P)
        den,num,X,Z=table[P]
        require(den in (1,2) and len(X)==180 and len(Z)==72
                and all(v<=0 for v in Z), ('bad dual',P))
        rhs=[];t2=[0]*36;cost=[];eql=[];tw=[];lo_cost=0
        for i,j in combinations(range(6),2):
            prev=len(rhs);rhs.extend(P[i]);rhs.extend(P[j])
            for a,x in enumerate(P[i]):
                for b,y in enumerate(P[j]):
                    lo=max(0,x+y-14)
                    hi=0 if x==y==2 else min(x,y)-1
                    ep=6*i+a if y==2 and x!=2 else 6*j+b if x==2 and y!=2 else -1
                    if ep>=0:t2[ep]+=lo
                    rhs[prev+a]-=lo;rhs[prev+6+b]-=lo
                    lo_cost+=comb(lo,2)
                    for c in range(lo,hi):
                        cost.append(c);eql.append((prev+a,prev+6+b));tw.append(ep)
        ub=[]
        for i,p in enumerate(P):
            for j,x in enumerate(p):
                u=6*i+j
                ub.extend([0,0] if x==2 else [x-t2[u],A-x+t2[u]])
        val=den*lo_cost+sum(a*b for a,b in zip(rhs,X))+sum(a*b for a,b in zip(ub,Z))
        for c,(u,v),e in zip(cost,eql,tw):
            lhs=X[u]+X[v]+(Z[2*e]-Z[2*e+1] if e>=0 else 0)
            val+=min(0,c*den-lhs)
        require(val==num, ('dual lower value',P,val,num))
        upper=(2*(S-253)*den-val)//den
        if upper>=3:R.append((S,upper,P))
    require(seen==table.keys(), 'missing or extraneous dual profile')
    want=[(274,4,((3,3,3,3,3,8),(3,3,3,3,3,8),(2,3,3,3,4,8),
        (2,2,2,3,7,7),(2,2,2,3,7,7),(2,2,2,3,7,7))),
        (275,3,((3,3,3,3,3,8),(3,3,3,3,3,8),(2,3,3,3,4,8),
        (2,2,2,3,7,7),(2,2,2,3,7,7),(2,2,2,3,6,8)))]
    require(sorted(R)==want, R)
    print("exact degree-two-coupled LP:",len(table),"certificates, two shapes",flush=True)
    return R

def last_two(R):
    from itertools import product
    for idx,(S,L,P) in enumerate(sorted(R)):
        A=23-2*sum(p.count(2) for p in P)
        require(A==3, A)
        T=[set(p) for p in P]
        possible=[t for t in product(*T) if t.count(2)==1 and sum(t)==28]
        # Every ordinary edge with a degree-two vertex uses degree 4 in part 2,
        # except possibly the two edges whose degree-two vertex itself is there.
        require(all(t[2] in (2,4) for t in possible), possible)
        require((any(t[2]==2 for t in possible))==(idx==1), possible)
        ordinary=4+(2 if idx==1 else 0)
        nonordinary=(23-A)-ordinary
        touched=(S-253)//3+2*L
        require(touched<nonordinary, (idx,touched,nonordinary))
        print("ordinary degree-two row cap",ordinary,
              "; touched cap",touched,"<",nonordinary,flush=True)

if __name__=="__main__":
    p=compute(23)
    low_exception_types(p)
    last_two(coupled_check(p))
    print("PASS: 23 edges excluded",flush=True)
