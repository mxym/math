#!/usr/bin/env python3
"""Independent 23-edge Ryser-kernel audit: direct convex cell margins and uncapped exact dual."""
from itertools import combinations,combinations_with_replacement,product
from collections import Counter,deque
from math import comb
from base64 import b85decode
from zlib import decompress
from json import loads
DUAL='c-rk<3v%K*5WJ96CHVvFSyH+GH8$BS#(*`Nza(45)~f^sJAr=l?dkda{QR7T`{VXCynHtf<G-($^}C<%ufrAm?(6%j+jaO1!~HQ1+pj;K|Ak>(AM>#HqV3DE&%4|t{(t=Z<sb3!FJ#W{=kV*s-PZ;B+1K{7csxGFAq?n)f0qJIBH`rm)HhhvF?jj@$*=EsV!mwu?&o*uBfh*zar4ISz3BOmcz%BS+P4e)-6?e#m}i@dhX4N!@1JKJ;x33@o=;&grZ7l4phGZF5jcN8$X4(hfuJEeo+*rgNsE9fd_9X5o5E1m5?(UMd$okWICSyGAh!MPlmia;EJ)ARf7*VThdB}$$Nyi?yWe4r;<sC#oZNEi`OHnyjxv2C=ry$KVP6vm;9@a}!ksfq&kQ+U1_Y({aP`Y0%N~v@-ZF4ZVGv~}-3qE%L3(m>c{*E@lRwH<kd+$nGZg;qgsDj4keH5u7b}&kWF8io$~IT#e~dk0?g=x|F(<6z(t=ft$;eG+6~i8EQeK>8^@>?T0p2J$l;$W6l@22_>0nz#_C?=8N3e*`*C}HZ^XSCbL~g!3-LzdZoO|v+uZH?y{5;<*x@X7ihfXAzPE7P8!JeJ;>|{SId`IC9CT}cv91U>5cg(_jdW3rXL*pP((N5As#MTQqHU`bwOk#@LWsM~tsTSelip%Jbx&(Ev9k@vnHD>fMvP}n#&(-WXOT3Yn4^=bjO78T48m+bnq#{r8%>G%ZC4~WgboKHW@B9i#3=>RLz^Md_+(L}tqI|q!devK4*aOm;jflx%mXV3b1LZJH9X8;^=YO_OjW0Xy|HUDfNUO$kz5RE@_8&5g98VrbhQzh<pvh9o(qW}_^;@f~L-o@?sC!@#9XU?ST4ST|%Uk@&Oj0Tf7K44PxSzc+FnA0*Xpq9>5M*%{N~P5j*5VzC%WjCsE-nHgB0KeD$69_x#vUs2L&bY5dJl<vPFs#dY7)b(f9Qe`U7R+mbRV3QqmwJ&CkU>8Qt%t$(Io1mfZ7Cs_Ixum!<;*-cY<KlK%lKJ#y}7-N>gSogm<Pk&;mW5nj?L-($q5#IKr+{XVirNM@@&k<}5+tkR#xbX=g5MNR3fMTBOIW)db@xP@`7E=HM(A)L2KZq7Gd~|BChV6e}V@=rCvXIb+WMXQ<O5-i$qa>cBH!;r^%v8$!%gtO=AhWg>OHH<x2p87V?Ji^h!m2|Lbx%%G1Mq()!nQ;^0~?_@<5gS*fr$YQ}!uL&7RF3m)e(fD>DF?mg_Th|vr@-u49+y>o|4z7q~PonzW$!oUNDohOCNi~g*)1WD|xSbk1C&+r$rO>FyQOwW%H8tuYwS*?z9El8G4$GBsb6D5F)_CS*#ixekCA0*|P8U<c<aBc9ZN*VzyJN8*_pXWyNIX&o1-<;}TQu$^$mU9ra6Ae3Z3;z~1`f8ZDDz|ta2d^quF%Ng-8N$`&rG&Z>efKbLxxspWP0xkct3Kh&gO1+nNVDx=7JnT=!_rxJ`GUOJVciUlW$*;+D|5Uj6L5zRlY6t*!ydUt~X#}fx31h0COu1tRdnq=cs!<ppH+MlPoUCfd#%jJe=4>ciFBkd!6FCNmc}^+Op)urre#lgISPqvoetJlm_xu2^_0frcc-IvSp{2EyD{jcVWGb(AtFc81nVAa-Xrw*Pm9to}T@rF=<pPGTOQ2aL;^3lo`(ke_tlgtsxCQdQ#*J&e6(hmbmBn{JLcea`u!%Q<ZY6LorvSM1CSADz#OGqvE~~8w~bUh1FsaKR}BrsZaVG^jK*%-IROIkZL~2I7BYL!4fH_YwP0>+%dxUpW#YuoqSwz`A?m6P!DfbLV(pT?Goa$F-5E^?qiDnV~R)h%lXnyK7kgcE9V$f<mzD7H`74CA5lnmPE>K+GiZ|(w3cd4&!BPhUzg!xw!KxZq6>#$QBOtpR9m>LHFeRO71C3&{LKo}jSj)UgkaQ!V6BT4g5+&5MIg8PhZ)LdD@}2?5VH4`TMfS|=ImX^f)pWArm|7V^yuD?wgYB?)xtavU$oR?vs(DKezTvza6R@o+~)LLP3rk^!|s0FPy>A^sn^}tr|4|~A+OP4U+f+&K1PjRmZ~QXNMv!P<sT!HU;ZWwu$Q;^LQulgciBVZhd}1!*7I3gTWE9{IcwYRj{_q|)DqUXNnT@l|5|u&n&CMD_3pZqC}7k{IXL^M6LN5(HtM3N;Xy?o51A(_8ETcUw-bbnscPQT-t*@_$^9>9CnEF<K;wq+>(X8pJ;!aZmQc?DZ(d?i!N$Om7YUwdBVjmaET~(^UcK_dDP-%6DVa;hbL!Sa?v_HcB!e=)!9Lx>i`~vk-agE}^U}9JM-yPwskHPxs|ps;F2x8{WEi@-O>0OuGcydTZWCFVBqa_dTXrtU0PN4I6C-)cD=-v(+;>mnVNW0&U;jpZ0i7`;BWCbXLqF$zO$T@yp)k_`p|7$;X*}F4XbWA1r0e8Jw_6@+39$a{PP70x@TrE<J(p>tX(YkeuFeBrgrqCvXso<+5FybYv3E9_sx;dw7Y`cFmBMQ<^(|#r#OaDSIh;zjV{U`YzVXfAs(?UPy$bY}V#|~rnFmXO`f3Ev5d*Odc+Z5oe=qOf;WP-7A{qO4mW?&Moy|y?=NjXJ@I=kRP<OgY>+oF-yw~Arq#?}}uP!N)MQGSsnslzk*wiJjQX}fz<m~oyIPf-w*>h_<tNz?KwjXp2F@5%nz7V@6INE@xLvpZNOH3`ouSt4z?_8D_z^#IhTm_}WfMbLf?+K;lZyN<&tPpgeEauQl*q6?0({AY0x7F39&nOk2Um?jegVC2Y6paE#=!dzZhShL}3Q^c-YV=#v=)B_E2#l)w^I36v^siMF?>DI8n8On4VWLu)7#j)`%kK#;7biyFI5C>ETLf1<ajcl<q#+j~Tw324!&CQEPhN78p?SaEfZlC(*jBcs<4`$uG-*wrXkJV+aD-E7H2us3mz{ZbM&=n`hfldLZPP>Rz3G-3fl@8L1SF?Mx5=EeDIIEpB3Fzr0maA{<10wm(SeNq73(*MD$HA*)iM|lUBKFO6^!Px8Y&|kUjpjuW%_y<fh?fK_9KlhVv!O}uL{*`KV>q!bP6uj-#3+XpE<r1XE`!)-UJfohQ)bLhQlh7Z94z#g4o7&T~b=9BdmDJQuBpnQk`!HD3v}0RHzEA+}G77;+q3KPwj8ZO@sHWA4MBT$i&QR{Gs&83B(I%v1>VYB$s-T7m-GF6X7|TqqG#Gd!DbJDpl7~OfFMeP|Ex0ie+T>yL-j5XWTou%%POm%_*62m%5vF3V-rZS8ArS-SK5I;ef-mKb>4#EjkFQ4+opEp=C9evkcLdzstXqe;O0cmBr+QBw+wb2Cn$gWeJ(;5|?dJHIf=H(%tk0fzhC1BuglpMyq>vWm8>p5I)sjBS{nC$l%VuP>mdz^l#BwXkiWq7Bi)%+56?6XH3e|>>w?DIN!`f3qX7GryIw|Gq_w=fATtsv*0k*_tRdu__KQ*Y6+TL^K~`*>mMG0<?e}v@#QuyCT>F$dS>^yp{2AbpEka{eJ_W(Y1aE^HNAh3`gk|#b6cI=-<{_-g>Eu+K#O+Ux~pneqdDr+FBoJAt1Y$KMpJT4CT8o~QVSzfOC5g+5(-9_cpkdMGrgw100O27n2vqhU9TCrDGKEoLur`ms}XdB4t-yfTH!r51JT$E?}viudjlOaGod4v8XN8n^`?43YH%Kuy{X=t>h?`_)Xvbkp;dQ1{A{VIj%i?CkPt<7tF7fYSbfZ1WvVKDUv|~8a2yXBDM?*AJS!`%O6pJ_fI!mbnSJ&=f!KOjm#AvVRSrzhJg&+c?X)*VDBsDL;1LvY*Txz}xW=B~t&bLBSY?MMityY*_AJ)Lb7NftvqF)o%eD{2*c=qO4%OtMva{+XuQCGYm=%hsxw2bdp{TJ!5vVj~i;yiYE6LY(aFT#OA>rxp2mOp>M)9-@6@OYVzXDezcRaao4Pyjtig(K9=1?eylkci;9SI>8<ZdI$udzewqfYL^LFMOcxpHxNoK_}<8Z^Sf9I;oXgj$(bj<qDtk>O(NlN%^OIeX7bkZJ={+iC*_>d+cfXnYYh-&8pWOd_=PMr%Y78*}USPt<eQ^3`kR+hE!~2}}o$S-PZCI@GIT_o?kOO>J{UpnXhYIFw0@-6Z0cez8qrRHij#IS=gBUw(B;i>0xOS#z*7hxGj+3zFU-?=;(pm^R>}tv1?(>NeU0GeEwt+@3lhZ2(!^Le{ooY1w5!z<dZ8k<RpK5jmmLA!?;V{NifarONVC8pvW+zt^V5Dv!1ZRd6zbxgmmImyBH<D~}&pi4KIY=$6Zf$~$5v4!YbLDoLvGO=t*(G8b*356LUJ`9Kk2a(OZD=_-x76D+IH)HSVv#?qAvf-{yr74`X)kXy){Jrd)Iq*3*xZH7Oi+Q+o+l(rz6#T?5@kC>h2SR4tgvga`bpW_a$=ysg9D?fB|5rfLMC3qC6tyN9uDPT>jl_$YkXc21`*gP=SG;1vTi)7?>E!I$DsRwI$URPCnf^7xnw@S63SaK@6fMaIvS?*pFa6RgoJRcF{2LnwrIT!G&tPN)FI?&nV_9~j3*7K&Q3Ug7aE9MR1ivQd5c2c8tytAf}EDLX^m;Ch?HHB&m'
def flow(a,b):
    I,J=len(a),len(b)
    lo=[[max(0,x+y-14)for y in b]for x in a]
    hi=[[0 if x==y==2 else min(x,y)-1 for y in b]for x in a]
    c=[r[:]for r in lo]
    rs=[x-sum(r)for x,r in zip(a,c)];cs=[b[j]-sum(r[j]for r in c)for j in range(J)]
    if min(rs+cs)<0 or any(lo[i][j]>hi[i][j] for i in range(I)for j in range(J)):return None
    def distances(allv=False):
        # Direct residual arcs in codegrees, not unit-cost arc expansion:
        # increasing c costs c, decreasing costs -(c-1).
        st=(list(range(I+J))if allv else [i for i in range(I)if rs[i]])
        ds=[99]*(I+J);pr=[-1]*(I+J);queue=deque(st);active=set(st)
        for x in st:ds[x]=0
        while queue:
            x=queue.popleft();active.remove(x)
            e=(((I+j,c[x][j])for j in range(J)if c[x][j]<hi[x][j])if x<I else
               ((i,1-c[i][x-I])for i in range(I)if c[i][x-I]>lo[i][x-I]))
            for y,h in e:
                if ds[y]>ds[x]+h:
                    ds[y]=ds[x]+h;pr[y]=x
                    if y not in active:active.add(y);queue.append(y)
        return ds,pr
    for _ in range(sum(rs)):
        ds,pr=distances();j=min((j for j in range(J)if cs[j]),key=lambda j:ds[I+j])
        if ds[I+j]==99:return None
        cs[j]-=1;x=I+j
        while pr[x]>=0:
            y=pr[x]
            if x>=I:c[y][x-I]+=1
            else:c[x][y-I]-=1
            x=y
        assert x<I and rs[x];rs[x]-=1
    assert [sum(r)for r in c]==list(a)and [sum(r[j]for r in c)for j in range(J)]==list(b)
    ds,pr=distances(True)
    assert all((c[i][j]==hi[i][j] or ds[I+j]<=ds[i]+c[i][j])and (c[i][j]==lo[i][j]or ds[i]<=ds[I+j]+1-c[i][j])for i in range(I)for j in range(J))
    return sum(comb(v,2)for r in c for v in r)
def profiles():
    # Generate by multiplicities of each degree 2,...,8; no original partition generator.
    pat=[]
    for t8 in range(3):
     for t7 in range(4):
      for t6 in range(4):
       for t5 in range(5):
        for t4 in range(6):
         for t3 in range(8):
          z=23-8*t8-7*t7-6*t6-5*t5-4*t4-3*t3
          if z<0 or z%2:continue
          p=(2,)*(z//2)+(3,)*t3+(4,)*t4+(5,)*t5+(6,)*t6+(7,)*t7+(8,)*t8
          if len(p)>=6 and sum(p[-2:])<=14:pat.append(p)
    pat.sort(key=lambda p:(-sum(comb(i,2)for i in p),p));assert len(pat)==80
    ft=[[None]*80 for _ in pat]
    for i,a in enumerate(pat):
        for j,b in enumerate(pat[:i+1]):ft[i][j]=ft[j][i]=flow(a,b)
    S=[sum(comb(x,2)for x in p)for p in pat];D=[2*p.count(2)for p in pat];H=[sum(x for x in p if x>=4)for p in pat]
    tally=0;ok={}
    def rec(p,ss,dd,hh,bb):
        nonlocal tally
        left=6-len(p)
        if left==0:
            if ss>=253 and hh>=69:
                tally+=1;F=2*(ss-253)-bb
                if F>=0:ok[tuple(sorted(pat[i]for i in p))]=(ss,F)
            return
        for i in range(p[-1]if p else 0,80):
            if ss+left*S[i]<253:break
            if dd+D[i]>23:continue
            vs=[ft[i][j]for j in p]
            if None not in vs:rec(p+[i],ss+S[i],dd+D[i],hh+H[i],bb+sum(vs))
    rec([],0,0,0,0);assert tally==229202 and len(ok)==576 and max(f for s,f in ok.values())==13
    return ok
def dual(ok):
    tab=loads(decompress(b85decode(DUAL)))
    assert len(tab)==156;seen=set();last=[]
    for P,den,v,X,Z in tab:
        tag=tuple(sorted(tuple(p)for p in P));assert tag in ok and tag not in seen
        seen.add(tag);S,F=ok[tag];assert F>=3
        A=23-2*sum(p.count(2)for p in P);assert A in (1,3)and all(len(p)==6 for p in P)
        assert den in (1,2) and len(X)==180 and len(Z)==72 and max(Z)<=0
        ix=0;val=0
        for i,j in combinations(range(6),2):
            a,b=P[i],P[j];U,V=X[ix:ix+6],X[ix+6:ix+12];ix+=12
            val+=sum(x*y for x,y in zip(a,U))+sum(x*y for x,y in zip(b,V))
            for h,x in enumerate(a):
                for k,y in enumerate(b):
                    e=6*i+h if y==2 and x!=2 else 6*j+k if x==2 and y!=2 else None
                    c0=U[h]+V[k]+(Z[2*e]-Z[2*e+1]if e is not None else 0)
                    # Minimize exactly over whole allowable integer cell. This
                    # is NOT the preceding verifier's sum of separate increment minima.
                    lo=max(0,x+y-14);hi=0 if x==y==2 else min(x,y)-1
                    val+=min(den*comb(t,2)-c0*t for t in range(lo,hi+1))
        for i,p in enumerate(P):
            for j,x in enumerate(p):
                if x!=2:
                    k=12*i+2*j;val+=x*Z[k]+(A-x)*Z[k+1]
        assert val==v
        U=(2*(S-253)*den-v)//den
        if U>=3:last.append((P,U,S-253))
    assert seen=={p for p,(s,f) in ok.items()if f>=3}
    assert sorted((u,e)for p,u,e in last)==[(3,22),(4,21)]
    for p,u,e in last:
        Q=next(i for i,a in enumerate(p)if 4 in a)
        A=23-2*sum(r.count(2)for r in p)
        types={s[Q]for s in product(*map(set,p))if sum(s)==28 and s.count(2)==1}
        assert types==({4} if e==21 else {2,4}) and (e//3+2*u)<23-A-sum(types)
    cnt=Counter()
    for P,(s,f)in ok.items():
        A=23-2*sum(p.count(2)for p in P)
        for L in range(3):
            for m in range(L+1):
                x=s-253-L-m
                if 0<=L<=f and x>=0 and x%3==0 and x//3<=A//2+2*L:
                    cnt[L,A,x//3,m]+=1;assert max(p.count(2)for p in P)<=3
    assert cnt=={(1,1,2,1):1,(2,3,5,2):12,(2,3,5,1):8,(2,3,5,0):4,(2,1,4,2):28,(2,1,4,1):10,(2,1,4,0):1,(2,1,3,0):3,(2,5,5,2):2}
    print('PASS: 80 part patterns; 229202 feasible profiles; 576/156/2 filters; last touched bounds 15<16,13<14')
def geometry():
    a=(0,0,0);b=(1,1,1);c=(0,1,2)
    def match(x,y):return sum(i==j for i,j in zip(x,y))
    for d in [None,(1,0,3),(3,0,1)]:
        base=[a,b,c]+([d]if d else [])
        for x in product(range(5),repeat=3):
            if not any(all(match(x,row)+h in (1,4) for row in base)for h in range(4)):continue
            if d is None:
                assert (x[1]==0)==(x[0]==1)==(x[2]==2)
                assert (x[1]==1)==(x[2]==0)and(x[0]==0)==(x[2]==1)
            elif d==(1,0,3):
                assert (x[1]==1)==(x[2]==0)==(x[2]==3)
                assert (x[1]==0)==(x[2]==2)==(x[2]==1)
                assert (x[0]==1)==(x[2]==0)==(x[2]==2)
            else:
                assert (x[2]==0)==(x[0]==3)and(x[0]==1)==(x[2]==2)
    # For the first square some first-order equalities force no regular outsider
    # to use either third value. Baseline rows account for the extra occurrences.
    print('PASS local center and both square ordinary/high indicator identities')
if __name__=='__main__':geometry();dual(profiles())
