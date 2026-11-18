"""Small exhaustive checks of cut definitions, the coding bound and mixed parallel cells."""
from itertools import combinations, product
from math import comb

def require(b, label):
    if not b:
        raise ArithmeticError(label)

def graphs(n):
    pairs=list(combinations(range(n),2))
    for m in range(1<<len(pairs)):
        g=[0]*n
        for j,(a,b) in enumerate(pairs):
            if m>>j&1: g[a]|=1<<b;g[b]|=1<<a
        if len(components(g,(1<<n)-1))==1:yield g

def components(g,live):
    out=[]
    while live:
        c=live&-live;todo=c
        while todo:
            b=todo&-todo;todo^=b
            add=g[b.bit_length()-1]&live&~c
            c|=add;todo|=add
        out.append(c);live^=c
    return out

def objects(g):
    full=(1<<len(g))-1
    sets=[components(g,full^s) for s in range(full+1)]
    global_=[];terminal=[];clean=[]
    # No appeal to restoring a single vertex: scan in inclusion-compatible
    # order, requiring no previously minimal subset to be contained in s.
    for s,cc in enumerate(sets):
        if len(cc)>=2 and not any(d&s==d for d in global_):global_.append(s)
        if not(s&3) and not any(c&3==3 for c in cc):
            if not any(d&s==d for d in terminal):
                terminal.append(s)
                if len(cc)==2:clean.append(s)
    return sets,global_,clean

def nb(g,c):
    a=0
    for i in range(len(g)):
        if c>>i&1:a|=g[i]
    return a&~c

def code(g,root,actions=None,target=None):
    c=1<<root;out=0; tape=[];idx=0
    while True:
        candidates=nb(g,c)&~out
        if not candidates:break
        v=candidates&-candidates
        if actions is None:yes=bool(v&target)
        else:yes=actions[idx];idx+=1
        tape.append(yes)
        if yes:c|=v
        else:out|=v
    if actions is not None:require(idx==len(actions),'code tape not exhausted')
    return c,out,tuple(tape)

def embedded(g,lab,H):
    for i,adj in enumerate(g):
        for j in range(len(g)):
            if adj>>j&1:H[lab[i]]|=1<<lab[j]

def par(g,h):
    N=len(g)+len(h)-2;H=[0]*N
    embedded(g,list(range(len(g))),H)
    embedded(h,[0,1]+list(range(len(g),N)),H)
    return H

def selector(base,k):
    # Keep one new source, one sink, k common gates and disjoint cell interiors.
    p=len(base)-2; family=list(combinations(range(k),k//2))
    H=[0]*(2+k+p*len(family));H[0]=sum(1<<(2+j) for j in range(k))
    for j in range(k): H[2+j]|=1
    def position(c,v):return 1 if v==1 else 2+k+c*p+v-2
    def put(x,y):H[x]|=1<<y;H[y]|=1<<x
    for i,F in enumerate(family):
        for v in range(2,len(base)):
            if base[0]>>v&1:
                for j in F: put(2+j,position(i,v))
            for u in range(1,v):
                if base[u]>>v&1:put(position(i,u),position(i,v))
    return H,family

def known_witnesses(base,k):
    _,_,clean=objects(base);H,fam=selector(base,k);p=len(base)-2
    universe=(1<<len(H))-1; unique=set()
    for disabled in [-1]+list(range(len(fam))):
        gates=sum(1<<(2+j) for j in fam[disabled]) if disabled>=0 else 0
        choices=[clean if i!=disabled else [0] for i in range(len(fam))]
        for vals in product(*choices):
            seg=gates
            for i,mask in enumerate(vals):seg|=(mask>>2)<<(2+k+i*p)
            require(seg not in unique,'gate-witness collision');unique.add(seg)
            parts=components(H,universe^seg)
            require(len(parts)==2 and not any(u&3==3 for u in parts),'selector gave dirty or unseparated cut')
            # Test all proper subsets directly, not just single restorations.
            w=seg
            while w:
                w=(w-1)&seg
                require(len(components(H,universe^w))==1,'selector cut not inclusion-minimal')
    M=len(fam);g=len(clean)
    require(len(unique)==g**M+M*g**(M-1),'gate witness total')
    return len(unique)

def main():
    ng=n3=n4=0
    for n in range(3,7):
        for g in graphs(n):
            ng+=1; sets,Ss,_=objects(g);codes=set()
            for s in Ss:
                cc=sets[s]
                require(all(nb(g,c)==s for c in cc),'non-full global shore')
                if len(cc)==3:
                    a,b,c=[(u&-u).bit_length()-1 for u in cc]
                    H=g[:];H[b]|=1<<c;H[c]|=1<<b
                    parts=components(H,((1<<n)-1)^s)
                    require(len(parts)==2 and not any((u>>a)&(u>>b)&1 for u in parts),'bad three-shore merge')
                    require(all(nb(H,u)==s for u in parts),'merged shore not full')
                    n3+=1
                if len(cc)>=4:
                    c=min(cc,key=lambda u:(u.bit_count(),u));a=(c&-c).bit_length()-1
                    mask,bdry,tape=code(g,a,target=c)
                    require((mask,bdry)==(c,s) and code(g,a,actions=tape)[:2]==(c,s),'decoder')
                    require(len(tape)+3*sum(tape)<=n-4 and (a,tape) not in codes,'budget or collision')
                    codes.add((a,tape));n4+=1
    print('Connected labeled graphs on 3 through 6 vertices:',ng,'; three-shore cases:',n3,'; four-plus-shore codes:',n4)
    small=list(graphs(3))+list(graphs(4))
    pairs=endpoint=pile=0
    for g,h in product(small,repeat=2):
        a=objects(g)[2];b=objects(h)[2];H=par(g,h);sets,Ss,cl=objects(H)
        pred={x|((y>>2)<<len(g)) for x in a for y in b}
        separated={s for s in Ss if not (s&3) and not any(c&3==3 for c in sets[s])}
        require(pred==set(cl)==separated,'mixed parallel product')
        A=((1<<len(g))-1)^3;B=((1<<len(H))-1)^((1<<len(g))-1)
        for s in set(Ss)-pred:
            require(not(s&A and s&B),'nonlocal exceptional cut')
            endpoint+=bool(s&3);pile+=1
        pairs+=1
    print('Ordered mixed-cell graph pairs with terminal adjacency allowed:',pairs,'; localized exceptional cuts:',pile,'; containing terminals:',endpoint)
    require(ng==27474 and n3>0 and n4>0 and pairs==1764,'unexpected case counts')
    # Nontrivial overlapping gates at k=4. Base interiors form a path; a second
    # base with one local dangling component at a cut vertex exercises cleanliness.
    extra=[[4,8,1|8,2|4], [4,8,1|8|16,2|4,4]]
    tested=0
    for base,k in [(extra[0],3),(extra[0],4),(extra[1],4)]+[(g,2) for g in small if not g[0]&2 and len(components(g,((1<<len(g))-1)^1))==1]:
        tested+=known_witnesses(base,k)
    p=3;g=3;k=8;M=comb(k,k//2)
    require((g**M+M*g**(M-1))**p>g**(p*M+k),'exact normalized gain')
    print('Distinct certified gate witnesses across test instances:',tested,'; strict p=3, k=8 integer comparison passed.')
    print('PASS')
if __name__=='__main__':main()
