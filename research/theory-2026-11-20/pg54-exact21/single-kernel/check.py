from itertools import product

def require(condition):
    if not condition:
        raise RuntimeError('Finite-field check failed')

F=range(4)
def m(a,b):
    r=(a if b&1 else 0)^((a<<1) if b&2 else 0)
    return r^(7 if r&4 else 0)
def tag(u,v,z):return m(u,z)^m(m(v,z),m(v,z))
graphs={tuple(tag(u,v,z) for z in F) for u,v in product(F,repeat=2)}
require(len(graphs)==16)
for u,v in product(F,repeat=2):
    require((len({tag(u,v,z) for z in F})==4)==bool(bool(u)^bool(v)))
def rank(cols):
    piv={}
    for c in cols:
        while c and (b:=c.bit_length()) in piv: c^=piv[b]
        if c:piv[c.bit_length()]=c
    return len(piv)
def columns(i,u,v,linear):
    return tuple((((z if i!=1 else 0)<<2) | ((z if i!=0 else 0)<<4)) | (m(u^v,z) if linear else tag(u,v,z)) for z in (1,2))
cs={(i,u,v,a):columns(i,u,v,a) for i,u,v,a in product(range(3),F,F,range(2))}
old=new=0
for coords in product(product(F,F),repeat=3):
    ro,rn=(rank([c for i,(u,v) in enumerate(coords) for c in cs[i,u,v,a]]) for a in range(2))
    require(ro!=6 or rn==6)
    old+=(ro==6);new+=(rn==6)
require((old,new)==(1536,3072))
print('16 distinct graphs; 6 invertible tags; 4096 circuit lifts: 1536 originally direct, all retained among 3072 direct replacements.')
def tr(z):return z^m(z,z)
for u,v,z in product(F,repeat=3):
    require(tr(tag(u,v,z))==tr(m(u^v,z)))
print('Trace identity verified for all 64 (u,v,z).')
