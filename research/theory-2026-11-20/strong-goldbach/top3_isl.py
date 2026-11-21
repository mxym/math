"""Read JSON lines from the row-first generator, verify each necessary set is included
in the advertised integer-k families by exact ISL set subtraction via ctypes.
Usage: node top3_pencils.js | python3 -O top3_isl.py
Requires system libisl (tested .so.23). No floating-point optimizer.
"""
import sys, json, ctypes as c, ctypes.util, hashlib
P,S,I=c.c_void_p,c.c_char_p,c.c_int
lib=c.CDLL(ctypes.util.find_library('isl'))
def fun(n,out,*args):
    f=getattr(lib,n);f.restype=out;f.argtypes=list(args);return f
ctx=fun('isl_ctx_alloc',P)()
read=fun('isl_set_read_from_str',P,P,S)
empty=fun('isl_set_is_empty',I,P)
subset=fun('isl_set_is_subset',I,P,P)
free=fun('isl_set_free',P,P)
T={"001000011001100010":["k>=2","d0=0","d1=2*k","d2=0","d3=k","d4=0","d5=0"],"001000020001100010":["k>=2","d0=0","d1=2*k","d2=0","d3=k","d4=0","d5=0"],"010000002001100001":["k>=2","d0=0","d1=2*k","d2=0","d3=k","d4=0","d5=0"],"001100000000000020":["k>=4","d0=0","d1=k","d2=0","3*d3=1+2*k","d4=k","d5=0"],"100001000000000020":["k>=4","d0=0","d1=k","d2=k","3*d3=1+2*k","d4=0","d5=0"],"010002000001000100":["k>=3","d0>=0","2*d0<=k-1","d1=0","2*d2=1+3*k","d3=k-d0","d4=k","d5=0"],"010002010001000100":["k>=3","d0=0","d1=0","2*d2=1+k","d3=k","d4=k","d5=0"],"020100000001000002":["k>=4","d0=0","d1=k","d2=0","3*d3=k-1","3*d4=1+2*k","d5=0"],"020100010000000001":["k>=3","d0=0","d1=k","d2=0","d3=k","2*d4=1+3*k","d5=0"],"100020000001000002":["k>=4","3*d0>=k+2","d0<=k","d1=0","d2=k-d0","3*d3=k-1","3*d4=1+2*k","d5=0"],"100020010000000001":["k>=3","4*d0>=3*k+3","d0<=k","d1=0","d2=k-d0","d3=k","2*d4=1+3*k","d5=0"]}
seen=set(); inputs=[]; live=[]
for line in sys.stdin:
    o=json.loads(line); tag,t,Q=o['id'].split('/'); Q=int(Q)
    ID=o['rail']+':'+o['id'];inputs.append(ID)
    A=read(ctx,o['ss'].encode())
    if not A:raise RuntimeError('parse '+ID)
    e=empty(A)
    if e not in (0,1):raise RuntimeError('ISL failed')
    if not e:
        if tag not in T:raise RuntimeError('new support '+ID)
        body=' and '.join(T[tag]+[f'j={Q}*k'])
        B=read(ctx,('{ [j,d0,d1,d2,d3,d4,d5] : exists ( k : '+body+') }').encode())
        if not B or subset(A,B)!=1:raise RuntimeError('new branch '+ID)
        free(B);seen.add(tag);live.append(ID)
    free(A)
def stamp(L):
    return (len(L),hashlib.sha256(('\n'.join(sorted(L))+'\n').encode()).hexdigest())
print('slices',*stamp(inputs));print('nonempty',*stamp(live));print('templates',len(seen))
if stamp(inputs)!=(5813,'8f7c7378e11493a5c126ea7e4a5fe6bcf839742db3c9342392b6321a5dd0ab1a') or stamp(live)!=(21,'1d2d34a057c5530a930900bafb56cef629820c959ca81afcf36a147613e2d552') or len(inputs)!=len(set(inputs)) or seen!=set(T):raise RuntimeError('incomplete ledger')
print('exact nonempty slice IDs (not all physical orbits):')
for s in sorted(live):print(s)
