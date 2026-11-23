"""Exact three-Hoffman-coclique local-star certificate; Python standard library."""
from itertools import permutations, combinations_with_replacement
CERT={
    0: ([(('cn', 0, 0), -14756), (('adj', 0, 1), -179952), (('cn', 0, 3), 55098), (('cn', 1, 1), 276675), (('cn', 1, 2), -156498), (('cn', 3, 3), 26460)],-21227832),
    1: ([(('cn', 0, 0), -1948), (('adj', 0, 1), -37704), (('cn', 0, 1), -1746), (('adj', 0, 3), 44208), (('adj', 0, 7), -27272), (('cn', 0, 7), 13307), (('cn', 1, 1), 68520), (('cn', 1, 2), -44112), (('cn', 3, 3), 12960)],-2899008),
    2: ([(('cn', 0, 0), -3070), (('adj', 0, 1), -72828), (('cn', 0, 1), -43657), (('adj', 0, 3), 50904), (('adj', 0, 7), -42980), (('cn', 0, 7), 39891), (('cn', 1, 1), 198520), (('cn', 1, 2), -95200), (('cn', 1, 6), 133824), (('cn', 3, 3), 29808)],-819504),
    5: ([(('cn', 0, 0), 44), (('adj', 0, 1), 186), (('cn', 0, 1), -528), (('adj', 0, 3), -792), (('adj', 0, 7), 616), (('cn', 0, 7), -22), (('cn', 1, 2), 1323), (('cn', 1, 3), 135), (('cn', 1, 6), 729), (('cn', 1, 7), -459), (('cn', 7, 7), 198)],-1584),
    6: ([(('cn', 0, 0), 10616), (('cn', 0, 1), -155256), (('adj', 0, 3), -353832), (('adj', 0, 7), 148624), (('cn', 1, 1), -32055), (('cn', 1, 2), 366576), (('cn', 1, 3), 276556), (('cn', 1, 6), 143936), (('cn', 3, 3), 164674), (('cn', 3, 5), -90022), (('cn', 7, 7), 23095)],-8527104),
    7: ([(('cn', 0, 0), 86858), (('adj', 0, 1), 125916), (('cn', 0, 1), -535011), (('cn', 0, 3), 180), (('adj', 0, 7), 1216012), (('cn', 0, 7), -210811), (('cn', 1, 1), -291060), (('cn', 1, 2), 1318464)],-54802008),
    8: ([(('adj', 0, 1), 12), (('cn', 0, 1), -31), (('cn', 0, 7), 7), (('cn', 1, 2), 78)],-6468),
}
CONTROL={
    3: [(29, 1), (30, 24), (31, 1), (32, 7), (37, 2), (38, 3), (41, 1), (44, 1), (50, 3), (51, 1), (54, 1), (55, 4), (70, 1), (71, 4), (81, 4), (82, 3), (83, 2), (86, 5), (87, 1), (88, 3), (90, 5), (92, 2), (93, 7), (96, 5), (97, 5), (98, 3)],
    4: [(18, 3), (25, 3), (31, 10), (32, 7), (37, 4), (39, 1), (50, 1), (52, 7), (55, 13), (57, 3), (73, 1), (82, 3), (84, 7), (87, 3), (89, 7), (91, 4), (94, 6), (95, 4), (97, 4), (98, 4), (99, 4)],
}

def venn(ks,t):
 k12,k13,k23=ks
 return [99-66+sum(ks)-t,22-k12-k13+t,22-k12-k23+t,k12-t,22-k13-k23+t,k13-t,k23-t,t]
def stars(c,y):
 q=[i for i in range(1,8)if not y&i and c[i]]
 ans=[]
 def go(j,ns,rs):
  if j==len(q):
   if any(rs):return
   base=14-sum(ns)
   if 0<=base<=c[0]-(not y):
    h=[0]*8;h[0]=base
    for i,v in zip(q,ns):h[i]=v
    ans.append(tuple(h))
   return
  i=q[j];n=min([c[i]]+[rs[k]for k in range(3)if i>>k&1])
  for z in range(n+1):
   v=[a-z*((i>>k)&1) for k,a in enumerate(rs)]
   go(j+1,ns+[z],v)
 go(0,[],[0 if y>>k&1 else 4 for k in range(3)])
 return ans

def labels(t):
    c=venn((8,8,8),t)
    at=[(i,h)for i in range(8)if c[i] for h in stars(c,i)]
    return c,at

def entry(row,i,h):
    typ,*v=row
    if typ=='m':
        return int(i==v[0])
    a,b=v
    if typ=='adj':
        return (i==a)*h[b]-(i==b)*h[a]
    assert typ=='cn'
    return h[a]*h[b]+(i==a)*h[b]

def rhs(row,c):
    typ,*v=row
    if typ=='m':return c[v[0]]
    a,b=v
    return 0 if typ=='adj' else 2*c[a]*c[b]+12*c[a]*(a==b)

def moves(i,h):
    # These six permutations rename the three cocliques, not graph vertices.
    for p in permutations(range(3)):
        f=[sum(((m>>j)&1)<<p[j]for j in range(3)) for m in range(8)]
        b=[0]*8
        for m in range(8):b[f[m]]=h[m]
        yield f[i],b

def main():
    for t in range(9):
        c,at=labels(t)
        assert sum(c)==99 and len(at)==[60,84,95,99,100,94,76,39,9][t]
        if t in CERT:
            terms,target=CERT[t]
            assert len(dict(terms))==len(terms) and target<0
            assert sum(w*rhs(k,c) for k,w in terms)==target
            for i,h in at:
                six=sum(w*entry(k,j,g) for j,g in moves(i,h) for k,w in terms)
                assert six>=0
            print("triple intersection",t,": impossible; target",target)
        else:
            terms=CONTROL[t]
            assert len(terms)==len(dict(terms)) and all(0<=i<len(at) and w>0 for i,w in terms)
            laws=[('m',i) for i in range(8)]
            laws += [('adj',i,j) for i in range(8)for j in range(i+1,8)]
            laws += [('cn',i,j)for i,j in combinations_with_replacement(range(8),2)]
            for k in laws:
                assert sum(w*entry(k,*at[i])for i,w in terms)==rhs(k,c)
            print("triple intersection",t,": nonnegative integer star control")
if __name__=="__main__":main()
