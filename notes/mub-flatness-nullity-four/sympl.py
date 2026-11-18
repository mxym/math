def sym(x,y,n):
 m=(1<<n)-1
 return ((((x>>n)&(y&m)).bit_count()+((y>>n)&(x&m)).bit_count())%2)
def lags(n):
 L={frozenset({0})}
 for r in range(n):
  L={frozenset((*s,*(x^y for y in s))) for s in L for x in range(1,4**n) if x not in s and not any(sym(x,y,n) for y in s)}
 return [set(s)-{0} for s in L]
