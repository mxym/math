"""Exact fixed-H M=3 Hoffman-axis certificate on the {018,024,230} face.
Run beside two_type_true_hoffman.py and its existing native dependencies."""
import sympy as sp
import two_type_true_hoffman as parent

def check():
 old=parent.illegal
 try:
  assert (2,30) in old
  parent.illegal=old-{(2,30)}
  os,ix,by,rows,rhs,r=parent.buildcore()
 finally:parent.illegal=old
 def K(key,ang):
  sel=dict(by[key]).get(ang)
  return [int(q==sel)for q in os]
 def add(v,b):rows.append(v);rhs.append(b)
 add(r({(1,27):1,(0,18):-9}),0)
 add(K((2,22),22),1);add(r({(0,14):1}),0);add(K((2,22),15),0);add(r({(2,22):1}),3)
 dirs=[((0,0,0,0),1),((1,2,3,1),1),((1,-1,1,-2),1),((2,-1,1,2),1)]
 for d in (2,4,6,8):
  extra=parent.moments(by,ix,[d],dirs);rows.extend(extra);rhs.extend([0]*len(extra))
 # Rows M x = b; append b to every coefficient row.
 A=sp.Matrix([v+[b] for v,b in zip(rows,rhs)]);B,piv=A.to_DM().rref();B=B.to_Matrix()
 assert len(os)==119 and len(piv)==106
 S=r({(1,23):1,(0,0):-99})
 positive=[(9,(4,46),2),(18,(2,22),8),(9,(2,34),1),(72,(1,23),11),
           (20,(1,29),11),(2,(1,29),4),(2,(1,29),-3),(27,(1,23),4),(-18,(2,34),-6)]
 left=[86*z+6*w+sum(n*K(key,d)[i]for n,key,d in positive) for i,(z,w) in enumerate(zip(S,r({(2,34):1})))]
 target=sp.Matrix([left+[237+27*77]])
 for i,p in enumerate(piv):target-=target[0,p]*B[i,:]
 assert not any(target)
 print('M=3 pooled true Hoffman chart: 86 S <=237. With S+M=0 mod 3 this forces S=0.')
if __name__=='__main__':check()
