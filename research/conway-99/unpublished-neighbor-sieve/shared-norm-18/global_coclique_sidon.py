"""Integer arithmetic bounds for the global coclique-difference injection."""
from math import comb

def main():
    out=[]
    for k in range(16):
        n=22-k
        total=10*n
        pairs=2*comb(n,2)-n*comb(4,2)
        sq=2*pairs+total
        assert pairs==n*(n-7) and sq==2*n*(n-2)>0
        hit=(total*total+sq-1)//sq
        z=99-2*n-hit
        out.append(z-k)
        assert k<=z<=k+5 and n+max(0,2*k-z)>15
    assert out==[0,0,1,2,2,3,3,4,4,4,5,4,4,3,2,0]
    print("Global Sidon bound: all 16 possible intersection sizes pass.")

if __name__=="__main__":main()
