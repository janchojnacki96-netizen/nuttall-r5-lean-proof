"""Independent exact-rational witness finder for W5 cell 51.

This mirrors the existing certified evaluation formulas, not Lean's
proof checker. Printed floats are display-only; all signs and the
generated witness endpoints use exact Fraction comparisons.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial as fac, comb, floor, ceil
from time import monotonic

D = 2**768
def point(q): return (Q(q), Q(q))
def add(A,B): return (A[0]+B[0], A[1]+B[1])
def neg(A): return (-A[1], -A[0])
def sub(A,B): return add(A,neg(B))
def mul(A,B):
    p=[x*y for x in A for y in B]
    return min(p),max(p)
def inv(A):
    assert A[0]*A[1]>0
    return 1/A[1],1/A[0]
def ipow(A,n):
    v=point(1)
    for _ in range(n): v=mul(v,A)
    return v
def isum(it):
    v=point(0)
    for a in it: v=add(v,a)
    return v
def rnd(A): return Q(floor(A[0]*D),D),Q(ceil(A[1]*D),D)

@lru_cache(None)
def expneg(a,b):
    # Matches the existing monotone Taylor65 and outward fixed-point squaring.
    lo=sum((a/1024)**k/fac(k) for k in range(65))
    hi=sum((b/1024)**k/fac(k) for k in range(65))+Q(2,3**65*fac(65))
    assert 0<=a<=b<=Q(1024,3)
    A=rnd(inv((lo,hi)))
    for _ in range(10): A=rnd(mul(A,A))
    return A

@lru_cache(None)
def poly(k,z):
    if k==0: return Q(1)
    return k*poly(k-1,z)+z**k

@lru_cache(None)
def mass(k,L,U):
    return sub(mul(expneg(L,L),point(poly(k,L))),mul(expneg(U,U),point(poly(k,U))))

def root(q,L,steps):
    z=1+q*L; lo=Q(1); hi=z
    for _ in range(steps):
        m=(lo+hi)/2
        if m**4<=z: lo=m
        else: hi=m
    return lo,hi

@lru_cache(None)
def moment(y,k,h,steps,H=48):
    q=y*y; lo=hi=point(0)
    for L in reversed(range(0,H,h)):
        L=Q(L); U=min(L+h,H); t=q/(1+q*L)
        c=[1-t*L/4-3*t*t*L*L/32,t/4+3*t*t*L/16,-3*t*t/32]
        d=[c[0]-7*t**3*L**3/128,c[1]+21*t**3*L**2/128,c[2]-21*t**3*L/128,7*t**3/128]
        R=root(q,L,steps)
        l=mul(R,isum(mul(point(v),mass(k+j,L,U)) for j,v in enumerate(c)))
        u=mul(R,isum(mul(point(v),mass(k+j,L,U)) for j,v in enumerate(d)))
        lo=rnd(add(l,lo)); hi=rnd(add(u,hi))
    return lo[0],hi[1]+expneg(Q(H),Q(H))[1]*(poly(k,Q(H))+q*poly(k+1,Q(H))/4)

def cubic(a,b,n,k):
    y=a/n; z=b/n
    return (fac(k)+y*y*fac(k+1)/4-3*y**4*fac(k+2)/32,fac(k)+z*z*fac(k+1)/4-3*z**4*fac(k+2)/32+7*z**6*fac(k+3)/128)

def factor(i,j,t): return Q((-1)**(i+j-t),fac(t)*fac(i-t)*fac(j-t))
def choose(n,k): return comb(n,k) if 0<=k<=n else 0

def matrix(a,b,h,steps,sharp=(1,2),degrees=range(9)):
    X=(a,b); scale=mul(ipow(X,2),point(Q(1,4)))
    M={n:[rnd((moment(a/n,k,h,steps)[0], moment(b/n,k,h,steps)[1])) if n in sharp and (n!=1 or k in degrees) else cubic(a,b,n,k) for k in range(9)] for n in range(1,7)}
    E={n:expneg(Q(n*n-1)/b**2,Q(n*n-1)/a**2) for n in range(2,7)}
    def first(i,j):
        def coeff(k):
            return isum(mul(point(factor(i,j,t)*choose(t,k-(i+j-2*t))),ipow(X,(i+j-2*t)+2*(k-(i+j-2*t)))) for t in range(min(i,j)+1) if i+j-2*t<=k)
        return sub(point(Q((-1)**i,fac(i)) if i==j else 0),mul(scale,isum(mul(coeff(k),M[1][k]) for k in range(9))))
    def higher(n,i,j):
        p=n*n; G=mul(point(p-1),inv(X))
        base=isum(mul(point(factor(i,j,t)),mul(ipow(G,i+j-2*t),point(p**t))) for t in range(min(i,j)+1))
        def mm(t):
            m=i+j-2*t
            return mul(point(factor(i,j,t)),isum(mul(point(choose(m,s)*choose(t,u)*p**(t-u)),mul(ipow(G,m-s),mul(ipow(X,s+2*u),M[n][s+u]))) for s in range(m+1) for u in range(t+1)))
        return sub(mul(point(p),mul(E[n],base)),mul(scale,mul(E[n],isum(mm(t) for t in range(min(i,j)+1)))))
    B={}
    for i in range(5):
        for j in range(i,5):
            B[i,j]=B[j,i]=add(add(first(i,j),isum(higher(n,i,j) for n in range(2,7))),(-Q(1,10**20),Q(1,10**20)))
    return B

def pivots(B):
    B={ij:rnd(A) for ij,A in B.items()}
    out=[]
    for k in range(5):
        A=B[k,k]; ok=A[0]>0 if k%2==0 else A[1]<0
        out.append((k+1,ok,float(A[0]),float(A[1])))
        if not ok: break
        # Outward rounding decreases denominator growth without narrowing.
        B={(i,j):rnd(sub(B[i,j],mul(mul(B[i,k],B[k,j]),inv(A)))) for i in range(k+1,5) for j in range(k+1,5)}
    return out

if __name__=='__main__':
    a=Q(148367,262144); b=Q(145,256); mid=(a+b)/2
    assert a <= Q(56597518920898438,10**17) and b == Q(56640625000000000,10**17)
    t=monotonic(); B=matrix(a,b,4,8,sharp=(1,))
    print('full widened dyadic cell, sharp n=1 only:', a,b)
    C={ij:(Q(floor(z[0]*10**6)-1,10**6),Q(ceil(z[1]*10**6)+1,10**6)) for ij,z in B.items()}
    print('upper witness intervals in millionths:')
    for i in range(5):
        for j in range(i,5):
            l,u=C[i,j]; print(i,j,int(l*10**6),int(u*10**6))
            assert l<=B[i,j][0]<=B[i,j][1]<=u
    print('exact, unrounded Schur replay of compact witness:')
    for k in range(5):
        A=C[k,k]; ok=A[0]>0 if k%2==0 else A[1]<0
        print(k+1,ok,floor(A[0]*10**6),ceil(A[1]*10**6))
        assert ok
        C={(i,j):sub(C[i,j],mul(mul(C[i,k],C[k,j]),inv(A))) for i in range(k+1,5) for j in range(k+1,5)}
    print('seconds:',monotonic()-t)
