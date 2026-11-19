#!/usr/bin/env python3
"""Independent W5 certificate check with pure arbitrary-precision integer arithmetic.

Every interval [L,H] denotes exact [L/2^768,H/2^768].
Integer floor and ceiling are outward; square roots use exact isqrt;
exp(-z) is enclosed using positive Taylor terms and a remainder.
The formal proof of these algorithms in Lean remains a separate obligation.
"""
from __future__ import annotations
from fractions import Fraction
from pathlib import Path
import math
import time

B = 768
S = 1 << B

def cd(n: int, d: int) -> int:
    return -((-n) // d)

class I:
    __slots__ = ('l', 'h')
    def __init__(self, l, h=None):
        self.l = l
        self.h = l if h is None else h
        assert self.l <= self.h
    def __add__(self, o):
        return I(self.l + o.l, self.h + o.h)
    def __sub__(self, o):
        return I(self.l - o.h, self.h - o.l)
    def __neg__(self):
        return I(-self.h, -self.l)
    def __mul__(self, o):
        a = self.l * o.l
        b = self.l * o.h
        c = self.h * o.l
        d = self.h * o.h
        return I(min(a,b,c,d)//S, cd(max(a,b,c,d),S))
    def __truediv__(self, o):
        assert o.l > 0 or o.h < 0, 'division by interval spanning zero'
        inv = I((S*S)//o.h, cd(S*S,o.l))
        return self * inv
    def __pow__(self,p):
        assert p >= 0
        r = ONE
        a = self
        while p:
            if p & 1:
                r = r*a
            if p > 1:
                a = a*a
            p >>= 1
        return r
    def root(self):
        assert self.l >= 0, 'negative interval sqrt'
        a = math.isqrt(self.l*S)
        b = math.isqrt(self.h*S)
        if b*b < self.h*S:
            b += 1
        return I(a,b)
    def positive(self):
        return self.l > 0
    def negative(self):
        return self.h < 0

def Q(n:int,d:int=1)->I:
    assert d>0
    return I((n*S)//d,cd(n*S,d))

ZERO = Q(0)
ONE = Q(1)
FACT = [math.factorial(i) for i in range(100)]
N = 64
REM = Q(2,3**(N+1)*FACT[N+1]).h

def expminus_point(z:int)->I:
    assert z >= 0
    k=0
    while z>(S//4)*(1<<k):
        k+=1
    a=I(z,z)/Q(1<<k)
    assert a.h*3<S
    term=ONE
    e=ONE
    for j in range(1,N+1):
        term=term*a/Q(j)
        e=e+term
    e=e+I(0,REM)
    r=ONE/e
    for _ in range(k):
        r=r*r
    return r

def expminus(a:I)->I:
    assert a.l>=0
    return I(expminus_point(a.h).l,expminus_point(a.l).h)

BIN=[Q(k,4) for k in range(257)]

def init_moments():
    prev=None
    mass=[]
    for i,z in enumerate(BIN):
        v=expminus_point(z.l)
        power=ONE
        series=ZERO
        moments=[]
        for j in range(10):
            if j:
                power=power*z/Q(j)
            series=series+power
            moments.append(Q(FACT[j])*v*series)
        if prev is not None:
            mass.append([prev[j]-moments[j] for j in range(10)])
        prev=moments
    return mass,prev

def get_moments(c:I,mass,tail):
    m=[I(0,(tail[j]+tail[j+1]).h) for j in range(9)]
    for b in range(256):
        weight=(ONE+c*I(BIN[b].l,BIN[b+1].h)).root().root()
        for j in range(9):
            m[j]=m[j]+weight*mass[b][j]
    return m

def poly(i:int,j:int,p:int,d:I,x:I,x2:I):
    coeff=[ZERO for _ in range(9)]
    for k in range(min(i,j)+1):
        h=i+j-2*k
        fac=Q((-1)**(i+j-k),FACT[k]*FACT[i-k]*FACT[j-k])
        for a in range(h+1):
            lhs=Q(math.comb(h,a))*(d**(h-a))*(x**a)
            for b in range(k+1):
                rhs=Q(math.comb(k,b)*p**(k-b))*(x2**b)
                coeff[a+b]=coeff[a+b]+fac*lhs*rhs
    return coeff

def check(l:Fraction,r:Fraction,far:bool,mass,tail):
    x=I(Q(l.numerator,l.denominator).l,Q(r.numerator,r.denominator).h)
    x2=x*x
    E=Q(1,10**35)
    A=[[I(-E.h,E.h) for j in range(5)] for i in range(5)]
    for n in range(1,2 if far else 12):
        p=n*n
        amp=ONE if n==1 else Q(p)*expminus(Q(p-1)/x2)
        d=ZERO if n==1 else Q(p-1)/x
        moments=get_moments(x2/Q(p),mass,tail)
        for i in range(5):
            for j in range(i+1):
                pol=poly(i,j,p,d,x,x2)
                integ=ZERO
                for s in range(9):
                    integ=integ+pol[s]*moments[s]
                A[i][j]=A[i][j]+amp*(pol[0]-x2/Q(4*p)*integ)
    margins=[]
    for k in range(5):
        pivot=A[k][k]
        good=pivot.negative() if k%2 else pivot.positive()
        if not good:
            raise ValueError(f'fail at k={k+1}, x=[{l},{r}], pivot={[pivot.l,pivot.h]}')
        margin=pivot.l/S if k%2==0 else -pivot.h/S
        margins.append(margin)
        for i in range(k+1,5):
            for j in range(k+1,i+1):
                A[i][j]=A[i][j]-A[i][k]*A[j][k]/pivot
    return margins

def main():
    t0=time.monotonic()
    entries=[]
    for line in Path(__file__).with_name('w5_przedzialy.txt').read_text().splitlines():
        if line.startswith('Certified'):
            continue
        l,r,flag=line.split()
        entries.append((Fraction(l),Fraction(r),int(flag)))
    assert len(entries)==51 and entries[0]==(Fraction(0),Fraction(1,8),1)
    assert entries[-1][1]==Fraction(145,256)
    assert all(entries[i][1]==entries[i+1][0] for i in range(50))
    for n,y in [(12,3),(2,64)]:
        bound=Q(2*5*4096*30000000000)*Q(n)**26*Q(y)**4*expminus(Q((n*n-1)*y))
        if not bound.h < Q(1,10**35).l:
            raise ValueError('tail bound failure')
        print(f'TAIL({n},{y})<1e-35 VERIFIED (integer arithmetic)',flush=True)
    ratio=Q(3,2)**26*expminus(Q(15))
    assert ratio.h < Q(1,2).l
    mass,tail=init_moments()
    mins=[(float('inf'),-1) for _ in range(5)]
    for idx,(l,r,far) in enumerate(entries):
        margins=check(l,r,far,mass,tail)
        for j,m in enumerate(margins):
            if m<mins[j][0]:
                mins[j]=(m,idx+1)
        print(f'PASS {idx+1}/51 elapsed={time.monotonic()-t0:.2f}s',flush=True)
    print('Minimum signed pivot bounds per order:',mins)
    print('PASS: exact integer fixed-point interval proof verified 255 signs',flush=True)

if __name__=='__main__':
    main()
