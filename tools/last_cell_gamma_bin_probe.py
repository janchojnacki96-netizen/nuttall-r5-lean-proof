"""Exact rational witness finder for last-cell Gamma primitive replay.
The output is not a proof. Lean independently verifies the exponential
table, each local bin inequality, and the final sum comparison.
"""
import json
from last_cell_exact_probe import Q, D, expneg, root, mass, isum, mul, point, poly, moment, rnd, floor, ceil


def local(y,k,L,U,up):
    q=y*y
    t=q/(1+q*L)
    c=[1-t*L/4-3*t*t*L*L/32,t/4+3*t*t*L/16,-3*t*t/32]
    d=[c[0]-7*t**3*L**3/128,c[1]+21*t**3*L**2/128,c[2]-21*t**3*L/128,7*t**3/128]
    return mul(root(q,L,8),isum(mul(point(v),mass(k+j,L,U)) for j,v in enumerate(d if up else c)))


def generate():
    a,b=Q(148367,262144),Q(145,256)
    scale=10**16
    E=[]
    lower=[]
    upper=[]
    for i in range(13):
        z=expneg(Q(4*i),Q(4*i))
        assert all(v*D==int(v*D) for v in z)
        E.append([int(z[0]*D),int(z[1]*D)])
    for i in range(12):
        L,U=Q(4*i),Q(4*(i+1))
        lower.append([floor(local(a,k,L,U,False)[0]*scale) for k in range(9)])
        upper.append([ceil(local(b,k,L,U,True)[1]*scale) for k in range(9)])
    for k in range(9):
        lo=Q(sum(r[k] for r in lower),scale)
        hi=Q(sum(r[k] for r in upper),scale)+expneg(Q(48),Q(48))[1]*(poly(k,Q(48))+b*b*poly(k+1,Q(48))/4)
        old=rnd((moment(a,k,4,8)[0],moment(b,k,4,8)[1]))
        wlo=Q(floor(old[0]*10**8),10**8)
        whi=Q(ceil(old[1]*10**8),10**8)
        assert wlo<=lo<=hi<=whi
    return {"E":E,"lower":lower,"upper":upper}


if __name__=="__main__":
    print(json.dumps(generate(),indent=2))
