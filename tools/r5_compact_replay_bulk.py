"""Reproduce the compact replay certificate data for the remaining R5 cells.

This is an independent exact Fraction witness finder, not Lean proof.
Run e.g. python tools/r5_compact_replay_bulk.py --verify-all or
python tools/r5_compact_replay_bulk.py --lean 4 27 39 50.
The Lean checker independently validates the integer tables.
"""
import argparse
try:
    from last_cell_exact_probe import Q, D, expneg, root, mass, isum, mul, point, poly, moment, rnd, floor, ceil, matrix, sub, inv
except ModuleNotFoundError:
    from last_cell_probe import Q, D, expneg, root, mass, isum, mul, point, poly, moment, rnd, floor, ceil, matrix, sub, inv

ENDPOINT_NUMERATORS = [12500000000000000, 34570312500000000, 40087890625000000, 42846679687500000, 45605468750000000, 46984863281250000, 48364257812500000, 49053955078125000, 49743652343750000, 50433349609375000, 51123046875000000, 51467895507812500, 51812744140625000, 52157592773437500, 52502441406250000, 52847290039062500, 53192138671875000, 53536987304687500, 53709411621093750, 53881835937500000, 54054260253906250, 54226684570312500, 54399108886718750, 54571533203125000, 54743957519531250, 54916381835937500, 55088806152343750, 55175018310546875, 55261230468750000, 55347442626953125, 55433654785156250, 55519866943359375, 55606079101562500, 55692291259765625, 55778503417968750, 55864715576171875, 55950927734375000, 56037139892578125, 56123352050781250, 56166458129882812, 56209564208984375, 56252670288085938, 56295776367187500, 56338882446289062, 56381988525390625, 56425094604492188, 56468200683593750, 56511306762695312, 56554412841796875, 56597518920898438, 56640625000000000]
ENDPOINTS = [Q(n,10**17) for n in ENDPOINT_NUMERATORS]
S = 2**24
STEPS = 12
MS, ES, WS, BS = 10**8,10**40,10**6,10**16

def local(y,k,L,U,up,steps=STEPS):
    q=y*y
    t=q/(1+q*L)
    c=[1-t*L/4-3*t*t*L*L/32,t/4+3*t*t*L/16,-3*t*t/32]
    d=[c[0]-7*t**3*L**3/128,c[1]+21*t**3*L**2/128,c[2]-21*t**3*L/128,7*t**3/128]
    return mul(root(q,L,steps),isum(mul(point(v),mass(k+j,L,U)) for j,v in enumerate(d if up else c)))

def make(cell):
    assert 4 <= cell <= 50
    orig_a, orig_b = ENDPOINTS[cell-2], ENDPOINTS[cell-1]
    a,b=Q(floor(orig_a*S),S),Q(ceil(orig_b*S),S)
    assert a<=orig_a<=orig_b<=b<=Q(145,256)
    M=[]
    for k in range(9):
        z=rnd((moment(a,k,4,STEPS)[0],moment(b,k,4,STEPS)[1]))
        M.append((floor(z[0]*MS),ceil(z[1]*MS)))
    E=[(0,0),(0,0)]
    for n in range(2,7):
        z=expneg(Q(n*n-1)/b**2,Q(n*n-1)/a**2)
        E.append((floor(z[0]*ES),ceil(z[1]*ES)))
    original=matrix(a,b,4,STEPS,sharp=(1,))
    W=[[(floor(original[i,j][0]*WS)-1,ceil(original[i,j][1]*WS)+1) if i<=j else (0,0) for j in range(5)] for i in range(5)]
    replay=matrix(a,b,4,STEPS,sharp=(1,),moment_table=[(Q(l,MS),Q(u,MS)) for l,u in M],
        exp_table={n:(Q(E[n][0],ES),Q(E[n][1],ES)) for n in range(2,7)})
    assert all(Q(W[i][j][0],WS)<=replay[i,j][0]<=replay[i,j][1]<=Q(W[i][j][1],WS)
               for i in range(5) for j in range(i,5))
    lo,hi=[],[]
    for i in range(12):
        L,U=Q(4*i),Q(4*(i+1))
        lo.append([floor(local(a,k,L,U,False)[0]*BS) for k in range(9)])
        hi.append([ceil(local(b,k,L,U,True)[1]*BS) for k in range(9)])
    for k in range(9):
        lower=Q(sum(r[k] for r in lo),BS)
        upper=Q(sum(r[k] for r in hi),BS)+expneg(Q(48),Q(48))[1]*(poly(k,Q(48))+b*b*poly(k+1,Q(48))/4)
        assert Q(M[k][0],MS)<=lower<=upper<=Q(M[k][1],MS)
    B={(i,j):(Q(W[min(i,j)][max(i,j)][0],WS),Q(W[min(i,j)][max(i,j)][1],WS)) for i in range(5) for j in range(5)}
    for k in range(5):
        A=B[k,k]
        assert (A[0]>0 if k%2==0 else A[1]<0),(cell,k,A)
        B={(i,j):sub(B[i,j],mul(mul(B[i,k],B[k,j]),inv(A))) for i in range(k+1,5) for j in range(k+1,5)}
    return a,b,M,E,W,lo,hi,A[0]

def lean_int(v):
    return str(v) if v>=0 else "("+str(v)+")"

def lean_vector(xs):
    if isinstance(xs,tuple):
        return "("+", ".join(lean_int(v) for v in xs)+")"
    if isinstance(xs,list):
        return "#["+", ".join(lean_vector(v) for v in xs)+"]"
    return lean_int(xs)

def lean_cell(cell,d):
    a,b,M,E,W,lo,hi,p5=d
    name=f"thetaCompactReplayCell{cell:02}"
    return f"""def {name} : ThetaCompactReplayCellData :=
  thetaCompactReplayDataFromArrays ({int(a*S)} / {S}) ({int(b*S)} / {S}) {STEPS}
    {lean_vector(M)}
    {lean_vector(E)}
    {lean_vector(W)}
    {lean_vector(lo)}
    {lean_vector(hi)}
"""

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("cells",type=int,nargs="*")
    p.add_argument("--lean",action="store_true")
    p.add_argument("--verify-all",action="store_true")
    args=p.parse_args()
    cells=list(range(4,51)) if args.verify_all else args.cells
    if args.lean:
        print("import W5.ThetaCompactReplayData\n\nnamespace W5\n")
    results=[]
    for c in cells:
        d=make(c)
        results.append((d[-1],c))
        if args.lean: print(lean_cell(c,d))
        else: print(f"cell {c}: PASS, fifth-pivot lower = {float(d[-1]):.10g}",flush=True)
    if args.lean: print("end W5")
    elif results:
        v,c=min(results);print(f"PASS {len(results)} cells; minimum pivot5 lower = {float(v):.10g} (cell {c})")
