from fractions import Fraction as F

def feasible(q, constraints):
    """q=(A,B,C); constraints=(a,b,strict) meaning a*t+b >=0 or >0."""
    A,B,C=map(F,q)
    lo=hi=None
    lc=hc=False
    for a,b,strict in constraints:
        a,b=F(a),F(b)
        if not a:
            if b<0 or (strict and not b): return False
            continue
        v=-b/a
        if a>0:
            if lo is None or v>lo: lo,lc=v,not strict
            elif v==lo: lc=lc and not strict
        else:
            if hi is None or v<hi: hi,hc=v,not strict
            elif v==hi: hc=hc and not strict
    if lo is not None and hi is not None and (lo>hi or (lo==hi and not(lc and hc))): return False
    def inside(t):
        return (lo is None or t>lo or (t==lo and lc)) and (hi is None or t<hi or (t==hi and hc))
    if not A:
        return inside(-C/B) if B else C==0
    def val(t): return A*t*t+B*t+C
    v=-B/(2*A)
    if inside(v) and val(v)==0: return True
    if lo is not None and lc and val(lo)==0: return True
    if hi is not None and hc and val(hi)==0: return True
    points=[lo]+([v] if (lo is None or lo<v) and (hi is None or v<hi) else [])+[hi]
    for l,r in zip(points,points[1:]):
        if l is not None and r is not None and l==r: continue
        if (A if l is None else val(l))*(A if r is None else val(r))<0: return True
    return False

if __name__=='__main__':
    assert feasible((1,0,-1),[(1,-1,False)])
    assert not feasible((1,0,-1),[(1,-1,True)])
    assert feasible((1,0,-2),[(1,-1,True),(-1,2,True)])
    assert not feasible((1,0,0),[(1,0,True)])
    assert feasible((1,0,0),[(1,0,False),(-1,0,False)])
    assert not feasible((0,0,0),[(1,0,True),(-1,0,False)])
    print('PASS')
