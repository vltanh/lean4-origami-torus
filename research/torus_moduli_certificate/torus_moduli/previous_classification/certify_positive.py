"""Exact interval existence certificates for types 4,5,6 (Lutz numbering).
Seeds from FabianLander/low-vertex-flat-tori/data/flat-embedded/type-{4,5,6}.csv,
second rows. The preconditioners are fixed rational inputs. All acceptance checks
use integer outward-rounded interval arithmetic; decimals printed are diagnostic.
"""
from fractions import Fraction
from math import isqrt
from itertools import combinations
import json
from pathlib import Path

FACES={
4:'012 031 024 053 045 152 134 146 165 264 257 276 374 356 367 475',
5:'012 031 024 053 045 152 136 164 147 175 263 237 274 256 357 465',
6:'012 031 024 053 045 152 136 164 147 175 274 256 267 357 376 465'}
SEEDS={
4:'-0.607867553379072,-0.05533158859105297,-0.49081296852081974,-0.6139413163649111,0.27935571541264276,0.07912083537017725,0.44203324317676135,0.03690933433304718,0.22317669154371453,0.19384710442409103,-0.5488520896850666,-0.3581659712542159,0.25671014830887723,-0.18425627691694266,0.3200817374081607,-0.38043551042561446,0.31853338918326696,-0.7303393416260849,0.4459837278741993,0.0758366856908444,0.21286922889740073,-0.36576649332961725,0.2793424918869759,-0.7098608310164157',
5:'0.18197457769237554,0.7580190749622752,0.450100684431877,0.5555859764293868,-1.0563533978579924,-0.347740350378255,-0.2471245049875923,0.7823425103709422,0.3858714213329437,-0.7156879060502385,-0.09857972670087116,-0.4898816638957145,0.10977132472067429,-0.597855329509704,0.8730338093100432,0.9044857333558625,-0.508021867310781,-0.011845750331255298,0.14879632604033935,0.5561279227120114,0.4896247280118395,-0.5765872260920023,-0.22836436571975693,-0.48524221409862844',
6:'0.32467724943178017,-0.22220686932578482,-0.21221722610341948,-0.960354968775553,0.19558977430791055,-0.9275413898821329,0.5758552927313737,0.219928404041229,-0.4905939671431473,-0.04615207992523954,-0.09360819717033729,0.26421712019860505,-0.4478531493482282,0.03975739052483718,-0.2590451262795818,-0.8254476738218319,1.0250200741158007,-0.5938921000867735,-0.7020741917884924,1.0435115095215073,-0.32392537026122026,0.5843809005598226,0.21832744884502714,-0.46397373959917687'}
Q=1<<100
class I:
    def __init__(self,a,b=None):
        if b is None:
            if isinstance(a,I): self.l,self.h=a.l,a.h;return
            f=Fraction(str(a));self.l=f.numerator*Q//f.denominator;self.h=-((-f.numerator*Q)//f.denominator)
        else: self.l,self.h=a,b
    def __add__(a,b):
        b=I(b);return I(a.l+b.l,a.h+b.h)
    __radd__=__add__
    def __neg__(a):return I(-a.h,-a.l)
    def __sub__(a,b):return a+-I(b)
    def __rsub__(a,b):return I(b)+-a
    def __mul__(a,b):
        b=I(b);v=[x*y for x in (a.l,a.h) for y in (b.l,b.h)];return I(min(v)//Q,-((-max(v))//Q))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=I(b);assert b.l>0 or b.h<0
        return I(min(x*Q//y for x in (a.l,a.h) for y in (b.l,b.h)),max(-((-x*Q)//y) for x in (a.l,a.h) for y in (b.l,b.h)))
    def sqrt(a):
        assert a.l>=0
        l=isqrt(a.l*Q);h=isqrt(a.h*Q);return I(l,h+(h*h<a.h*Q))
    def absmax(a):return max(abs(a.l),abs(a.h))
    def sign(a):
        assert a.l>0 or a.h<0, (a.l/Q,a.h/Q)
        return 1 if a.l>0 else -1
    def mid(a):return (a.l+a.h)/(2*Q)

def dot(a,b):return sum(x*y for x,y in zip(a,b))
def sub(a,b):return [x-y for x,y in zip(a,b)]
def cross(a,b):return [a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0]]
def vertices(p):return [p[3*i:3*i+3] for i in range(8)]

def evaluate(p,faces,need_jac=True):
    p=vertices(p);fs=[];J=[];angle_bounds=[];cs=[]
    for v in range(8):
        re,im=I(1),I(0);row=[I(0) for _ in range(24)];upper=0
        for t in faces:
            if v not in t:continue
            b,c=[i for i in t if i!=v];u,w=sub(p[b],p[v]),sub(p[c],p[v]);d=dot(u,w);u2,w2=dot(u,u),dot(w,w)
            cr=dot(cross(u,w),cross(u,w)).sqrt();norm=(u2*w2).sqrt();co,si=d/norm,cr/norm
            re,im=re*co-im*si,re*si+im*co
            # upper bound in units pi/4; all triangle angles in (0,pi).
            if (d-cr).l>0:upper+=1
            elif d.l>0:upper+=2
            elif (cr+d).l>0:upper+=3
            else:upper+=4
            if need_jac:
                du=[(d*x/u2-y)/cr for x,y in zip(u,w)]
                dw=[(d*y/w2-x)/cr for x,y in zip(u,w)]
                for k in range(3):
                    row[3*b+k]+=du[k];row[3*c+k]+=dw[k];row[3*v+k]-=du[k]+dw[k]
        fs.append(im);cs.append(re);angle_bounds.append(upper);J.append([re*x for x in row])
    return fs,J,angle_bounds,cs

def verify_embedding(p,faces):
    p=vertices(p);signs={}
    margins=[]
    for t in combinations(range(8),4):
        a,b,c,d=t;det=dot(sub(p[b],p[a]),cross(sub(p[c],p[a]),sub(p[d],p[a])))
        signs[t]=det.sign();margins.append(min(abs(det.l),abs(det.h)))
    E={tuple(sorted(e)) for t in faces for e in combinations(t,2)};F={tuple(sorted(t)) for t in faces};n=0
    for C in combinations(range(8),5):
        s=[(-1)**i*signs[C[:i]+C[i+1:]] for i in range(5)]
        pos=tuple(v for v,i in zip(C,s) if i>0);neg=tuple(v for v,i in zip(C,s) if i<0)
        assert not ((pos in E and neg in F) or (neg in E and pos in F)), ('intersect',C,pos,neg)
        n+=sum(not set(e)&set(f) and set(e)|set(f)==set(C) for e in E for f in F)
    return min(margins)/Q,n

def certify(t):
    f=[tuple(map(int,x)) for x in FACES[t].split()];p=[I(x) for x in SEEDS[t].split(',')];fs,J,ub,cos=evaluate(p,f)
    print('type',t,'seed sin residual',max(x.absmax()/Q for x in fs),'angle upper bounds',ub)
    # The column choices and rational matrices were found by numerical QR.
    # They are now fixed input; the verifier has no numerical dependencies.
    cols,raw_A=json.loads(Path(__file__).with_name('preconditioners.json').read_text())[str(t)]
    assert len(set(cols))==7 and all(0<=j<24 for j in cols)
    A=[[I(x) for x in row] for row in raw_A]
    R=I('0.000000001');box=[x+I(-R.h,R.h) if i in cols else x for i,x in enumerate(p)]
    ff,JJ,upper,cc=evaluate(box,f)
    assert all(x<16 for x in upper) and all(x.l>0 for x in cc)
    e=[dot(row,fs[:7]) for row in A];beta=max(x.absmax() for x in e)
    B=[[I(int(i==j))-sum(A[i][k]*JJ[k][cols[j]] for k in range(7)) for j in range(7)] for i in range(7)]
    q=max(sum(x.absmax() for x in row) for row in B)
    # beta and q are upper bounds scaled by Q. Ensure beta+q*r < r.
    assert q<Q and beta*Q+q*R.h<R.l*Q, (beta/Q,q/Q,R.l/Q)
    margin,pairs=verify_embedding(box,f)
    print('PASS',t,'free',cols,'beta',beta/Q,'q',q/Q,'r',R.l/Q,'min determinant',margin,'disjoint edge/face checks',pairs,'upper',upper)
    assert beta*10**15<3*Q and q*50000<Q
    return True

if __name__=='__main__':
    for t in (4,5,6):certify(t)
