#!/usr/bin/env python3
"""Exact algebra checks; no claim of metric infeasibility."""
from itertools import product
import sympy as S
a,b,c=S.symbols('a b c');A=S.Matrix([[a,b],[b,c]]);D=A.det()
u,v,w,z=S.symbols('u v w z');U=S.Matrix([[u,v],[w,z]])
x,y,h,k=S.symbols('x y h k');V=S.Matrix([[x,y],[h,k]])
e,f,g,i=S.symbols('e f g i');B=S.Matrix([[e,f],[g,i]])
M=A.row_join(U).col_join(V.row_join(B));R=D*B-V*A.adjugate()*U
assert S.expand(D*M.det()-R.det())==0
ac,ad,bc,bd,M,L,U,V,w,s,k=S.symbols('ac ad bc bd M L U V w s k',nonzero=True)
alpha,beta,alpha2,beta2=ac/M,bc/L,ad/M,bd/L
hc2=2*alpha*(beta*w-U);hd2=2*beta2*(alpha2*w-V)
hchd=s+(alpha*beta2+alpha2*beta)*w-beta*V-alpha2*U
k=ac/ad
assert S.cancel(hc2+k*k*hd2-2*k*hchd-2*k*((beta-k*beta2)*V-s))==0
k=bd/bc
assert S.cancel(hd2+k*k*hc2-2*k*hchd-2*k*((alpha2-k*alpha)*U-s))==0
r={1:S.Matrix([0,0,0]),2:S.Matrix([2,1,0]),5:S.Matrix([1,2,0]),3:S.Matrix([1,-2,3]),4:S.Matrix([-1,4,-2]),0:S.Matrix([3,1,-1]),6:S.Matrix([1,4,5]),7:S.Matrix([0,-2,2])}
G=lambda i,j:(r[i].T*S.diag(1,3,1)*r[j])[0]
D=S.Matrix.hstack(r[2][:2,0],r[5][:2,0]).det()
T={j:D*r[j][:2,0] for j in r};H={j:D**2*G(j,j)-(T[j].T*S.diag(1,3)*T[j])[0] for j in (0,3,4,6,7)}
J={(i,j):D**2*G(i,j)-(T[i].T*S.diag(1,3)*T[j])[0] for i,j in product((3,4),(0,6,7))}
W={1:0,2:0,5:0,3:H[3]*H[0],4:J[3,0]*J[4,0],**{j:H[0]*J[3,j] for j in (0,6,7)}}
assert all(W[i]==D*H[0]*S.sqrt(H[3])*r[i][2] for i in r)
for j in (6,7):assert J[4,0]*J[3,j]==J[4,j]*J[3,0]
# Wrong sign passes squared tests but not mixed tests.
assert (-J[4,6])**2==H[4]*H[6]
assert J[4,0]*J[3,6]!=-J[4,6]*J[3,0]
print('PASS Schur determinant, two slack-square identities, signed Gram completion')
