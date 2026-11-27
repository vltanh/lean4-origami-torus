#!/usr/bin/env python3
"""Exact symbolic checks for the twisted, equally spaced Type 7 two-ring obstruction."""
import itertools as it
import sympy as s

def cross(u,v): return u[0]*v[1]-u[1]*v[0]
def V(x,y): return s.Matrix([x,y])
def J(u): return V(-u[1],u[0])
def z(e): return s.expand(e)==0

# Check the underlying triangulation against Lutz 7.
F=[]
for i in range(4):
 j=(i+1)%4
 F.extend([(i,j,4+i),(4+i,4+j,j),(i,j,4+(i+2)%4),(4+i,4+j,(i+3)%4)])
canon=lambda f:{tuple(sorted(t)) for t in f}
lutz=canon([tuple(map(int,t)) for t in '356 325 364 302 341 310 506 524 547 570 674 601 617 214 207 271'.split()])
p=next(p for p in it.permutations(range(8)) if canon([tuple(p[i] for i in t) for t in F])==lutz)
print('Type 7 isomorphism:',p)

# Arbitrary diagonal offsets, half-diagonals and centroid displacement.
b=V(*s.symbols('b0 b1'));t=V(*s.symbols('t0 t1'));u=V(*s.symbols('u0 u1'));v=V(*s.symbols('v0 v1'));w=V(*s.symbols('w0 w1'));zv=V(*s.symbols('z0 z1'));C=V(*s.symbols('c0 c1'))
B=[b+u,-b+v,b-u,-b-v];T=[C+t+w,C-t+zv,C+t-w,C-t-zv]
e=[cross(B[(i+1)%4]-B[i],(T[i]+T[(i+2)%4])/2-B[i]) for i in range(4)]
f=[cross(T[(i+1)%4]-T[i],(B[(i+1)%4]+B[(i+3)%4])/2-T[i]) for i in range(4)]
print('Midpoint pair sums B:',[s.factor(e[i]+e[i+2]) for i in range(2)])
print('Midpoint pair sums T:',[s.factor(f[i]+f[i+2]) for i in range(2)])
# Normalized offsets and zero centroid displacement.
a,h,c,d,vx,vy,zx,zy=s.symbols('a h c d vx vy zx zy');b=V(1,0);t=V(0,1);u=V(a,h);v=V(vx,vy);w=V(c,d);zv=V(zx,zy)
B=[b+u,-b+v,b-u,-b-v];T=[t+w,-t+zv,t-w,-t-zv]
e=[cross(B[(i+1)%4]-B[i],(T[i]+T[(i+2)%4])/2-B[i]) for i in range(4)]
f=[cross(T[(i+1)%4]-T[i],(B[(i+1)%4]+B[(i+3)%4])/2-T[i]) for i in range(4)]
assert s.solve([e[0]-e[2],e[1]-e[3]],(vx,vy))=={vx:-h,vy:a}
assert s.solve([f[0]-f[2],f[1]-f[3]],(zx,zy))=={zx:-d,zy:c}
B=[q.subs({vx:-h,vy:a}) for q in B];T=[q.subs({zx:-d,zy:c}) for q in T]
K=-a*(c+d)+h*(c-d);M=a*(c-d)+h*(c+d)
assert z(K*K+M*M-2*(a*a+h*h)*(c*c+d*d))
E=[B[(i+1)%4]-B[i] for i in range(4)];F=[T[(i+1)%4]-T[i] for i in range(4)]
ks=[cross(E[i],T[i]-B[i]) for i in range(4)];ls=[cross(F[i],B[(i+1)%4]-T[i]) for i in range(4)]
print('B cross products:',list(map(s.expand,ks)));print('T cross products:',list(map(s.expand,ls)))
A,D,L=s.symbols('A D L');H=s.Matrix([[A,D],[D,L]])
P=[s.expand((q.T*H*q)[0]-k*k) for q,k in zip(E,ks)];Q=[s.expand((q.T*H*q)[0]-k*k) for q,k in zip(F,ls)]
print('Opposite differences B:',[s.factor((P[i]-P[i+2])/8) for i in range(2)])
print('Opposite differences T:',[s.factor((Q[i]-Q[i+2])/8) for i in range(2)])
print('Sum B:',s.factor(sum(P)))
sol=s.solve([P[0]-P[2],P[1]-P[3]],(A,D));sol2=s.solve([Q[0]-Q[2],Q[1]-Q[3]],(D,L));print('B solution',sol);print('T solution',sol2)
R=s.groebner([a*a+h*h-2,c*c+d*d-2],a,h,c,d,A,D,L)
red=lambda q:R.reduce(s.expand(q))[1]
assert all(red(q-r)==0 for q,r in zip(ks,[K-2*d,K+2*c,K+2*d,K-2*c]))
assert all(red(q-r)==0 for q,r in zip(ls,[K-2*h,K+2*a,K+2*h,K-2*a]))
assert all(red(q-r)==0 for q,r in zip([(P[0]-P[2])/8,(P[1]-P[3])/8,(Q[0]-Q[2])/8,(Q[1]-Q[3])/8],[A*(a+h)-D*(a-h)+K*d,-A*(a-h)-D*(a+h)-K*c,D*(c+d)-L*(c-d)+K*h,-D*(c-d)-L*(c+d)-K*a]))
assert red(sum(P)/2-(12*A+4*L-2*K*K-8))==0
for expr in [(a+h)*(A*(a+h)-D*(a-h)+K*d)-(a-h)*(-A*(a-h)-D*(a+h)-K*c)-(4*A-K*K),-(a-h)*(A*(a+h)-D*(a-h)+K*d)-(a+h)*(-A*(a-h)-D*(a+h)-K*c)-(4*D+K*M),-(c-d)*(D*(c+d)-L*(c-d)+K*h)-(c+d)*(-D*(c-d)-L*(c+d)-K*a)-(4*L-K*K)]:
 assert red(expr)==0
assert red(K*K+M*M-8)==0
print('PASS: normalized altitude identities force A=L=K^2/4, D=-KM/4, K^2=M^2=4, det H=0.')
