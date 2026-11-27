# Type 4 is near-universal: every modulus off the sharp-rhombic ray

## Theorem

In Lutz numbering, Type 4 has an embedded piecewise-affine isometric realization of every flat torus with reduced modulus x+i*y, where 0<=x<1/2, y>0, x^2+y^2>=1. The claim includes every rectangular torus, every rhombic torus on the unit-circle arc except the hexagonal endpoint, and arbitrarily large aspect ratios. The realization can be chosen regular (rank nine for the seven angle deficits and two shape coordinates). No claim is made for x=1/2.

`prior_wide/verify.py` covers 0<=x<=9/20, as proved in the previous iteration. `verify_open.py` closes 9/20<=x<1/2. Run both scripts with Python 3 and SymPy, with assertions enabled. The actual outputs are included. The two proofs use only exact rational polynomial computations and a standard implicit-function argument; no numerical search is trusted.

## New construction

Set w=y^2, delta=1-2*x, H=1+(3/2)*delta^2, a=H*x, D=H-1+a, q=H/D and r=-(2/3)*D. Use the planar family in the previous wide certificate, with these replacements for H and r. In physical coordinates (X,y*Y), its rational coordinates (X,Y) are

    p0=(0,0)
    p1=(1-a-r,H+q*r)
    p2=(1/2,0)
    p3=(a+T3,H+q*T3)
    p4=(1,0)
    p5=(1+T5,q*T5)
    p6=(a,H)
    p7=(1-a,H)

where

    T5=((a*a-a+H*H*w)*q/H-1)/(1+q*q*w)
    T3=-(-a*a*q+2*a*H+a*q+H*H*q*w+H*q*q*r*w+H*r-H)/((H+q*r)*(q*q*w+1))

On the open strip all denominators in these formulas are nonzero: H>0, D>0, H+q*r=H/3>0 and w>0. The script proves the face area signs, convexity of the quadrilateral used to flip 35 to 26, the exact cone-angle identities, the marked lattice periods, and the nonzero horizontal seven-by-seven angle-deficit minor. It computes the cone angles at a base point x=9/20,w=1-x^2 using exact bounds by pi/4, then uses continuity and the complex angle-product identities throughout the connected strip. The explicit two-parameter family gives the two independent modulus derivatives in the kernel of the deficit differential. The new triangulation is isomorphic to Type 4, as checked by the explicit relabeling in the script. All calculations of flatness and modulus are the same as in the earlier wide proof, now with different H and r.

Use the new heights

    (0, 6*delta, 1, -(5/2)*delta^2, 0, 2, 0, (9/8)*delta).

The script certifies 68 of 70 affine determinant signs for these heights, and a strict nonintersection witness for all 140 disjoint edge-face pairs. Each quadruple has a noncollinear projected triple, so the two uncertified signs can be avoided by arbitrarily small generic perturbation of heights, preserving all strict witnesses. This gives an embedded lifted complex. At any fixed target modulus, the implicit function theorem gives horizontal corrections tending to zero as the chosen generic heights are scaled by epsilon tending to zero. Undoing the vertical scale shows embeddedness persists, as in prior_wide/README.md. Flatness and the target modulus are preserved exactly by the implicit function theorem. The rank-nine condition persists at sufficiently small positive epsilon.

### Open-endpoint sign test

Substitute x=9/20+t/20, w=1-x^2+h with 0<=t<1 and h>=0. For any polynomial in t,h write it as sum_j c_j(t) h^j. To prove strict positivity, the code checks all Bernstein coefficients of every c_j on [0,1] are nonnegative and the first Bernstein coefficient of c_0 is strictly positive. The zeroth Bernstein basis function (1-t)^degree is strictly positive for t<1, so this proves the desired sign everywhere on the open strip, even if the polynomial vanishes at t=1. For rational functions numerator and denominator are checked separately. The same test applied to -P proves negativity. This is why the proof covers arbitrarily close to the boundary without claiming the endpoint.

At x=1/2 the family itself degenerates: H=1, p0=p3 and p6=p7. It cannot simply be inflated there by the same regularity argument. This is a limitation of this construction, not a nonexistence result for Type 4.

## Remaining case families

`remaining_markings/verify_orbits.py` reproduces the winding-marking orbit count from the previous finite reduction (see reduction_README.md) and additionally uses the 12-element hexagonal lattice point group at x=1/2,w=3/4. The full ray has 2,1,4 marking orbits for Types 4,5,7, respectively; at the hexagonal endpoint these merge to 1,1,2. Since Types 4 and 7 now cover all x<1/2, only the two Type 5 interior families and the seven sharp-ray families remain, nine in total. The nine original SMT-LIB systems are copied in `remaining_markings/systems`, with the four hexagonal specializations in `remaining_markings/hex`. No SMT satisfiability or infeasibility is claimed. A single infeasible marking is not enough to disprove universality; all admissible markings at a fixed modulus would have to be infeasible. Conversely, existence in one marking is sufficient for that modulus, but not for universality of the whole ray.

## Limitations and attribution

The Type 4 proof builds on the earlier Lander square planar seed and on the inflation method of Doyle, Lander, Schwartz and Trettel (arXiv:2611.21909). The Type 7 interior coverage combines Doyle and Schwartz's near-universality (arXiv:2510.12623) with the previously certified rectangular strip. The new result does not settle Type 4, 5 or 7 universality. Direct numerical distance-fit attempts at sharp moduli did not find embedded witnesses; they are not nonexistence certificates. The Type 2 impossibility result from prior work is still pending independent audit and is not a premise of the Type 4 proof. The new argument has not undergone independent peer review or novelty verification.
