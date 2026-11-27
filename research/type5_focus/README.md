# Type 5 only: hexagonal feasibility and projection obstructions

Goal: decide universality of Lutz Type 5, preferably by an exact obstruction at the hexagonal modulus. **No universality status is changed.** All existing orientation and marking reductions remain subject to their earlier proof audits.

## Two height orbits

With anchor face 125, let the five heights correspond to vertices (0,3,4,6,7). Normalize height 3 positive. The previous 138 clique-sign patterns give seven height patterns: all positive (102 clique patterns), and six split patterns (6 clique patterns apiece). The six triangulation automorphisms act transitively on the split patterns modulo reflection. `verify_crossing_cycle.py` checks every automorphism, the induced lattice matrix, preservation of the exact hexagonal metric, and preservation of the entire cocycle up to gauge. Thus two height families suffice: all positive and (+,+,-,-,-). This does not reduce the continuous problem to two finite points.

## A metric-independent projection obstruction

In any linear projection of an embedded Type 5 torus, the following four pairs of disjoint edges cannot all cross transversely in their interiors:

    A: 27 and 45
    B: 37 and 45
    R: 05 and 24
    C: 04 and 35

At a crossing, record the nonzero signed difference between the heights of the first and second edge. First assume the projection is generic, so every face projects to a nondegenerate triangle. In the common projected region of two faces sharing at most one vertex, the difference of their affine height functions has constant strict sign away from any common vertex. Indeed if the signs at two such points differed, their segment would contain a zero. A shared vertex cannot lie in the interior of this segment, because it is an extreme point of the projected triangles. The zero would violate embeddedness. For the four face pairs below, the crossing points are in their common regions, not at a common vertex (strict transverse crossings and generic projection).

| Faces | Crossing differences imply |
|---|---|
| 237 and 045 | sign A = sign B |
| 274 and 045 | sign A = -sign R |
| 357 and 045 | sign B = -sign C |
| 024 and 053 | sign C = -sign R |

Multiplying these four equations gives a contradiction. Nongeneric projections with all four strict crossings are also impossible, since the crossings persist under a small generic perturbation of the projection direction. This establishes a necessary condition for **arbitrary** embedded realizations, independently of flatness or marking.

## Entire coincident planar hexagonal family excluded

Use the previous hexagonal marking and gauge K_1i=0. Write intrinsic coordinates as (x,y) with physical norm x^2+3y^2, and impose the coincident planar base condition r_i=p_i (in the anchor plane). Equal squared lengths of the nonzero-shift edges give ten independent linear equations on the fourteen intrinsic coordinates. The exact solution family is parametrized by p6=(u,v), p7=(a,b), with d=u/3+v-a/3, h=b-d, c=a+1/2-3h/2:

    p1=(0,0), p4=(a,d), p7=(a,b)
    p0=(a+1/2,b-1/6), p2=(a+1/2,d+1/6)
    p3=(c,(d+b)/2-1/6), p5=(c,(d+b)/2+1/6).

Even weak nearest-edge constraints on the edges 14 and 10 imply -1/2<=a<=0. Consistent nonzero intrinsic face orientations on 012 and 147 give the same sign to -(a+1/2)(1/3-h) and ah. In particular -1/2<a<0 and 0<h<1/3. Translate the x origin to a, the y origin to (d+b)/2, then scale the axes by 2 and 6. With s=3h in (0,1), the six relevant planar points become

    p4=(0,-s), p7=(0,s), p0=(1,s-1), p2=(1,1-s),
    p3=(1-s,-1), p5=(1-s,1).

All four forbidden crossings now follow from quadratic orientation determinants, whose strict signs on the entire interval (0,1) are verified by their exact Bernstein coefficients. Thus no vertical lift of any such planar configuration is embedded. In fact, no embedded realization has any of these projections or any sufficiently close projection, as all four crossings are strict. This is not a general nonexistence theorem at the hexagonal metric: planar bases with r != p, boundary-degenerate projections, and three-dimensional configurations outside these projection neighborhoods are not covered.

## General projection-cycle filter

`projection_cycles.py` constructs the signed graph of the 153 possible disjoint-edge comparisons. Connect two comparisons if their edges lie in the same pair of triangles sharing at most one vertex; the relative sign is prescribed by which triangle contains which edge. A negative-product cycle of active transverse crossings is impossible by the height-order argument above. Enumerating cycles of length at most four, then removing supersets of smaller inconsistent cycles, yields nine triples and 438 quadruples (447 forbidden crossing sets total). These are necessary conditions, not a complete characterization of liftability. `focused_system.py` optionally adds all of them to the two hexagonal metric systems as exact Boolean combinations of planar determinant inequalities. The exact full-system embedding constraints remain in the default generator.

## Reproduction and computational limitations

Requires Python 3 and SymPy for the two exact checkers. Run `python verify_crossing_cycle.py` and `python projection_cycles.py`. Both passed. `python focused_system.py` generates the two full SMT systems; `python solve.py 6000 systems/*.smt2` uses libz3. The pre-filter full SMT systems both timed out at 6000 ms. The split branch with all 447 projection clauses, both without and with full embedding constraints, returned unknown (timeout at 7000 ms). Neither is an infeasibility certificate. Other tests: the six split clique patterns converged to zero margin in floating optimization, a first moment/RLT relaxation remained too loose, and continuation toward large aspect ratio did not give a certified embedding. An elongated relaxed numerical solution without embedding conditions is not an exact proof. No claim about feasibility or infeasibility of the full hexagonal system follows from these experiments.

Next useful gate: close one of the two height families by exact infeasibility or obtain a certified embedded hexagonal witness. If both families are excluded at this one metric, Type 5 is not universal. If an embedding is found, that does not prove universality. Do not switch to another type or mistake restricted planar-family obstructions for closure.
