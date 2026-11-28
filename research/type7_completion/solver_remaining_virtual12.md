# Virtual edge 12 at the remaining ray-1 endpoint

This package gives exact necessary direction restrictions at the endpoint
handled by `remaining_ray1_endpoint.py`. It does **not** exclude the whole
endpoint. Every zero leading bracket remains allowed.

## Coordinates and complete sign binding

The first transverse stretch has points

\[
\begin{aligned}
R_0&=(0,0,0), &R_1=R_2=R_4&=(0,0,1),\\
R_3&=(1/2,0,1), &R_5&=(1/2,c,0),\\
R_6&=(0,d,0), &R_7&=(1/2,e,0).
\end{aligned}
\]

The independently checked first-width cone forces the transverse
coordinates of 2 and 4 to vanish. Thus its nonzero width can be normalized
by `max(abs(c),abs(d),abs(e)) = 1`. The six faces of the cube `[-1,1]^3`
cover every such profile; the computation uses their entire faces.

The source module enumerates all 331 generic primary sign completions of
its necessary first-stretch formula. Its separately emitted blocking CNF
binds that list to an independent completeness check. The present packet
stores the sorted 70-character sign strings and compares them with a
fresh source enumeration. It does not use scratch enumeration indices.

For a separately normalized virtual edge `R2-R1 -> a=(aX,aY,aZ)`, the
necessary rows are all nonzero macro four-brackets and the ten virtual
four-brackets `[12jk]`, with `j,k` in `{0,3,5,6,7}`. Their ordered forms
before parity conversion to increasing vertex order are

| `(j,k)` | Ordered determinant |
|---|---|
| `(0,3)` | `-aY/2` |
| `(0,5)` | `c*aX-aY/2` |
| `(0,6)` | `d*aX` |
| `(0,7)` | `e*aX-aY/2` |
| `(3,5)` | `(c*aZ+aY)/2` |
| `(3,6)` | `(d*aZ+aY)/2` |
| `(3,7)` | `(e*aZ+aY)/2` |
| `(5,6)` | `(d-c)*aX+(d*aZ+aY)/2` |
| `(5,7)` | `(e-c)*(aX+aZ/2)` |
| `(6,7)` | `(e-d)*aX-(d*aZ+aY)/2` |

The checker reconstructs these determinants directly from coordinates.
For each generic completion, the signed actual determinant is constrained
only to be nonnegative. No assumption is made about the relative scale
or direction of the other collapsed edge to vertex 4.

## Exact direction conclusions

The replayed surviving counts are:

| Direction family | Surviving primary sign completions |
|---|---:|
| `(1,aY,2)` | 172 |
| `(0,1,0)` | 0 |
| `(0,-1,0)` | 0 |
| `(r-1,aY,-2r)`, every `0<r<1` | 0 |
| `(-1,aY,0)` | 15 |
| `(0,aY,-2)` | 38 |
| `(0,aY,2)` | 172 |

Here `aY` is free except in the two pure-transverse rows. A surviving
completion has a rational witness for this necessary linear relaxation;
it is not claimed to realize the metrics or a torus embedding.

The parameter family covers the whole quadrant `aX<0,aZ<0` up to positive
rescaling. Therefore a compatible nonzero direction cannot have both
coordinates negative, and cannot have both zero. In particular,
`aZ=2*aX` implies `aX>0`.

The pure-transverse exclusion also proves a uniform bound
`abs(aY) <= C*(abs(aX)+abs(aZ))` for this necessary family, for some finite
constant `C`. Otherwise divide a sequence by `abs(aY)`, choose a fixed
one of the finite sign completions, and take a convergent subsequence of
the normalized macro profiles. The limit would satisfy one of the two
excluded pure-transverse systems. This conclusion does not require a
prior relative-width assumption.

For the endpoint metric dichotomy proved in the source module, the
continuous deficit family has direction `(r-1,aY,-2r)`. The proof reduces
it to `r=0` or `r=1`; the other deficit branch has direction `(0,aY,2)`.
The corresponding three boundary families remain for metric analysis.

## Polynomial Farkas certificates

For fixed directions the rows are rational affine inequalities in
`(c,d,e,aY)`. For the open quadrant their coefficients are affine in `r`.
Every rejected cube-face system has an exact identity

\[
\sum_i w_i(r)\bigl(A_i(r)x+b_i(r)\bigr)=-p(r),
\qquad w_i(r)\ge0,\quad p(r)>0.
\]

Replay checks every coefficient of this identity exactly. It expands
each weight and residual in the Bernstein basis on `[0,1]`. Nonnegative
Bernstein coefficients give nonnegative weights; a nonzero nonnegative
Bernstein coefficient vector gives a strictly positive residual at every
`0<r<1`, since every Bernstein basis function is positive there.
The 102 open-quadrant certificates need only weights among
`1`, `2`, `1-r`, `2r`, `2(1-r)`, and residuals among
`1`, `2`, `1-r`, `2r`. Thus no sampled parameter is used in the proof.

Rows are regrouped by their full exact coefficient vectors. Each rejected
group has all six normalization faces checked. Each surviving group has
one exactly checked rational witness. The replay checks the complete
partition of all 331 sign completions in every direction family.

## Reproduction

```sh
python research/type7_completion/solver_remaining_virtual12.py
python research/type7_completion/solver_remaining_virtual12.py --produce /tmp/virtual12.json
```

The second command uses SciPy's LP implementation only to find supports;
SymPy solves each supported identity exactly and replay is mandatory.
The first command does not import SciPy or trust any floating-point
solver status. The separate endpoint coverage CNF must also be replayed
before these conclusions are used with its claimed complete model list.

The frozen packet has 426 exact Farkas certificates and is 227,480 bytes.
A fresh process, including the 331-model enumeration and all replay,
took 0.91 seconds in this workspace. Fresh production plus mandatory
replay took 4.814 seconds and reproduced the packet byte for byte.
Memoizing repeated symbolic bracket rows is material here: uncached
production plus replay took 124.19 seconds. The cache changes no rows or
certificate rules.
