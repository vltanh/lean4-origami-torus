# Fourteen angular patterns on the regular C1 component

This necessary topological reduction applies to both remaining markings.
It assumes that projected endpoint triangles `234` and `067` are
noncollinear and that `0<alpha,beta<1`. It does not exclude any metric
case. The closed metric identities, including the exceptional corner,
remain in [the C1 circle package](solver_remaining_c1_geometry.md).

## Cap orientations and complete coverage

The spatial limit has coordinates `r_i=(P_i,z_i)`, with `P0=P1=0` and

\[
z=(0,\alpha/2,1/2,1/2,1/2,\beta/2,0,0).
\]

All other vertices lie strictly below the upper cap and strictly above
the lower cap. Thus the five brackets `[234j]` have a common sign
opposite the planar orientation of `234`, and the five `[067j]` have
the planar orientation of `067`. These cap brackets have nonzero
limits, so the signs persist along the original sequence and under a
sufficiently small generic perturbation.

The producer checks all four possible pairs of cap orientations against
the shared necessary topology and linking formula. Three are excluded.
The only surviving pair has

\[
\operatorname{cross}(P_3-P_2,P_4-P_2)>0,\qquad
\operatorname{cross}(P_6,P_7)>0.
\]

Its primary generic sign projections number 132. They induce fourteen
patterns of the fifteen anchor cross products, in the order

\[
23,24,25,26,27,34,35,36,37,45,46,47,56,57,67.
\]

The exact identity

\[
[01ij]=\frac{\alpha}{2}\operatorname{cross}(P_i,P_j)
\]

relates these signs to the projected geometry. Every actual limit sign
is **weak**: a plus permits zero and a minus permits zero. A zero minor
may take either sign in the generic completion. The generated JSON
records all fourteen words and all 132 primary completions.

Six separately emitted CNFs certify the reduction: three exclude the
other cap orientations, one blocks all fourteen anchor patterns, one
blocks all 132 primary completions, and one proves the two extra signs
below. Independent replay of these formulas is required; raw solver
status is not a certificate.

Fresh independent replay of all six formulas passed in 0.605 seconds
in this workspace.

## Two additional planar orientation constraints

Besides the cap signs and the signs common to every anchor pattern,
exactly two further brackets are unanimous:

\[
[3456]\le0,\qquad [4567]\le0.
\]

Using the vectors from the circle package,

\[
\begin{aligned}
E_3&=P_4-P_3,& F&=P_7-P_6,\\
R_5&=P_5-\beta P_3-(1-\beta)P_6,&Y_5&=\beta E_3-R_5,
\end{aligned}
\]

symbolic determinant expansion gives

\[
2[3456]=\operatorname{cross}(R_5,E_3),\qquad
2[4567]=-\operatorname{cross}(Y_5,F).
\]

Consequently the metric dot identities can be used together with
`cross(R5,E3)<=0` and `cross(Y5,F)>=0`. These directions matter: norm
and dot identities alone do not encode this topology.

The producer checks all fifteen anchor formulas and both extra formulas
with symbolic parameters and arbitrary projected coordinates. Complete
Boolean assignments also witness both signs of every nonunanimous
primary variable; each assignment is checked against every input clause.
These witnesses and the extra-sign UNSAT proof establish that no further
single bracket sign is forced by this cap formula.

## Reproduction and limits

```sh
python research/type7_completion/exhaustive_c1_angles.py /tmp/c1-angles
python research/type7_completion/solver_cnf_certificates.py /tmp/c1-angles-rup \
  --checker /tmp/solver-check-rup /tmp/c1-angles
```

Use the independent checker built from `solver_check_rup.cpp`, with
assertions enabled. The metric component remains open after this
reduction. Degenerate cap triangles and height endpoints require their
own covers; their vanishing cap brackets do not justify these ten units.
