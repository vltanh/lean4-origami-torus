# Closed C1 circle and dot identities

`solver_remaining_c1_geometry.py` checks a small projected metric system
for both remaining markings. Its identities hold on the entire closed
C1 component, including zero weights and zero cap areas. It does not
exclude that component.
The [turning-angle companion](solver_remaining_c1_turning.md) uses these
identities to exclude its regular part for ray 1, with boundaries and
ray 2 still requiring separate arguments.

## Parameters and endpoint triangles

Write `alpha=2A`, `beta=-2B`. The bounded-axis C1 component has

\[
1/4\le\alpha\le1,\qquad0\le\beta\le1,
\]

and limiting spatial axial levels

\[
z_0=z_6=z_7=0,\quad z_2=z_3=z_4=1/2,
\quad z_1=\alpha/2,\quad z_5=\beta/2.
\]

The axis gauge gives `P0=P1=0`. Each cyclic horizontal weight satisfies
`0<=h_i<=1/2`; their sum is `7/2` for marking 1 and `5/2` for marking 2.
Set `delta_i=1/2-h_i`.

For an edge of cyclic distance one its horizontal displacement is
`-h_i`; for distance two or three it is `1` minus the corresponding sum
of weights. Reverse the sign on a reversed edge. The checker verifies
these formulas against both original cocycles, using the exact weight
sum. It independently checks that the sum of the sixteen oriented
normalized double face areas is **+2**, fixing the orientation convention.

The upper cap 234 has edge lengths
`h2`, `h3`, `1-h2-h3`, and the lower cap 067 has edge lengths
`1-h6-h7`, `h6`, `h7`. Thus each has perimeter 1.
For the upper cap, this statement uses

\[
(1-(\alpha+\beta)/2)T_{24}=0,
\qquad T_{ij}=|P_j-P_i|^2-X_{ij}^2.
\]

Its coefficient vanishes only at `alpha=beta=1`. At that corner `q24`
remains present and the upper-cap conclusion requires the separately
proved alternative C0 description. None of the identities below divides
by this coefficient or uses `T24=0`.

## Two linked vector pairs

Define

\[
\begin{aligned}
E_2&=P_2-P_3,& E_3&=P_4-P_3,& F&=P_7-P_6,\\
R_1&=-\alpha P_3,&Y_0&=\alpha P_2,\\
R_5&=P_5-\beta P_3-(1-\beta)P_6,&Y_5&=\beta E_3-R_5.
\end{aligned}
\]

The associated nonnegative scalars are

\[
\begin{aligned}
\rho_1&=\alpha(1-h_1-h_2)+(1-\alpha)h_0,\\
\sigma_0&=(1-\alpha)(1-h_0)+\alpha h_1,\\
\rho_5&=\beta(1-h_3-h_4)+(1-\beta)h_5,\\
\sigma_5&=(1-\beta)(1-h_5)+\beta h_4.
\end{aligned}
\]

The exact necessary identities are:

| Pair | Norm identity | Dot identity |
|---|---|---|
| `R1,E2` | `|R1|²=rho1²` | `R1·E2+h2*rho1=delta1` |
| `Y0,P7` | `|Y0|²=sigma0²-2(1-alpha)*delta0` | `Y0·P7+h7*sigma0=delta0` |
| `R5,E3` | `|R5|²=rho5²` | `R5·E3+h3*rho5=delta4` |
| `Y5,F` | `|Y5|²=sigma5²-2(1-beta)*delta5` | `Y5·F+h6*sigma5=delta5` |

Their links are

\[
\begin{aligned}
R_1+Y_0&=\alpha E_2,&\rho_1+\sigma_0&=1-\alpha h_2,\\
R_5+Y_5&=\beta E_3,&\rho_5+\sigma_5&=1-\beta h_3.
\end{aligned}
\]

In the face-axis orientation `P3=(p3,0)`, `p3>=0`, the first norm identity
gives the useful exact limit formula

\[
\alpha p_3=\alpha(1-h_1-h_2)+(1-\alpha)h_0.
\]

## Exact source combinations

The six named stress identities are

\[
\begin{aligned}
F_{12}&=(\alpha-1)(T_{01}-\alpha T_{02})-\alpha T_{12},\\
F_{13}&=(\alpha-1)(T_{01}-\alpha T_{03})-\alpha T_{13},\\
F_0&=T_{01}-\alpha T_{02}-T_{17}+\alpha T_{27},\\
S&=T_{35}-(1-\beta)T_{36}-T_{45}+(1-\beta)T_{46},\\
V&=-\beta T_{35}+\beta(1-\beta)T_{36}-(1-\beta)T_{56},\\
D&=T_{57}-T_{56}-\beta(T_{47}-T_{46}).
\end{aligned}
\]

The checker independently verifies that their coefficient rows annihilate
the full 29-by-14 auxiliary system. The row for `D` includes minus the
fifth universal product-scale syzygy. Thus no product scale is discarded.

For each norm or dot formula above, subtract its right side and call the
result `N1`, `J1`, `N0`, `J0`, `N5`, `J4`, `N5lower`, `J5` in table order.
The universal polynomial identities checked are

\[
\begin{aligned}
N_1&=-F_{13},&2\alpha J_1&=F_{12}-F_{13}+\alpha^2T_{23},\\
N_0&=-F_{12},&2J_0&=(\alpha-1)T_{07}-F_0,\\
N_5&=-V,&2J_4&=S+\beta T_{34},\\
N_{5,\mathrm{lower}}&=N_5-\beta S,
&2J_5&=D-(1-\beta)T_{67}.
\end{aligned}
\]

The remaining metric rows give `T23=T34=T07=T67=0`. Since `alpha>=1/4`,
these polynomial identities yield every entry in the table. There is no
small-edge or triangle-area division.

Run:

```sh
python research/type7_completion/solver_remaining_c1_geometry.py
```

The exact replay checks eight scalar consequences, the two vector links,
the two scalar links, six full-system stress bindings, and both cocycle
and orientation conventions. It took 0.72 seconds in this workspace.
