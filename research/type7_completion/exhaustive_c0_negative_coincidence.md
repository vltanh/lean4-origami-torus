# The negative-other-cap coincidence case of C0

For ray 1 and `0<u,v<1/2`, a C0 limit with `P1=P3` and a regular
negatively oriented lower cap 067 is impossible. The proof uses one
actual-trit certificate and the exact C0 metric radius. It makes no
assumption about the order of the two intermediate heights.

## 1. Four zero-safe actual consequences

Use the full source
`exhaustive_c0_collinear.ActualModel('1_equals_3', -1, ...)`.
It retains the necessary topology and linking clauses, both strict
height cuts, interpolation at the coincident vertices, rank clauses,
weak Grassmann–Pluecker relations, and 49 exact uniform height
relations. The regular lower cap has `C67=cross(P6,P7)<0`.

The new CNF proves the conjunction

\[
[0156]=0,\qquad [0157]\le0,\qquad
[1567]\ge0,\qquad [0127]>0.
\tag{1}
\]

These are actual trit statements. In particular, the negation of
the last conclusion includes both zero and negative values; its
strictness is not inferred from a generic completion.

## 2. A segment forced by the signs

Here `d1=d2=0`, `P0=P1=P3=0`, and `|P2|=1/2`.
Put

\[
M=d_6+d_7=|P_6|>0,\qquad \ell_v=1-2v>0.
\]

Since `2[0156]=C56`, the first conclusion of (1) forces
`P5=t P6` for a real scalar `t`. The second conclusion is
`C57=t C67<=0`, so `t>=0`. The exact determinant identity is

\[
2[1567]=C_{57}-C_{56}-\ell_v C_{67}
=(t-\ell_v)C_{67}.
\tag{2}
\]

Because `C67<0`, the third conclusion gives `t<=lv`. Thus

\[
0\le t\le\ell_v,\qquad
|P_5-\ell_v P_6|\le\ell_v M.
\tag{3}
\]

Every sign and the orientation factor in (2) is checked by direct
determinant expansion in the companion.

## 3. The exact radius is strictly larger

The core C0 stress says

\[
d_0=h_1h_7+P_2\cdot P_7,
\qquad h_1=1/2,\quad |P_7|=h_7>0.
\]

The last conclusion of (1) gives `C27>0`, so these two nonzero
vectors are not parallel. Strict Cauchy–Schwarz therefore yields

\[
d_0>0.
\tag{4}
\]

The exact metric radius, valid on this closed cap boundary, is

\[
Q_5=P_5-2vP_3-\ell_vP_6=P_5-\ell_vP_6,
\qquad
|Q_5|=d_3+d_4+\ell_vD,
\qquad D=d_0+M.
\]

All deficits are nonnegative, and (4) gives

\[
|Q_5|>\ell_vM,
\]

contradicting (3). This closes the entire negative-other-cap
coincidence case without a rate assumption or a further blow-up.

## Consequences and remaining scope

The earlier [collinear-cap package](exhaustive_c0_collinear.md)
already excludes both strict upper line orders when the regular
lower cap is negatively oriented. This note completes the negative
orientation by covering the remaining coincidence order.

Together with [the positive-orientation extension](exhaustive_c0_collinear_positive.md),
every upper-collinear/regular-lower C0 limit is excluded for
`0<v<=u<1/2`. The checked marked cap-swap gives the corresponding
regular-upper/collinear-lower cases. The positive-other-cap,
both-nonpositive mixed branch with `v>u`, both-collinear limits,
and height endpoints remain separate problems.

## Reproduction

```sh
python research/type7_completion/exhaustive_c0_negative_coincidence.py /tmp/c0-negative-coincidence
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-negative-coincidence-rup \
  --checker /tmp/type7-rup-check /tmp/c0-negative-coincidence
```

The producer replays the source metric/core bindings and checks the
determinant, segment, Gram, and radius identities. Its single actual
CNF must have an independently accepted proof before using (1).
