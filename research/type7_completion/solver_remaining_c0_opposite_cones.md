# Reducing regular C0 to 42 positive-stem completions

For regular ray-1 C0 with `0<u<v<1/2`, the complete 202-word cover
reduces to exactly 42 generic completions with
`chi0136=+` and `chi2345=chi4567=-`. In particular, every actual
configuration with `cross(P3,P6)<0` is excluded. Actual zero cap-stem
determinants with a positive generic completion remain in the 42-word
cover.

The first part of the proof excludes completions with all three signs

\[
\chi_{0136}=\chi_{2345}=\chi_{4567}=-.
\tag{1}
\]

The opposite height order is already excluded. The proof retains
every actual zero: (1) supplies only weak signs
for the corresponding actual determinants. The existing complete
202-word cover contains 110 words satisfying (1), split into two
reflected sets of 55.

The second part strengthens the previously proved positive mixed
branch exclusion to cover its actual-zero completions too. Together
these remove 160 of the 202 generic words. Both arguments use the
[endpoint support bound](exhaustive_c0_endpoint_bound.md).

## 1. A complete finite cone split

Let `Cij=cross(Pi,Pj)` and use the usual C0 vectors

\[
\begin{gathered}
E=P_3-P_2,\quad F=P_7-P_6,\quad
\ell_u=1-2u,\quad\ell_v=1-2v,\\
Q_4=P_4-2uP_3-\ell_uP_6,\quad
Q_5=P_5-2vP_3-\ell_vP_6,\quad
S=\ell_vQ_4-\ell_uQ_5.
\end{gathered}
\]

The full generic topology source, positive regular cap units, and
three certified strict turning signs imply that (1) splits into
`chi0356=-` or `chi1346=+`. In the first branch the source gives
the following twelve weak actual signs:

\[
\begin{gathered}
[0134],[0146],[1346]\le0,\qquad [0346]\ge0,\\
[0236]\ge0,\quad [0356]\le0,\quad [1356]\ge0,\\
[0126]\le0,\quad[0234]\ge0,\quad[1246]\le0,\quad[0235]\ge0,\\
[3456]\le0.
\end{gathered}
\tag{2}
\]

The second branch gives their exact marked reflections under
`p(i)=1-i mod8`. The companion exports three CNFs: the exhaustive
two-branch disjunction and the two complete conjunctions of
consequences. Each requires independent RUP replay. A count of
sampled models is not used as a completeness argument.

The marked reflection has positive spatial orientation after the
checked axial and transverse reversals. It sends
`(u,v)` to `(1/2-v,1/2-u)`, preserves `v>u` and `C36`, exchanges
the two cap triangles, and interchanges the mixed brackets `2345`
and `4567`. The companion calls the existing exact cocycle and
coordinate checks. It therefore suffices to exclude the first
branch of (2).

## 2. Nonparallel cap stems

Suppose first that `C36<0`. Write

\[
P_4=a_4P_3+b_4P_6.
\]

The first four signs of (2) and the exact factors

\[
2[0346]=\operatorname{cross}(P_4-2uP_3,P_6),\qquad
2[1346]=-\operatorname{cross}(P_3,P_4-\ell_uP_6)
\]

give `0<=a4<=2u`, `0<=b4<=lu`. Consequently

\[
Q_4=-aP_3-bP_6,\qquad0\le a\le2u,\quad0\le b\le\ell_u.
\tag{3}
\]

The signs of `0356` and `1356` similarly give

\[
Q_5=cP_3+dP_6,\qquad c,d\ge0.
\tag{4}
\]

Both vectors are nonzero because their exact radii are positive.
Put `A=C23>0` and `cE=cross(E,P6)>=0`. In fact `cE>0`:
if it vanished, the facts that `P6` lies below the horizontal axis
and `E` lies above it would make `P6` a negative multiple of `E`.
Then the strict turn `cross(E,F)>0` would contradict
`cross(P6,F)=C67>0`.

The endpoint support theorem supplies

\[
R=\frac{h_2(-C_{36})}{c_E}<D,
\qquad D=d_0+|P_3|+|P_6|.
\tag{5}
\]

It follows that

\[
\operatorname{cross}(E,Q_4)<0.
\tag{6}
\]

To prove the strict sign, suppose instead that `aA-b*cE>=0`.
Then `a>0` and `theta=b*cE/(aA)` lies in `[0,1]`. The exact vector
identity

\[
C_{36}E=c_EP_3+AP_6
\]

rewrites `-Q4` as

\[
a\left((1-\theta)P_3+\theta(C_{36}/c_E)E\right).
\]

Both endpoint norms, `|P3|` and `R`, are strictly below `D`.
Its norm is therefore less than `aD<=2uD`. This contradicts
the exact radius `|Q4|=d4+d5+2uD`. This argument includes
`theta=1` and thus establishes the strict conclusion (6) from a
weak hypothetical antecedent.

Now `[3456]<=0` says `cross(Q4,Q5)>=0`. Equations (3)–(4) and
`C36<0` give

\[
bc\le ad,\qquad bc_E>aA.
\]

The second inequality makes `b>0`; the first and `Q5!=0` then
make `d>0`. The exact identity

\[
b\operatorname{cross}(E,Q_5)
=d(bc_E-aA)+A(ad-bc)>0
\tag{7}
\]

proves `cross(E,Q5)>0`, without dividing by `a` or `c`.
Consequently

\[
\operatorname{cross}(E,S)
=\ell_v\operatorname{cross}(E,Q_4)
 -\ell_u\operatorname{cross}(E,Q_5)<0.
\]

But `2[2345]=-cross(E,S)`, so the actual bracket is strictly
positive. This contradicts its negative generic completion in (1).

## 3. Parallel cap stems

It remains to handle `C36=0` in the same generic branch. The sign
`C26<=0`, together with `C23>0`, forces negative parallelism:

\[
P_3=(L,0),\quad P_6=(-M,0),\quad L,M>0.
\]

Write `P2=(x,y)` with `y<0`. Opposite signs on `0146` and `0346`
force `P4` onto the horizontal axis. The signs `0234>=0` and
`1246<=0` then give

\[
-\ell_uM\le P_{4x}\le2uL,
\qquad -2uL\le Q_{4x}\le\ell_uM.
\]

Since `|Q4|>=2uD>2uL`, the vector `Q4` points strictly to the
right. In particular `cross(E,Q4)<0`.

The sign `0356<=0` gives `Q5_y=P5_y<=0`, while
`cross(Q4,Q5)>=0` gives the reverse inequality. Thus `Q5_y=0`.
The sign `0235>=0` yields `P5_x<=2vL`, hence `Q5_x<=lv*M`.
Its exact radius is

\[
|Q_5|=d_3+d_4+\ell_vD>\ell_vM.
\]

Therefore `Q5` points strictly to the left, so `cross(E,Q5)>0`.
The same strict mixed-bracket contradiction follows. No division
by the vanishing cap-stem determinant has been used.

## 4. Generic positive mixed signs, including actual zeros

The original positive-cone source CNF has the generic antecedent
`chi2345=+`. It therefore supplies its twelve weak consequences even
when the actual bracket vanishes. These include `C36<=0`, the same
closed parallelogram for `P4`, and

\[
[2456]\ge0,\qquad [3456]\le0.
\]

Its exact identity gives

\[
K\operatorname{cross}(E,Q_4)
=\ell_u\operatorname{cross}(Q_4,Q_5)/2
 +\ell_u[2456]+2u[2345]\ge0.
\tag{8}
\]

When `C36<0`, the strict norm argument proving (6) contradicts
this weak conclusion: it already allows `theta=1`, and both endpoint
norms are strictly below `D`. No actual positive bracket is needed.

When `C36=0`, the same source gives `C26<=0` and the horizontal
interval for `Q4` proved in Section 3. Since `Q4!=0`, (8) and
`E_y>0` force `Q4` to point strictly left. Its norm is then at most
`2uL<2uD`, contrary to its exact radius. Thus every generic-positive
`2345` completion is excluded, including actual zero. The checked
reflection gives the identical conclusion for generic-positive
`4567`. The companion exports both generic implications explicitly.

## 5. Exact remaining cover

After Sections 2–4, every compatible generic completion has

\[
\chi_{0136}=+,\qquad\chi_{2345}=\chi_{4567}=-.
\]

The companion enumerates these 42 words and emits a completeness
CNF consisting of the full necessary source, these three units,
and one exact blocking clause for each listed word. Independent
RUP replay proves completeness. The JSON stores the same sorted
70-sign words used to create the blocks; no projected sign pattern
replaces a complete generic word.

## Reproduction and scope

```sh
python research/type7_completion/solver_remaining_c0_opposite_cones.py /tmp/c0-opposite-cones
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-opposite-cones-rup \
  --checker /tmp/type7-rup-check /tmp/c0-opposite-cones
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-opposite-cones-rup \
  --checker /tmp/type7-rup-check --replay-only
```

All six exported CNFs require independent replay. The proof combines
the independently replayed generic implications
with exact determinant identities and the analytic endpoint bound.
Every conclusion from a generic sign remains weak until the metric
argument establishes a strict sign. Degenerate caps, height endpoints,
and the remaining 42 generic completions are separate cases.
