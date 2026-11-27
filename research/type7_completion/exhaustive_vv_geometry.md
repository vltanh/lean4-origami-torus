# Both V/V cap alignments are geometrically impossible

This strengthens the final V/V step of `exhaustive_cap_shapes.md`: no
metric stress identity is needed for those two exceptional shape classes.
It also applies to an anisotropic blow-up of a common-line cap limit,
where the limiting metric cost is a seminorm and the original Euclidean
strictness argument would be unavailable.

## Statement and coordinates

Use the canonical caps
\(A=(0,1,4,5)\), \(B=(2,3,6,7)\), with their normalized axial coordinates
converging to 0 and 1 respectively.  Their transverse origins satisfy
\(P_0=P_2=0\).  Suppose both transverse caps have nonparallel V arms:

\[
P_0=P_4=0,\quad P_1=a,\quad P_5=p,
\qquad P_3=P_7=c,\quad P_6=c+d.
\]

The exhaustive weak direction-order calculation in
`exhaustive_cap_shapes.py` leaves exactly two alignments:

1. \(c\) is opposite to \(a\), and \(d\) has the direction of \(p\).
2. \(c\) is opposite to \(p\), and \(d\) has the direction of \(a\).

Since \(a,p\) are independent, an invertible transverse linear map sends
them to \((1,0)\) and \((0,1)\).  The remaining positive arm ratios are
arbitrary \(r,s>0\).  Appending the normalized axial coordinate gives

| Vertex | Both alignments | Alignment I | Alignment II |
| --- | --- | --- | --- |
| 0, 4 | \((0,0,0)\) | | |
| 1 | \((1,0,0)\) | | |
| 5 | \((0,1,0)\) | | |
| 2 | \((0,0,1)\) | | |
| 3, 7 | | \((-r,0,1)\) | \((0,-r,1)\) |
| 6 | | \((-r,s,1)\) | \((s,-r,1)\) |

Neither alignment admits a generic sign completion satisfying the
necessary Type 7 embedding and linking formula.

## Exact Boolean check

For each alignment, the verifier computes all 70 four-point determinants
symbolically.  Exactly 37 vanish.  One is
\([1256]=r-s\); its sign is left entirely free.  The other 32 are among

\[
\{1,-1,r,-r,s,-s,rs,-rs\}.
\]

Their signs therefore remain fixed for every pair of positive ratios,
without a finite-ratio or minimum-length assumption.  Appending these
32 sign units to `solver_chambers.base_formula()`, with its global
reflection gauge removed, gives two formulas with 409 variables and
8,410 clauses.  Both are UNSAT.  The independent C++ checker needs only
one search node for each: unit propagation already finds a contradiction.
Every zero determinant, and the sign-changing determinant \([1256]\),
keeps both generic completion signs available.

Reproduce with:

```bash
python research/type7_completion/exhaustive_vv_geometry.py /tmp/type7-vv
c++ -O2 research/orientation_checkpoint/check_unsat.cpp -o /tmp/type7-check
/tmp/type7-check < /tmp/type7-vv/vv_alignment_1.cnf
/tmp/type7-check < /tmp/type7-vv/vv_alignment_2.cnf
```

Both checker outputs must read `UNSAT nodes 1`; a process exit code alone
is not the verification condition.  The generic necessary formula and
the passage from an actual embedding to a sign completion have the same
premises as `geometric_audit.md` and the compiler `solver_chambers.py`.

## Why anisotropic blow-ups retain the conclusion

An invertible linear change of the two transverse coordinates preserves
all nonzero spatial orientation signs up to one common reflection.
Such a change may depend on the sequence and may include division by an
arbitrarily small transverse width.  If the resulting eight transverse
points converge, while normalized axial coordinates still converge to
the two cap levels, every nonzero determinant in the displayed limit
has its eventual sign in the actual configuration.  Select a subsequence
with one generic completion; its 32 fixed signs would satisfy one of
the two contradictory formulas.

This uses only convergence of the transformed coordinates.  It does not
compare the transverse width with \(t=y^{-2}\), impose a rate on in-plane
corrections, or use a positive-definite limiting norm.  Consequently a
common-line degeneration cannot have either of these V/V shapes as a
noncollinear transverse blow-up limit.

The marked symmetry verified in `exhaustive_cap_shapes.py` exchanges
the opposite-collision pairs \((04,37)\) and \((15,26)\), so the second
exceptional labelled shape class is covered as well.

## Complementary vertical-base trapezoid case

There is also a short stress obstruction when a common-line blow-up
produces the aligned trapezoids of `cap_limit.md`, with their common
base direction in the kernel of the limiting physical seminorm
\(h=|X|\).  All four base weights then vanish.  The closure and unit
perimeter of each cap force its two remaining leg weights to equal
\(1/2\).

If the odd edges are bases, both weight vectors are
\((1/2,0,1/2,0)\), and the two nonzero edge vectors in each cap are
opposite.  The mask's even-row/even-column block consists of ones, so

\[
\sum M_{ij}(h_i k_j-e_i\cdot f_j)
=1-(e_0+e_2)\cdot(f_0+f_2)=1.
\]

If the even edges are bases, the corresponding odd-row/odd-column
block is zero, and the same masked sum is zero.  Both contradict the
exact limiting value \(1/2\).  The verifier checks these identities
with an arbitrary symbolic dot product of the two first leg vectors;
their relative direction is immaterial.  This excludes the entire
vertical-base branch without a comparison between transverse width
and \(t\).
