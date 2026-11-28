# Excluding the regular ray-1 C0 diagonal

There is no ray-1 C0 limit with two noncollinear endpoint caps and
equal interior heights `0<u=v<1/2`. This is an asymptotic research
exclusion. The later [height-order proof](remaining_c0_height_order.md)
extends it to the full regular region `0<v<=u<1/2`; the present packet
remains an independent diagonal proof. The other height order,
collinear caps, and height endpoints require separate arguments.

The proof combines the [strict metric turn](exhaustive_c0_turning.md),
a positive projective normalization, and **50 exact polynomial
certificates**. The certificates have 496 nonzero terms in total.
Their replay checks integer coefficient identities with rational
weights; it does not invoke a nonlinear solver or an optimizer.

## 1. The actual strict disjunction

The regular C0 cap proof fixes the positive orientations of triangles
123 and 067. The turning argument proves

\[
[2367]>0,\qquad [0237]>0,\qquad [1267]<0.
\]

When `u=v`, its second comparison also proves

\[
\boxed{[2345]>0\quad\text{or}\quad[4567]>0.}             \tag{1}
\]

This is a statement about the **actual limiting determinants**.
It must be retained as a strict disjunction. Merely filtering generic
completion words by the corresponding positive sign, while allowing
both actual determinants to be zero, loses an essential hypothesis.

The common topological formula, the ten strict cap signs, the three
strict turn signs, and the generic version of (1) have a complete
50-word cover. The companion exports one CNF asserting the source
and excluding all 50 listed words. Its independent RUP replay proves
completeness without trusting the enumeration routine. Each word has
exactly one of the two positive signs in (1), so it produces one actual
strict branch. There are 25 branches of each kind.

## 2. A sign-preserving normalization of the common height

The original spatial levels are

\[
(0,1/2,1/2,1/2,u,u,0,0),\qquad 0<u<1/2,
\]

with transverse coordinates `P0=P1=0`. Set

\[
a=1-2u,\qquad c=2-8u,\qquad d=2u.
\]

Apply the projective map

\[
(P,z)\longmapsto
\left(\frac{P}{cz+d},\frac{az}{cz+d}\right).
\]

It fixes the levels 0 and 1/2 and sends `u` to 1/4. Its denominators
at the three occupied levels are respectively

\[
2u,\qquad 1-2u,\qquad 4u(1-2u),
\]

all strictly positive. The homogeneous matrix has determinant
`ad=2u(1-2u)>0`. Hence every ordered four-point determinant is
multiplied by `ad` divided by the product of its four positive
denominators. All 70 signs, all actual zeros, and every strict
hypothesis are preserved. Also `P0=P1=0` remains true.

The metric equations are used **before** this normalization, to prove
the strict signs and (1). The normalized configuration needs to retain
only those consequences and the topological signs; the proof does not
assert that a projective map preserves edge lengths.

## 3. Exact certificates in fifteen planar cross products

For `2<=i<j<=7`, put

\[
C_{ij}=\operatorname{cross}(P_i,P_j).
\]

There are fifteen such variables. At the normalized levels every
four-point determinant is a linear form in these variables. The
companion checks all 70 formulas directly against coordinate
determinants. It also checks the fifteen identities

\[
C_{ij}C_{kl}-C_{ik}C_{jl}+C_{il}C_{jk}=0
\quad(2\le i<j<k<l\le7).                              \tag{2}
\]

For a fixed generic word, let `Lq` be its signed determinant form,
scaled by a positive rational to primitive integer coefficients.
Compatibility with the actual configuration gives `Lq>=0`, including
every actual zero. Five of these forms are strictly positive:
the two cap anchors `[0123]`, `[0167]` and the three turn determinants
with their stated signs. The branch of (1) supplies a sixth strict
form.

Every frozen certificate has the form

\[
\sum_{i,j}\lambda_{ij}\,\operatorname{prim}(L_iL_j)
+\sum_{r,s}\mu_{rs}\,\operatorname{prim}(L_rL_s)
+\sum_k\nu_k G_k=0.                                  \tag{3}
\]

Here `Gk` are the identities (2), `lambda,mu>=0`, and the indices in
the second sum refer only to the six strict forms. Their coefficients
satisfy `sum(mu)=1`. The primitive scaling in (3) always divides by
a positive integer. Consequently the first sum is nonnegative,
the second is strictly positive, and the third is zero. This is the
required contradiction.

The replay checks all 120 degree-two coefficient positions in each
identity, every coefficient sign, the strict-index restrictions,
and the normalization of the positive strict sum. It also checks
that every source word and every compatible actual branch has exactly
one certificate. The companion's LP routine is optional discovery
code; floating-point output is accepted only after reconstructing and
checking the complete rational identity.

## Reproduction and scope

```sh
python research/type7_completion/exhaustive_c0_diagonal.py /tmp/c0-diagonal
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-diagonal-rup \
  --checker /tmp/type7-rup-check /tmp/c0-diagonal
python research/type7_completion/solver_cnf_certificates.py /tmp/c0-diagonal-rup \
  --checker /tmp/type7-rup-check --replay-only
```

The previously checked C0 cap/orientation and turning packages remain
premises. The new source-coverage CNF must pass independent replay as
well as the polynomial verifier. Optional `--produce` regenerates the
frozen JSON packet from a bounded linear-program search and checks it
before saving it.

Production plus exact replay took 4.198 seconds; replay alone took
0.351 seconds in this shared workspace. These are observed runtimes,
not controlled benchmarks. This closes the entire regular diagonal
limit, rather than only one fixed-height slice, but supplies no
numerical height threshold and no new Lean theorem.
