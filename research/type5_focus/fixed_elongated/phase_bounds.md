# Exact phase bounds and a certified feasible relaxation of all 19 branches

**Status: 0/19 localized branches excluded.** The target remains the single sharp-rhombic metric y=10^6, with all nineteen cases (including the former boundary cells). This checkpoint uses the preceding fixed-metric localization and sharp-ray marking classification. It does not add new branches.

## 1. Four-point identity retaining the small terms

For a localized branch write physical intrinsic lifts as
    b_i = y*(a_i/4-a_1/4+q_i)+z_i,
where a_i is the digit label, q_i the integer representative from the preceding generator, and z_i a real correction. For cap vertices a_i is 0 or 2, so z differences in one cap are genuine coherent physical vertical differences, with absolute value <=2*y/1000. Across caps, the gap separation interval gives |z_j-z_i|<=13*y/500. These are conservative initial bounds, not asymptotic assumptions.

Choose any pair i,j in the first cap and k,l in the second cap for which all four cross edges exist. Their vertical displacements are sigma_uv*y/2+z_v-z_u, where sigma_uv=+1 or -1 is determined by the discrete label and cocycle. Write d_uv for actual extrinsic squared distances and X_uv for the known intrinsic horizontal displacement. The exact Euclidean polarization identity is

    (r_j-r_i) dot (r_l-r_k) = (d_il+d_jk-d_ik-d_jl)/2.

Substitute the four edge metric equations. The right-hand side is

    (z_j-z_i)*(z_l-z_k) + y*L(z)/2 + H,

where

    L(z) = sigma_il*(z_l-z_i)+sigma_jk*(z_k-z_j)
          -sigma_ik*(z_k-z_i)-sigma_jl*(z_l-z_j),
    H=(X_il^2+X_jk^2-X_ik^2-X_jl^2)/2.

All cross edges have |X|<1/2, so |H|<=1/4. By contraction along the torus, including for missing edges, the distances between the same-cap endpoints are at most sqrt(1/4+(z_j-z_i)^2) and sqrt(1/4+(z_l-z_k)^2). Indeed choose the coherent vertical lifts and then a horizontal translate of size at most 1/2. Cauchy-Schwarz therefore gives the exact necessary inequality, for any known bounds A>=|z_j-z_i|, B>=|z_l-z_k|,

    |L(z)| <= (2/y)*(sqrt(A^2+1/4)*sqrt(B^2+1/4)+A*B+1/4).

It applies to every actual embedding, including collapsed or almost-collinear cap polygons. It requires neither nonzero tetrahedral determinants nor any orientation archive.

A useful special case is sigma_ik=sigma_jk=-sigma_il=-sigma_jl. Then |L|=2*|z_j-z_i|. Using sqrt(a^2+1/4)<=a+1/2 and the actual absolute differences a,b yields
    (y-2*b-1/2)*a <= (b+1)/2.
Since b<=2000 and y=10^6, the initial bound on a improves to less than 0.001005 physical units. The general algorithm below also handles the other sign arrays.

## 2. Exact propagation across all cap pairs

The row L is integral. For each of 19 cases, enumerate every complete cross rectangle, form its row, and use the above bound. Add current pair difference bounds as rows too. Sort by bound, take an independent basis by rational Gaussian elimination, and express every pair difference in that basis. If row L_j has bound c_j and the target pair difference is sum lambda_j L_j, its bound is sum |lambda_j| c_j. Thus no LP or floating tolerance is used. Both the normalized row identities and the final target row combinations are checked exactly. Also propagate the ordinary triangle inequality for the phase differences. Square-root upper bounds and new bounds are rounded upward to a rational grid of denominator 10^9. Twelve sweeps suffice for the recorded bounds; further sweeps are not a proof obligation.

At y=10^6, all 19 branches have at least one cross-cap pair whose physical vertical separation after subtracting its nominal half-period differs from zero by at most 8.000001. In 16 branches some cross pair has phase difference below 0.0013, and in several branches the bound is approximately 5e-7. Selected same-cap pairs also improve from 2000 to the 1e-6 scale. This is a quantitative sharpening of the existing finite-metric branches, not an additional case decomposition. Other vertices can retain large phase widths. The precise bounds are produced by phase.py. They are necessary constraints, not equalities or uniform lower bounds on determinant magnitudes.

## 3. Exact witnesses for the entire four-point relaxation

For each branch impose:
* the previous linear localization (both centers eliminated);
* every propagated phase bound;
* strict nearest-image inequalities and all sixteen strict oriented intrinsic face areas;
* every cross rectangle Cauchy-Schwarz inequality, using actual same-cap edge lengths if known and the coherent-lift contraction bound otherwise.

This relaxation deliberately omits global Euclidean Gram compatibility, the rank-three condition and embedding tests. It is feasible in **all nineteen branches**. The rational coordinates in phase_witnesses.json (seven x coordinates followed by seven physical z corrections, vertex order 0,2,3,4,5,6,7) verify each inequality directly using Python Fraction. Vertex 1 is zero. They also verify the signed area sum -2*y.

Local libz3 runs with 1000 ms per query returned SAT for 16 rectangle systems and UNKNOWN for 3. At 18000 ms, branch 00022220 returned SAT and the other two timed out. The witnesses for 16 branches were read from rational solver models; the other three were selected by floating SLSQP, rounded to rationals, and then subjected to the same exact checker. All 19 checks passed. No numerical optimizer margin or solver SAT answer is relied on as the certificate. None of these points has been shown to be an extrinsic metric realization or embedding.

**Do not try to prove this relaxation UNSAT.** Any successful exclusion needs an additional condition, notably the full signed Gram metric compatibility or the embedding constraints.

## 4. Stronger metric trials and reproduction

The optional Gram generator retains the above rectangle inequalities and phase bounds, and uses fourteen real variables with physical phase offsets. Add the four principal and two mixed 4x4 Gram determinant equations of the earlier signed-completion proof, and the five positive anchor-tetrahedron determinants. This is still only a necessary relaxation of the embedded problem: it omits the other nonedge and intersection tests from the full generator. In local libz3 trials, the first fourteen Gram queries returned UNKNOWN with a 1200 ms timeout; the five remaining returned UNKNOWN at 3000 ms. No infeasibility certificate or metric witness resulted.

Run from this directory:
    python phase.py
    python phase.py /tmp/type5-phase-rect rect
    python phase.py /tmp/type5-phase-gram gram
    python ../solve.py 1200 /tmp/type5-phase-gram/*.smt2

The phase calculation, rational witness verification, generation and solver trials were executed locally on transcribed face/cocycle data, subsequently checked against the actual repository. The committed version imports the existing branch generator rather than the transcribed local data, and includes additional explicit row-identity assertions; it has not been replayed from a fresh checkout in this environment. All inherited geometric audit qualifications remain. No new claim about Type 5 universality, and no closure of hexagonal B1.1 or any of the nineteen elongated branches.
