module

public import OrigamiTorus.Defs
public import OrigamiTorus.Geometry.AngleDerivative
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Final real elimination for the Type 4 and Type 7 horizontal rank argument. -/

@[expose] public section

namespace OrigamiTorus

section

variable {ι : Type*} [Fintype ι]

/-- The inverse chord coefficient of a vertex in a weighted angle differential. -/
noncomputable def inverseChordBalance (z : ι → ℂ) (ε : ι → ι → ℝ) (c : ι → ℝ) (v : ι) : ℂ :=
  ∑ w, (ε v w : ℂ) * (c v - c w) / (z w - z v)

/-- Removing a common nonzero complex scale from the positions preserves
the vanishing of every inverse chord equation. -/
theorem inverseChordBalance_mul_eq_zero_iff (z : ι → ℂ) (ε : ι → ι → ℝ) (c : ι → ℝ)
    (v : ι) (scale : ℂ) (hs : scale ≠ 0) :
    inverseChordBalance (fun w => scale * z w) ε c v = 0 ↔ inverseChordBalance z ε c v = 0 := by
  have he : inverseChordBalance (fun w => scale * z w) ε c v =
      scale⁻¹ * inverseChordBalance z ε c v := by
    unfold inverseChordBalance
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [← mul_sub,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left (inv_ne_zero hs),fun h => by rw [h,mul_zero]⟩

private theorem weightedTurns_eq_balances (z : ι → ℂ) (ε : ι → ι → ℝ)
    (hε : ∀ v w, ε w v = -ε v w) (c : ι → ℝ) (movement : ι → ℂ) :
    (∑ v, (c v : ℂ) * ∑ w, (ε v w : ℂ) * ((movement w - movement v) / (z w - z v))) =
      -(∑ v, movement v * inverseChordBalance z ε c v) := by
  let k (v w : ι) : ℂ := (ε v w : ℂ) / (z w - z v)
  have hsym (v w : ι) : k w v = k v w := by
    dsimp [k]
    rw [hε v w,Complex.ofReal_neg,show z v - z w = -(z w - z v) by ring,neg_div_neg_eq]
  have hswap :
      (∑ v, ∑ w, (c v : ℂ) * k v w * movement w) = ∑ v, ∑ w, (c w : ℂ) * k v w * movement v := by
    rw [Finset.sum_comm]
    simp only [hsym]
  calc
    _ = (∑ v, ∑ w, (c v : ℂ) * k v w * movement w) -
        (∑ v, ∑ w, (c v : ℂ) * k v w * movement v) := by
      simp only [← Finset.sum_sub_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      simp only [k,div_eq_mul_inv]
      ring
    _ = -(∑ v, movement v * inverseChordBalance z ε c v) := by
      rw [hswap,← Finset.sum_sub_distrib,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro v _
      simp only [inverseChordBalance,← Finset.sum_sub_distrib,Finset.mul_sum,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro w _
      simp only [k,div_eq_mul_inv]
      ring

/-- Testing a weighted angle derivative against every planar motion is
equivalent to the complex inverse chord equation at every vertex. -/
theorem weightedTurns_vanish_iff_inverseChordBalance (z : ι → ℂ) (ε : ι → ι → ℝ)
    (hε : ∀ v w, ε w v = -ε v w) (c : ι → ℝ) :
    (∀ movement : ι → ℂ, (∑ v, (c v : ℂ) *
      ∑ w, (ε v w : ℂ) * ((movement w - movement v) / (z w - z v))).im = 0) ↔
      ∀ v, inverseChordBalance z ε c v = 0 := by
  classical
  simp only [weightedTurns_eq_balances z ε hε c,Complex.neg_im,neg_eq_zero]
  constructor
  · intro h v
    have htest (u : ℂ) : (u * inverseChordBalance z ε c v).im = 0 := by
      simpa only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using
        h (fun w => if w = v then u else 0)
    exact Complex.ext (by simpa [Complex.mul_im] using htest Complex.I) (by simpa using htest 1)
  · intro h movement
    simp [h]

end

/-- A left dependence among the planar cone-angle derivatives is equivalent
to the inverse chord equations in the shared Type 4 and Type 7 labeling. -/
theorem planar_cone_angle_left_kernel (z : Vertex → ℂ) (c : Vertex → ℝ)
    (h : ∀ v (f : Triangle × Bool), f ∈ Type7.orientedFaces → ∀ a b,
      cornerRays v f.1 = some (a,b) →
      if f.2 then 0 < ((starRingEnd ℂ) (z a-z v)*(z b-z v)).im
      else ((starRingEnd ℂ) (z a-z v)*(z b-z v)).im < 0) :
    (∀ δ : Vertex → ℂ, (∑ v, c v * deriv (fun t : ℝ =>
      (Type7.orientedFaces.map (fun f => Type4.chartEuclideanCorner (fun j => z j + t • δ j) v f.1)).sum) 0) = 0) ↔
      ∀ v, inverseChordBalance z (fun v w => (negativeBlockCoefficient v w : ℝ)) c v = 0 := by
  let ε (v w : Vertex) : ℝ := planarTurnCoefficient Type7.orientedFaces v w
  have hε (v w : Vertex) : ε w v = -ε v w := by
    dsimp only [ε]
    rw [planarTurnCoefficient_type7_antisymm v w,Int.cast_neg]
  have hd (δ : Vertex → ℂ) (v : Vertex) :=
    (hasDerivAt_planar_cone Type7.orientedFaces z δ v (h v)).deriv
  have him (a : ℝ) (b : ℂ) : a * b.im = ((a : ℂ) * b).im := by simp [Complex.mul_im]
  have hsum (f : Vertex → ℂ) : (∑ v, f v).im = ∑ v, (f v).im := by
    simpa only [Complex.imCLM_apply] using map_sum Complex.imCLM f Finset.univ
  simp_rw [hd,him,← hsum]
  have hb (v : Vertex) : inverseChordBalance z ε c v =
      (-2 : ℂ) * inverseChordBalance z (fun v w => (negativeBlockCoefficient v w : ℝ)) c v := by
    unfold inverseChordBalance
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    simp only [ε,planarTurnCoefficient_type7_eq_negativeBlocks,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,
      Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_ofNat,div_eq_mul_inv]
    ring
  have he := weightedTurns_vanish_iff_inverseChordBalance z ε hε c
  simpa only [ε,rayVariation,Complex.ofReal_intCast,hb,mul_eq_zero,show (-2 : ℂ) ≠ 0 by norm_num,
    false_or] using he

/-- The inverse chord equations describe the actual Type 7 rectangular
family's left angle-derivative kernel. -/
theorem rectangular_cone_angle_left_kernel (w : ℝ) (hw : 1 ≤ w) (c : Vertex → ℝ) :
    let z := Type7.physicalComplex w ∘ Type7.rectangularPoint w
    (∀ δ : Vertex → ℂ, (∑ v, c v * deriv (fun t : ℝ =>
      (Type7.orientedFaces.map (fun f => Type4.chartEuclideanCorner (fun j => z j + t • δ j) v f.1)).sum) 0) = 0) ↔
      ∀ v, inverseChordBalance z (fun v w => (negativeBlockCoefficient v w : ℝ)) c v = 0 := by
  apply planar_cone_angle_left_kernel
  apply planarCornerSigns_of_face_areas Type7.orientedFaces _ w (by linarith)
  exact fun f hf => Type7.rectangular_face_orientation w hw f.1 f.2 hf

/-- The same inverse chord equations apply on both polynomially scaled
trapezoidal charts before the Type 4 flip. -/
theorem trapezoid_cone_angle_left_kernel {second : Bool} {x w : ℝ}
    (hd : Type4.domain second x w) (c : Vertex → ℝ) :
    let p := Type4.polynomialPoints x w (if second then 2/3 else 1/3) (Type4.trapezoidHeight second x) 1
    let z := Type7.physicalComplex w ∘ p
    (∀ δ : Vertex → ℂ, (∑ v, c v * deriv (fun t : ℝ =>
      (Type7.orientedFaces.map (fun f => Type4.chartEuclideanCorner (fun j => z j + t • δ j) v f.1)).sum) 0) = 0) ↔
      ∀ v, inverseChordBalance z (fun v w => (negativeBlockCoefficient v w : ℝ)) c v = 0 := by
  apply planar_cone_angle_left_kernel
  obtain ⟨_,_,hw⟩ := Type4.domain_bounds hd
  apply planarCornerSigns_of_face_areas Type7.orientedFaces _ w hw
  intro f hf
  have hs := Type4.poly_chart_face_signs hd f hf
  cases he : f.2
  · simpa [he,neg_pos] using hs
  · simpa [he] using hs

/-- The radial projection of an inverse chord coefficient expressed through
the difference of squared distances from the center. -/
theorem two_re_chord_quotient (z w center : ℂ) (h : w ≠ z) :
    2 * ((z - center) / (w - z)).re =
      -1 + (Complex.normSq (w - center) - Complex.normSq (z - center)) / Complex.normSq (w - z) := by
  have hn := (Complex.normSq_pos.mpr (sub_ne_zero.mpr h)).ne'
  rw [Complex.div_re]
  field_simp [hn]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

/-- After normalizing the coefficient at vertex 0, the reduced balance equations
force every coefficient to vanish. The geometric derivation of the balances uses
projections of the inverse chord equations at vertices 1, 3, 5 and 6. -/
theorem reduced_balances_force_zero (coefficients : Vertex → ℝ) (D s r L K α β P B C : ℝ)
    (hD : 0 < D) (hs : s < 0) (hL : 0 ≤ L) (hK : 0 < K) (hα : 0 < α)
    (hβ : 0 < β) (hP : 0 < P) (hB : 0 < B) (hC : 0 < C)
    (h0 : coefficients 0 = 0) (h2 : 2*coefficients 2 = coefficients 4)
    (h1 : coefficients 1-coefficients 7 = -(r/s)*(coefficients 3-coefficients 6))
    (h7 : coefficients 6+coefficients 7 = coefficients 4)
    (hcouple : L*coefficients 6+K*(coefficients 3-coefficients 6) = 0)
    (h4 : coefficients 4 = 2*coefficients 6+α*(coefficients 6/D+(coefficients 3-coefficients 6)/s))
    (h5 : coefficients 5 = -(β*coefficients 6)-P*(coefficients 3-coefficients 6)/s)
    (h5' : (1+B+C)*coefficients 5 = coefficients 4+B*coefficients 7+C*coefficients 6) : coefficients = 0 := by
  let u := coefficients 6
  let X := coefficients 3-coefficients 6
  let A := coefficients 4
  let μ := L/((-s)*K)
  have hμ : 0 ≤ μ := div_nonneg hL (mul_nonneg (neg_pos.mpr hs).le hK.le)
  have hXu : X = -(L*u)/K := by
    apply (eq_div_iff hK.ne').mpr
    change L*u+K*X=0 at hcouple
    linarith only [hcouple]
  have hXdiv : X/s = μ*u := by
    rw [hXu]
    dsimp [μ]
    field_simp [hs.ne,hK.ne']
  let a := 2+α*(1/D+μ)
  let b := β+P*μ
  have ha : 2 ≤ a := by
    dsimp [a]
    linarith only [mul_nonneg hα.le (add_nonneg (one_div_nonneg.mpr hD.le) hμ)]
  have hb : 0 < b := add_pos_of_pos_of_nonneg hβ (mul_nonneg hP.le hμ)
  have hAu : A = a*u := by
    change A = 2*u+α*(u/D+X/s) at h4
    rw [h4,hXdiv]
    dsimp [a]
    ring
  have h7u : coefficients 7 = (a-1)*u := by
    change u+coefficients 7=A at h7
    linear_combination h7+hAu
  have h5u : coefficients 5 = -b*u := by
    change coefficients 5 = -(β*u)-P*X/s at h5
    rw [h5,mul_div_assoc,hXdiv]
    dsimp [b]
    ring
  have hq : 0 < (1+B+C)*b+a+B*(a-1)+C := by
    have ha₀ : 0 < a := by linarith
    have ha₁ : 0 < a-1 := by linarith
    positivity
  change (1+B+C)*coefficients 5=A+B*coefficients 7+C*u at h5'
  rw [h5u,hAu,h7u] at h5'
  have heq : ((1+B+C)*b+a+B*(a-1)+C)*u=0 := by linear_combination -h5'
  have hu : u=0 := (mul_eq_zero.mp heq).resolve_left hq.ne'
  have hX : X=0 := by simpa [hu] using hXu
  have hA : coefficients 4=0 := by simpa [A,hu] using hAu
  have h7z : coefficients 7=0 := by simpa [hu] using h7u
  have h5z : coefficients 5=0 := by simpa [hu] using h5u
  have h3z : coefficients 3=0 := by change coefficients 3-u=0 at hX; linarith only [hX,hu]
  have h1z : coefficients 1=0 := by
    change coefficients 1-coefficients 7 = -(r/s)*X at h1
    simpa [h7z,hX] using h1
  have h2z : coefficients 2=0 := by linarith only [h2,hA]
  funext v
  fin_cases v
  · exact h0
  · exact h1z
  · exact h2z
  · exact h3z
  · exact hA
  · exact h5z
  · exact hu
  · exact h7z

end OrigamiTorus
