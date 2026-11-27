module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The change of triangle angles under vertex-based variations of squared
edge lengths, and the positive quadratic form obtained by summing the three
angle variations. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus

/-- The dot product recovered from two squared sides and the opposite squared side. -/
def metricDot (a b c : ℝ) : ℝ := (a+b-c)/2

/-- The squared area of the parallelogram on the two incident sides. -/
def metricGram (a b c : ℝ) : ℝ := a*b-(metricDot a b c)^2

/-- The angle between the sides with squared lengths `a` and `b`. -/
def squaredLengthAngle (a b c : ℝ) : ℝ :=
  Real.arccos (metricDot a b c/(Real.sqrt a*Real.sqrt b))

theorem angle_eq_squaredLengthAngle {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) :
    InnerProductGeometry.angle u v = squaredLengthAngle (‖u‖^2) (‖v‖^2) (‖u-v‖^2) := by
  unfold InnerProductGeometry.angle squaredLengthAngle metricDot
  rw [Real.sqrt_sq (norm_nonneg u), Real.sqrt_sq (norm_nonneg v), norm_sub_sq_real]
  congr 2
  ring

private theorem metricCos_open {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hg : 0 < metricGram a b c) :
    ‖metricDot a b c/(Real.sqrt a*Real.sqrt b)‖ < 1 := by
  let d := Real.sqrt a*Real.sqrt b
  have hd : 0 < d := mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb)
  have hds : d^2 = a*b := by dsimp [d]; rw [mul_pow,Real.sq_sqrt ha.le,Real.sq_sqrt hb.le]
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hd,div_lt_one hd]
  have hs : (metricDot a b c)^2 < d^2 := by
    rw [hds]
    exact sub_pos.mp hg
  exact (sq_lt_sq₀ (abs_nonneg _) hd.le).mp (by rw [sq_abs]; exact hs)

theorem contDiffAt_squaredLengthAngle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c : E → ℝ} {p : E} (ha : ContDiffAt ℝ 1 a p) (hb : ContDiffAt ℝ 1 b p)
    (hc : ContDiffAt ℝ 1 c p) (ha₀ : 0 < a p) (hb₀ : 0 < b p)
    (hg : 0 < metricGram (a p) (b p) (c p)) :
    ContDiffAt ℝ 1 (fun q => squaredLengthAngle (a q) (b q) (c q)) p := by
  let T q := metricDot (a q) (b q) (c q) / (Real.sqrt (a q)*Real.sqrt (b q))
  have htop : ContDiffAt ℝ 1 (fun q => metricDot (a q) (b q) (c q)) p :=
    ((ha.add hb).sub hc).div_const 2
  have hbot : ContDiffAt ℝ 1 (fun q => Real.sqrt (a q)*Real.sqrt (b q)) p :=
    ((Real.contDiffAt_sqrt ha₀.ne').comp p ha).mul ((Real.contDiffAt_sqrt hb₀.ne').comp p hb)
  have hT : ContDiffAt ℝ 1 T p :=
    htop.div hbot (mul_pos (Real.sqrt_pos.mpr ha₀) (Real.sqrt_pos.mpr hb₀)).ne'
  have hcos : |T p| < 1 := by
    simpa only [T,Real.norm_eq_abs] using metricCos_open ha₀ hb₀ hg
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hcos
  exact (Real.contDiffAt_arccos hlo.ne' hhi.ne).comp p hT

/-- Under the infinitesimal scaling `a'=(u+v)*a`, `b'=(u+w)*b`,
`c'=(v+w)*c`, this is the derivative of the angle at the vertex of weight `u`. -/
def conformalAngleVelocity (a b c u v w : ℝ) : ℝ :=
  ((b-metricDot a b c)*(v-u)+(a-metricDot a b c)*(w-u))/(2*Real.sqrt (metricGram a b c))

theorem hasDerivAt_squaredLengthAngle_conformal {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hg : 0 < metricGram a b c) (u v w : ℝ) :
    HasDerivAt (fun t : ℝ => squaredLengthAngle
      (a+t*((u+v)*a)) (b+t*((u+w)*b)) (c+t*((v+w)*c)))
      (conformalAngleVelocity a b c u v w) 0 := by
  let A (t : ℝ) := a+t*((u+v)*a)
  let B (t : ℝ) := b+t*((u+w)*b)
  let C (t : ℝ) := c+t*((v+w)*c)
  let d := Real.sqrt a*Real.sqrt b
  let s := metricDot a b c
  let e := s/d
  have ha' : HasDerivAt A ((u+v)*a) 0 := by
    simpa only [A,id_eq,one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const ((u+v)*a)).const_add a)
  have hb' : HasDerivAt B ((u+w)*b) 0 := by
    simpa only [B,id_eq,one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const ((u+w)*b)).const_add b)
  have hc' : HasDerivAt C ((v+w)*c) 0 := by
    simpa only [C,id_eq,one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const ((v+w)*c)).const_add c)
  have ha₀ : A 0 = a := by simp [A]
  have hb₀ : B 0 = b := by simp [B]
  have hc₀ : C 0 = c := by simp [C]
  have hsA : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsB : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hd : 0 < d := mul_pos hsA hsB
  have hd₂ : d^2 = a*b := by dsimp [d]; rw [mul_pow,Real.sq_sqrt ha.le,Real.sq_sqrt hb.le]
  have hA := (Real.hasDerivAt_sqrt (ha₀.symm ▸ ha.ne')).comp 0 ha'
  have hB := (Real.hasDerivAt_sqrt (hb₀.symm ▸ hb.ne')).comp 0 hb'
  have hD : HasDerivAt (fun t => Real.sqrt (A t)*Real.sqrt (B t))
      ((u+(v+w)/2)*d) 0 := by
    have he := hA.mul hB
    simp only [Function.comp_apply, ha₀, hb₀] at he
    convert he using 1
    · rfl
    · dsimp only [d]
      field_simp [hsA.ne',hsB.ne']
      rw [← Real.sq_sqrt ha.le, ← Real.sq_sqrt hb.le]
      simp only [Real.sqrt_sq hsA.le, Real.sqrt_sq hsB.le]
      ring
  have hS : HasDerivAt (fun t => metricDot (A t) (B t) (C t))
      (((u+v)*a+(u+w)*b-(v+w)*c)/2) 0 :=
    ((ha'.add hb').sub hc').div_const 2
  have hD₀ : (fun t => Real.sqrt (A t)*Real.sqrt (B t)) 0 ≠ 0 := by
    simpa only [ha₀,hb₀] using hd.ne'
  let Q (t : ℝ) := metricDot (A t) (B t) (C t)/(Real.sqrt (A t)*Real.sqrt (B t))
  have hcos := hS.div hD hD₀
  change HasDerivAt Q _ 0 at hcos
  simp only [ha₀,hb₀,hc₀] at hcos
  have hunit : |e| < 1 := by simpa only [e,s,d,Real.norm_eq_abs] using metricCos_open ha hb hg
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hunit
  have he₀ : Q 0 = e := by simp only [Q,ha₀,hb₀,hc₀,e,s,d]
  have hsine : Real.sqrt (1-e^2) = Real.sqrt (metricGram a b c)/d := by
    have hArg : 1-e^2 = metricGram a b c/d^2 := by
      dsimp only [e,s,metricGram]
      field_simp [hd.ne']
      linarith only [hd₂]
    rw [hArg,Real.sqrt_div hg.le,Real.sqrt_sq hd.le]
  have hlo' : Q 0 ≠ -1 := he₀.symm ▸ hlo.ne'
  have hhi' : Q 0 ≠ 1 := he₀.symm ▸ hhi.ne
  have hangle := (Real.hasDerivAt_arccos hlo' hhi').comp 0 hcos
  simp only [he₀,hsine] at hangle
  convert hangle using 1
  · rfl
  · change conformalAngleVelocity a b c u v w =
      -(1/(Real.sqrt (metricGram a b c)/d)) *
        ((((u+v)*a+(u+w)*b-(v+w)*c)/2*d-s*((u+(v+w)/2)*d))/d^2)
    unfold conformalAngleVelocity
    field_simp [hd.ne',(Real.sqrt_pos.mpr hg).ne']
    dsimp [s,metricDot]
    ring

/-- The three conformal angle variations of a nondegenerate triangle give a
nonnegative quadratic form, with equality precisely for a common weight. -/
theorem conformalAngle_energy {a b c : ℝ} (ha : 0 < a) (hg : 0 < metricGram a b c)
    (u v w : ℝ) :
    let E := -(u*conformalAngleVelocity a b c u v w +
      v*conformalAngleVelocity a c b v u w +
      w*conformalAngleVelocity b c a w u v)
    0 ≤ E ∧ (E = 0 ↔ u = v ∧ u = w) := by
  let d := Real.sqrt (metricGram a b c)
  let s := metricDot a b c
  let g := metricGram a b c
  let N := (a*(w-u)-s*(v-u))^2+g*(v-u)^2
  let E := -(u*conformalAngleVelocity a b c u v w +
    v*conformalAngleVelocity a c b v u w +
    w*conformalAngleVelocity b c a w u v)
  have hd : 0 < d := Real.sqrt_pos.mpr hg
  have hg₁ : metricGram a c b = metricGram a b c := by unfold metricGram metricDot; ring
  have hg₂ : metricGram b c a = metricGram a b c := by unfold metricGram metricDot; ring
  have hE : E = N/(a*(2*d)) := by
    simp only [E,conformalAngleVelocity,hg₁,hg₂]
    dsimp only [N,s,g,metricGram,metricDot,d]
    field_simp [ha.ne',hd.ne']
    ring
  change 0 ≤ E ∧ (E = 0 ↔ u=v ∧ u=w)
  rw [hE]
  have hden : 0 < a*(2*d) := by positivity
  have hN : 0 ≤ N := add_nonneg (sq_nonneg _) (mul_nonneg hg.le (sq_nonneg _))
  refine ⟨div_nonneg hN hden.le,?_⟩
  constructor
  · intro h
    have hn := (div_eq_zero_iff.mp h).resolve_right hden.ne'
    have hv₂ : g*(v-u)^2 ≤ 0 := by
      dsimp only [N] at hn
      linarith only [hn,sq_nonneg (a*(w-u)-s*(v-u))]
    have hv : v-u = 0 := by
      by_contra hn'
      exact (not_le_of_gt (mul_pos hg (sq_pos_of_ne_zero hn'))) hv₂
    have hw : w-u = 0 := by
      dsimp only [N] at hn
      simp only [hv,mul_zero,sub_zero,zero_pow (by decide : 2 ≠ 0),add_zero] at hn
      exact (mul_eq_zero.mp (sq_eq_zero_iff.mp hn)).resolve_left ha.ne'
    exact ⟨(sub_eq_zero.mp hv).symm,(sub_eq_zero.mp hw).symm⟩
  · rintro ⟨rfl,rfl⟩
    simp [N]

end OrigamiTorus
