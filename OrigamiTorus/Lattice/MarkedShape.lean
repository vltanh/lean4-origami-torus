module

public import OrigamiTorus.Geometry.AngleInflation
public import OrigamiTorus.Type4.Periods
import Mathlib.Tactic

/-! Local development of the two marked loops using squared edge lengths. -/

@[expose] public section

namespace OrigamiTorus

theorem developedTwo : Nat.AtLeastTwo 2 := ⟨by decide⟩

/-- The horizontal coordinate of a triangle corner in the chart taking its first
two corners to 0 and 1. The arguments are the squared lengths AB, AC, and BC. -/
noncomputable def developedRe (ab ac bc : ℝ) : ℝ :=
  letI : Nat.AtLeastTwo 2 := developedTwo
  (ab+ac-bc)/(2*ab)

/-- The squared height of the third triangle corner in the same chart. -/
noncomputable def developedHeightSq (ab ac bc : ℝ) : ℝ := ac/ab-(developedRe ab ac bc)^2

/-- The third vertex in the chart taking the first two vertices to 0 and 1.
The side tag chooses which half-plane contains that vertex. -/
noncomputable def developedCorner (positive : Bool) (ab ac bc : ℝ) : ℂ :=
  (developedRe ab ac bc : ℂ) +
    ((if positive then 1 else -1) * Real.sqrt (developedHeightSq ab ac bc) : ℝ) * Complex.I

theorem contDiffAt_developedCorner {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} (sign : Bool) {ab ac bc : E → ℝ} {x : E}
    (hab : ContDiffAt ℝ n ab x) (hac : ContDiffAt ℝ n ac x) (hbc : ContDiffAt ℝ n bc x)
    (hn : ab x ≠ 0) (hh : developedHeightSq (ab x) (ac x) (bc x) ≠ 0) :
    ContDiffAt ℝ n (fun q => developedCorner sign (ab q) (ac q) (bc q)) x := by
  have hr : ContDiffAt ℝ n (fun q => developedRe (ab q) (ac q) (bc q)) x :=
    ((hab.add hac).sub hbc).div (contDiffAt_const.mul hab) (mul_ne_zero (by norm_num) hn)
  have hhs : ContDiffAt ℝ n (fun q => developedHeightSq (ab q) (ac q) (bc q)) x :=
    (hac.div hab hn).sub (hr.pow 2)
  have hroot := (Real.contDiffAt_sqrt (n := n) hh).comp x hhs
  have hi := (contDiffAt_const (c := if sign then (1 : ℝ) else -1)).mul hroot
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x hr).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp x hi).mul contDiffAt_const)

/-- The height formula is the square of the imaginary part of the normalized
third corner when the lengths come from a planar triangle. -/
theorem developed_coords_planar (u v : ℂ) (hu : u ≠ 0) :
    let ab := Complex.normSq u
    let ac := Complex.normSq v
    let bc := Complex.normSq (v-u)
    developedRe ab ac bc = (v/u).re ∧ developedHeightSq ab ac bc = (v/u).im^2 := by
  let z := v/u
  have hzu : u*z = v := by rw [mul_comm]; exact div_mul_cancel₀ v hu
  have hsub : u*(z-1) = v-u := by rw [mul_sub,hzu,mul_one]
  have hac : Complex.normSq v = Complex.normSq u * Complex.normSq z := by
    rw [← Complex.normSq_mul,hzu]
  have hbc : Complex.normSq (v-u) = Complex.normSq u * Complex.normSq (z-1) := by
    rw [← Complex.normSq_mul,hsub]
  have hab : Complex.normSq u ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hu)
  change developedRe (Complex.normSq u) (Complex.normSq v) (Complex.normSq (v-u)) = z.re ∧
    developedHeightSq (Complex.normSq u) (Complex.normSq v) (Complex.normSq (v-u)) = z.im^2
  have hre : developedRe (Complex.normSq u) (Complex.normSq v) (Complex.normSq (v-u)) = z.re := by
    rw [developedRe,hac,hbc,Complex.normSq_apply z,Complex.normSq_apply (z-1)]
    simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,sub_zero]
    field_simp [hab]
    ring
  refine ⟨hre,?_⟩
  rw [developedHeightSq,hre,hac,mul_div_cancel_left₀ _ hab,Complex.normSq_apply]
  ring

/-- Exact planar recovery on the selected side of the base edge. -/
theorem developedCorner_planar (sign : Bool) (u v : ℂ) (hu : u ≠ 0)
    (hs : if sign then 0 ≤ (v/u).im else (v/u).im ≤ 0) :
    developedCorner sign (Complex.normSq u) (Complex.normSq v) (Complex.normSq (v-u)) = v/u := by
  obtain ⟨hr,hi⟩ := developed_coords_planar u v hu
  apply Complex.ext
  · simpa [developedCorner] using hr
  · simp only [developedCorner,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add,hi,Real.sqrt_sq_eq_abs]
    cases sign
    · simpa [abs_of_nonpos hs]
    · simpa [abs_of_nonneg hs]

theorem developedCorner_reverse (sign : Bool) (ab ac bc : ℝ) :
    developedCorner (!sign) ab ac bc = (starRingEnd ℂ) (developedCorner sign ab ac bc) := by
  cases sign <;> apply Complex.ext <;> simp [developedCorner]

theorem developedCorner_scale (sign : Bool) (ab ac bc k : ℝ) (hk : k ≠ 0) :
    developedCorner sign (k*ab) (k*ac) (k*bc) = developedCorner sign ab ac bc := by
  have hr : developedRe (k*ab) (k*ac) (k*bc) = developedRe ab ac bc := by
    unfold developedRe
    rw [← mul_add,← mul_sub,mul_left_comm 2,mul_div_mul_left _ _ hk]
  simp only [developedCorner, developedHeightSq, hr, mul_div_mul_left _ _ hk]

namespace Type7

noncomputable def triangleCorner (s : Vertex → Vertex → ℝ) (positive : Bool)
    (a b c : Vertex) : ℂ := developedCorner positive (s a b) (s a c) (s b c)

/-- Develop the six triangles meeting the marked walks. The common root chart
takes vertex 3 to 0 and vertex 5 to 1. The diagonal 35 is the unflipped chart. -/
noncomputable def markingDisplacements (s : Vertex → Vertex → ℝ) : ℂ × ℂ :=
  let z₂ := triangleCorner s false 3 5 2
  let z₆ := triangleCorner s true 3 5 6
  let z₄ := 1+(z₂-1)*triangleCorner s true 5 2 4
  let z₀ := z₂-z₂*triangleCorner s true 2 3 0
  let z₄' := z₆*triangleCorner s true 3 6 4
  let z₀' := z₆+(1-z₆)*triangleCorner s true 6 5 0
  (z₄'-z₄,z₀-z₀')

/-- The local complex ratio of the marked displacements. -/
noncomputable def markedShape (s : Vertex → Vertex → ℝ) : ℂ :=
  let (U,V) := markingDisplacements s
  V/U

def markingTriangles : List Triangle := [(3,5,2),(3,5,6),(5,2,4),(2,3,0),(3,6,4),(6,5,0)]

theorem markedShape_scale (s : Vertex → Vertex → ℝ) (k : ℝ) (hk : k ≠ 0) :
    markedShape (fun a b => k*s a b) = markedShape s := by
  simp only [markedShape,markingDisplacements,triangleCorner,developedCorner_scale _ _ _ _ _ hk]

/-- The marked ratio is smooth whenever the six developed triangles and the
first marked displacement are nondegenerate. -/
theorem contDiffAt_markedShape {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {s : E → Vertex → Vertex → ℝ} {x : E}
    (hs : ∀ a b, ContDiffAt ℝ n (fun u => s u a b) x)
    (htri : ∀ f ∈ markingTriangles,
      s x f.1 f.2.1 ≠ 0 ∧
        developedHeightSq (s x f.1 f.2.1) (s x f.1 f.2.2) (s x f.2.1 f.2.2) ≠ 0)
    (hU : (markingDisplacements (s x)).1 ≠ 0) :
    ContDiffAt ℝ n (fun u => markedShape (s u)) x := by
  have ht (sign : Bool) {a b c : Vertex}
      (hf : (a,b,c) ∈ markingTriangles) :
      ContDiffAt ℝ n (fun u => triangleCorner (s u) sign a b c) x :=
    contDiffAt_developedCorner sign (hs a b) (hs a c) (hs b c) (htri _ hf).1 (htri _ hf).2
  have h2 := ht false (a := 3) (b := 5) (c := 2) (by simp [markingTriangles])
  have h6 := ht true (a := 3) (b := 5) (c := 6) (by simp [markingTriangles])
  have h4 := ht true (a := 5) (b := 2) (c := 4) (by simp [markingTriangles])
  have h0 := ht true (a := 2) (b := 3) (c := 0) (by simp [markingTriangles])
  have h4' := ht true (a := 3) (b := 6) (c := 4) (by simp [markingTriangles])
  have h0' := ht true (a := 6) (b := 5) (c := 0) (by simp [markingTriangles])
  have hfirst : ContDiffAt ℝ n (fun u => (markingDisplacements (s u)).1) x :=
    (h6.mul h4').sub (contDiffAt_const.add ((h2.sub contDiffAt_const).mul h4))
  have hsecond : ContDiffAt ℝ n (fun u => (markingDisplacements (s u)).2) x :=
    (h2.sub (h2.mul h0)).sub (h6.add ((contDiffAt_const.sub h6).mul h0'))
  simpa only [markedShape,div_eq_mul_inv] using hsecond.mul (hfirst.fun_inv hU)

/-- Squared edge lengths in physical complex coordinates. -/
noncomputable def planarEdgeSq (p : Vertex → ℂ) (a b : Vertex) : ℝ :=
  Complex.normSq (p b-p a)

theorem markedShape_planar_smul (p : Vertex → ℂ) {c : ℝ} (hc : c ≠ 0) :
    markedShape (planarEdgeSq (fun i => c • p i)) = markedShape (planarEdgeSq p) := by
  have he : planarEdgeSq (fun i => c • p i) =
      fun a b => Complex.normSq (c : ℂ)*planarEdgeSq p a b := by
    funext a b
    simp only [planarEdgeSq,Complex.real_smul,← mul_sub,Complex.normSq_mul]
  rw [he,markedShape_scale _ _ (Complex.normSq_pos.mpr (Complex.ofReal_ne_zero.mpr hc)).ne']

/-- Squared edge lengths for a spatial placement. -/
def spatialEdgeSq (q : Vertex → Point3) (a b : Vertex) : ℝ :=
  Type5.squared3 (q b-q a)

theorem spatialEdgeSq_angleLift_zero (p : Vertex → ℂ) (h : Vertex → ℝ) :
    spatialEdgeSq (angleLift p h 0) = planarEdgeSq p := by
  funext a b
  simp [spatialEdgeSq,angleLift,planarEdgeSq,Type5.squared3,Type5.squared2,Type5.horizontal,
    Type5.dot,Complex.normSq_apply]

theorem triangleCorner_planar (p : Vertex → ℂ) (sign : Bool) (a b c : Vertex)
    (hab : p b-p a ≠ 0)
    (h : if sign then 0 ≤ ((p c-p a)/(p b-p a)).im else ((p c-p a)/(p b-p a)).im ≤ 0) :
    triangleCorner (planarEdgeSq p) sign a b c = (p c-p a)/(p b-p a) := by
  have he : p c-p a-(p b-p a) = p c-p b := by ring
  unfold triangleCorner planarEdgeSq
  rw [← he]
  exact developedCorner_planar sign _ _ hab h

theorem triangleCorner_planar_reflected (p : Vertex → ℂ) (a b c : Vertex)
    (hab : p b-p a ≠ 0) (h : ((p c-p a)/(p b-p a)).im ≤ 0) :
    triangleCorner (planarEdgeSq p) true a b c = (starRingEnd ℂ) ((p c-p a)/(p b-p a)) := by
  change developedCorner (!false) _ _ _ = _
  rw [developedCorner_reverse]
  exact congrArg (starRingEnd ℂ) (triangleCorner_planar p false a b c hab h)

/-- Reflection of a complex direction across the line parallel to the first argument. -/
noncomputable def reflectComplex (axis direction : ℂ) : ℂ :=
  axis * (starRingEnd ℂ) (direction/axis)

/-- The two local loop displacements on a planar folded base are exactly its
reflection formulas, expressed in the common chart with edge 35 of length one. -/
theorem markingDisplacements_planar (p : Vertex → ℂ)
    (h35 : p 5-p 3 ≠ 0) (h52 : p 2-p 5 ≠ 0) (h23 : p 3-p 2 ≠ 0)
    (h36 : p 6-p 3 ≠ 0) (h65 : p 5-p 6 ≠ 0)
    (h2 : ((p 2-p 3)/(p 5-p 3)).im ≤ 0)
    (h6 : 0 ≤ ((p 6-p 3)/(p 5-p 3)).im)
    (h4 : 0 ≤ ((p 4-p 5)/(p 2-p 5)).im)
    (h0 : 0 ≤ ((p 0-p 2)/(p 3-p 2)).im)
    (h4' : ((p 4-p 3)/(p 6-p 3)).im ≤ 0)
    (h0' : ((p 0-p 6)/(p 5-p 6)).im ≤ 0) :
    let U := p 3-p 4+reflectComplex (p 6-p 3) (p 4-p 3)
    let V := p 0-p 5+reflectComplex (p 5-p 6) (p 5-p 0)
    markingDisplacements (planarEdgeSq p) = (U/(p 5-p 3),V/(p 5-p 3)) := by
  simp only [markingDisplacements, triangleCorner_planar p false 3 5 2 h35 h2,
    triangleCorner_planar p true 3 5 6 h35 h6,triangleCorner_planar p true 5 2 4 h52 h4,
    triangleCorner_planar p true 2 3 0 h23 h0]
  rw [triangleCorner_planar_reflected p 3 6 4 h36 h4',triangleCorner_planar_reflected p 6 5 0 h65 h0']
  let d := p 5-p 3
  have hA : 1+((p 2-p 3)/d-1)*((p 4-p 5)/(p 2-p 5)) = (p 4-p 3)/d := by
    dsimp only [d]
    field_simp [h35,h52]
    ring
  have hB : (p 2-p 3)/d-(p 2-p 3)/d*((p 0-p 2)/(p 3-p 2)) = (p 0-p 3)/d := by
    dsimp only [d]
    field_simp [h35,h23]
    ring
  have hC : 1-(p 6-p 3)/d = (p 5-p 6)/d := by
    dsimp only [d]
    field_simp [h35]
    ring
  have hD : (p 0-p 6)/(p 5-p 6) = 1-(p 5-p 0)/(p 5-p 6) := by
    field_simp [h65]
    ring
  rw [hA,hB,hC,hD,map_sub,map_one]
  apply Prod.ext <;> dsimp only [reflectComplex,d] <;> ring

private theorem physical_normSq (w : ℝ) (hw : 0 ≤ w) (a : ℝ × ℝ) :
    Complex.normSq (physicalComplex w a) = weightedSquare w a := by
  simp only [physicalComplex,Complex.normSq_apply,weightedSquare,weightedDot]
  rw [show Real.sqrt w*a.2*(Real.sqrt w*a.2) = w*a.2*a.2 by
    calc
      _ = (Real.sqrt w)^2*(a.2*a.2) := by ring
      _ = _ := by rw [Real.sq_sqrt hw]; ring]

private theorem physical_dot (w : ℝ) (hw : 0 ≤ w) (a b : ℝ × ℝ) :
    (physicalComplex w a).re*(physicalComplex w b).re+
      (physicalComplex w a).im*(physicalComplex w b).im = weightedDot w a b := by
  simp only [physicalComplex,weightedDot]
  rw [show Real.sqrt w*a.2*(Real.sqrt w*b.2) = w*a.2*b.2 by
    calc
      _ = (Real.sqrt w)^2*(a.2*b.2) := by ring
      _ = _ := by rw [Real.sq_sqrt hw]; ring]

private theorem physical_sub (w : ℝ) (a b : ℝ × ℝ) :
    physicalComplex w (a-b) = physicalComplex w a-physicalComplex w b := by
  apply Complex.ext <;> simp [physicalComplex,mul_sub]

private theorem physical_add (w : ℝ) (a b : ℝ × ℝ) :
    physicalComplex w (a+b) = physicalComplex w a+physicalComplex w b := by
  apply Complex.ext <;> simp [physicalComplex,mul_add]

private theorem reflectComplex_formula (a b : ℂ) (ha : Complex.normSq a ≠ 0) :
    reflectComplex a b = ((2*(a.re*b.re+a.im*b.im)/Complex.normSq a : ℝ) : ℂ)*a-b := by
  apply Complex.ext <;>
    simp only [reflectComplex,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,
      add_zero,Complex.div_re,Complex.div_im] <;>
    field_simp [ha] <;> simp only [Complex.normSq_apply] <;> ring

theorem reflectComplex_physical (w : ℝ) (hw : 0 ≤ w) (a b : ℝ × ℝ)
    (ha : weightedSquare w a ≠ 0) :
    reflectComplex (physicalComplex w a) (physicalComplex w b) =
      physicalComplex w (reflectDirection w a b) := by
  rw [reflectComplex_formula _ _ (by rwa [physical_normSq w hw]),physical_normSq w hw,
    physical_dot w hw,reflectDirection,physical_sub]
  apply Complex.ext <;> simp [physicalComplex,Type5.smul2] <;> ring

theorem physical_period_ratio (w x : ℝ) (hw : 0 ≤ w) (a b : ℝ × ℝ)
    (ha : 0 < weightedSquare w a)
    (hx : weightedDot w a b = x*weightedSquare w a)
    (hy : Type5.cross a b = weightedSquare w a) :
    physicalComplex w b/physicalComplex w a = ⟨x,Real.sqrt w⟩ := by
  have hcross : (physicalComplex w b).im*(physicalComplex w a).re -
      (physicalComplex w b).re*(physicalComplex w a).im = Real.sqrt w*Type5.cross a b := by
    simp only [physicalComplex,Type5.cross]
    ring
  apply Complex.ext
  · rw [Complex.div_re,← add_div]
    rw [mul_comm (physicalComplex w b).re,mul_comm (physicalComplex w b).im,
      physical_dot w hw,physical_normSq w hw,hx,mul_div_cancel_right₀ _ ha.ne']
  · rw [Complex.div_im,← sub_div,hcross,physical_normSq w hw,hy,mul_div_cancel_right₀ _ ha.ne']

private theorem normalizedCorner_im (p : Vertex → ℝ × ℝ) (w : ℝ) (a b c : Vertex) :
    let z := physicalComplex w ∘ p
    ((z c-z a)/(z b-z a)).im =
      Real.sqrt w*area p a b c/Complex.normSq (z b-z a) := by
  dsimp only
  rw [Complex.div_im,← sub_div]
  congr 1
  simp only [Function.comp_apply,Complex.sub_re,Complex.sub_im,physicalComplex,area]
  ring

theorem normalizedCorner_sign (p : Vertex → ℝ × ℝ) (w : ℝ) (hw : 0 < w)
    (a b c : Vertex) (positive : Bool)
    (hs : 0 < if positive then area p a b c else -area p a b c) :
    let z := physicalComplex w ∘ p
    z b-z a ≠ 0 ∧
      0 < if positive then ((z c-z a)/(z b-z a)).im else -((z c-z a)/(z b-z a)).im := by
  let z := physicalComplex w ∘ p
  have hab : z b-z a ≠ 0 := by
    intro he
    have h := sub_eq_zero.mp he
    have h₁ : (p b).1 = (p a).1 := congrArg Complex.re h
    have h₂ := mul_left_cancel₀ (Real.sqrt_pos.mpr hw).ne'
      (show Real.sqrt w*(p b).2 = Real.sqrt w*(p a).2 from congrArg Complex.im h)
    have hba := Prod.ext h₁ h₂
    have hz : area p a b c = 0 := by
      simp only [area,hba]
      ring
    simp [hz] at hs
  refine ⟨hab,?_⟩
  have hn := Complex.normSq_pos.mpr hab
  change 0 < if positive then ((z c-z a)/(z b-z a)).im else -((z c-z a)/(z b-z a)).im
  rw [normalizedCorner_im p w a b c]
  cases positive
  · simp only [Bool.false_eq_true,ite_false,← neg_div,← mul_neg]
    exact div_pos (mul_pos (Real.sqrt_pos.mpr hw) hs) hn
  · exact div_pos (mul_pos (Real.sqrt_pos.mpr hw) hs) hn

/-- The two marked displacements from a scaled planar chart. -/
theorem markingDisplacements_scaled_planar (p : Vertex → ℝ × ℝ) (w : ℝ) (hw : 0 < w)
    (hs : ∀ f ∈ orientedFaces, 0 <
      if f.2 then area p f.1.1 f.1.2.1 f.1.2.2 else -area p f.1.1 f.1.2.1 f.1.2.2) :
    let z := physicalComplex w ∘ p
    let d := z 5-z 3
    let U := p 3-p 4+reflectDirection w (p 6-p 3) (p 4-p 3)
    let V := p 0-p 5+reflectDirection w (p 5-p 6) (p 5-p 0)
    markingDisplacements (planarEdgeSq z) = (physicalComplex w U/d,physicalComplex w V/d) := by
  let z := physicalComplex w ∘ p
  have hswap (a b c : Vertex) : area p a c b = -area p a b c := by unfold area; ring
  have hcycle (a b c : Vertex) : area p c a b = area p a b c := by unfold area; ring
  obtain ⟨h35,h2⟩ := normalizedCorner_sign p w hw 3 5 2 false (by
    change 0 < -area p 3 5 2
    rw [hswap]
    simpa using hs ((3,2,5),true) (by decide +kernel))
  obtain ⟨_,h6⟩ := normalizedCorner_sign p w hw 3 5 6 true (hs ((3,5,6),true) (by decide +kernel))
  obtain ⟨h52,h4⟩ := normalizedCorner_sign p w hw 5 2 4 true (hs ((5,2,4),true) (by decide +kernel))
  obtain ⟨h23,h0⟩ := normalizedCorner_sign p w hw 2 3 0 true (by
    change 0 < area p 2 3 0
    rw [hcycle]
    exact hs ((3,0,2),true) (by decide +kernel))
  obtain ⟨h36,h4'⟩ := normalizedCorner_sign p w hw 3 6 4 false (hs ((3,6,4),false) (by decide +kernel))
  obtain ⟨h65,h0'⟩ := normalizedCorner_sign p w hw 6 5 0 false (by
    change 0 < -area p 6 5 0
    rw [hcycle]
    exact hs ((5,0,6),false) (by decide +kernel))
  have hf := markingDisplacements_planar z h35 h52 h23 h36 h65 (neg_pos.mp h2).le h6.le
    h4.le h0.le (neg_pos.mp h4').le (neg_pos.mp h0').le
  have hd (a b : Vertex) : z a-z b = physicalComplex w (p a-p b) := (physical_sub w _ _).symm
  have hnorm (a b : Vertex) (hn : z a-z b ≠ 0) : weightedSquare w (p a-p b) ≠ 0 := by
    rw [← physical_normSq w hw.le,← hd]
    exact (Complex.normSq_pos.mpr hn).ne'
  dsimp only at hf ⊢
  rw [hf,physical_add,physical_add,hd 3 4,hd 6 3,hd 4 3,hd 0 5,hd 5 6,hd 5 0,
    reflectComplex_physical w hw.le _ _ (hnorm 6 3 h36),
    reflectComplex_physical w hw.le _ _ (hnorm 5 6 h65)]

private theorem markingTriangle_areas (p : Vertex → ℝ × ℝ)
    (hs : ∀ f ∈ orientedFaces, 0 <
      if f.2 then area p f.1.1 f.1.2.1 f.1.2.2 else -area p f.1.1 f.1.2.1 f.1.2.2) :
    ∀ f ∈ markingTriangles, area p f.1 f.2.1 f.2.2 ≠ 0 := by
  have h (a b c : Vertex) (s : Bool) (hm : ((a,b,c),s) ∈ orientedFaces) :
      area p a b c ≠ 0 := by
    have hp := hs ((a,b,c),s) hm
    intro he
    simp [he] at hp
  have hswap (a b c : Vertex) : area p a c b = -area p a b c := by unfold area; ring
  have hcycle (a b c : Vertex) : area p c a b = area p a b c := by unfold area; ring
  intro f hf
  simp only [markingTriangles,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl
  · change area p 3 5 2 ≠ 0
    rw [hswap]
    exact neg_ne_zero.mpr (h 3 2 5 true (by decide +kernel))
  · exact h 3 5 6 true (by decide +kernel)
  · exact h 5 2 4 true (by decide +kernel)
  · change area p 2 3 0 ≠ 0
    rw [hcycle]
    exact h 3 0 2 true (by decide +kernel)
  · exact h 3 6 4 false (by decide +kernel)
  · change area p 6 5 0 ≠ 0
    rw [hcycle]
    exact h 5 0 6 false (by decide +kernel)

theorem markingTriangles_regular_planar (p : Vertex → ℝ × ℝ) (w : ℝ) (hw : 0 < w)
    (hs : ∀ f ∈ orientedFaces, 0 <
      if f.2 then area p f.1.1 f.1.2.1 f.1.2.2 else -area p f.1.1 f.1.2.1 f.1.2.2) :
    let s := planarEdgeSq (physicalComplex w ∘ p)
    ∀ f ∈ markingTriangles, s f.1 f.2.1 ≠ 0 ∧
      developedHeightSq (s f.1 f.2.1) (s f.1 f.2.2) (s f.2.1 f.2.2) ≠ 0 := by
  let z := physicalComplex w ∘ p
  dsimp only
  rintro ⟨a,b,c⟩ hf
  have harea := markingTriangle_areas p hs (a,b,c) hf
  change area p a b c ≠ 0 at harea
  have hcorner : z b-z a ≠ 0 ∧ ((z c-z a)/(z b-z a)).im ≠ 0 := by
    rcases lt_or_gt_of_ne harea with hn|hp
    · obtain ⟨h₁,h₂⟩ := normalizedCorner_sign p w hw a b c false (neg_pos.mpr hn)
      exact ⟨h₁,(neg_pos.mp h₂).ne⟩
    · obtain ⟨h₁,h₂⟩ := normalizedCorner_sign p w hw a b c true hp
      exact ⟨h₁,h₂.ne'⟩
  have he : z c-z a-(z b-z a) = z c-z b := by ring
  change Complex.normSq (z b-z a) ≠ 0 ∧ developedHeightSq (Complex.normSq (z b-z a))
    (Complex.normSq (z c-z a)) (Complex.normSq (z c-z b)) ≠ 0
  rw [← he,(developed_coords_planar (z b-z a) (z c-z a) hcorner.1).2]
  exact ⟨(Complex.normSq_pos.mpr hcorner.1).ne',pow_ne_zero _ hcorner.2⟩

end Type7

namespace Type4

open Type5 (smul2)
open Type7

/-- The local shape function agrees with the prescribed modulus on both charts
before the flip. -/
theorem trapezoid_markedShape {nearEndpoint : Bool} {x w : ℝ} (hd : domain nearEndpoint x w) :
    let p := polynomialPoints x w (if nearEndpoint then 2/3 else 1/3) (trapezoidHeight nearEndpoint x) 1
    markedShape (planarEdgeSq (physicalComplex w ∘ p)) = ⟨x,Real.sqrt w⟩ := by
  let H := trapezoidHeight nearEndpoint x
  let c : ℝ := if nearEndpoint then 2/3 else 1/3
  let p := polynomialPoints x w c H 1
  let z := physicalComplex w ∘ p
  let D := H-1+H*x
  let R : ℝ × ℝ := (D,H)
  let N : ℝ × ℝ := (-w*H,D)
  let E := smul2 x R+N
  let S := ( (H*x)^2-H*x-(1-c)*H^2*w-D*(2*(H*x)-c*D-1))/(1-c)
  obtain ⟨hx,_,hw⟩ := domain_bounds hd
  have hH : 1 < H := height_gt_one hd
  have hHpos : 0 < H := by linarith
  have hD : 0 < D := add_pos_of_pos_of_nonneg (sub_pos.mpr hH) (mul_nonneg hHpos.le hx)
  have hc : 1-c ≠ 0 := by cases nearEndpoint <;> norm_num [c]
  have hs := poly_chart_face_signs hd
  have h35 := (normalizedCorner_sign p w hw 3 5 6 true (hs ((3,5,6),true) (by decide +kernel))).1
  have h36 := (normalizedCorner_sign p w hw 3 6 4 false (hs ((3,6,4),false) (by decide +kernel))).1
  have hr : 0 < weightedSquare w R := by
    change 0 < D*D+w*H*H
    positivity
  have hE₂ : 0 < E.2 := add_pos_of_nonneg_of_pos (mul_nonneg hx hHpos.le) hD
  have he : 0 < weightedSquare w E := by
    simp only [weightedSquare,weightedDot]
    exact add_pos_of_nonneg_of_pos (mul_self_nonneg _) (mul_pos (mul_pos hw hE₂) hE₂)
  have haxes : p 3-p 6 = smul2 S R ∧ p 5-p 6 = smul2 (-H^2) E := trapezoid_crease_axes x w c H
  have haxis : p 6-p 3 = smul2 (-S) R := by
    rw [← neg_sub, haxes.1]
    apply Prod.ext <;> simp [smul2]
  have hSne : -S ≠ 0 := by
    intro h
    have hzero : p 6-p 3 = 0 := by rw [haxis,h]; simp [smul2]
    apply h36
    change physicalComplex w (p 6)-physicalComplex w (p 3) = 0
    rw [← physical_sub,hzero]
    apply Complex.ext <;> simp [physicalComplex]
  have hperiods := markingDisplacements_scaled_planar p w hw hs
  dsimp only at hperiods
  rw [haxis,haxes.2,reflectDirection_scale w _ _ _ hSne hr.ne',
    reflectDirection_scale w _ _ _ (neg_ne_zero.mpr (pow_ne_zero _ hHpos.ne')) he.ne'] at hperiods
  let P := trapezoidMarkingPeriods x w c H
  have hU : P.1 = p 3-p 4+reflectDirection w R (p 4-p 3) := by
    unfold P trapezoidMarkingPeriods
    change p 2-p 4+(p 3-p 2)+_ = _
    abel
  have hV : P.2 = p 0-p 5+reflectDirection w E (p 5-p 0) := by
    unfold P trapezoidMarkingPeriods
    change p 2-p 5+(p 0-p 2)+_ = _
    abel
  rw [← hU,← hV] at hperiods
  change markedShape (planarEdgeSq z) = _
  unfold markedShape
  rw [hperiods]
  dsimp only
  rw [div_div_div_cancel_right₀ h35]
  obtain ⟨hpos,hreal,himag⟩ := trapezoid_period_ratios x w c H hx hw hH hc
  exact physical_period_ratio w x hw.le P.1 P.2 hpos hreal himag

end Type4

namespace Type7

/-- The first trapezoidal chart specializes to the rectangular one up to its
constant common scale. -/
theorem trapezoid_at_rectangle (w : ℝ) (v : Vertex) :
    Type4.polynomialPoints 0 w (1/3) (Type4.trapezoidHeight false 0) 1 v =
      (13/20 : ℝ)^2 • rectangularPoint w v := by
  fin_cases v <;> apply Prod.ext <;>
    norm_num [Type4.polynomialPoints,Type4.trapezoidHeight,rectangularPoint] <;> ring

theorem rectangular_markedShape (w : ℝ) (hw : 1 ≤ w) :
    markedShape (planarEdgeSq (physicalComplex w ∘ rectangularPoint w)) = ⟨0,Real.sqrt w⟩ := by
  have hd : Type4.domain false 0 w := by
    exact ⟨le_rfl,by norm_num,by simpa using hw⟩
  have h := Type4.trapezoid_markedShape hd
  let c : ℝ := (13/20)^2
  let u : ℂ := c
  have hp (v : Vertex) :
      physicalComplex w (Type4.polynomialPoints 0 w (1/3) (Type4.trapezoidHeight false 0) 1 v) =
        u*physicalComplex w (rectangularPoint w v) := by
    rw [trapezoid_at_rectangle]
    change physicalComplex w (c • rectangularPoint w v) = u*_
    rw [show c • rectangularPoint w v = (c*(rectangularPoint w v).1,c*(rectangularPoint w v).2) from rfl]
    apply Complex.ext <;>
      simp only [u,physicalComplex,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,zero_mul,sub_zero,zero_add] <;> ring
  have hs : planarEdgeSq (physicalComplex w ∘
      Type4.polynomialPoints 0 w (1/3) (Type4.trapezoidHeight false 0) 1) =
      fun a b => Complex.normSq u * planarEdgeSq (physicalComplex w ∘ rectangularPoint w) a b := by
    funext a b
    simp only [planarEdgeSq,Function.comp_apply,hp,← mul_sub,Complex.normSq_mul]
  have hu : Complex.normSq u ≠ 0 := by
    exact (Complex.normSq_pos.mpr (Complex.ofReal_ne_zero.mpr (by norm_num [c]))).ne'
  change markedShape (planarEdgeSq (physicalComplex w ∘
    Type4.polynomialPoints 0 w (1/3) (Type4.trapezoidHeight false 0) 1)) = _ at h
  rwa [hs,markedShape_scale _ _ hu] at h

/-- The shape coordinates extend smoothly to spatial lifts near the
rectangular planar base. -/
theorem contDiffAt_rectangular_spatial_markedShape (w : ℝ) (hw : 1 ≤ w) (h : Vertex → ℝ) :
    let z := physicalComplex w ∘ rectangularPoint w
    ContDiffAt ℝ 1 (fun x : ℝ × (Vertex → ℂ) => markedShape (spatialEdgeSq (angleLift x.2 h x.1))) (0,z) := by
  let z := physicalComplex w ∘ rectangularPoint w
  let s (x : ℝ × (Vertex → ℂ)) := spatialEdgeSq (angleLift x.2 h x.1)
  have hs : s (0,z) = planarEdgeSq z := spatialEdgeSq_angleLift_zero z h
  have hsd (a b : Vertex) : ContDiffAt ℝ 1 (fun x => s x a b) (0,z) := by
    have hsq : ContDiff ℝ 1 (Type5.squared3 : Point3 → ℝ) := by
      unfold Type5.squared3 Type5.squared2 Type5.horizontal Type5.dot
      fun_prop
    have hf := contDiff_pi.mp (contDiff_angleLift h)
    exact (hsq.comp ((hf b).sub (hf a))).contDiffAt
  have htri := markingTriangles_regular_planar (rectangularPoint w) w (by linarith) (by
    intro f hf
    have hsign := rectangular_face_orientation w hw f.1 f.2 hf
    cases hh : f.2
    · simpa only [hh,Bool.false_eq_true,ite_false,neg_pos] using hsign
    · simpa only [hh,ite_true] using hsign)
  have hU : (markingDisplacements (s (0,z))).1 ≠ 0 := by
    rw [hs]
    intro he
    have hz := rectangular_markedShape w hw
    change (markingDisplacements (planarEdgeSq z)).2/(markingDisplacements (planarEdgeSq z)).1 =
      ⟨0,Real.sqrt w⟩ at hz
    rw [he,div_zero] at hz
    exact (Real.sqrt_pos.mpr (by linarith)).ne' (congrArg Complex.im hz).symm
  apply contDiffAt_markedShape (s := s) hsd _ hU
  rw [hs]
  exact htri

end Type7

end OrigamiTorus
