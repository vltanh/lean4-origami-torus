module

public import OrigamiTorus.EightVertex.Type5.Reconstruction
import Mathlib.Tactic

/-! Projected face intersections and orientation obstructions in planar hexagonal folds. -/

@[expose] public section

namespace OrigamiTorus.Type5.ProjectedFaces

/-- With both tips above the anchor plane, interleaved projected cones force the
relative interiors of the two spatial triangles to meet. Coordinates are based
at the shared vertex, and the two horizontal rays point to the other anchors. -/
theorem intersect_of_cones (A B U V : Plane ℝ) (h k s t p q : ℝ)
    (hh : 0 < h) (hk : 0 < k) (hs : 0 < s) (ht : 0 < t) (hp : 0 < p) (hq : 0 < q)
    (ha : A = s • B + t • V) (hb : B = p • A + q • U) :
    ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ a+b < 1 ∧ 0 < c ∧ 0 < d ∧ c+d < 1 ∧
      a • atHeight A 0 + b • atHeight U h = c • atHeight B 0 + d • atHeight V k := by
  let a := k*t*p+h*q
  let b := k*q*t
  let c := k*t+h*q*s
  let d := h*q*t
  have ha' : 0 < a := by dsimp [a]; positivity
  have hb' : 0 < b := by dsimp [b]; positivity
  have hc' : 0 < c := by dsimp [c]; positivity
  have hd' : 0 < d := by dsimp [d]; positivity
  have he : a • atHeight A 0 + b • atHeight U h = c • atHeight B 0 + d • atHeight V k := by
    have ax := congrArg Prod.fst ha
    have ay := congrArg Prod.snd ha
    have bx := congrArg Prod.fst hb
    have by' := congrArg Prod.snd hb
    ext <;> simp only [a,b,c,d,atHeight,Prod.fst_add,Prod.snd_add,Prod.smul_fst,
      Prod.smul_snd,smul_eq_mul] at ax ay bx by' ⊢
    · linear_combination h*q*ax - k*t*bx
    · linear_combination h*q*ay - k*t*by'
    · ring
  let T := 1+a+b+c+d
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨a/T,b/T,c/T,d/T,div_pos ha' hT,div_pos hb' hT,?_,div_pos hc' hT,div_pos hd' hT,?_,?_⟩
  · rw [← add_div, div_lt_one hT]
    dsimp [T]; linarith
  · rw [← add_div, div_lt_one hT]
    dsimp [T]; linarith
  · simpa only [smul_add,smul_smul,div_eq_inv_mul] using congrArg (fun z : Space ℝ => T⁻¹ • z) he

/-- Normalize the projected triangle 012 to (0,0), (1,0), (0,1). The remaining
eight strict projected signs of mask 11149 put the anchor rays in the two
open cones required by the intersection theorem. -/
theorem cones_of_signs (x₃ y₃ x₅ y₅ x₆ y₆ : ℝ)
    (h013 : 0 < y₃) (h023 : x₃ < 0) (h035 : x₃*y₅-y₃*x₅ < 0)
    (h016 : 0 < y₆) (h056 : 0 < x₅*y₆-y₅*x₆)
    (h125 : 0 < 1-x₅-y₅) (h126 : 0 < x₆+y₆-1)
    (h256 : 0 < x₅*(y₆-1)-(y₅-1)*x₆) :
    ∃ s t p q : ℝ, 0 < s ∧ 0 < t ∧ 0 < p ∧ 0 < q ∧
      ((1,-1) : Plane ℝ) = s • (x₅,y₅-1) + t • (x₆,y₆-1) ∧
      ((x₅,y₅-1) : Plane ℝ) = p • (1,-1) + q • (0,-1) := by
  let D := x₅*(y₆-1)-(y₅-1)*x₆
  let s := (x₆+y₆-1)/D
  let t := (1-x₅-y₅)/D
  have hs : 0 < s := div_pos h126 h256
  have ht : 0 < t := div_pos h125 h256
  have ha : ((1,-1) : Plane ℝ) = s • (x₅,y₅-1) + t • (x₆,y₆-1) := by
    ext <;> simp only [s,t,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    all_goals
      field_simp [show D ≠ 0 from ne_of_gt h256]
      dsimp [D]
      ring
  have hx : 0 < x₅ := by
    by_contra! hn
    have hy : 0 < y₅ := by
      by_contra! hy
      linarith only [h035,mul_nonneg_of_nonpos_of_nonpos h023.le hy,mul_nonpos_of_nonneg_of_nonpos h013.le hn]
    have hz : x₆ < 0 := by
      by_contra! hz
      linarith only [h056,mul_nonpos_of_nonpos_of_nonneg hn h016.le,mul_nonneg hy.le hz]
    have eqx := congrArg Prod.fst ha
    change 1 = s*x₅+t*x₆ at eqx
    linarith only [eqx,mul_nonpos_of_nonneg_of_nonpos hs.le hn,mul_neg_of_pos_of_neg ht hz]
  refine ⟨s,t,x₅,1-x₅-y₅,hs,ht,hx,h125,ha,?_⟩
  ext <;> simp
  ring

/-- In the aligned coordinates of planar mask 3981, the lengths on edge 27
and the positive areas of faces 012 and 274 force a strict turn on 067. -/
theorem area067_positive (b t h : ℝ) (h012 : 0 < -b/2)
    (h274 : 0 < (36*b*t+6*b+6*t-12*h+5)/24)
    (edge27 : -6*b*t+12*b*h-5*b+2*t+4*h-1 = 0) : 0 < (1-2*t-4*h)/8 := by
  have hc : 0 < 9*b^2+3*b+1 := by nlinarith [sq_nonneg (3*b+1/2)]
  have hid : (9*b^2+3*b+1)*((1-2*t-4*h)/8) =
      (-3*b)*((36*b*t+6*b+6*t-12*h+5)/24) := by
    linear_combination -(3*b+1)/8 * edge27
  exact pos_of_mul_pos_right (hid ▸ mul_pos (by linarith : 0 < -3*b) h274) hc.le

/-- The two projected signs in mask 3501 would put an affine function above
zero between two endpoints where its values force it to be negative. -/
theorem turns3501_incompatible (u v b d l m n f : ℝ)
    (hu : 0 < u) (hu1 : u < 1) (hv : 0 < v) (hw : 2*u+v ≤ 1)
    (hlb : l < b) (hbd : b < d)
    (hdiff : m*b+n-f = (b-d)*(v-2*u))
    (hr : m*d+n = (2*u-v)*(2*u+v-1)/3)
    (hl : m*l+n = -v*(1-u)*(4*u^2+v)/(3*u)) : 0 < f ∨ m*b+n < 0 := by
  by_contra! bad
  have hvu : v ≤ 2*u := by
    by_contra! h
    linarith only [hdiff, bad.1, bad.2, mul_neg_of_neg_of_pos (sub_neg.mpr hbd) (sub_pos.mpr h)]
  have hr' : m*d+n ≤ 0 := by
    rw [hr]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hvu) (sub_nonpos.mpr hw)) (by norm_num)
  have hl' : m*l+n < 0 := by
    rw [hl]
    have : 0 < 1-u := sub_pos.mpr hu1
    have : 0 < 4*u^2+v := by positivity
    exact div_neg_of_neg_of_pos (by rw [neg_mul, neg_mul]; exact neg_neg_of_pos (by positivity)) (by positivity)
  rcases lt_or_ge 0 m with hm | hm
  · linarith only [bad.2, hr', mul_lt_mul_of_pos_left hbd hm]
  · linarith only [bad.2, hl', mul_le_mul_of_nonpos_left hlb.le hm]

end OrigamiTorus.Type5.ProjectedFaces
