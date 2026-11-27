module

public import OrigamiTorus.AngleRank
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic

/-! The hand elimination of the horizontal angle dependencies on the rectangular family. -/

public section

namespace OrigamiTorus.Type7

private noncomputable abbrev H : ℝ := 33/20
private noncomputable abbrev D : ℝ := 13/20
private noncomputable abbrev r : ℝ := -D/3

private noncomputable def h (y : ℝ) : ℝ := y*H
private noncomputable def k (y : ℝ) : ℝ := h y/D
private noncomputable def d (y : ℝ) : ℝ := 1+(k y)^2
private noncomputable def s (y : ℝ) : ℝ := (73/40-H*(H/D)*y^2)/d y
private noncomputable def t (y : ℝ) : ℝ := (h y*k y-1)/d y
private noncomputable def j (y : ℝ) : ℝ := (h y+k y)/d y
private noncomputable def R (y : ℝ) : ℂ := 1+(k y : ℂ)*Complex.I

/-- The rectangular base in physical coordinates after removing its common scale. -/
private noncomputable def chart (y : ℝ) : Vertex → ℂ :=
  ![0, (1-(r : ℂ))+((h y+k y*r : ℝ) : ℂ)*Complex.I, 1/2,
    (h y : ℂ)*Complex.I+(s y : ℂ)*R y, 1, 1+(t y : ℂ)*R y,
    (h y : ℂ)*Complex.I, 1+(h y : ℂ)*Complex.I]

private theorem d_pos (y : ℝ) : 0 < d y := by
  unfold d
  positivity

private theorem r_neg : r < 0 := by norm_num

private theorem h_pos {y : ℝ} (hy : 1 ≤ y) : 0 < h y := by
  have : 0 < y := by linarith
  unfold h
  positivity

private theorem chart_signs {y : ℝ} (hy : 1 ≤ y) : s y < r ∧ 0 < t y ∧ 0 < j y := by
  have hyprod := mul_nonneg (sub_nonneg.mpr hy) (show 0 ≤ y+1 by linarith)
  have hy₂ : 1 ≤ y^2 := by nlinarith only [hyprod]
  refine ⟨(div_lt_iff₀ (d_pos y)).mpr ?_,div_pos ?_ (d_pos y),div_pos ?_ (d_pos y)⟩
  · unfold d k h
    norm_num
    nlinarith only [hy₂]
  · simp only [k,h]
    norm_num
    nlinarith only [hy₂]
  · unfold k
    have := h_pos hy
    positivity

private theorem chart_scaled {y : ℝ} (hy : 1 ≤ y) (v : Vertex) :
    physicalComplex (y^2) (rectangularPoint (y^2) v) = (d y : ℂ)*chart y v := by
  have hy₀ : 0 ≤ y := by linarith
  have hsqrt : Real.sqrt (y^2) = y := by rw [Real.sqrt_sq hy₀]
  have hd := (d_pos y).ne'
  fin_cases v <;> apply Complex.ext <;>
    simp [chart,rectangularPoint,physicalComplex,hsqrt,R,Complex.mul_re,Complex.mul_im,
      Complex.sub_re,Complex.sub_im] <;>
    norm_num [h,k,d,s,t] at hd ⊢ <;>
    field_simp [hd] <;> ring

theorem row_1 (z : Vertex → ℂ) (c : Vertex → ℝ) :
    inverseChordBalance z (fun v w => (negativeBlockCoefficient v w : ℝ)) c 1 =
      ((c 1-c 3 : ℝ) : ℂ)/(z 3-z 1)+((c 1-c 7 : ℝ) : ℂ)/(z 7-z 1) -
      ((c 1-c 0 : ℝ) : ℂ)/(z 0-z 1)-((c 1-c 4 : ℝ) : ℂ)/(z 4-z 1) := by
  norm_num [inverseChordBalance,negativeBlockCoefficient,Fin.sum_univ_succ]
  ring

theorem row_2 (z : Vertex → ℂ) (c : Vertex → ℝ) :
    inverseChordBalance z (fun v w => (negativeBlockCoefficient v w : ℝ)) c 2 =
      ((c 2-c 4 : ℝ) : ℂ)/(z 4-z 2)-((c 2-c 0 : ℝ) : ℂ)/(z 0-z 2) := by
  norm_num [inverseChordBalance,negativeBlockCoefficient,Fin.sum_univ_succ]
  ring

theorem row_3 (z : Vertex → ℂ) (c : Vertex → ℝ) :
    inverseChordBalance z (fun v w => (negativeBlockCoefficient v w : ℝ)) c 3 =
      ((c 3-c 4 : ℝ) : ℂ)/(z 4-z 3)+((c 3-c 0 : ℝ) : ℂ)/(z 0-z 3) -
      ((c 3-c 6 : ℝ) : ℂ)/(z 6-z 3)-((c 3-c 1 : ℝ) : ℂ)/(z 1-z 3) := by
  norm_num [inverseChordBalance,negativeBlockCoefficient,Fin.sum_univ_succ]
  ring

theorem row_5 (z : Vertex → ℂ) (c : Vertex → ℝ) :
    inverseChordBalance z (fun v w => (negativeBlockCoefficient v w : ℝ)) c 5 =
      ((c 5-c 7 : ℝ) : ℂ)/(z 7-z 5)+((c 5-c 6 : ℝ) : ℂ)/(z 6-z 5) -
      ((c 5-c 4 : ℝ) : ℂ)/(z 4-z 5)-((c 5-c 0 : ℝ) : ℂ)/(z 0-z 5) := by
  norm_num [inverseChordBalance,negativeBlockCoefficient,Fin.sum_univ_succ]
  ring

theorem row_6 (z : Vertex → ℂ) (c : Vertex → ℝ) :
    inverseChordBalance z (fun v w => (negativeBlockCoefficient v w : ℝ)) c 6 =
      ((c 6-c 0 : ℝ) : ℂ)/(z 0-z 6)+((c 6-c 3 : ℝ) : ℂ)/(z 3-z 6) -
      ((c 6-c 5 : ℝ) : ℂ)/(z 5-z 6)-((c 6-c 7 : ℝ) : ℂ)/(z 7-z 6) := by
  norm_num [inverseChordBalance,negativeBlockCoefficient,Fin.sum_univ_succ]
  ring

noncomputable abbrev balance (z : Vertex → ℂ) (c : Vertex → ℝ) (v : Vertex) : ℂ :=
  inverseChordBalance z (fun v w => (negativeBlockCoefficient v w : ℝ)) c v

theorem re_scaled_chord (K denom : ℂ) (c : ℝ) :
    (K*((c : ℂ)/denom)).re = c*(K/denom).re := by
  have he : K*((c : ℂ)/denom) = (c : ℂ)*(K/denom) := by
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  simp

theorem im_scaled_chord (K denom : ℂ) (c : ℝ) :
    (K*((c : ℂ)/denom)).im = c*(K/denom).im := by
  have he : K*((c : ℂ)/denom) = (c : ℂ)*(K/denom) := by
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  simp

theorem re_on_circle {v w C : ℂ} (hne : w ≠ v)
    (he : Complex.normSq (w-C) = Complex.normSq (v-C)) :
    ((v-C)/(w-v)).re = -1/2 := by
  have hp := two_re_chord_quotient v w C hne
  rw [he,sub_self,zero_div,add_zero] at hp
  linarith only [hp]

private theorem horizontal_row (y : ℝ) (c : Vertex → ℝ)
    (hc : balance (chart y) c 2 = 0) :
    2*c 2 = c 0+c 4 := by
  unfold balance at hc
  rw [row_2] at hc
  have he := congrArg Complex.re hc
  norm_num [chart,Complex.sub_re,Complex.div_re,Complex.sub_im,Complex.normSq_sub] at he
  linarith only [he]

private theorem first_circle_row {y : ℝ} (hy : 1 ≤ y) (c : Vertex → ℝ)
    (hc : balance (chart y) c 5 = 0) :
    c 6+c 7 = c 0+c 4 := by
  let z := chart y
  let C : ℂ := (1/2 : ℂ) + ((h y/2 : ℝ) : ℂ)*Complex.I
  have hty := (chart_signs hy).2.1
  have ht : d y*t y = h y*k y-1 := by
    unfold t
    field_simp [(d_pos y).ne']
  have hd (w : Vertex) (hw : w = 0 ∨ w = 4 ∨ w = 6 ∨ w = 7) :
      Complex.normSq (z w-C) = 1/4+(h y)^2/4 := by
    rcases hw with rfl | rfl | rfl | rfl <;>
      norm_num [Complex.normSq_apply,z,chart,C,Complex.div_re,Complex.div_im,Complex.mul_re,
        Complex.mul_im,Complex.sub_re,Complex.sub_im] <;> ring
  have h5 : Complex.normSq (z 5-C) = 1/4+(h y)^2/4 := by
    norm_num [Complex.normSq_apply,z,chart,C,R,Complex.div_re,Complex.div_im,Complex.mul_re,
      Complex.mul_im,Complex.sub_re,Complex.sub_im]
    change (1+(k y)^2)*t y = h y*k y-1 at ht
    linear_combination (t y)*ht
  have hn (w : Vertex) (hw : w = 0 ∨ w = 4 ∨ w = 6 ∨ w = 7) : z w ≠ z 5 := by
    intro he
    have hr := congrArg Complex.re he
    rcases hw with rfl | rfl | rfl | rfl <;>
      norm_num [z,chart,R,Complex.mul_re] at hr <;> linarith only [hr,hty]
  have hp (w : Vertex) (hw : w = 0 ∨ w = 4 ∨ w = 6 ∨ w = 7) :
      ((z 5-C)/(z w-z 5)).re = -1/2 := re_on_circle (hn w hw) ((hd w hw).trans h5.symm)
  unfold balance at hc
  rw [row_5] at hc
  have he := congrArg (fun b : ℂ => ((z 5-C)*b).re) hc
  simp only [mul_add,mul_sub,Complex.add_re,Complex.sub_re,re_scaled_chord,mul_zero,
    Complex.zero_re] at he
  rw [hp 7 (by simp),hp 6 (by simp),hp 4 (by simp),hp 0 (by simp)] at he
  linarith only [he]

private theorem second_circle_row {y : ℝ} (hy : 1 ≤ y) (c : Vertex → ℝ)
    (hc : balance (chart y) c 3 = 0) (hcircle : c 6+c 7 = c 0+c 4) :
    c 1-c 7 = -(r/s y)*(c 3-c 6) := by
  let z := chart y
  let b := (r^2-r+(h y+k y*r)^2)/(h y+k y*r)
  let C : ℂ := ⟨1/2,b/2⟩
  let power (a : ℂ) := Complex.normSq (a-C)-Complex.normSq C
  have hs := (chart_signs hy).1.trans r_neg
  have hRise : 0 < h y+k y*r := by
    have he : h y+k y*r = (2/3)*h y := by
      unfold k
      norm_num [r,D] <;> ring
    rw [he]
    positivity [h_pos hy]
  have hb : b*(h y+k y*r) = r^2-r+(h y+k y*r)^2 :=
    div_mul_cancel₀ _ hRise.ne'
  have hp (a : ℂ) : power a = a.re^2-a.re+a.im^2-b*a.im := by
    simp only [power,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,C]
    ring
  have hconstant : (h y)^2-b*h y = d y*r*s y := by
    have hS : d y*s y = 73/40-H*(H/D)*y^2 := by
      unfold s
      field_simp [(d_pos y).ne']
    apply mul_right_cancel₀ hRise.ne'
    calc
      _ = (h y)^2*(h y+k y*r)-h y*(r^2-r+(h y+k y*r)^2) := by
        linear_combination -(h y)*hb
      _ = (73/40-H*(H/D)*y^2)*r*(h y+k y*r) := by
        simp only [k,h]
        norm_num [H,D,r] <;> ring
      _ = _ := by rw [← hS]; ring
  have hroot : d y*r^2+(-1+2*h y*k y-b*k y)*r+((h y)^2-b*h y) = 0 := by
    unfold d
    linear_combination -hb
  have hlinear : -1+2*h y*k y-b*k y = -(d y*(r+s y)) := by
    have he : r*((-1+2*h y*k y-b*k y)+d y*(r+s y)) = 0 := by
      linear_combination hroot-hconstant
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp he).resolve_left r_neg.ne)
  have hp0 : power (z 0) = 0 := by simp [hp,z,chart]
  have hp4 : power (z 4) = 0 := by simp [hp,z,chart]
  have hp1 : power (z 1) = 0 := by
    rw [hp]
    simp [z,chart,Complex.sub_re,Complex.mul_re,Complex.mul_im]
    linear_combination -hb
  have hp3 : power (z 3) = 0 := by
    rw [hp]
    simp [z,chart,R,Complex.mul_re,Complex.mul_im]
    have he : (s y)^2-s y+(h y+s y*k y)^2-b*(h y+s y*k y) =
        d y*(s y)^2+(-1+2*h y*k y-b*k y)*s y+((h y)^2-b*h y) := by
      unfold d
      ring
    rw [he,hlinear,hconstant]
    ring
  have hp6 : power (z 6) = d y*r*s y := by
    simpa [hp,z,chart,Complex.mul_re,Complex.mul_im] using hconstant
  have hn (w : Vertex) (hw : w = 0 ∨ w = 4 ∨ w = 1 ∨ w = 6) : z w ≠ z 3 := by
    intro he
    have hr := congrArg Complex.re he
    rcases hw with rfl | rfl | rfl | rfl <;>
      norm_num [z,chart,R,Complex.sub_re,Complex.mul_re] at hr <;> linarith only [hs,r_neg,hr]
  have hchord (w : Vertex) (hw : w = 0 ∨ w = 4 ∨ w = 1) :
      ((z 3-C)/(z w-z 3)).re = -1/2 := by
    have hP : power (z w) = 0 := by
      rcases hw with rfl | rfl | rfl
      · exact hp0
      · exact hp4
      · exact hp1
    have he : Complex.normSq (z w-C) = Complex.normSq (z 3-C) := by
      dsimp only [power] at hP hp3
      linarith only [hP,hp3]
    have hne : z w ≠ z 3 := hn w (by rcases hw with rfl | rfl | rfl <;> simp)
    exact re_on_circle hne he
  have hchord6 : ((z 3-C)/(z 6-z 3)).re = (-1+r/s y)/2 := by
    have hpDiff : Complex.normSq (z 6-C)-Complex.normSq (z 3-C) = d y*r*s y := by
      dsimp only [power] at hp6 hp3
      linarith only [hp3,hp6]
    have hnSq : Complex.normSq (z 6-z 3) = d y*(s y)^2 := by
      simp [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,z,chart,R,Complex.mul_re,Complex.mul_im,d]
      ring
    have hratio : (d y*r*s y)/(d y*(s y)^2) = r/s y := by
      field_simp [(d_pos y).ne',hs.ne]
    have hp := two_re_chord_quotient (z 3) (z 6) C (hn 6 (by simp))
    rw [hpDiff,hnSq,hratio] at hp
    linarith only [hp]
  unfold balance at hc
  rw [row_3] at hc
  have he := congrArg (fun b : ℂ => ((z 3-C)*b).re) hc
  simp only [mul_add,mul_sub,Complex.add_re,Complex.sub_re,re_scaled_chord,mul_zero,
    Complex.zero_re] at he
  rw [hchord 4 (by simp),hchord 0 (by simp),hchord 1 (by simp),hchord6] at he
  linarith only [he,hcircle]

private theorem chord_56 (y : ℝ) :
    chart y 5-chart y 6 = -(j y : ℂ)*Complex.I*R y := by
  apply Complex.ext <;>
    norm_num [chart,R,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im] <;>
    unfold t j <;> field_simp [(d_pos y).ne'] <;> unfold d <;> ring

private theorem chord_75 (y : ℝ) :
    chart y 7-chart y 5 = chart y 7*R y/(d y : ℂ) := by
  have hd := (d_pos y).ne'
  apply Complex.ext <;>
    norm_num [chart,R,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
      Complex.div_re,Complex.div_im,Complex.normSq_ofReal] <;>
    unfold t <;> field_simp [hd] <;> (try unfold d) <;> ring

private theorem one_div_neg_imaginary (a : ℝ) :
    (1 : ℂ)/(-(a : ℂ)*Complex.I) = ((1/a : ℝ) : ℂ)*Complex.I := by
  rw [Complex.ofReal_div,Complex.ofReal_one,one_div,one_div,mul_inv_rev,Complex.inv_I,inv_neg]
  ring

private theorem vertical_row {y : ℝ} (hy : 1 ≤ y) (c : Vertex → ℝ)
    (h0 : c 0 = 0) (hc : balance (chart y) c 6 = 0) (hcircle : c 6+c 7 = c 0+c 4) :
    c 4 = (2+1/D)*c 6+(c 3-c 6)/s y ∧
    (c 6-c 5)/j y = c 6/h y-k y*(c 6-c 7) := by
  let z := chart y
  have hnR : R y ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp [R,Complex.mul_re] at hr
  have hh := h_pos hy
  have hz0 : z 0-z 6 = -(h y : ℂ)*Complex.I := by simp [z,chart]
  have hz3 : z 3-z 6 = (s y : ℂ)*R y := by simp [z,chart]
  have hz5 : z 5-z 6 = -(j y : ℂ)*Complex.I*R y := chord_56 y
  have hz7 : z 7-z 6 = 1 := by simp [z,chart]
  have hctrl0 : R y/(z 0-z 6) = R y*(((1/h y : ℝ) : ℂ)*Complex.I) := by
    rw [hz0,← mul_one_div,one_div_neg_imaginary]
  have hctrl3 : R y/(z 3-z 6) = ((1/s y : ℝ) : ℂ) := by
    rw [hz3]
    simpa only [one_mul,Complex.ofReal_div,Complex.ofReal_one] using
      mul_div_mul_right (1 : ℂ) (s y : ℂ) hnR
  have hctrl5 : R y/(z 5-z 6) = ((1/j y : ℝ) : ℂ)*Complex.I := by
    rw [hz5,← one_div_neg_imaginary]
    simpa only [one_mul] using mul_div_mul_right (1 : ℂ) (-(j y : ℂ)*Complex.I) hnR
  have hctrl7 : R y/(z 7-z 6) = R y := by rw [hz7,div_one]
  have hkh : k y*(1/h y) = 1/D := by
    unfold k
    field_simp [hh.ne',show D ≠ 0 by norm_num [D]]
  change balance z c 6 = 0 at hc
  unfold balance at hc
  rw [row_6] at hc
  have he := congrArg (fun b : ℂ => R y*b) hc
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [mul_add,mul_sub,Complex.add_re,Complex.sub_re,re_scaled_chord,mul_zero,
    Complex.zero_re,hctrl0,hctrl3,hctrl5,hctrl7] at hre
  simp only [mul_add,mul_sub,Complex.add_im,Complex.sub_im,im_scaled_chord,mul_zero,
    Complex.zero_im,hctrl0,hctrl3,hctrl5,hctrl7] at him
  simp [R,Complex.mul_re,Complex.mul_im,h0] at hre him
  simp only [one_div] at hkh
  rw [hkh] at hre
  constructor
  · simp only [div_eq_mul_inv]
    linarith only [hre,hcircle,h0]
  · rw [div_eq_mul_inv,div_eq_mul_inv]
    linarith only [him]

@[expose] noncomputable def normalizedChord (v w : ℂ) : ℂ := w*(1-v)/(w-v)

theorem chord_normalization {v w : ℂ} (hne : w ≠ v) :
    (v*(1-v)/(w-v)).re = v.re-1+(normalizedChord v w).re := by
  have he : v*(1-v)/(w-v) = v-1+normalizedChord v w := by
    unfold normalizedChord
    field_simp [sub_ne_zero.mpr hne]
    ring
  rw [he]
  simp

theorem normalizedChord_zero (v : ℂ) : normalizedChord v 0 = 0 := by
  simp [normalizedChord]

theorem normalizedChord_one {v : ℂ} (h : v ≠ 1) : normalizedChord v 1 = 1 := by
  simp [normalizedChord,sub_ne_zero.mpr h.symm]

private theorem coupled_row {y : ℝ} (hy : 1 ≤ y) (c : Vertex → ℝ)
    (h0 : c 0 = 0) (hc : balance (chart y) c 1 = 0)
    (hcircle : c 6+c 7 = c 0+c 4)
    (hY : c 1-c 7 = -(r/s y)*(c 3-c 6))
    (hA : c 4 = (2+1/D)*c 6+(c 3-c 6)/s y) : c 3 = c 6 := by
  let z := chart y
  let M := h y*(h y+k y)/d y
  let X := c 3-c 6
  have hs := (chart_signs hy).1.trans r_neg
  have hr := r_neg
  have hd := (d_pos y).ne'
  have hD : 0 < D := by norm_num [D]
  have hM : 0 < M := by
    have hh := h_pos hy
    have hk : 0 < k y := div_pos hh hD
    exact div_pos (mul_pos hh (add_pos hh hk)) (d_pos y)
  have hn (w : Vertex) (hw : w = 0 ∨ w = 4 ∨ w = 3 ∨ w = 7) : z w ≠ z 1 := by
    intro he
    have hRe := congrArg Complex.re he
    rcases hw with rfl | rfl | rfl | rfl <;>
      norm_num [z,chart,R,Complex.sub_re,Complex.mul_re] at hRe <;> linarith only [hs,hr,hRe]
  have hZ3 : normalizedChord (z 1) (z 3) = -(D : ℂ) := by
    unfold normalizedChord
    apply (div_eq_iff (sub_ne_zero.mpr (hn 3 (by simp)))).mpr
    apply Complex.ext <;>
      norm_num [z,chart,R,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im] <;>
      unfold s <;> field_simp [hd] <;> simp only [d,k,h] <;> norm_num [D,H,r] <;> ring
  have hZ7 : (normalizedChord (z 1) (z 7)).re = 1+M/r := by
    have hnSq : Complex.normSq (z 7-z 1) = d y*r^2 := by
      norm_num [Complex.normSq_apply,z,chart,R,Complex.sub_re,Complex.sub_im,Complex.mul_re,
        Complex.mul_im,d]
      ring
    rw [normalizedChord,Complex.div_re,hnSq,← add_div]
    norm_num [z,chart,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,M]
    field_simp [hd,hr.ne]
    unfold d
    ring
  have h0R : (z 1*(1-z 1)/(z 0-z 1)).re = -r := by
    rw [chord_normalization (hn 0 (by simp))]
    norm_num [z,chart,normalizedChord_zero,Complex.sub_re,Complex.mul_re]
  have h4R : (z 1*(1-z 1)/(z 4-z 1)).re = 1-r := by
    have hn1 : z 1 ≠ 1 := by
      simpa [z,chart] using (hn 4 (by simp)).symm
    have hz4 : z 4 = 1 := by simp [z,chart]
    rw [chord_normalization (hn 4 (by simp)),hz4,normalizedChord_one hn1]
    norm_num [z,chart,Complex.sub_re,Complex.mul_re]
  have h3R : (z 1*(1-z 1)/(z 3-z 1)).re = -r-D := by
    rw [chord_normalization (hn 3 (by simp)),hZ3]
    norm_num [z,chart,Complex.sub_re,Complex.mul_re]
  have h7R : (z 1*(1-z 1)/(z 7-z 1)).re = -r+1+M/r := by
    rw [chord_normalization (hn 7 (by simp)),hZ7]
    norm_num [z,chart,Complex.sub_re,Complex.mul_re]
    ring
  change balance z c 1 = 0 at hc
  unfold balance at hc
  rw [row_1] at hc
  have hre := congrArg (fun b : ℂ => ((z 1*(1-z 1))*b).re) hc
  simp only [mul_add,mul_sub,Complex.add_re,Complex.sub_re,re_scaled_chord,mul_zero,
    Complex.zero_re] at hre
  rw [← mul_sub (z 1) 1 (z 1),h3R,h7R,h0R,h4R] at hre
  have hYproduct : (c 1-c 7)*(1+M/r) = -(r+M)*X/s y := by
    rw [hY]
    dsimp only [X]
    field_simp [hs.ne,hr.ne]
    ring
  have hnormalized : 0 = r*X-D*(c 1-c 3)-(r+M)*X/s y-(c 1-c 4) := by
    dsimp only [X] at hYproduct ⊢
    linear_combination -hre+hYproduct+r*hcircle
  have h1 : c 1 = c 4-c 6-(r/s y)*X := by
    change c 1-c 7 = -(r/s y)*X at hY
    linear_combination hY+hcircle+h0
  have h3 : c 3 = c 6+X := by dsimp only [X]; ring
  have hcoef : 0 = (D+r+(D*(r-1)-M)/s y)*X := by
    have hA' : c 4 = (2+1/D)*c 6+X/s y := hA
    rw [h1,h3,hA'] at hnormalized
    convert hnormalized using 1 <;> field_simp [hs.ne,hD.ne'] <;> ring
  have hpos : 0 < D+r+(D*(r-1)-M)/s y := by
    have hDr : 0 < D+r := by norm_num [D,r]
    have hnum : D*(r-1)-M < 0 := by
      have hmul := mul_neg_of_pos_of_neg hD (show r-1 < 0 by linarith only [hr])
      linarith only [hmul,hM]
    exact add_pos hDr (div_pos_of_neg_of_neg hnum hs)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcoef.symm).resolve_left hpos.ne')

private theorem last_row {y : ℝ} (hy : 1 ≤ y) (c : Vertex → ℝ)
    (hc : balance (chart y) c 5 = 0) (hcircle : c 6+c 7 = c 0+c 4) :
    (1+d y*t y+h y*t y/j y)*c 5 = c 4+d y*t y*c 7+(h y*t y/j y)*c 6 := by
  let z := chart y
  obtain ⟨_,ht,hj⟩ := chart_signs hy
  have hn (w : Vertex) (hw : w = 0 ∨ w = 4 ∨ w = 6 ∨ w = 7) : z w ≠ z 5 := by
    intro he
    have hRe := congrArg Complex.re he
    rcases hw with rfl | rfl | rfl | rfl <;>
      norm_num [z,chart,R,Complex.mul_re] at hRe <;> linarith only [ht,hRe]
  have hz6 : z 6 = (h y : ℂ)*Complex.I := by simp [z,chart]
  have hnum : 1-z 5 = -(t y : ℂ)*R y := by simp [z,chart]
  have h65 : z 6-z 5 = (j y : ℂ)*Complex.I*R y := by
    change chart y 6-chart y 5 = _
    rw [← neg_sub, chord_56]
    ring
  have hZ7 : normalizedChord (z 5) (z 7) = -(d y*t y : ℝ) := by
    unfold normalizedChord
    apply (div_eq_iff (sub_ne_zero.mpr (hn 7 (by simp)))).mpr
    rw [hnum, show z 7-z 5 = z 7*R y/(d y : ℂ) from chord_75 y]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (d_pos y).ne'] <;> ring
  have hZ6 : normalizedChord (z 5) (z 6) = -(h y*t y/j y : ℝ) := by
    unfold normalizedChord
    apply (div_eq_iff (sub_ne_zero.mpr (hn 6 (by simp)))).mpr
    rw [hnum,h65,hz6]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hj.ne'] <;> ring
  have hn1 : z 5 ≠ 1 := by simpa [z,chart] using (hn 4 (by simp)).symm
  change balance z c 5 = 0 at hc
  unfold balance at hc
  rw [row_5] at hc
  have hre := congrArg (fun b : ℂ => ((z 5*(1-z 5))*b).re) hc
  simp only [mul_add,mul_sub,Complex.add_re,Complex.sub_re,re_scaled_chord,mul_zero,
    Complex.zero_re] at hre
  rw [← mul_sub (z 5) 1 (z 5),chord_normalization (hn 7 (by simp)),chord_normalization (hn 6 (by simp)),
    chord_normalization (hn 4 (by simp)),chord_normalization (hn 0 (by simp)),hZ7,hZ6] at hre
  have hz0 : z 0 = 0 := by simp [z,chart]
  have hz4 : z 4 = 1 := by simp [z,chart]
  rw [hz0,hz4,normalizedChord_zero,normalizedChord_one hn1] at hre
  norm_num [z,chart,R,Complex.mul_re] at hre
  linear_combination -hre-(t y)*hcircle

private theorem normalized_balance_zero {y : ℝ} (hy : 1 ≤ y) (c : Vertex → ℝ)
    (h0 : c 0 = 0) (hc : ∀ v, balance (chart y) c v = 0) : c = 0 := by
  let u := c 6
  have hD : 0 < D := by norm_num [D]
  have hh := h_pos hy
  obtain ⟨_,ht,hj⟩ := chart_signs hy
  have hcircle := first_circle_row hy c (hc 5)
  have hY := second_circle_row hy c (hc 3) hcircle
  obtain ⟨hA,hImag⟩ := vertical_row hy c h0 (hc 6) hcircle
  have h3 := coupled_row hy c h0 (hc 1) hcircle hY hA
  rw [h3,sub_self,zero_div,add_zero] at hA
  rw [h3,sub_self,mul_zero] at hY
  have h7 : c 7 = (1+1/D)*u := by
    dsimp only [u]
    linear_combination hcircle+h0+hA
  have hminus : c 6-c 7 = -u/D := by
    rw [h7]
    dsimp only [u]
    ring
  have hjproduct : j y*(1/h y+k y/D) = 1+1/D := by
    have he : 1/h y+k y/D = d y/h y := by
      unfold d k
      field_simp [hh.ne',hD.ne']
    rw [he]
    unfold j
    field_simp [(d_pos y).ne',hh.ne',hD.ne']
    unfold k
    field_simp [hD.ne']
  have h5 : c 5 = -u/D := by
    rw [hminus] at hImag
    have he : c 6-c 5 = j y*(u*(1/h y+k y/D)) := by
      rw [mul_comm (j y)]
      apply (div_eq_iff hj.ne').mp
      dsimp only [u] at hImag ⊢
      linear_combination hImag
    have he' : c 6-c 5 = (1+1/D)*u := by
      rw [he,← hjproduct]
      ring
    dsimp only [u] at he' ⊢
    linear_combination -he'
  let B := d y*t y
  let C := h y*t y/j y
  have hB : 0 < B := mul_pos (d_pos y) ht
  have hC : 0 < C := div_pos (mul_pos hh ht) hj
  have hL := last_row hy c (hc 5) hcircle
  change (1+B+C)*c 5 = c 4+B*c 7+C*c 6 at hL
  rw [h5,hA,h7] at hL
  have he : ((1+B+C)/D+(2+1/D)+B*(1+1/D)+C)*u = 0 := by
    dsimp only [u] at hL ⊢
    linear_combination -hL
  have hp : 0 < (1+B+C)/D+(2+1/D)+B*(1+1/D)+C := by positivity
  have hu : c 6 = 0 := (mul_eq_zero.mp he).resolve_left hp.ne'
  have h4z : c 4 = 0 := by simp [hu] at hA; exact hA
  have h7z : c 7 = 0 := by simpa [u,hu] using h7
  have h5z : c 5 = 0 := by simpa [u,hu] using h5
  have h1z : c 1 = 0 := by simpa [h7z] using hY
  have h2z := horizontal_row y c (hc 2)
  have h3z : c 3 = 0 := h3.trans hu
  funext v
  fin_cases v
  · exact h0
  · exact h1z
  · change c 2 = 0; linarith only [h2z,h0,h4z]
  · exact h3z
  · exact h4z
  · exact h5z
  · exact hu
  · exact h7z

theorem balance_subtract_constant (z : Vertex → ℂ) (c : Vertex → ℝ) (v : Vertex)
    (a : ℝ) : balance z (fun w => c w-a) v = balance z c v := by
  unfold balance inverseChordBalance
  apply Finset.sum_congr rfl
  intro w _
  push_cast
  have hdiff : ((c v : ℂ)-a)-((c w : ℂ)-a) = (c v : ℂ)-c w := by ring
  rw [hdiff]

/-- Every left dependence of the horizontal cone-angle differential on the
Type 7 rectangular family is constant, including at the square. -/
theorem rectangular_angle_dependence_constant (w : ℝ) (hw : 1 ≤ w) (c : Vertex → ℝ) :
    let z := physicalComplex w ∘ rectangularPoint w
    (∀ δ : Vertex → ℂ, (∑ v, c v * deriv (fun t : ℝ =>
      (orientedFaces.map (fun f => Type4.chartEuclideanCorner (fun v => z v+t • δ v) v f.1)).sum) 0) = 0) ↔
      ∀ v, c v = c 0 := by
  refine (rectangular_cone_angle_left_kernel w hw c).trans ?_
  let y := Real.sqrt w
  have hw₀ : 0 ≤ w := by linarith
  have hy : 1 ≤ y := (Real.le_sqrt (by norm_num) hw₀).mpr (by simpa using hw)
  have hwy : y^2 = w := Real.sq_sqrt hw₀
  constructor
  · intro hc
    let normalized (v : Vertex) := c v-c 0
    have hbal (v : Vertex) : balance (chart y) normalized v = 0 := by
      rw [balance_subtract_constant (chart y) c v (c 0)]
      apply (inverseChordBalance_mul_eq_zero_iff _ _ _ v (d y : ℂ)
        (Complex.ofReal_ne_zero.mpr (d_pos y).ne')).mp
      have he : (fun j => (d y : ℂ)*chart y j) = physicalComplex w ∘ rectangularPoint w := by
        funext j
        simp only [Function.comp_apply]
        rw [← hwy]
        exact (chart_scaled hy j).symm
      rw [he]
      exact hc v
    have hz : normalized = 0 := normalized_balance_zero hy normalized (sub_self _) hbal
    intro v
    exact sub_eq_zero.mp (congrFun hz v)
  · intro hc v
    unfold inverseChordBalance
    simp [hc]

theorem rectangular_corners_nondegenerate (w : ℝ) (hw : 1 ≤ w) :
    let z := physicalComplex w ∘ rectangularPoint w
    ∀ f ∈ faces, ∀ v a b, cornerRays v f = some (a,b) →
      z a ≠ z v ∧ z b ≠ z v ∧ 0 < InnerProductGeometry.angle (z a-z v) (z b-z v) ∧
        InnerProductGeometry.angle (z a-z v) (z b-z v) < Real.pi := by
  have hfaces : orientedFaces.map Prod.fst = faces := by decide +kernel
  rw [← hfaces]
  exact planarCorners_nondegenerate_of_face_areas orientedFaces (rectangularPoint w) w (by linarith)
    (fun f hf => rectangular_face_orientation w hw f.1 f.2 hf)

/-- A constant left dependence is the only relation when the seven independent
cone angles have surjective differential. This criterion proves surjectivity. -/
theorem seven_cone_derivative_surjective (z : Vertex → ℂ)
    (hnondegenerate : ∀ f ∈ faces, ∀ v a b, cornerRays v f = some (a,b) →
      z a ≠ z v ∧ z b ≠ z v ∧ 0 < InnerProductGeometry.angle (z a-z v) (z b-z v) ∧
        InnerProductGeometry.angle (z a-z v) (z b-z v) < Real.pi)
    (hdependence : ∀ c : Vertex → ℝ,
      (∀ δ : Vertex → ℂ, (∑ v, c v * deriv (fun t : ℝ =>
        (orientedFaces.map (fun f => Type4.chartEuclideanCorner (fun j => z j+t • δ j) v f.1)).sum) 0) = 0) →
        ∀ v, c v = c 0) :
    Function.Surjective (fderiv ℝ (sevenConeAngles faces : (Vertex → ℂ) → Fin 7 → ℝ) z) := by
  have hfaces : orientedFaces.map Prod.fst = faces := by decide +kernel
  have hcd := contDiffAt_coneAngles (n := 1) faces z hnondegenerate
  have hcd7 : ContDiffAt ℝ 1 (sevenConeAngles faces : (Vertex → ℂ) → Fin 7 → ℝ) z :=
    contDiffAt_pi.mpr (fun i => (contDiffAt_pi.mp hcd) i.succ)
  let L := fderiv ℝ (sevenConeAngles faces : (Vertex → ℂ) → Fin 7 → ℝ) z
  change Function.Surjective L
  apply (LinearMap.dualMap_injective_iff (f := L.toLinearMap)).mp
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro φ hφ
  have hvan (δ : Vertex → ℂ) : φ (L δ) = 0 := by
    exact congrArg (fun (g : Module.Dual ℝ (Vertex → ℂ)) => g δ) hφ
  let c : Vertex → ℝ := Fin.cases 0 (fun i => φ (Pi.single i 1))
  have heval (x : Fin 7 → ℝ) : φ x = ∑ i, φ (Pi.single i 1)*x i := by
    have hh := congrArg φ (pi_eq_sum_univ' x)
    simpa only [map_sum,map_smul,smul_eq_mul,mul_comm] using hh
  have hcoord (δ : Vertex → ℂ) (i : Fin 7) :
      (L δ) i = deriv (fun t : ℝ =>
        (orientedFaces.map (fun f => Type4.chartEuclideanCorner (fun j => z j+t • δ j) i.succ f.1)).sum) 0 := by
    let P : (Fin 7 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have hp : HasFDerivAt (fun q => coneAngles faces q i.succ) (P.comp L) z :=
      P.hasFDerivAt.comp z (hcd7.differentiableAt (by norm_num)).hasFDerivAt
    have he := deriv_line_eq_fderiv hp.differentiableAt δ
    rw [hp.fderiv,← hfaces] at he
    have hline (t : ℝ) : z + t • δ = fun j => z j + t • δ j := rfl
    simpa only [coneAngles_eq_chart,ContinuousLinearMap.comp_apply,P,ContinuousLinearMap.proj_apply,
      hline] using he.symm
  have hdep : ∀ δ : Vertex → ℂ, (∑ v, c v * deriv (fun t : ℝ =>
      (orientedFaces.map (fun f => Type4.chartEuclideanCorner (fun j => z j+t • δ j) v f.1)).sum) 0) = 0 := by
    intro δ
    rw [Fin.sum_univ_succ]
    simp only [c,Fin.cases_zero,zero_mul,zero_add,Fin.cases_succ,← hcoord δ]
    rw [← heval]
    exact hvan δ
  have hconst := hdependence c hdep
  have hzero (i : Fin 7) : φ (Pi.single i 1) = 0 := by
    simpa only [c,Fin.cases_zero,Fin.cases_succ] using hconst i.succ
  apply LinearMap.ext
  intro x
  rw [heval]
  simp only [hzero,zero_mul,Finset.sum_const_zero,LinearMap.zero_apply]

/-- The derivative of the seven independent cone angles of the Type 7
rectangular family is surjective at every rectangular modulus. -/
theorem rectangular_seven_cone_derivative_surjective (w : ℝ) (hw : 1 ≤ w) :
    let z := physicalComplex w ∘ rectangularPoint w
    Function.Surjective (fderiv ℝ (sevenConeAngles faces : (Vertex → ℂ) → Fin 7 → ℝ) z) :=
  seven_cone_derivative_surjective _ (rectangular_corners_nondegenerate w hw)
    (fun c => (rectangular_angle_dependence_constant w hw c).mp)

end OrigamiTorus.Type7
