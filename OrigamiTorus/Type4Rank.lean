module

public import OrigamiTorus.Type4RankGeometry
public import OrigamiTorus.Type7Rank
import Mathlib.Tactic

/-! The horizontal cone-angle rank calculation on the two Type 4 charts. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type4.TrapezoidChart

open Type7 (balance row_1 row_2 row_3 row_5 row_6 re_scaled_chord im_scaled_chord re_on_circle)

variable {p : TrapezoidChart}

private def circleCenter (g : ℝ) : ℂ := ⟨1/2,g/2⟩

private def circlePower (g : ℝ) (z : ℂ) : ℝ :=
  Complex.normSq (z-circleCenter g)-Complex.normSq (circleCenter g)

private theorem circlePower_eq (g : ℝ) (z : ℂ) :
    circlePower g z = z.re^2-z.re+z.im^2-g*z.im := by
  simp only [circlePower,circleCenter,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

private theorem circlePower_mirror (g u v : ℝ) :
    circlePower g ⟨1-u,v⟩ = circlePower g ⟨u,v⟩ := by
  simp only [circlePower_eq]
  ring

private theorem circle_inverse_chord {g : ℝ} {v w : ℂ} (hne : w ≠ v)
    (he : circlePower g w = circlePower g v) :
    ((v-circleCenter g)/(w-v)).re = -1/2 := by
  apply re_on_circle hne
  unfold circlePower at he
  linarith only [he]

private theorem horizontal_row (c : Vertex → ℝ) (hc : balance p.z c 2 = 0) :
    2*c 2 = c 0+c 4 := by
  unfold balance at hc
  rw [row_2] at hc
  have he := congrArg Complex.re hc
  norm_num [z₀,z₂,z₄,Complex.sub_re,Complex.div_re,Complex.sub_im,Complex.normSq_sub] at he
  linarith only [he]

private theorem first_circle_row (hp : p.Bounds) (hs : 0 < p.s) (c : Vertex → ℝ)
    (hc : balance p.z c 5 = 0) : c 6+c 7 = c 0+c 4 := by
  let g := (p.a^2-p.a+p.h^2)/p.h
  have hg : g*p.h = p.a^2-p.a+p.h^2 := div_mul_cancel₀ _ hp.h_pos.ne'
  have h5 : p.d*p.s = g*p.k-1 := by
    have he : g*p.k = (p.a^2-p.a+p.h^2)/p.D := by
      rw [k,← mul_div_assoc,hg]
    rw [he,s]
    field_simp [p.d_pos.ne']
  have hp5 : circlePower g (p.z 5) = 0 := by
    simp only [circlePower_eq,z₅,R,Complex.add_re,Complex.add_im,Complex.mul_re,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im]
    change (1+p.k^2)*p.s = g*p.k-1 at h5
    linear_combination p.s*h5
  have hp6 : circlePower g (p.z 6) = 0 := by
    simp only [circlePower_eq,z₆]
    linarith only [hg]
  have hp7 : circlePower g (p.z 7) = 0 := by
    rw [z₇,circlePower_mirror,← z₆,hp6]
  have hchord (v : Vertex) (hv : v = 0 ∨ v = 4 ∨ v = 6 ∨ v = 7) :
      ((p.z 5-circleCenter g)/(p.z v-p.z 5)).re = -1/2 := by
    apply circle_inverse_chord
    · intro he
      have hr := congrArg Complex.re he
      rcases hv with rfl | rfl | rfl | rfl <;>
        norm_num [z₀,z₄,z₅,z₆,z₇,R,Complex.add_re,Complex.mul_re] at hr <;>
        linarith only [hr,hs,hp.a_nonneg,hp.a_lt_half]
    · rw [hp5]
      rcases hv with rfl | rfl | rfl | rfl
      · simp [z₀,circlePower_eq]
      · simp [z₄,circlePower_eq]
      · exact hp6
      · exact hp7
  unfold balance at hc
  rw [row_5] at hc
  have he := congrArg (fun b : ℂ => ((p.z 5-circleCenter g)*b).re) hc
  simp only [mul_add,mul_sub,Complex.add_re,Complex.sub_re,re_scaled_chord,mul_zero,
    Complex.zero_re] at he
  rw [hchord 7 (by simp),hchord 6 (by simp),hchord 4 (by simp),hchord 0 (by simp)] at he
  linarith only [he]

private theorem second_circle_row (hp : p.Bounds) (ht : p.t < 0) (c : Vertex → ℝ)
    (hc : balance p.z c 3 = 0) (hcircle : c 6+c 7 = c 0+c 4) :
    c 1-c 7 = -(p.r/p.t)*(c 3-c 6) := by
  let g := ((p.a+p.r)^2-(p.a+p.r)+(p.h+p.k*p.r)^2)/(p.h+p.k*p.r)
  have hg : g*(p.h+p.k*p.r) = (p.a+p.r)^2-(p.a+p.r)+(p.h+p.k*p.r)^2 :=
    div_mul_cancel₀ _ hp.h_add_kr_pos.ne'
  let l := 2*p.a-1+2*p.h*p.k-g*p.k
  let q := p.a^2-p.a+p.h^2-g*p.h
  have he (u : ℝ) : circlePower g (p.z 6+(u : ℂ)*p.R) = p.d*u^2+l*u+q := by
    simp only [circlePower_eq,z₆,R,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,d,l,q]
    ring
  have hroot : p.d*p.r^2+l*p.r+q = 0 := by
    simp only [d,l,q]
    linear_combination -hg
  have hbase : p.d*(-p.D)^2+l*(-p.D)+q = p.H*(p.H-1) := by
    rw [← he,Complex.ofReal_neg,neg_mul,← sub_eq_add_neg,hp.z₆_sub_D_R,circlePower_eq]
    simp only [Complex.ofReal_re,Complex.ofReal_im]
    ring
  have hprod : p.d*(-p.D-p.r)*(-p.D-p.t) = p.H*(p.H-1) := by
    rw [t]
    field_simp [hp.D_add_r_pos.ne',p.d_pos.ne']
    ring
  have hl : l = -(p.d*(p.r+p.t)) := by
    have hf : (p.D+p.r)*(l+p.d*(p.r+p.t)) = 0 := by
      linear_combination hroot-hbase+hprod
    linarith only [(mul_eq_zero.mp hf).resolve_left hp.D_add_r_pos.ne']
  have hq : q = p.d*p.r*p.t := by
    rw [hl] at hroot
    linear_combination hroot
  have hp3 : circlePower g (p.z 3) = 0 := by
    rw [z₃,he,hl,hq]
    ring
  have hp6 : circlePower g (p.z 6) = p.d*p.r*p.t := by
    simpa only [circlePower_eq,z₆,q] using hq
  have hp1 : circlePower g (p.z 1) = 0 := by
    have he₁ : p.z 1 = ⟨1-(p.a+p.r),p.h+p.k*p.r⟩ := by
      rw [z₁]
      congr 1
      ring
    rw [he₁,circlePower_mirror,circlePower_eq]
    linarith only [hg]
  have hi3 : 0 < (p.z 3).im := by
    simp only [z₃,z₆,R,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
    rw [← hp.mul_k_D]
    linarith only [mul_pos hp.k_pos hp.D_add_t_pos]
  have hn (v : Vertex) (hv : v = 0 ∨ v = 4 ∨ v = 1 ∨ v = 6) : p.z v ≠ p.z 3 := by
    intro hv'
    rcases hv with rfl | rfl | rfl | rfl
    · simpa [z₀,← hv'] using hi3
    · simpa [z₄,← hv'] using hi3
    · have hr := congrArg Complex.re hv'
      norm_num [z₁,z₃,z₆,R,Complex.add_re,Complex.mul_re] at hr
      linarith only [hr,ht,hp.r_neg,hp.a_lt_half]
    · have hr := congrArg Complex.re hv'
      norm_num [z₃,z₆,R,Complex.add_re,Complex.mul_re] at hr
      linarith only [hr,ht]
  have hchord (v : Vertex) (hv : v = 0 ∨ v = 4 ∨ v = 1) :
      ((p.z 3-circleCenter g)/(p.z v-p.z 3)).re = -1/2 := by
    apply circle_inverse_chord (hn v (by rcases hv with rfl | rfl | rfl <;> simp))
    rw [hp3]
    rcases hv with rfl | rfl | rfl
    · simp [z₀,circlePower_eq]
    · simp [z₄,circlePower_eq]
    · exact hp1
  have hchord6 : ((p.z 3-circleCenter g)/(p.z 6-p.z 3)).re = (-1+p.r/p.t)/2 := by
    have hdiff : Complex.normSq (p.z 6-circleCenter g)-Complex.normSq (p.z 3-circleCenter g) =
        p.d*p.r*p.t := by
      unfold circlePower at hp3 hp6
      linarith only [hp3,hp6]
    have hsq : Complex.normSq (p.z 6-p.z 3) = p.d*p.t^2 := by
      simp only [z₃,sub_add_cancel_left,Complex.normSq_neg,Complex.normSq_mul,Complex.normSq_ofReal]
      simp only [Complex.normSq_apply,R,d]
      ring
    have hratio : p.d*p.r*p.t/(p.d*p.t^2) = p.r/p.t := by
      field_simp [p.d_pos.ne',ht.ne]
    have hr := two_re_chord_quotient (p.z 3) (p.z 6) (circleCenter g) (hn 6 (by simp))
    rw [hdiff,hsq,hratio] at hr
    linarith only [hr]
  unfold balance at hc
  rw [row_3] at hc
  have heq := congrArg (fun b : ℂ => ((p.z 3-circleCenter g)*b).re) hc
  simp only [mul_add,mul_sub,Complex.add_re,Complex.sub_re,re_scaled_chord,mul_zero,
    Complex.zero_re] at heq
  rw [hchord 4 (by simp),hchord 0 (by simp),hchord 1 (by simp),hchord6] at heq
  linarith only [heq,hcircle]


private theorem div_real_re (v : ℂ) (a : ℝ) : (v/(a : ℂ)).re = v.re/a := by
  simp only [div_eq_mul_inv,← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero]

private theorem div_real_im (v : ℂ) (a : ℝ) : (v/(a : ℂ)).im = v.im/a := by
  simp only [div_eq_mul_inv,← Complex.ofReal_inv,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_add]

private theorem vertical_row (hp : p.Bounds) (ht : p.t < 0) (c : Vertex → ℝ)
    (hc : balance p.z c 6 = 0) (h0 : c 0 = 0) (hcircle : c 6+c 7 = c 4) :
    c 4 = 2*c 6+(p.b*p.D/(p.D+p.a))*(c 6/p.D+(c 3-c 6)/p.t) ∧
    c 5 = -(p.b/(p.D+p.a)*c 6)-(p.e*p.H*(p.x^2+p.y^2)/(p.D+p.a))*(c 3-c 6)/p.t := by
  let u := c 6
  let ξ := (c 3-c 6)/p.t
  let W := (u-c 7)/p.b
  have hnorm : 0 < p.D+p.a := add_pos_of_pos_of_nonneg hp.D_pos hp.a_nonneg
  have hH : (p.H : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.H_pos.ne'
  have hT : (p.t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne
  have hE : (p.e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.e_pos.ne'
  have he₀ : p.R*p.τ/(p.z 0-p.z 6) = -p.R/(p.H : ℂ) := by
    rw [z₀,z₆_eq,zero_sub]
    field_simp [hH,hp.τ_ne_zero]
  have he₃ : p.R*p.τ/(p.z 3-p.z 6) = p.τ/(p.t : ℂ) := by
    rw [z₃,add_sub_cancel_left]
    field_simp [hT,p.R_ne_zero]
  have he₅ : p.R*p.τ/(p.z 5-p.z 6) = -(1 : ℂ)/(p.e : ℂ) := by
    rw [hp.z₅_sub_z₆]
    field_simp [hE,hp.τ_ne_zero,p.R_ne_zero]
  have he₇ : p.R*p.τ/(p.z 7-p.z 6) = p.R*p.τ/(p.b : ℂ) := by rw [z₇_sub_z₆]
  unfold balance at hc
  rw [row_6] at hc
  have hi := congrArg (fun v => (p.R*p.τ*v).im) hc
  have hr := congrArg (fun v => (p.R*p.τ*v).re) hc
  simp only [mul_add,mul_sub,Complex.add_im,Complex.sub_im,im_scaled_chord,mul_zero,
    Complex.zero_im,he₀,he₃,he₅,he₇,h0,sub_zero] at hi
  simp only [mul_add,mul_sub,Complex.add_re,Complex.sub_re,re_scaled_chord,mul_zero,
    Complex.zero_re,he₀,he₃,he₅,he₇,h0,sub_zero] at hr
  simp only [div_real_re,div_real_im] at hi hr
  simp only [R,τ,Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
    Complex.one_re,Complex.one_im] at hi hr
  have hI : -u*(p.k/p.H)-ξ*p.y-W*(p.y+p.k*p.x) = 0 := by
    dsimp only [u,ξ,W]
    linear_combination hi
  have hR : -u/p.H-ξ*p.x+(u-c 5)/p.e-W*(p.x-p.k*p.y) = 0 := by
    dsimp only [u,ξ,W]
    linear_combination hr
  have hk : p.k*p.D = p.H*p.y := hp.mul_k_D
  have hkH : p.k/p.H = p.y/p.D := by
    field_simp [hp.H_pos.ne',hp.D_pos.ne']
    exact hk
  have hIx : p.y+p.k*p.x = p.y*(p.D+p.a)/p.D := by
    apply (eq_div_iff hp.D_pos.ne').mpr
    unfold a
    linear_combination p.x*hk
  have hbalance : W*(p.D+p.a) = -u-p.D*ξ := by
    have hi' : (-u-W*(p.D+p.a)-p.D*ξ)*p.y = 0 := by
      rw [hkH,hIx] at hI
      field_simp [hp.D_pos.ne'] at hI
      linear_combination hI
    linarith only [(mul_eq_zero.mp hi').resolve_right hp.y_pos.ne']
  have hW : W*p.b = u-c 7 := div_mul_cancel₀ _ hp.b_pos.ne'
  have h4 : c 4 = 2*u-p.b*W := by
    change u+c 7 = c 4 at hcircle
    linarith only [hW,hcircle]
  have hequiv : p.e*(p.D/p.H+p.k*p.y) = p.H := by
    unfold e d
    field_simp [hp.D_pos.ne',p.d_pos.ne',hp.H_pos.ne',ne_of_gt (show 0 < 1+p.k^2 by positivity)]
    linear_combination -p.k*hk
  have h₅ : (p.D+p.a)*(u-c 5) = p.H*u+p.e*p.H*(p.x^2+p.y^2)*ξ := by
    have hR' : u-c 5 = p.e*(u/p.H+ξ*p.x+W*(p.x-p.k*p.y)) := by
      linear_combination (norm := (field_simp [hp.e_pos.ne'] <;> ring)) p.e*hR
    rw [hR']
    have heq : (p.D+p.a)*(u/p.H+ξ*p.x+W*(p.x-p.k*p.y)) =
        u*(p.D/p.H+p.k*p.y)+ξ*p.H*(p.x^2+p.y^2) := by
      have hxa : p.a/p.H = p.x := by unfold a; field_simp [hp.H_pos.ne']
      have ha : p.a = p.H*p.x := rfl
      linear_combination (p.x-p.k*p.y)*hbalance+p.y*ξ*hk+u*hxa+p.x*ξ*ha
    rw [mul_left_comm,heq]
    linear_combination u*hequiv
  constructor
  · have hb : W = (-u-p.D*ξ)/(p.D+p.a) := (eq_div_iff hnorm.ne').mpr hbalance
    rw [h4,hb]
    dsimp only [u,ξ]
    field_simp [hnorm.ne',hp.D_pos.ne']
    ring
  · have hsum : p.D+p.a-p.H = -p.b := by unfold D b; ring
    have hnum : c 5*(p.D+p.a) = -p.b*u-p.e*p.H*(p.x^2+p.y^2)*ξ := by
      linear_combination -h₅+u*hsum
    rw [(eq_div_iff hnorm.ne').mpr hnum]
    dsimp only [u,ξ]
    ring


open Type7 (normalizedChord chord_normalization normalizedChord_zero normalizedChord_one)

private theorem last_row (hp : p.Bounds) (hs : 0 < p.s) (c : Vertex → ℝ)
    (hc : balance p.z c 5 = 0) (hcircle : c 6+c 7 = c 0+c 4) :
    (1+p.d*p.D*p.s/(p.D+p.a)+p.H*p.s/p.e)*c 5 =
      c 4+p.d*p.D*p.s/(p.D+p.a)*c 7+p.H*p.s/p.e*c 6 := by
  have hn (v : Vertex) (hv : v = 0 ∨ v = 4 ∨ v = 6 ∨ v = 7) : p.z v ≠ p.z 5 := by
    intro he
    have hr := congrArg Complex.re he
    rcases hv with rfl | rfl | rfl | rfl <;>
      norm_num [z₀,z₄,z₅,z₆,z₇,R,Complex.add_re,Complex.mul_re] at hr <;>
      linarith only [hr,hs,hp.a_nonneg,hp.a_lt_half]
  have hnum : 1-p.z 5 = -(p.s : ℂ)*p.R := by rw [z₅]; ring
  have h65 : p.z 6-p.z 5 = (p.e : ℂ)*p.τ*p.R := by
    rw [← neg_sub, hp.z₅_sub_z₆]
    ring
  have hZ7 : normalizedChord (p.z 5) (p.z 7) = -(p.d*p.D*p.s/(p.D+p.a) : ℝ) := by
    have hda := add_pos_of_pos_of_nonneg hp.D_pos hp.a_nonneg
    have hdaC : (p.D : ℂ)+(p.a : ℂ) ≠ 0 := by exact_mod_cast hda.ne'
    unfold normalizedChord
    apply (div_eq_iff (sub_ne_zero.mpr (hn 7 (by simp)))).mpr
    rw [hnum,hp.z₇_sub_z₅]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hp.D_pos.ne',
      Complex.ofReal_ne_zero.mpr p.d_pos.ne',hdaC] <;> ring
  have hZ6 : normalizedChord (p.z 5) (p.z 6) = -(p.H*p.s/p.e : ℝ) := by
    unfold normalizedChord
    apply (div_eq_iff (sub_ne_zero.mpr (hn 6 (by simp)))).mpr
    rw [hnum,h65,z₆_eq]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hp.e_pos.ne'] <;> ring
  have hn1 : p.z 5 ≠ 1 := by simpa only [z₄] using (hn 4 (by simp)).symm
  unfold balance at hc
  rw [row_5] at hc
  have hre := congrArg (fun b : ℂ => ((p.z 5*(1-p.z 5))*b).re) hc
  simp only [mul_add,mul_sub,Complex.add_re,Complex.sub_re,re_scaled_chord,mul_zero,
    Complex.zero_re] at hre
  rw [← mul_sub (p.z 5) 1 (p.z 5),chord_normalization (hn 7 (by simp)),chord_normalization (hn 6 (by simp)),
    chord_normalization (hn 4 (by simp)),chord_normalization (hn 0 (by simp)),hZ7,hZ6] at hre
  rw [z₀,z₄,normalizedChord_zero,normalizedChord_one hn1] at hre
  simp only [z₅,R,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.neg_re,Complex.one_re,Complex.one_im,Complex.zero_re,one_mul,mul_one,mul_zero,sub_zero] at hre
  linear_combination -hre-p.s*hcircle


private def M (p : TrapezoidChart) : ℝ := (p.a*(1-p.a)+p.h^2+p.h*p.k*p.b)/p.d
private def L (p : TrapezoidChart) : ℝ := 2*p.a*p.H/(p.D+p.a)
private def α (p : TrapezoidChart) : ℝ := p.b*p.D/(p.D+p.a)
private def K (p : TrapezoidChart) : ℝ := p.D+p.r+(p.D*p.r-M p-(p.H-1)*α p)/p.t

private theorem M_pos (hp : p.Bounds) : 0 < M p := by
  have ha : 0 ≤ 1-p.a := by linarith only [hp.a_lt_half]
  exact div_pos (add_pos (add_pos_of_nonneg_of_pos (mul_nonneg hp.a_nonneg ha)
    (sq_pos_of_pos hp.h_pos)) (mul_pos (mul_pos hp.h_pos hp.k_pos) hp.b_pos)) p.d_pos

private theorem normalized_at_three (hp : p.Bounds) (hne : p.z 3 ≠ p.z 1) :
    normalizedChord (p.z 1) (p.z 3) = -(p.H-1 : ℝ) := by
  have h₃ : p.z 3 = ((1-p.H : ℝ) : ℂ)+((p.D+p.t : ℝ) : ℂ)*p.R := by
    rw [z₃,← hp.z₆_sub_D_R]
    push_cast
    ring
  have hprod : (p.D+p.t)*(p.D+p.r)*p.d = p.H*(p.H-1) := by
    rw [t]
    field_simp [hp.D_add_r_pos.ne',p.d_pos.ne']
    ring
  have hprodC : ((p.D+p.t : ℝ) : ℂ)*((p.D+p.r : ℝ) : ℂ)*(p.d : ℂ) =
      (p.H : ℂ)*((p.H : ℂ)-1) := by exact_mod_cast hprod
  have h₁ : (p.H : ℂ)-p.z 1 = ((p.D+p.r : ℝ) : ℂ)*(starRingEnd ℂ) p.R := by
    rw [hp.z₁_eq]
    ring
  have he : (p.R*((p.H : ℂ)-p.z 1)) = ((p.D+p.r : ℝ) : ℂ)*(p.d : ℂ) := by
    rw [h₁,← mul_left_comm,R_mul_conj]
  have hrel : p.z 3*((p.H : ℂ)-p.z 1) = ((p.H : ℂ)-1)*p.z 1 := by
    conv_lhs => rw [h₃,add_mul,mul_assoc,he,← mul_assoc,hprodC]
    push_cast
    ring
  unfold normalizedChord
  apply (div_eq_iff (sub_ne_zero.mpr hne)).mpr
  push_cast
  linear_combination hrel

private theorem normalized_at_seven (hp : p.Bounds) (hne : p.z 7 ≠ p.z 1) :
    (normalizedChord (p.z 1) (p.z 7)).re = 1-p.a+M p/p.r := by
  have hn : (p.r : ℂ)*(starRingEnd ℂ) p.R ≠ 0 := by
    rw [← z₇_sub_z₁]
    exact sub_ne_zero.mpr hne
  have he : normalizedChord (p.z 1) (p.z 7) =
      p.z 7+(p.z 7*(1-p.z 7)*p.R)/((p.r : ℂ)*(p.d : ℂ)) := by
    have hnum : 1-p.z 1 = 1-p.z 7 + ((p.r : ℂ)*(starRingEnd ℂ) p.R) := by
      rw [← z₇_sub_z₁]
      ring
    rw [normalizedChord,hnum,z₇_sub_z₁,mul_add,add_div,mul_div_cancel_right₀ _ hn,add_comm]
    apply congrArg (fun u : ℂ => p.z 7+u)
    apply (div_eq_div_iff hn (mul_ne_zero (Complex.ofReal_ne_zero.mpr hp.r_neg.ne)
      (Complex.ofReal_ne_zero.mpr p.d_pos.ne'))).mpr
    rw [show p.z 7*(1-p.z 7)*p.R*((p.r : ℂ)*(starRingEnd ℂ) p.R) =
      p.z 7*(1-p.z 7)*((p.r : ℂ)*(p.R*(starRingEnd ℂ) p.R)) by ring, R_mul_conj]
  rw [he,← Complex.ofReal_mul,Complex.add_re,div_real_re]
  simp only [z₇,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    R,Complex.one_re,Complex.one_im,M,b]
  ring

private theorem coupled_row (hp : p.Bounds) (ht : p.t < 0) (c : Vertex → ℝ)
    (hc : balance p.z c 1 = 0) (h0 : c 0 = 0) (h7 : c 6+c 7 = c 4)
    (h1 : c 1-c 7 = -(p.r/p.t)*(c 3-c 6))
    (h4 : c 4 = 2*c 6+α p*(c 6/p.D+(c 3-c 6)/p.t)) :
    L p*c 6+K p*(c 3-c 6) = 0 := by
  have hn (v : Vertex) (hv : v = 0 ∨ v = 4 ∨ v = 3 ∨ v = 7) : p.z v ≠ p.z 1 := by
    intro he
    rcases hv with rfl | rfl | rfl | rfl
    · have hi := congrArg Complex.im he
      norm_num [z₀,z₁] at hi
      exact hp.h_add_kr_pos.ne' hi.symm
    · have hi := congrArg Complex.im he
      norm_num [z₄,z₁] at hi
      exact hp.h_add_kr_pos.ne' hi.symm
    · have hr := congrArg Complex.re he
      norm_num [z₃,z₆,z₁,R,Complex.add_re,Complex.mul_re] at hr
      linarith only [hr,ht,hp.r_neg,hp.a_lt_half]
    · have hr := congrArg Complex.re he
      norm_num [z₇,z₁] at hr
      linarith only [hr,hp.r_neg]
  have hn1 : p.z 1 ≠ 1 := by simpa only [z₄] using (hn 4 (by simp)).symm
  have hp3 := normalized_at_three hp (hn 3 (by simp))
  have hp7 := normalized_at_seven hp (hn 7 (by simp))
  unfold balance at hc
  rw [row_1] at hc
  have hre := congrArg (fun b : ℂ => ((p.z 1*(1-p.z 1))*b).re) hc
  simp only [mul_add,mul_sub,Complex.add_re,Complex.sub_re,re_scaled_chord,mul_zero,
    Complex.zero_re] at hre
  rw [← mul_sub (p.z 1) 1 (p.z 1),chord_normalization (hn 3 (by simp)),
    chord_normalization (hn 7 (by simp)),chord_normalization (hn 0 (by simp)),
    chord_normalization (hn 4 (by simp)),hp3,hp7,z₀,z₄,normalizedChord_zero,normalizedChord_one hn1] at hre
  norm_num [z₁,h0] at hre
  let u := c 6
  let X := c 3-c 6
  let ξ := X/p.t
  have h17 : c 1-c 7 = -p.r*ξ := by
    rw [h1]
    dsimp only [ξ,X]
    ring
  have h13 : c 1-c 3 = α p*(u/p.D+ξ)-p.r*ξ-X := by
    dsimp only [u,ξ,X] at h17 ⊢
    linarith only [h17,h7,h4]
  have h14 : c 1-c 4 = -u-p.r*ξ := by
    dsimp only [u]
    linarith only [h17,h7]
  have hproj : (p.a+p.r)*X-(p.H-1)*(c 1-c 3) +
      (1-p.a+M p/p.r)*(c 1-c 7)-(c 1-c 4) = 0 := by
    dsimp only [X]
    linear_combination hre-(p.a+p.r)*h7
  rw [h13,h17,h14] at hproj
  have hM : (M p/p.r)*p.r = M p := div_mul_cancel₀ _ hp.r_neg.ne
  have hα : α p/p.D = p.b/(p.D+p.a) := by
    unfold α
    field_simp [hp.D_pos.ne']
  have hL : L p = 1-(p.H-1)*(α p/p.D) := by
    rw [hα,L]
    field_simp [(add_pos_of_pos_of_nonneg hp.D_pos hp.a_nonneg).ne']
    simp only [D,b]
    ring
  change L p*u+K p*X = 0
  rw [K,hL]
  have hD : p.D = p.H-1+p.a := rfl
  calc
    _ = (p.a+p.r)*X-(p.H-1)*(α p*(u/p.D+ξ)-p.r*ξ-X) +
          (1-p.a+M p/p.r)*(-p.r*ξ)-(-u-p.r*ξ) := by
      change _ =
        (p.a+p.r)*X-(p.H-1)*(α p*(u/p.D+ξ)-p.r*ξ-X) +
          (1-p.a+M p/p.r)*(-p.r*ξ)-(-u-p.r*ξ)
      simp only [hD,ξ,div_eq_mul_inv] at hM ⊢
      linear_combination X*p.t⁻¹*hM
    _ = 0 := hproj

end OrigamiTorus.Type4.TrapezoidChart

namespace OrigamiTorus.Type4

open Type7 (balance balance_subtract_constant)

namespace TrapezoidChart

variable {p : TrapezoidChart}

private theorem normalized_balance_zero (hp : p.Bounds) (hs : 0 < p.s) (ht : p.t < 0)
    (c : Vertex → ℝ) (h0 : c 0 = 0) (hc : ∀ v, balance p.z c v = 0) : c = 0 := by
  have h2 := horizontal_row c (hc 2)
  have hcircle := first_circle_row hp hs c (hc 5)
  have h1 := second_circle_row hp ht c (hc 3) hcircle
  have h7 : c 6+c 7 = c 4 := by simpa only [h0,zero_add] using hcircle
  obtain ⟨h4,h5⟩ := vertical_row hp ht c (hc 6) h0 h7
  have hcouple := coupled_row hp ht c (hc 1) h0 h7 h1 h4
  have hlast := last_row hp hs c (hc 5) hcircle
  have hda := add_pos_of_pos_of_nonneg hp.D_pos hp.a_nonneg
  have hL : 0 ≤ L p := by
    unfold L
    positivity [hp.a_nonneg,hp.H_pos,hda]
  have hα : 0 < α p := div_pos (mul_pos hp.b_pos hp.D_pos) hda
  have hK : 0 < K p := by
    unfold K
    have hnum : p.D*p.r-M p-(p.H-1)*α p < 0 := by
      linarith only [mul_neg_of_pos_of_neg hp.D_pos hp.r_neg,M_pos hp,
        mul_pos (sub_pos.mpr hp.height) hα]
    exact add_pos hp.D_add_r_pos (div_pos_of_neg_of_neg hnum ht)
  have hτ : 0 < p.x^2+p.y^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hp.y_pos)
  exact reduced_balances_force_zero c p.D p.t p.r (L p) (K p) (α p) (p.b/(p.D+p.a))
    (p.e*p.H*(p.x^2+p.y^2)/(p.D+p.a)) (p.d*p.D*p.s/(p.D+p.a)) (p.H*p.s/p.e)
    hp.D_pos ht hL hK hα (div_pos hp.b_pos hda)
    (div_pos (mul_pos (mul_pos hp.e_pos hp.H_pos) hτ) hda)
    (div_pos (mul_pos (mul_pos p.d_pos hp.D_pos) hs) hda)
    (div_pos (mul_pos hp.H_pos hs) hp.e_pos) h0
    (by simpa only [h0,zero_add] using h2) h1 h7 hcouple h4 h5 hlast

end TrapezoidChart

/-- Throughout both trapezoidal charts, the only left dependences of the
horizontal cone-angle differential are constant. -/
theorem trapezoid_angle_dependence_constant {second : Bool} {x w : ℝ}
    (hd : domain second x w) (c : Vertex → ℝ) :
    let p := polynomialPoints x w (if second then 2/3 else 1/3) (trapezoidHeight second x) 1
    let z := Type7.physicalComplex w ∘ p
    (∀ δ : Vertex → ℂ, (∑ v, c v * deriv (fun t : ℝ =>
      (Type7.orientedFaces.map (fun f => chartEuclideanCorner (fun j => z j+t • δ j) v f.1)).sum) 0) = 0) ↔
      ∀ v, c v = c 0 := by
  refine (trapezoid_cone_angle_left_kernel hd c).trans ?_
  let p := TrapezoidChart.mk x (Real.sqrt w) (trapezoidHeight second x) (if second then 2/3 else 1/3)
  have hp : p.Bounds := TrapezoidChart.ofDomain_bounds hd
  have hs : 0 < p.s := by
    apply hp.s_pos
    change 1 ≤ x^2+(Real.sqrt w)^2
    rw [Real.sq_sqrt (domain_bounds hd).2.2.le]
    linarith only [hd.2.2]
  have ht : p.t < 0 := TrapezoidChart.ofDomain_t_neg hd
  constructor
  · intro hc
    let n : Vertex → ℝ := fun v => c v-c 0
    have hbal (v : Vertex) : balance p.z n v = 0 := by
      rw [balance_subtract_constant p.z c v (c 0)]
      apply (inverseChordBalance_mul_eq_zero_iff _ _ _ v (p.Q : ℂ)
        (Complex.ofReal_ne_zero.mpr hp.Q_pos.ne')).mp
      have he : (fun j => (p.Q : ℂ)*p.z j) = Type7.physicalComplex w ∘ polynomialPoints x w p.cut p.H 1 := by
        funext j
        exact (TrapezoidChart.scaled_chart hd j).symm
      rw [he]
      exact hc v
    have he := TrapezoidChart.normalized_balance_zero hp hs ht n (sub_self _) hbal
    intro v
    exact sub_eq_zero.mp (congrFun he v)
  · intro hc v
    unfold inverseChordBalance
    simp [hc]

theorem trapezoid_corners_nondegenerate {second : Bool} {x w : ℝ} (hd : domain second x w) :
    let p := polynomialPoints x w (if second then 2/3 else 1/3) (trapezoidHeight second x) 1
    let z := Type7.physicalComplex w ∘ p
    ∀ f ∈ Type7.faces, ∀ v a b, cornerRays v f = some (a,b) →
      z a ≠ z v ∧ z b ≠ z v ∧ 0 < InnerProductGeometry.angle (z a-z v) (z b-z v) ∧
        InnerProductGeometry.angle (z a-z v) (z b-z v) < Real.pi := by
  have hfaces : Type7.orientedFaces.map Prod.fst = Type7.faces := by decide +kernel
  rw [← hfaces]
  apply planarCorners_nondegenerate_of_face_areas Type7.orientedFaces _ w (domain_bounds hd).2.2
  intro f hf
  have hs := poly_chart_face_signs hd f hf
  cases he : f.2
  · simpa [he,neg_pos] using hs
  · simpa [he] using hs

/-- Both Type 4 charts have rank seven in the independent horizontal cone angles. -/
theorem trapezoid_seven_cone_derivative_surjective {second : Bool} {x w : ℝ} (hd : domain second x w) :
    let p := polynomialPoints x w (if second then 2/3 else 1/3) (trapezoidHeight second x) 1
    let z := Type7.physicalComplex w ∘ p
    Function.Surjective (fderiv ℝ (sevenConeAngles Type7.faces : (Vertex → ℂ) → Fin 7 → ℝ) z) :=
  Type7.seven_cone_derivative_surjective _ (trapezoid_corners_nondegenerate hd)
    (fun c => (trapezoid_angle_dependence_constant hd c).mp)

end OrigamiTorus.Type4
