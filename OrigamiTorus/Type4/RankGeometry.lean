module

public import OrigamiTorus.Geometry.AngleRank
import Mathlib.Tactic

/-! The unscaled complex trapezoid chart and its chord identities. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type4

structure TrapezoidChart where
  x : ℝ
  y : ℝ
  H : ℝ
  cut : ℝ

namespace TrapezoidChart

variable (p : TrapezoidChart)

def a : ℝ := p.H*p.x
def D : ℝ := p.H-1+p.a
def h : ℝ := p.H*p.y
def k : ℝ := p.h/p.D
def d : ℝ := 1+p.k^2
def r : ℝ := -p.cut*p.D
def b : ℝ := 1-2*p.a
def e : ℝ := p.H^2/(p.D*p.d)
def s : ℝ := ((p.a^2-p.a+p.h^2)/p.D-1)/p.d
def t : ℝ := -p.D+p.H*(p.H-1)/((p.D+p.r)*p.d)
def R : ℂ := ⟨1,p.k⟩
def τ : ℂ := ⟨p.x,p.y⟩

def z : Vertex → ℂ :=
  ![0, ⟨1-p.a-p.r,p.h+p.k*p.r⟩, 1/2, (⟨p.a,p.h⟩ : ℂ)+(p.t : ℂ)*p.R,
    1, 1+(p.s : ℂ)*p.R, ⟨p.a,p.h⟩, ⟨1-p.a,p.h⟩]

structure Bounds : Prop where
  height : 1 < p.H
  x_nonneg : 0 ≤ p.x
  y_pos : 0 < p.y
  a_lt_half : p.a < 1/2
  cut_pos : 0 < p.cut
  cut_lt_one : p.cut < 1

variable {p}

theorem Bounds.H_pos (hp : p.Bounds) : 0 < p.H := zero_lt_one.trans hp.height
theorem Bounds.a_nonneg (hp : p.Bounds) : 0 ≤ p.a := mul_nonneg hp.H_pos.le hp.x_nonneg

theorem Bounds.D_pos (hp : p.Bounds) : 0 < p.D :=
  add_pos_of_pos_of_nonneg (sub_pos.mpr hp.height) hp.a_nonneg

theorem Bounds.h_pos (hp : p.Bounds) : 0 < p.h := mul_pos hp.H_pos hp.y_pos
theorem Bounds.k_pos (hp : p.Bounds) : 0 < p.k := div_pos hp.h_pos hp.D_pos
theorem d_pos (p : TrapezoidChart) : 0 < p.d := by unfold d; positivity
theorem Bounds.r_neg (hp : p.Bounds) : p.r < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hp.cut_pos) hp.D_pos

theorem D_add_r (p : TrapezoidChart) : p.D+p.r = (1-p.cut)*p.D := by unfold r; ring

theorem Bounds.D_add_r_pos (hp : p.Bounds) : 0 < p.D+p.r := by
  rw [D_add_r]
  exact mul_pos (sub_pos.mpr hp.cut_lt_one) hp.D_pos

theorem Bounds.b_pos (hp : p.Bounds) : 0 < p.b := by
  unfold b
  linarith only [hp.a_lt_half]

theorem Bounds.e_pos (hp : p.Bounds) : 0 < p.e :=
  div_pos (sq_pos_of_pos hp.H_pos) (mul_pos hp.D_pos p.d_pos)

theorem Bounds.D_add_t_pos (hp : p.Bounds) : 0 < p.D+p.t := by
  have he : p.D+p.t = p.H*(p.H-1)/((p.D+p.r)*p.d) := by unfold t; ring
  rw [he]
  exact div_pos (mul_pos hp.H_pos (sub_pos.mpr hp.height)) (mul_pos hp.D_add_r_pos p.d_pos)

theorem Bounds.mul_k_D (hp : p.Bounds) : p.k*p.D = p.h := div_mul_cancel₀ _ hp.D_pos.ne'

theorem Bounds.h_add_kr_pos (hp : p.Bounds) : 0 < p.h+p.k*p.r := by
  rw [← hp.mul_k_D, ← mul_add]
  exact mul_pos hp.k_pos hp.D_add_r_pos

theorem Bounds.s_pos (hp : p.Bounds) (hy : 1 ≤ p.x^2+p.y^2) : 0 < p.s := by
  have hnorm : p.H^2 ≤ p.a^2+p.h^2 := by
    unfold a h
    nlinarith only [mul_nonneg (sq_nonneg p.H) (sub_nonneg.mpr hy)]
  unfold s
  apply div_pos _ p.d_pos
  apply sub_pos.mpr
  apply (lt_div_iff₀ hp.D_pos).mpr
  unfold D
  nlinarith only [hnorm, hp.a_lt_half, mul_pos hp.H_pos (sub_pos.mpr hp.height)]

theorem ofDomain_bounds {second : Bool} {x w : ℝ} (hd : domain second x w) :
    (TrapezoidChart.mk x (Real.sqrt w) (trapezoidHeight second x) (if second then 2/3 else 1/3)).Bounds := by
  obtain ⟨hx,_,hw⟩ := domain_bounds hd
  refine ⟨height_gt_one hd,hx,Real.sqrt_pos.2 hw,height_mul_lt_half hd,?_,?_⟩ <;>
    cases second <;> norm_num

def Q : ℝ := p.D^2+p.h^2

theorem Bounds.Q_pos (hp : p.Bounds) : 0 < p.Q :=
  add_pos_of_pos_of_nonneg (sq_pos_of_pos hp.D_pos) (sq_nonneg p.h)

theorem Bounds.d_mul_D_sq (hp : p.Bounds) : p.d*p.D^2 = p.Q := by
  unfold d k Q
  field_simp [hp.D_pos.ne']

theorem Bounds.s_mul_Q (hp : p.Bounds) :
    p.s*p.Q = p.D*(p.a^2-p.a+p.h^2-p.D) := by
  rw [← hp.d_mul_D_sq]
  unfold s
  field_simp [p.d_pos.ne',hp.D_pos.ne']

theorem Bounds.t_mul_Q (hp : p.Bounds) :
    p.t*p.Q = p.D*(p.H*(p.H-1)/(1-p.cut)-p.Q) := by
  rw [← hp.d_mul_D_sq]
  unfold t
  rw [D_add_r]
  field_simp [p.d_pos.ne',hp.D_pos.ne',sub_ne_zero.mpr hp.cut_lt_one.ne'] <;> ring

theorem scaled_chart {second : Bool} {x w : ℝ} (hd : domain second x w) (v : Vertex) :
    let p := TrapezoidChart.mk x (Real.sqrt w) (trapezoidHeight second x) (if second then 2/3 else 1/3)
    Type7.physicalComplex w (polynomialPoints x w p.cut p.H 1 v) = (p.Q : ℂ)*p.z v := by
  let p := TrapezoidChart.mk x (Real.sqrt w) (trapezoidHeight second x) (if second then 2/3 else 1/3)
  have hp : p.Bounds := ofDomain_bounds hd
  have hh : p.h^2 = p.H^2*w := by
    unfold h
    rw [mul_pow]
    exact congrArg (p.H^2 * ·) (Real.sq_sqrt (domain_bounds hd).2.2.le)
  have hc : 1-p.cut ≠ 0 := sub_ne_zero.mpr hp.cut_lt_one.ne'
  have hr : p.r = -p.cut*p.D := rfl
  have hs := hp.s_mul_Q
  have ht := hp.t_mul_Q
  have hk := hp.mul_k_D
  have hS :
      ((p.a^2-p.a-(1-p.cut)*p.h^2)-p.D*(2*p.a-p.cut*p.D-1))/(1-p.cut) =
        p.H*(p.H-1)/(1-p.cut)-p.Q := by
    rw [Q]
    field_simp [hc]
    unfold D
    ring
  have him (u : ℝ) : Real.sqrt w * (p.H * u) = p.h*u := by
    change Real.sqrt w*(p.H*u) = (p.H*Real.sqrt w)*u
    ring
  have h₃ : p.k*(p.t*p.Q) = p.h*(p.H*(p.H-1)/(1-p.cut)-p.Q) := by
    rw [ht,← mul_assoc,hk]
  have h₅ : p.k*(p.s*p.Q) = p.h*(p.a^2-p.a+p.h^2-p.D) := by
    rw [hs,← mul_assoc,hk]
  change Type7.physicalComplex w (polynomialPoints x w p.cut p.H 1 v) = (p.Q : ℂ)*p.z v
  fin_cases v <;> apply Complex.ext <;>
    norm_num [Type7.physicalComplex,polynomialPoints,z,R,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im,Complex.div_re,Complex.div_im,Complex.normSq_apply,
      show p.H*x = p.a by rfl,show p.H-1+p.a = p.D by rfl,← hh,show p.D^2+p.h^2 = p.Q by rfl,hr]
  all_goals try rw [mul_assoc (1-p.cut), ← hh]
  all_goals try rw [hS]
  all_goals try rw [mul_add,him,him]
  all_goals try rw [mul_comm (1-p.cut) p.H,mul_assoc p.H,him]
  all_goals try rw [him]
  all_goals
    first | (ring; done) | linear_combination -ht | linear_combination -hs |
      linear_combination -h₃ | linear_combination -h₅ | linear_combination p.cut*p.Q*hk

theorem Bounds.t_neg (hp : p.Bounds) (hheight : p.H-1 < (1-p.cut)*p.H*p.y^2) :
    p.t < 0 := by
  have hprod := mul_lt_mul_of_pos_left hheight hp.H_pos
  have hd := hp.d_mul_D_sq
  have he : (p.D+p.r)*p.d*p.D = (1-p.cut)*p.Q := by
    rw [D_add_r, ← hd]
    ring
  have hQ : (1-p.cut)*p.h^2 ≤ (1-p.cut)*p.Q := by
    unfold Q
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg p.D)) (sub_nonneg.mpr hp.cut_lt_one.le)
  have h : p.H*(p.H-1) < (p.D+p.r)*p.d*p.D := by
    rw [he]
    unfold TrapezoidChart.h at hQ
    nlinarith only [hprod,hQ]
  unfold t
  rw [neg_add_lt_iff_lt_add,add_zero]
  exact (div_lt_iff₀ (mul_pos hp.D_add_r_pos p.d_pos)).mpr (by simpa only [mul_comm p.D] using h)

theorem ofDomain_t_neg {second : Bool} {x w : ℝ} (hd : domain second x w) :
    (TrapezoidChart.mk x (Real.sqrt w) (trapezoidHeight second x) (if second then 2/3 else 1/3)).t < 0 := by
  obtain ⟨hx,hx',hw⟩ := domain_bounds hd
  have hw' : 3/4 < w := by
    nlinarith only [hd.2.2,mul_pos (sub_pos.mpr hx') (show 0 < 1/2+x by linarith)]
  apply (ofDomain_bounds hd).t_neg
  dsimp only
  rw [Real.sq_sqrt hw.le]
  have hH : 0 < trapezoidHeight second x := zero_lt_one.trans (height_gt_one hd)
  cases second
  · norm_num only [Bool.false_eq_true,if_false]
    have hmax : trapezoidHeight false x < 2 := by
      simp [trapezoidHeight]
      apply (div_lt_iff₀ (by linarith)).mpr
      linarith
    nlinarith only [mul_pos hH (sub_pos.mpr hw'),hmax]
  · norm_num only [if_true]
    have hlow : (9/20 : ℝ) ≤ x := hd.1
    have hmax : trapezoidHeight true x < 4/3 := by
      simp [trapezoidHeight]
      nlinarith only [mul_nonneg (show 0 ≤ (1:ℝ)/10-(1-2*x) by linarith)
        (show 0 ≤ (1:ℝ)/10+(1-2*x) by linarith)]
    nlinarith only [mul_pos hH (sub_pos.mpr hw'),hmax]

theorem z₀ (p : TrapezoidChart) : p.z 0 = 0 := rfl
theorem z₁ (p : TrapezoidChart) : p.z 1 = ⟨1-p.a-p.r,p.h+p.k*p.r⟩ := rfl
theorem z₂ (p : TrapezoidChart) : p.z 2 = 1/2 := rfl
theorem z₄ (p : TrapezoidChart) : p.z 4 = 1 := rfl
theorem z₅ (p : TrapezoidChart) : p.z 5 = 1+(p.s : ℂ)*p.R := rfl
theorem z₆ (p : TrapezoidChart) : p.z 6 = ⟨p.a,p.h⟩ := rfl
theorem z₇ (p : TrapezoidChart) : p.z 7 = ⟨1-p.a,p.h⟩ := rfl
theorem z₃ (p : TrapezoidChart) : p.z 3 = p.z 6+(p.t : ℂ)*p.R := rfl

theorem R_ne_zero (p : TrapezoidChart) : p.R ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  norm_num [R] at he

theorem Bounds.τ_ne_zero (hp : p.Bounds) : p.τ ≠ 0 := by
  intro h
  have he := congrArg Complex.im h
  exact hp.y_pos.ne' he

theorem z₆_eq (p : TrapezoidChart) : p.z 6 = (p.H : ℂ)*p.τ := by
  apply Complex.ext <;> simp [z₆,a,h,τ,Complex.mul_re,Complex.mul_im]

theorem Bounds.z₆_sub_D_R (hp : p.Bounds) : p.z 6-(p.D : ℂ)*p.R = (1-p.H : ℝ) := by
  apply Complex.ext
  · simp [z₆,R,Complex.sub_re,Complex.mul_re,D]
  · simp [z₆,R,Complex.sub_im,Complex.mul_im,mul_comm p.D p.k,hp.mul_k_D]

theorem Bounds.z₁_eq (hp : p.Bounds) : p.z 1 = (p.H : ℂ)-((p.D+p.r : ℝ) : ℂ)*(starRingEnd ℂ) p.R := by
  have hk := hp.mul_k_D
  apply Complex.ext
  · simp [z₁,R,Complex.sub_re,Complex.mul_re,D]
    ring
  · simp [z₁,R,Complex.sub_im,Complex.mul_im]
    linear_combination -hk

theorem z₇_sub_z₁ (p : TrapezoidChart) : p.z 7-p.z 1 = (p.r : ℂ)*(starRingEnd ℂ) p.R := by
  apply Complex.ext <;> simp [z₁,z₇,R,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im] <;> ring

theorem z₇_sub_z₆ (p : TrapezoidChart) : p.z 7-p.z 6 = (p.b : ℂ) := by
  apply Complex.ext <;> simp [z₆,z₇,b,Complex.sub_re,Complex.sub_im] <;> ring

theorem R_mul_conj (p : TrapezoidChart) : p.R*(starRingEnd ℂ) p.R = (p.d : ℂ) := by
  apply Complex.ext <;>
    simp only [R,d,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im] <;> ring

theorem Bounds.z₅_sub_z₆ (hp : p.Bounds) :
    p.z 5-p.z 6 = -(p.e : ℂ)*p.τ*p.R := by
  apply Complex.ext <;>
    simp only [z₅,z₆,R,τ,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
      Complex.add_re,Complex.add_im,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.one_re,Complex.one_im] <;>
    unfold s e <;> field_simp [hp.D_pos.ne',p.d_pos.ne'] <;>
    rw [d,k] <;> field_simp [hp.D_pos.ne'] <;> simp only [D,a,h] <;> ring

theorem Bounds.z₇_sub_z₅ (hp : p.Bounds) :
    p.z 7-p.z 5 = (((p.D+p.a)/(p.D*p.d) : ℝ) : ℂ)*p.z 7*p.R := by
  apply Complex.ext <;>
    simp only [z₅,z₇,R,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
      Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.one_re,Complex.one_im] <;>
    unfold s <;> field_simp [hp.D_pos.ne',p.d_pos.ne'] <;>
    rw [d,k] <;> field_simp [hp.D_pos.ne'] <;> ring

end TrapezoidChart

end OrigamiTorus.Type4
