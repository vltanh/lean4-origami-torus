module

public import OrigamiTorus.FaceDevelopment
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-! Complex affine transitions between developed triangles. -/

@[expose] public section

namespace OrigamiTorus

abbrev ComplexMotion := ℂ ≃ᵃ[ℂ] ℂ

namespace ComplexMotion

/-- The complex factor by which the affine map rotates and scales differences. -/
def multiplier (g : ComplexMotion) : ℂ := g.linear 1

theorem linear_apply (g : ComplexMotion) (z : ℂ) : g.linear z = multiplier g*z := by
  have h := g.linear.map_smul z (1 : ℂ)
  simpa [smul_eq_mul,multiplier,mul_comm] using h

theorem apply_eq (g : ComplexMotion) (z : ℂ) : g z = multiplier g*z+g 0 := by
  have h := g.map_vadd (0 : ℂ) z
  change g (z+0) = g.linear z+g 0 at h
  simpa only [add_zero,linear_apply] using h

theorem apply_sub (g : ComplexMotion) (z w : ℂ) :
    g z-g w = multiplier g*(z-w) := by
  rw [apply_eq g z,apply_eq g w]
  ring

@[simp] theorem multiplier_one : multiplier 1 = 1 := rfl

@[simp] theorem multiplier_mul (g h : ComplexMotion) :
    multiplier (g*h) = multiplier g*multiplier h := by
  change g.linear (h.linear 1) = _
  exact linear_apply g _

/-- An affine motion is determined by its action on the two endpoints of an edge. -/
theorem eq_of_eq_two_points {g h : ComplexMotion} {a b : ℂ} (hab : b ≠ a)
    (ha : g a = h a) (hb : g b = h b) : g = h := by
  have hm : multiplier g = multiplier h := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hab)
    rw [← apply_sub,← apply_sub,hb,ha]
  have hv : g 0 = h 0 := by
    rw [apply_eq g a,apply_eq h a,hm] at ha
    exact add_left_cancel ha
  ext z
  rw [apply_eq g z,apply_eq h z,hm,hv]

theorem eq_one_of_multiplier_one_of_fixed {g : ComplexMotion} (hm : multiplier g = 1)
    {z : ℂ} (hz : g z = z) : g = 1 := by
  have hv : g 0 = 0 := by
    rw [apply_eq g z,hm,one_mul] at hz
    exact add_left_cancel (hz.trans (add_zero z).symm)
  ext w
  rw [apply_eq g w,hm,hv,one_mul,add_zero]
  rfl

/-- A direct affine similarity with a nonidentity linear part has one fixed center. -/
theorem existsUnique_fixed_of_multiplier_ne_one (g : ComplexMotion) (hm : multiplier g ≠ 1) :
    ∃! z, g z = z := by
  let m := multiplier g
  let c := g 0/(1-m)
  have hm' : 1-m ≠ 0 := sub_ne_zero.mpr hm.symm
  have he : (1-m)*c = g 0 := by
    dsimp only [c]
    rw [mul_comm,div_mul_cancel₀ _ hm']
  refine ⟨c,?_,?_⟩
  · change g c = c
    rw [apply_eq]
    change m*c+g 0 = c
    linear_combination -he
  · intro w hw
    rw [apply_eq] at hw
    apply mul_left_cancel₀ hm'
    change (1-m)*w = (1-m)*c
    rw [he]
    change m*w+g 0 = w at hw
    linear_combination -hw

theorem fixes_of_commute_of_unique_fixed {g h : ComplexMotion} (hc : Commute g h) {c : ℂ}
    (hg : g c = c) (hunique : ∀ z, g z = z → z = c) : h c = c := by
  apply hunique
  have hh := congrArg (fun e : ComplexMotion => e c) hc.eq
  change g (h c) = h (g c) at hh
  rwa [hg] at hh

theorem cross_eq_of_fixed_of_unit (g : ComplexMotion) {c : ℂ} (hc : g c = c)
    (hunit : Complex.normSq (multiplier g) = 1) (a b : ℂ) :
    complexCross (g a-c) (g b-c) = complexCross (a-c) (b-c) := by
  calc
    _ = complexCross (g a-g c) (g b-g c) := by rw [hc]
    _ = _ := by rw [apply_sub,apply_sub,complexCross_mul,hunit,one_mul]

theorem inverse_offset (g : ComplexMotion) (hm : multiplier g = 1) : g⁻¹ (0 : ℂ) = -(g 0) := by
  have h := g.apply_symm_apply (0 : ℂ)
  rw [apply_eq g (g.symm 0),hm,one_mul] at h
  change g.symm 0 = -(g 0)
  linear_combination h

/-- An affine map between two copies of a directed nonzero edge. -/
noncomputable def alongEdge (a b A B : ℂ) (hab : b ≠ a) (hAB : B ≠ A) : ComplexMotion :=
  let m := (B-A)/(b-a)
  (LinearEquiv.smulOfNeZero ℂ ℂ m (div_ne_zero (sub_ne_zero.mpr hAB) (sub_ne_zero.mpr hab))).toAffineEquiv *
    AffineEquiv.constVAdd ℂ ℂ (-a) |>.trans (AffineEquiv.constVAdd ℂ ℂ A)

theorem alongEdge_apply (a b A B : ℂ) (hab : b ≠ a) (hAB : B ≠ A) (z : ℂ) :
    alongEdge a b A B hab hAB z = (B-A)/(b-a)*(z-a)+A := by
  change A+((B-A)/(b-a))*(-a+z) = _
  ring

theorem alongEdge_source (a b A B : ℂ) (hab : b ≠ a) (hAB : B ≠ A) :
    alongEdge a b A B hab hAB a = A := by rw [alongEdge_apply,sub_self,mul_zero,zero_add]

theorem alongEdge_target (a b A B : ℂ) (hab : b ≠ a) (hAB : B ≠ A) :
    alongEdge a b A B hab hAB b = B := by
  rw [alongEdge_apply,div_mul_cancel₀ _ (sub_ne_zero.mpr hab),sub_add_cancel]

theorem alongEdge_multiplier (a b A B : ℂ) (hab : b ≠ a) (hAB : B ≠ A) :
    multiplier (alongEdge a b A B hab hAB) = (B-A)/(b-a) := by
  have h := apply_sub (alongEdge a b A B hab hAB) b a
  rw [alongEdge_source,alongEdge_target] at h
  exact (eq_div_iff (sub_ne_zero.mpr hab)).mpr h.symm

theorem alongEdge_unit (a b A B : ℂ) (hab : b ≠ a) (hAB : B ≠ A)
    (h : Complex.normSq (B-A) = Complex.normSq (b-a)) :
    Complex.normSq (multiplier (alongEdge a b A B hab hAB)) = 1 := by
  rw [alongEdge_multiplier,Complex.normSq_div,h,div_self (Complex.normSq_pos.mpr (sub_ne_zero.mpr hab)).ne']

end ComplexMotion

open InnerProductGeometry

theorem arg_div_eq_angle_of_cross_pos (u v : ℂ) (h : 0 < complexCross u v) :
    (v/u).arg = angle u v := by
  have hu : u ≠ 0 := by
    intro he
    simp [complexCross,he] at h
  have hangle := Type7.complexCorner_arg_angle true 0 u v
    (by simpa only [Type7.complexCorner,ite_true,sub_zero,complexCross] using h)
  have hratio : v/u = ((Complex.normSq u)⁻¹ : ℝ) *
      ((starRingEnd ℂ) u*v) := by
    rw [div_eq_mul_inv,Complex.inv_def]
    ring
  rw [hratio,Complex.arg_real_mul _ (inv_pos.mpr (Complex.normSq_pos.mpr hu))]
  simpa only [Type7.complexCorner,ite_true,sub_zero] using hangle

/-- The multiplier around a flat vertex is one when the angles are taken in
their positive cyclic order and the edge transitions preserve lengths. -/
theorem turn_product_eq_one {ι : Type*} [Fintype ι] (u v : ι → ℂ)
    (hpos : ∀ i, 0 < complexCross (u i) (v i))
    (hangle : ∑ i, angle (u i) (v i) = 2*Real.pi)
    (hunit : Complex.normSq (∏ i, v i/u i) = 1) :
    (∏ i, v i/u i) = 1 := by
  let r : ℝ := ∏ i, ‖v i/u i‖
  have hp (i : ι) : v i/u i = (‖v i/u i‖ : ℂ) *
      Complex.exp ((angle (u i) (v i) : ℂ)*Complex.I) := by
    rw [← arg_div_eq_angle_of_cross_pos _ _ (hpos i),Complex.norm_mul_exp_arg_mul_I]
  have hE : (∏ i, Complex.exp ((angle (u i) (v i) : ℂ)*Complex.I)) = 1 := by
    rw [← Complex.exp_sum,← Finset.sum_mul,← Complex.ofReal_sum,hangle,Complex.ofReal_mul]
    exact Complex.exp_two_pi_mul_I
  have hh : (∏ i, v i/u i) = (r : ℂ) := by
    calc
      _ = ∏ i, (‖v i/u i‖ : ℂ) * Complex.exp ((angle (u i) (v i) : ℂ)*Complex.I) :=
        Finset.prod_congr rfl (fun i _ => hp i)
      _ = _ := by rw [Finset.prod_mul_distrib,← Complex.ofReal_prod,hE,mul_one]
  have hr : 0 ≤ r := Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  rw [hh,Complex.normSq_ofReal] at hunit
  have he : r = 1 := (sq_eq_sq₀ hr zero_le_one).mp (by nlinarith)
  rw [hh,he,Complex.ofReal_one]

theorem cyclic_predecessor_succ {n : ℕ} (i : Fin n) :
    (finRotate (n+1)).symm i.succ = i.castSucc := by
  apply (finRotate (n+1)).symm_apply_eq.mpr
  exact (finRotate_of_lt i.isLt).symm

/-- A value agreeing with its predecessor all around a cycle is constant. -/
theorem eq_initial_of_eq_predecessor {α : Type*} {n : ℕ} (C : Fin (n+1) → α)
    (h : ∀ i, C i = C ((finRotate (n+1)).symm i)) (i : Fin (n+1)) : C i = C 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have he := h i.succ
    rw [cyclic_predecessor_succ] at he
    exact he.trans ih

private theorem ordered_product_moves_last {n : ℕ} (g : Fin n → ComplexMotion) (C : Fin (n+1) → ℂ)
    (h : ∀ i : Fin n, g i (C i.succ) = C i.castSucc) :
    (List.ofFn g).prod (C (Fin.last n)) = C 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,List.prod_append,List.prod_singleton]
    change (List.ofFn fun i => g i.castSucc).prod (g (Fin.last n) (C (Fin.last (n+1)))) = C 0
    have he := h (Fin.last n)
    rw [Fin.succ_last] at he
    rw [he]
    exact ih (fun i => g i.castSucc) (fun i => C i.castSucc)
      (fun i => by simpa only [Fin.castSucc_succ] using h i.castSucc)

/-- The ordered edge transitions around a flat vertex compose to the identity. -/
theorem vertex_motion_eq_one {n : ℕ} (g : Fin (n+1) → ComplexMotion) (C u v : Fin (n+1) → ℂ)
    (hfix : ∀ i, g i (C i) = C ((finRotate (n+1)).symm i))
    (hratio : ∀ i, (g i).multiplier = v ((finRotate (n+1)).symm i)/u i)
    (hunit : ∀ i, Complex.normSq (g i).multiplier = 1)
    (hpos : ∀ i, 0 < complexCross (u i) (v i))
    (hangle : ∑ i, angle (u i) (v i) = 2*Real.pi) :
    (List.ofFn g).prod = 1 := by
  let w := (List.ofFn g).prod
  have hM : w.multiplier = ∏ i, (g i).multiplier := by
    have hm (l : List ComplexMotion) : l.prod.multiplier = (l.map ComplexMotion.multiplier).prod := by
      induction l with
      | nil => rfl
      | cons a l ih => simp only [List.prod_cons,List.map_cons,ComplexMotion.multiplier_mul,ih]
    rw [hm,List.map_ofFn,List.prod_ofFn]
    rfl
  have he : w.multiplier = ∏ i, v i/u i := by
    rw [hM]
    simp only [hratio,Finset.prod_div_distrib,(finRotate (n+1)).symm.prod_comp]
  have hn : Complex.normSq w.multiplier = 1 := by rw [hM,map_prod]; simp [hunit]
  apply ComplexMotion.eq_one_of_multiplier_one_of_fixed (z := C (Fin.last n))
  · rw [he]
    exact turn_product_eq_one u v hpos hangle (by simpa only [he] using hn)
  · rw [List.ofFn_succ,List.prod_cons]
    change g 0 ((List.ofFn fun i => g i.succ).prod (C (Fin.last n))) = _
    rw [ordered_product_moves_last _ C (fun i => by simpa only [cyclic_predecessor_succ] using hfix i.succ)]
    have h0 := hfix (0 : Fin (n+1))
    rw [(finRotate (n+1)).symm_apply_eq.mpr (finRotate_last (n := n)).symm] at h0
    exact h0

end OrigamiTorus
