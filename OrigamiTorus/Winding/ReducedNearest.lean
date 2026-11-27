module

public import OrigamiTorus.Winding.ShortestWinding
import Mathlib.Tactic

/-! Strict shortestness from the three lattice directions of a reduced basis. -/

@[expose] public section

namespace OrigamiTorus.Winding

private theorem cast_le_square {a : ℤ} (ha : 0 ≤ a) : (a : ℝ) ≤ (a : ℝ)^2 := by
  by_cases h : a = 0
  · simp [h]
  have h₁ : (1 : ℝ) ≤ a := by exact_mod_cast (show (1 : ℤ) ≤ a by omega)
  nlinarith only [mul_nonneg (show (0 : ℝ) ≤ a by linarith) (sub_nonneg.mpr h₁)]

private theorem cone_bound {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : (a,b) ≠ (0,0))
    {A B D α β : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hα : α < A) (hβ : β < B) :
    (a : ℝ)*α+(b : ℝ)*β < A*(a : ℝ)^2+2*D*a*b+B*(b : ℝ)^2 := by
  have har : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hbr : (0 : ℝ) ≤ b := by exact_mod_cast hb
  have hn : ¬ (a = 0 ∧ b = 0) := fun hh => hne (Prod.ext hh.1 hh.2)
  have hp : (0 : ℝ) < (a : ℝ)+(b : ℝ) := by
    exact_mod_cast (show (0 : ℤ) < a+b by omega)
  have hl : (a : ℝ)*α+(b : ℝ)*β < (a : ℝ)*A+(b : ℝ)*B := by
    rcases lt_or_eq_of_le har with h | h
    · linarith only [mul_lt_mul_of_pos_left hα h,mul_le_mul_of_nonneg_left hβ.le hbr]
    · have hb' : (0 : ℝ) < b := by linarith only [h,hp]
      linarith only [mul_le_mul_of_nonneg_left hα.le har,mul_lt_mul_of_pos_left hβ hb']
  exact hl.trans_le (by nlinarith only [mul_le_mul_of_nonneg_left (cast_le_square ha) hA,
    mul_le_mul_of_nonneg_left (cast_le_square hb) hB,mul_nonneg (mul_nonneg hD har) hbr])

private theorem linear_lt_of_nonnegative_first {x w α β : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 1/2) (hw : 1 ≤ w)
    (hα : |α| < 1) (hβ : |β| < w) (hD : |α-β| < 1-2*x+w)
    {m n : ℤ} (hm : 0 ≤ m) (hne : (m,n) ≠ (0,0)) :
    (m : ℝ)*α+(n : ℝ)*β < (m : ℝ)^2+2*x*m*n+w*(n : ℝ)^2 := by
  by_cases hn : 0 ≤ n
  · simpa only [one_mul] using cone_bound hm hn hne zero_le_one (by linarith : 0 ≤ w) hx
      (abs_lt.mp hα).2 (abs_lt.mp hβ).2
  have hn' : 0 < -n := by omega
  have hB : 0 ≤ 1-2*x+w := by linarith
  by_cases hc : -n ≤ m
  · have h := cone_bound (a := m+n) (b := -n) (by omega) hn'.le (by simp; omega)
      zero_le_one hB (show 0 ≤ 1-x by linarith) (abs_lt.mp hα).2 (abs_lt.mp hD).2
    push_cast at h
    nlinarith only [h]
  · have hβ' : -β < w := by linarith only [(abs_lt.mp hβ).1]
    have h := cone_bound (a := -n-m) (b := m) (by omega) hm (by simp; omega)
      (show 0 ≤ w by linarith) hB (show 0 ≤ w-x by linarith) hβ' (abs_lt.mp hD).2
    push_cast at h
    nlinarith only [h]

private theorem linear_lt {x w α β : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 1/2) (hw : 1 ≤ w)
    (hα : |α| < 1) (hβ : |β| < w) (hD : |α-β| < 1-2*x+w)
    {m n : ℤ} (hne : (m,n) ≠ (0,0)) :
    (m : ℝ)*α+(n : ℝ)*β < (m : ℝ)^2+2*x*m*n+w*(n : ℝ)^2 := by
  by_cases hm : 0 ≤ m
  · exact linear_lt_of_nonnegative_first hx hx' hw hα hβ hD hm hne
  · have hd : |-α - -β| < 1-2*x+w := by
      rw [show -α - -β = -(α-β) by ring,abs_neg]
      exact hD
    have h := linear_lt_of_nonnegative_first hx hx' hw (m := -m) (n := -n)
      (by simpa only [abs_neg] using hα) (by simpa only [abs_neg] using hβ) hd
      (by omega) (by simpa [Prod.mk.injEq] using hne)
    push_cast at h
    nlinarith only [h]

/-- The three strict nearest-direction comparisons imply strict shortestness
against every nonzero period. The edge displacement is `(X,y*V)`. -/
theorem strictShortest_of_three {x y X V : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 1/2) (hw : 1 ≤ x^2+y^2)
    (h₁ : |2*X| < 1) (h₂ : |2*(X*x+y^2*V)| < x^2+y^2)
    (h₃ : |2*(X*(x-1)+y^2*V)| < (x-1)^2+y^2) :
    StrictShortest x y X V := by
  intro m n hn
  have hD : |-(2*X) - -(2*(X*x+y^2*V))| < 1-2*x+(x^2+y^2) := by
    rw [show -(2*X) - -(2*(X*x+y^2*V)) = 2*(X*(x-1)+y^2*V) by ring]
    convert h₃ using 1 <;> ring
  have h := linear_lt hx hx' hw (α := -(2*X)) (β := -(2*(X*x+y^2*V)))
    (by simpa only [abs_neg] using h₁) (by simpa only [abs_neg] using h₂) hD hn
  simp only [Type5.squared2,Type5.dot]
  linear_combination h

end OrigamiTorus.Winding
