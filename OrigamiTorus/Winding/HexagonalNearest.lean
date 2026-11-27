module

public import OrigamiTorus.Winding.ShortestWinding
import Mathlib.Tactic

/-! The three nearest directions determine the open Voronoi cell of the
hexagonal lattice. -/

@[expose] public section

namespace OrigamiTorus.Winding.Hexagonal

private theorem integral_square {a : ℤ} (ha : 0 ≤ a) : (a : ℝ) ≤ (a : ℝ)^2 := by
  by_cases hz : a = 0
  · simp [hz]
  have hp : 1 ≤ a := by omega
  have hR : (1 : ℝ) ≤ a := by exact_mod_cast hp
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show 0 ≤ (a : ℝ)-1 by linarith)]

private theorem cone_bound {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : (a,b) ≠ (0,0))
    {α β : ℝ} (hα : α < 1) (hβ : β < 1) :
    (a : ℝ)*α+(b : ℝ)*β < (a : ℝ)^2+(a : ℝ)*b+(b : ℝ)^2 := by
  have har : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hbr : (0 : ℝ) ≤ b := by exact_mod_cast hb
  have hn : ¬ (a = 0 ∧ b = 0) := fun hh => hne (Prod.ext hh.1 hh.2)
  have hpos : 0 < a+b := by omega
  have hposr : (0 : ℝ) < (a : ℝ)+(b : ℝ) := by exact_mod_cast hpos
  have hlt : (a : ℝ)*α+(b : ℝ)*β < (a : ℝ)+(b : ℝ) := by
    rcases lt_or_eq_of_le har with h | h
    · linarith only [mul_lt_mul_of_pos_left hα h,mul_le_mul_of_nonneg_left hβ.le hbr]
    · have hb' : (0 : ℝ) < b := by linarith only [h,hposr]
      linarith only [mul_le_mul_of_nonneg_left hα.le har,mul_lt_mul_of_pos_left hβ hb']
  exact hlt.trans_le (by linarith only [integral_square ha,integral_square hb,mul_nonneg har hbr])

private theorem linear_lt_of_nonnegative_first {α β : ℝ}
    (hα : |α| < 1) (hβ : |β| < 1) (hD : |α-β| < 1) {m n : ℤ}
    (hm : 0 ≤ m) (hne : (m,n) ≠ (0,0)) :
    (m : ℝ)*α+(n : ℝ)*β < (m : ℝ)^2+(m : ℝ)*n+(n : ℝ)^2 := by
  by_cases hn : 0 ≤ n
  · exact cone_bound hm hn hne (abs_lt.mp hα).2 (abs_lt.mp hβ).2
  have hn' : 0 < -n := by omega
  by_cases hc : -n ≤ m
  · have h := cone_bound (a := m+n) (b := -n) (by omega) hn'.le (by simp; omega)
      (abs_lt.mp hα).2 (abs_lt.mp hD).2
    push_cast at h
    nlinarith only [h]
  · have hβ' : -β < 1 := by linarith only [(abs_lt.mp hβ).1]
    have h := cone_bound (a := -n-m) (b := m) (by omega) hm (by simp; omega)
      hβ' (abs_lt.mp hD).2
    push_cast at h
    nlinarith only [h]

private theorem linear_lt {α β : ℝ}
    (hα : |α| < 1) (hβ : |β| < 1) (hD : |α-β| < 1) {m n : ℤ}
    (hne : (m,n) ≠ (0,0)) :
    (m : ℝ)*α+(n : ℝ)*β < (m : ℝ)^2+(m : ℝ)*n+(n : ℝ)^2 := by
  by_cases hm : 0 ≤ m
  · exact linear_lt_of_nonnegative_first hα hβ hD hm hne
  · have hd : |-α - -β| < 1 := by
      rw [show -α - -β = -(α-β) by ring,abs_neg]
      exact hD
    have h := linear_lt_of_nonnegative_first (m := -m) (n := -n)
      (by simpa only [abs_neg] using hα) (by simpa only [abs_neg] using hβ) hd
      (by omega) (by simpa [Prod.mk.injEq] using hne)
    push_cast at h
    nlinarith only [h]

/-- Strict comparisons with the three nearest lattice directions and their
negatives imply strict comparison with every nonzero lattice period. -/
theorem strictShortest_of_three {u v y : ℝ} (hy : y^2 = 3/4)
    (hu : |2*u+v| < 1) (hv : |u+2*v| < 1) (hd : |u-v| < 1) :
    StrictShortest (1/2) y (u+v/2) v := by
  intro m n hne
  have hD : |-(2*u+v) - -(u+2*v)| < 1 := by
    rw [show -(2*u+v) - -(u+2*v) = -(u-v) by ring,abs_neg]
    exact hd
  have hh := linear_lt (m := m) (n := n) (by simpa only [abs_neg] using hu)
    (by simpa only [abs_neg] using hv) hD hne
  simp only [Type5.squared2,Type5.dot]
  linear_combination (norm := (ring_nf; norm_num)) hh - ((v+(n : ℝ))^2-v^2)*hy

end OrigamiTorus.Winding.Hexagonal
