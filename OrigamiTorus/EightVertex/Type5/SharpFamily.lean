module

public import OrigamiTorus.EightVertex.Type5.SharpCore
import all OrigamiTorus.EightVertex.Type5.SharpCore
import Mathlib.Tactic

/-! The strict core inequalities for the embedded family on the open sharp ray. -/

@[expose] public section

namespace OrigamiTorus.Type5.SharpFamily

open SharpCore

/-- Dual coordinates of the intrinsic core, scaled as in `SharpCore`.
The sharp height satisfies `y² = 3/4 + t`. -/
noncomputable def core (t : ℝ) : Core :=
  let u := t / (1+2*t)
  let s : ℝ := -3/20
  let g := 147/62410*(1+u/4)
  let h : ℝ := 1/100
  let b := u^2*(h+2*s*g+9*u/400)
  let e := u^4/16384
  let norm := 1+t
  let pt (a d : ℝ) := (4*a/norm, 4*d/norm)
  ⟨pt s (-norm/2+e), pt (1/2-g*u^2) (b-s),
    pt (s-h*u^2) (norm*(1/2+s-u/10)), pt (u/36-1/2) (-norm/2+3*e)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
theorem shortest {t : ℝ} (ht : 0 < t) : ShortestCore (1/(1+t)) (core t) := by
  have ht₁ : 0 < 1+t := by positivity
  have ht₂ : 0 < 1+2*t := by positivity
  intro i k
  fin_cases i <;> fin_cases k <;>
    norm_num [margin, edges, point, period, core, squareShift, positiveShift,
      Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;>
    field_simp <;> apply sub_pos.mp <;> ring_nf <;> positivity

/-- The four intrinsic polygons have the strict oriented area bounds throughout
the open ray, including arbitrarily close to the hexagonal metric. -/
theorem area_bounds {t : ℝ} (ht : 0 < t) :
    0 < anchorArea (core t) ∧ anchorArea (core t) < 4*(1/(1+t)) ∧
    ∀ j ∈ leaves, 4*(1/(1+t)) < starArea (1/(1+t)) (core t) j ∧
      starArea (1/(1+t)) (core t) j < 20*(1/(1+t)) := by
  apply SharpCore.area_bounds (by positivity) _ (shortest ht)
  exact (div_le_one (by positivity)).2 (by linarith)

end OrigamiTorus.Type5.SharpFamily
