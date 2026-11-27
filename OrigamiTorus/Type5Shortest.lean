module

public import OrigamiTorus.ReducedNearest
public import OrigamiTorus.Type5ContinuationCertificate
import Mathlib.Tactic

/-! Strict shortestness of the marked edges of the exact Type 5 witnesses. -/

@[expose] public section

namespace OrigamiTorus.Type5

theorem square_edges_strictShortest {e : Edge} (he : e ∈ edgeList) :
    Winding.StrictShortest 0 1 (squareDisplacement e).1 (squareDisplacement e).2 := by
  obtain ⟨hx,hy⟩ := square_edge_slack he
  apply Winding.strictShortest_of_three (by norm_num) (by norm_num) (by norm_num) hx
  · simpa using hy
  · have h := abs_sub_le (2*(squareDisplacement e).2) 0 (2*(squareDisplacement e).1)
    rw [sub_zero,zero_sub,abs_neg] at h
    have he : 2*((squareDisplacement e).1*(0-1)+1^2*(squareDisplacement e).2) =
        2*(squareDisplacement e).2-2*(squareDisplacement e).1 := by ring
    rw [he]
    norm_num
    linarith only [h,hy,hx]

namespace Continuation

theorem edges_strictShortest {x y : ℝ} (h : ModulusBox x y) {e : Edge} (he : e ∈ edgeList) :
    let u := intrinsic x y e.2-intrinsic x y e.1+shift x y e.1 e.2
    Winding.StrictShortest x y u.1 (u.2/y) := by
  let u := intrinsic x y e.2-intrinsic x y e.1+shift x y e.1 e.2
  change Winding.StrictShortest x y u.1 (u.2/y)
  obtain ⟨hx,hx',hy,hw⟩ := modulus_bounds h
  have h₁ : 2*|dot u (translatePoint x y (1,0) (0,0))| < squared2 (translatePoint x y (1,0) (0,0)) :=
    nearest_slack h he (by decide +kernel)
  have h₂ : 2*|dot u (translatePoint x y (0,1) (0,0))| < squared2 (translatePoint x y (0,1) (0,0)) :=
    nearest_slack h he (by decide +kernel)
  have h₃ : 2*|dot u (translatePoint x y (-1,1) (0,0))| < squared2 (translatePoint x y (-1,1) (0,0)) :=
    nearest_slack h he (by decide +kernel)
  have hV : y^2*(u.2/y) = u.2*y := by field_simp [hy.ne']
  apply Winding.strictShortest_of_three hx.le hx'.le hw.le
  · rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    simpa [dot,squared2,translatePoint] using h₁
  · rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2),hV]
    simpa [dot,squared2,translatePoint,pow_two] using h₂
  · rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2),hV]
    simpa [dot,squared2,translatePoint,pow_two,sub_eq_add_neg,add_comm x (-1)] using h₃

end Continuation
end OrigamiTorus.Type5
