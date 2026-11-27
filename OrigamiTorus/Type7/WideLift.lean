module

public import OrigamiTorus.Type7.Strip
public import OrigamiTorus.Type7.WideCell0
public import OrigamiTorus.Type7.WideCell1
public import OrigamiTorus.Type7.WideCell2
public import OrigamiTorus.Type7.WideCell3
public import OrigamiTorus.Type7.WideCell4
public import OrigamiTorus.Type7.WideEndpoint
import Mathlib.Tactic

/-! The wider Type 7 cells certified by the same trapezoidal charts. -/

@[expose] public section

namespace OrigamiTorus.Type7

open Type4 (domain stripBase)
open Type4.StripLift

private theorem wider_checked (i : Fin 5) :
    (disjointPairs faces).all (widerPairCheck i) = true := by
  apply separation_checks_of_chunks
  fin_cases i
  · exact widerPairs0
  · exact widerPairs1
  · exact widerPairs2
  · exact widerPairs3
  · exact widerPairs4

theorem wider_cell_embedded_lift {i : Fin 5} {x w : ℝ}
    (hd : domain false x w) (hlo : ((wideBounds i).1 : ℝ) ≤ x) (hhi : x ≤ ((wideBounds i).2 : ℝ)) :
    ∃ z : Vertex → ℝ, Function.Injective (evaluateTriangles faces (angleLift (stripBase false x w) z 1)) := by
  refine wide_cell_embedded_lift_of_separation false i (widerHeight i) hd hlo hhi ?_
  intro t h ht ht' hh q hq
  exact separation_of_check (fun a b => signClosed_mul_pos a b ht ht' hh)
    (fun a b => signClosed_mul_neg a b ht ht' hh) q
    ((List.all_eq_true.mp (wider_checked i)) q hq)

theorem end_strip_embedded_lift {x w : ℝ} (hd : domain true x w) :
    ∃ z : Vertex → ℝ, Function.Injective (evaluateTriangles faces (angleLift (stripBase true x w) z 1)) := by
  refine Type4.end_strip_embedded_lift_of_separation false hd ?_
  intro t h ht ht' hh q hq
  exact separation_of_check (fun a b => sign_mul_pos a b ht ht' hh)
    (fun a b => sign_mul_neg a b ht ht' hh) q
    ((List.all_eq_true.mp endpointPairs) q hq)

/-- Every reduced modulus off the sharp-rhombic ray admits a regular
Type 7 embedding at the requested lattice scale. -/
theorem open_strip_regular_realizes_of_similarity {x w : ℝ}
    (hx : 0 ≤ x) (hx' : x < 1/2) (hw : 1-x^2 ≤ w)
    (a b D : ℂ) (refl : Bool) (hD : D ≠ 0)
    (hL : complexSimilarity D refl '' complexLattice 1 (x+Real.sqrt w*Complex.I) = complexLattice a b) :
    ChartRealizesWith false a b SpatiallyRegular := by
  obtain ⟨second,hd⟩ := Type4.domain_covers x w hx hx' hw
  have hlift : ∃ z : Vertex → ℝ, Function.Injective
      (evaluateTriangles faces (angleLift (stripBase second x w) z 1)) := by
    cases second
    · obtain ⟨i,hlo,hhi⟩ := wide_cell_cover hd
      exact wider_cell_embedded_lift hd hlo hhi
    · exact end_strip_embedded_lift hd
  obtain ⟨h,hemb⟩ := hlift
  exact chart_regular_realizes_of_lift hd h hemb a b D refl hD hL

theorem open_strip_regular_realizes {x w : ℝ}
    (hx : 0 ≤ x) (hx' : x < 1/2) (hw : 1-x^2 ≤ w) :
    ChartRealizesWith false 1 (x+Real.sqrt w*Complex.I) SpatiallyRegular := by
  have he : complexSimilarity 1 false = id := by funext p; simp [complexSimilarity]
  exact open_strip_regular_realizes_of_similarity hx hx' hw 1 _ 1 false one_ne_zero
    (by rw [he,Set.image_id])

theorem open_strip_realizes {x w : ℝ} (hx : 0 ≤ x) (hx' : x < 1/2) (hw : 1-x^2 ≤ w) :
    Realizes 1 (x+Real.sqrt w*Complex.I) :=
  (open_strip_regular_realizes hx hx' hw).realizes

end OrigamiTorus.Type7
