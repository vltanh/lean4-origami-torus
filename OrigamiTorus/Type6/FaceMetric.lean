module

public import OrigamiTorus.Type6.Periods
public import OrigamiTorus.Geometry.TriangleMetric
public import OrigamiTorus.Geometry.AffineDeterminants
import Mathlib.Tactic

/-! The fixed-period length equations yield an isometry on each lifted face. -/

@[expose] public section

namespace OrigamiTorus

open Type5 (squared2 squared3 smul2 smul3)

/-- Ordinary Euclidean coordinates recovered from the scaled spatial vertex. -/
noncomputable def physicalFoldedVertex (second : Bool) (x y : ℝ) (m : SheetMotion)
    (z : Vertex → ℝ) (t : ℝ) (i : Vertex) : Point3 :=
  let p := movedFoldedPoint second x (y^2) m i
  (p.1, p.2/y, t*z i)

/-- Ordinary Euclidean coordinates of a lifted corner, with periods `(1,0)` and `(x,y)`. -/
noncomputable def physicalIntrinsicCorner (second : Bool) (x y : ℝ) (m : SheetMotion)
    (a : Corner) : ℝ × ℝ :=
  let p := translatePoint x (y^2) a.2 (movedIntrinsicPoint second x (y^2) m a.1)
  (p.1, p.2/y)

def indexedSide (e : EdgeIndex) : LiftedSide :=
  let ((a,b),d) := edgePeriod e
  (a,b,d)

theorem oriented_side_index (f : Fin 16) (s : LiftedSide)
    (hs : s ∈ liftedSides (liftedFaces f)) :
    ∃ e : EdgeIndex, s = indexedSide e ∨ reverseSide s = indexedSide e := by
  let table := (List.finRange 24).map indexedSide
  have hc : ((List.finRange 16).flatMap fun j => liftedSides (liftedFaces j)).all
      (fun r => table.contains r || table.contains (reverseSide r)) = true := by decide +kernel
  have hm : s ∈ (List.finRange 16).flatMap (fun j => liftedSides (liftedFaces j)) :=
    List.mem_flatMap.mpr ⟨f, by simp, hs⟩
  have hor := List.all_eq_true.mp hc _ hm
  simp only [Bool.or_eq_true] at hor
  rcases hor with h | h
  · obtain ⟨e,_,he⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
    exact ⟨e, Or.inl he.symm⟩
  · obtain ⟨e,_,he⟩ := List.mem_map.mp (List.contains_iff_mem.mp h)
    exact ⟨e, Or.inr he.symm⟩

private theorem fixedPeriod_side_metric (table : EdgeIndex → Edge × Period) (second : Bool) (x y : ℝ) (m : SheetMotion) (z : Vertex → ℝ)
    (t : ℝ) (hy : y ≠ 0) (hlen : fixedPeriodResidual table second x (y^2) z (t,m) = 0)
    (a b : Corner)
    (hs : ∃ e : EdgeIndex, liftedSide a b = ((table e).1.1,(table e).1.2,(table e).2) ∨
      reverseSide (liftedSide a b) = ((table e).1.1,(table e).1.2,(table e).2)) :
    squared3 (physicalFoldedVertex second x y m z t b.1 - physicalFoldedVertex second x y m z t a.1) =
      squared2 (physicalIntrinsicCorner second x y m b - physicalIntrinsicCorner second x y m a) := by
  have metric (a b : Corner) (e : EdgeIndex) (he : liftedSide a b = ((table e).1.1,(table e).1.2,(table e).2)) :
      squared3 (physicalFoldedVertex second x y m z t b.1 -
        physicalFoldedVertex second x y m z t a.1) =
        squared2 (physicalIntrinsicCorner second x y m b - physicalIntrinsicCorner second x y m a) := by
    have ha : a.1 = (table e).1.1 := congrArg Prod.fst he
    have hb : b.1 = (table e).1.2 := congrArg (fun s : LiftedSide => s.2.1) he
    have hd : (liftedSide a b).2.2 = (table e).2 := congrArg (fun s : LiftedSide => s.2.2) he
    have h :
        scaledSquaredDistance (y^2) (movedFoldedPoint second x (y^2) m a.1)
            (movedFoldedPoint second x (y^2) m b.1) + y^2 * t^2 * (z b.1 - z a.1)^2 =
          scaledSquaredDistance (y^2) (movedIntrinsicPoint second x (y^2) m a.1)
            (translatePoint x (y^2) (liftedSide a b).2.2 (movedIntrinsicPoint second x (y^2) m b.1)) := by
      rw [hd,ha,hb]
      exact sub_eq_zero.mp (congrFun hlen e)
    apply mul_left_cancel₀ (pow_ne_zero 2 hy)
    simp only [physicalFoldedVertex, physicalIntrinsicCorner, translatePoint, scaledSquaredDistance,
      liftedSide, squared3, squared2, Type5.dot, Type5.horizontal, Prod.fst_sub, Prod.snd_sub,
      Int.cast_sub] at h ⊢
    field_simp [hy]
    linear_combination h
  obtain ⟨e,he | he⟩ := hs
  · exact metric a b e he
  · have hrev : reverseSide (liftedSide a b) = liftedSide b a := by
      simp [reverseSide, liftedSide, neg_sub]
    have h := metric b a e (hrev.symm.trans he)
    simp only [squared3, squared2, Type5.dot, Type5.horizontal, Prod.fst_sub, Prod.snd_sub] at h ⊢
    linear_combination h

/-- Squared distances between all affine points agree on the corresponding two triangles.
The parameters are differences of the second and third barycentric coordinates. -/
theorem fixedPeriod_face_metric (table : EdgeIndex → Edge × Period) (second : Bool) (x y : ℝ) (m : SheetMotion) (z : Vertex → ℝ)
    (t : ℝ) (hy : y ≠ 0) (hlen : fixedPeriodResidual table second x (y^2) z (t,m) = 0)
    (f : LiftedFace)
    (hside : ∀ k ∈ liftedSides f, ∃ e : EdgeIndex,
      k = ((table e).1.1,(table e).1.2,(table e).2) ∨
      reverseSide k = ((table e).1.1,(table e).1.2,(table e).2))
    (s r : ℝ) :
    let P (v : Corner) := physicalFoldedVertex second x y m z t v.1
    let Q := physicalIntrinsicCorner second x y m
    squared3 (smul3 s (P f.2.1 - P f.1) + smul3 r (P f.2.2 - P f.1)) =
      squared2 (smul2 s (Q f.2.1 - Q f.1) + smul2 r (Q f.2.2 - Q f.1)) := by
  dsimp only
  have h₁ := fixedPeriod_side_metric table second x y m z t hy hlen f.1 f.2.1 (hside _ (by simp [liftedSides]))
  have h₂ := fixedPeriod_side_metric table second x y m z t hy hlen f.2.1 f.2.2 (hside _ (by simp [liftedSides]))
  have h₃ := fixedPeriod_side_metric table second x y m z t hy hlen f.2.2 f.1 (hside _ (by simp [liftedSides]))
  have h₄ :
      squared3 (physicalFoldedVertex second x y m z t f.2.2.1 -
        physicalFoldedVertex second x y m z t f.1.1) =
        squared2 (physicalIntrinsicCorner second x y m f.2.2 - physicalIntrinsicCorner second x y m f.1) := by
    simp only [squared3, squared2, Type5.dot, Type5.horizontal, Prod.fst_sub, Prod.snd_sub] at h₃ ⊢
    linear_combination h₃
  exact triangle_squared_metric _ _ _ _ _ _ h₁ h₄ h₂ s r

theorem type6_face_metric (second : Bool) (x y : ℝ) (m : SheetMotion) (z : Vertex → ℝ)
    (t : ℝ) (hy : y ≠ 0) (hlen : lengthResidual second x (y^2) z (t,m) = 0)
    (j : Fin 16) (s r : ℝ) :
    let f := liftedFaces j
    let P (v : Corner) := physicalFoldedVertex second x y m z t v.1
    let Q := physicalIntrinsicCorner second x y m
    squared3 (smul3 s (P f.2.1 - P f.1) + smul3 r (P f.2.2 - P f.1)) =
      squared2 (smul2 s (Q f.2.1 - Q f.1) + smul2 r (Q f.2.2 - Q f.1)) := by
  apply fixedPeriod_face_metric edgePeriod second x y m z t hy hlen (liftedFaces j) _ s r
  intro k hk
  exact oriented_side_index j k hk

end OrigamiTorus
