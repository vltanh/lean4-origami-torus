module

public import OrigamiTorus.Type7.Development
public import OrigamiTorus.Lattice.FaceTransitions
import Mathlib.Tactic

/-! The affine maps identifying the two developed copies of each edge. -/

@[expose] public section

namespace OrigamiTorus.Type7

variable (flipped : Bool)

/-- The three edges in the positive boundary direction. -/
def directedSides (f : Triangle) : List Edge := [(f.1,f.2.1),(f.2.1,f.2.2),(f.2.2,f.1)]

/-- The face on the left of a directed side. The default is only used outside the edges. -/
def leftFace (a b : Vertex) : Fin 16 :=
  ((List.finRange 16).find? fun j => (directedSides (markedFace flipped j)).contains (a,b)).getD 0

def HasSide (a b : Vertex) : Prop := (a,b) ∈ directedSides (markedFace flipped (leftFace flipped a b))

instance (a b : Vertex) : Decidable (HasSide flipped a b) := inferInstanceAs
  (Decidable ((a,b) ∈ directedSides (markedFace flipped (leftFace flipped a b))))

theorem leftFace_of_side (j : Fin 16) (a b : Vertex) (h : (a,b) ∈ directedSides (markedFace flipped j)) :
    leftFace flipped a b = j := by
  revert j a b
  cases flipped <;> decide +kernel

theorem hasSide_of_side (j : Fin 16) (a b : Vertex) (h : (a,b) ∈ directedSides (markedFace flipped j)) :
    HasSide flipped a b := by
  unfold HasSide
  rwa [leftFace_of_side flipped j a b h]

theorem hasSide_rev (a b : Vertex) (h : HasSide flipped a b) : HasSide flipped b a := by
  revert a b
  cases flipped <;> decide +kernel

theorem labels_of_hasSide (a b : Vertex) (h : HasSide flipped a b) :
    a ≠ b ∧ a ∈ triangleVertexSet (markedFace flipped (leftFace flipped a b)) ∧
      b ∈ triangleVertexSet (markedFace flipped (leftFace flipped a b)) := by
  revert a b
  cases flipped <;> decide +kernel

theorem markedDevelopment_vertex_ne (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (i : Fin 16)
    {a b : Vertex} (hab : a ≠ b)
    (ha : a ∈ triangleVertexSet (markedFace flipped i)) (hb : b ∈ triangleVertexSet (markedFace flipped i)) :
    (markedDevelopment flipped q he i).point b ≠ (markedDevelopment flipped q he i).point a := by
  have hcover : ∀ s : Bool, ∀ a : Vertex, ∃ f ∈ faceChoice s, a ∈ triangleVertexSet f := by
    decide +kernel
  have hq := vertex_injective_of_injective_evaluateTriangles (faceChoice flipped) q (hcover flipped) he
  have h := (markedDevelopment flipped q he i).edge_metric a ha b hb
  intro hh
  rw [hh,sub_self,Complex.normSq_zero,mul_zero,spatialEdgeSq_euclidean] at h
  have e : Type2.euclideanPoint (q b)-Type2.euclideanPoint (q a) = 0 := by
    apply norm_eq_zero.mp
    by_contra hn
    exact pow_ne_zero 2 hn h.symm
  exact hab (hq (Type2.euclideanPoint_injective (sub_eq_zero.mp e)).symm)

theorem markedDevelopment_side_ne (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (a b : Vertex) (h : HasSide flipped a b) :
    (markedDevelopment flipped q he (leftFace flipped a b)).point b ≠
      (markedDevelopment flipped q he (leftFace flipped a b)).point a :=
  markedDevelopment_vertex_ne flipped q he _ (labels_of_hasSide flipped a b h).1
    (labels_of_hasSide flipped a b h).2.1 (labels_of_hasSide flipped a b h).2.2

/-- The direct motion from the left copy of an oriented edge to its right copy. -/
noncomputable def edgeTransition (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (a b : Vertex) : ComplexMotion :=
  let P (i : Fin 16) := (markedDevelopment flipped q he i).point
  if h : HasSide flipped a b then
    ComplexMotion.alongEdge (P (leftFace flipped a b) a) (P (leftFace flipped a b) b)
      (P (leftFace flipped b a) a) (P (leftFace flipped b a) b)
      (markedDevelopment_side_ne flipped q he a b h)
      (markedDevelopment_side_ne flipped q he b a (hasSide_rev flipped a b h)).symm
  else 1

theorem edgeTransition_apply_a (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (a b : Vertex) (h : HasSide flipped a b) :
    let P (i : Fin 16) := (markedDevelopment flipped q he i).point
    edgeTransition flipped q he a b (P (leftFace flipped a b) a) = P (leftFace flipped b a) a := by
  dsimp only [edgeTransition]
  rw [dite_eq_left h,ComplexMotion.alongEdge_source]

theorem edgeTransition_apply_b (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (a b : Vertex) (h : HasSide flipped a b) :
    let P (i : Fin 16) := (markedDevelopment flipped q he i).point
    edgeTransition flipped q he a b (P (leftFace flipped a b) b) = P (leftFace flipped b a) b := by
  dsimp only [edgeTransition]
  rw [dite_eq_left h,ComplexMotion.alongEdge_target]

theorem edgeTransition_unit (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (a b : Vertex) :
    Complex.normSq ((edgeTransition flipped q he a b).multiplier) = 1 := by
  dsimp only [edgeTransition]
  by_cases h : HasSide flipped a b
  · rw [dite_eq_left h]
    apply ComplexMotion.alongEdge_unit
    apply mul_left_cancel₀ (rootEdgeSq_pos flipped q he).ne'
    obtain ⟨_,ha,hb⟩ := labels_of_hasSide flipped a b h
    obtain ⟨_,hb',ha'⟩ := labels_of_hasSide flipped b a (hasSide_rev flipped a b h)
    rw [(markedDevelopment flipped q he (leftFace flipped b a)).edge_metric a ha' b hb',
      (markedDevelopment flipped q he (leftFace flipped a b)).edge_metric a ha b hb]
  · rw [dite_eq_right h]
    simp

theorem edgeTransition_rev (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (a b : Vertex) (h : HasSide flipped a b) :
    edgeTransition flipped q he b a = (edgeTransition flipped q he a b)⁻¹ := by
  have hr := hasSide_rev flipped a b h
  apply ComplexMotion.eq_of_eq_two_points (markedDevelopment_side_ne flipped q he b a hr)
  · rw [edgeTransition_apply_a flipped q he b a hr,AffineEquiv.inv_def]
    apply (AffineEquiv.eq_symm_apply _).mpr
    exact edgeTransition_apply_b flipped q he a b h
  · rw [edgeTransition_apply_b flipped q he b a hr,AffineEquiv.inv_def]
    apply (AffineEquiv.eq_symm_apply _).mpr
    exact edgeTransition_apply_a flipped q he a b h

theorem edgeTransition_eq_one (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (a b : Vertex) (h : HasSide flipped a b)
    (ha : (markedDevelopment flipped q he (leftFace flipped a b)).point a =
      (markedDevelopment flipped q he (leftFace flipped b a)).point a)
    (hb : (markedDevelopment flipped q he (leftFace flipped a b)).point b =
      (markedDevelopment flipped q he (leftFace flipped b a)).point b) :
    edgeTransition flipped q he a b = 1 := by
  apply ComplexMotion.eq_of_eq_two_points (markedDevelopment_side_ne flipped q he a b h)
  · rw [edgeTransition_apply_a flipped q he a b h]
    exact ha.symm
  · rw [edgeTransition_apply_b flipped q he a b h]
    exact hb.symm

theorem edgeTransition_tree (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (j : Fin 15) :
    let (_, (a,b)) := developmentTree flipped j
    edgeTransition flipped q he a b = 1 := by
  rcases h : developmentTree flipped j with ⟨⟨f,g⟩,a,b⟩
  have hl : ∀ j : Fin 15,
      let ((f,g),(a,b)) := developmentTree flipped j
      HasSide flipped a b ∧ ((leftFace flipped a b = f ∧ leftFace flipped b a = g) ∨
        (leftFace flipped a b = g ∧ leftFace flipped b a = f)) := by cases flipped <;> decide +kernel
  have ht := markedDevelopment_tree flipped q he j
  specialize hl j
  rw [h] at hl ht
  obtain ⟨hs,(⟨ha,hb⟩ | ⟨ha,hb⟩)⟩ := hl
  · apply edgeTransition_eq_one flipped q he a b hs <;> rw [ha,hb]
    · exact ht.1
    · exact ht.2
  · apply edgeTransition_eq_one flipped q he a b hs <;> rw [ha,hb]
    · exact ht.1.symm
    · exact ht.2.symm

end OrigamiTorus.Type7
