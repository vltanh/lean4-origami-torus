module

public import OrigamiTorus.EightVertex.Type7.Transitions
import Mathlib.Tactic

/-! The cyclic angle turns at a flat vertex give the identity transition. -/

@[expose] public section

open InnerProductGeometry

namespace OrigamiTorus.Type7

variable (flipped : Bool)

def chartLink (v : Vertex) : List Vertex :=
  if flipped then Type4.markedLinkCycle v else markedLinkCycle v

def linkSize (v : Vertex) : ℕ := (chartLink flipped v).length - 1 + 1

/-- The successive neighbors of a vertex in its positive link. -/
def linkLabel (v : Vertex) (i : Fin (linkSize flipped v)) : Vertex :=
  ((chartLink flipped v)[i.val]?).getD 0

theorem link_incidence (v : Vertex) (i : Fin (linkSize flipped v)) :
    let b := linkLabel flipped v i
    let c := linkLabel flipped v (finRotate _ i)
    let f := markedFace flipped (leftFace flipped v b)
    HasSide flipped v b ∧
      leftFace flipped b v = leftFace flipped v (linkLabel flipped v ((finRotate _).symm i)) ∧
      (f = (v,b,c) ∨ f = (b,c,v) ∨ f = (c,v,b)) := by
  revert v i
  cases flipped <;> decide +kernel

private theorem link_corner_perm (v : Vertex) :
    ((faceChoice flipped).filterMap (cornerRays v)).Perm
      (List.ofFn fun i : Fin (linkSize flipped v) => (linkLabel flipped v i,linkLabel flipped v (finRotate _ i))) := by
  revert v
  cases flipped <;> decide +kernel

private theorem coneAngles_eq_linkSum (Q : Vertex → EuclideanSpace ℝ (Fin 3)) (v : Vertex) :
    coneAngles (faceChoice flipped) Q v =
      ∑ i : Fin (linkSize flipped v),
        angle (Q (linkLabel flipped v i)-Q v) (Q (linkLabel flipped v (finRotate _ i))-Q v) := by
  let atCorner (e : Edge) := angle (Q e.1-Q v) (Q e.2-Q v)
  have he (fs : List Triangle) :
      coneAngles fs Q v = ((fs.filterMap (cornerRays v)).map atCorner).sum := by
    induction fs with
    | nil => rfl
    | cons f fs ih =>
      have hsum := ih
      cases hs : cornerRays v f with
      | none =>
        simpa only [coneAngles,List.filterMap_cons,hs,List.map_cons,List.sum_cons,zero_add] using hsum
      | some e =>
        obtain ⟨a,b⟩ := e
        simp only [coneAngles,List.filterMap_cons,hs,List.map_cons,List.sum_cons] at hsum ⊢
        rw [hsum]
  rw [he,((link_corner_perm flipped v).map atCorner).sum_eq,List.map_ofFn,List.sum_ofFn]
  rfl

private theorem orientation_at_cyclic {q : Vertex → Point3} {k : ℝ} {f : Triangle}
    (P : DevelopedFace q k f true) (a b c : Vertex)
    (hf : f = (a,b,c) ∨ f = (b,c,a) ∨ f = (c,a,b)) :
    0 < complexCross (P.point b-P.point a) (P.point c-P.point a) := by
  rcases hf with rfl | rfl | rfl
  · exact P.orientation
  · exact P.rotate.rotate.orientation
  · exact P.rotate.orientation

/-- The product of consecutive edge transitions around a vertex in positive link order. -/
noncomputable def vertexTransition (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (v : Vertex) : ComplexMotion :=
  (List.ofFn fun i : Fin (linkSize flipped v) => edgeTransition flipped q he v (linkLabel flipped v i)).prod

theorem vertexTransition_eq_one (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q))
    (hflat : ∀ v, coneAngles (faceChoice flipped) (Type2.euclideanPoint ∘ q) v = 2*Real.pi)
    (v : Vertex) : vertexTransition flipped q he v = 1 := by
  let n := linkSize flipped v
  let b := linkLabel flipped v
  let P (i : Fin n) := markedDevelopment flipped q he (leftFace flipped v (b i))
  let g (i : Fin n) := edgeTransition flipped q he v (b i)
  let C (i : Fin n) := (P i).point v
  let U (i : Fin n) := (P i).point (b i)-C i
  let V (i : Fin n) := (P i).point (b (finRotate n i))-C i
  have hfix (i : Fin n) : g i (C i) = C ((finRotate _).symm i) := by
    have hi := link_incidence flipped v i
    have hh := edgeTransition_apply_a flipped q he v (b i) hi.1
    rw [hi.2.1] at hh
    exact hh
  have hU (i : Fin n) : U i ≠ 0 :=
    sub_ne_zero.mpr (markedDevelopment_side_ne flipped q he v (b i) (link_incidence flipped v i).1)
  have hratio (i : Fin n) : (g i).multiplier = V ((finRotate _).symm i)/U i := by
    have hi := link_incidence flipped v i
    have hh := edgeTransition_apply_b flipped q he v (b i) hi.1
    rw [hi.2.1] at hh
    have h := ComplexMotion.apply_sub (g i) ((P i).point (b i)) (C i)
    have hb : g i ((P i).point (b i)) = (P ((finRotate _).symm i)).point (b i) := hh
    rw [hb,hfix] at h
    apply (eq_div_iff (hU i)).mpr
    simpa only [V,Equiv.apply_symm_apply] using h.symm
  have hh (i : Fin n) : 0 < complexCross (U i) (V i) :=
    orientation_at_cyclic (P i) v (b i) (b (finRotate _ i)) (link_incidence flipped v i).2.2
  have hang (i : Fin n) :
      angle (Type2.euclideanPoint (q (b i))-Type2.euclideanPoint (q v))
        (Type2.euclideanPoint (q (b (finRotate _ i)))-Type2.euclideanPoint (q v)) =
      angle (U i) (V i) := by
    have hi := (link_incidence flipped v i).2.2
    apply (P i).angle_at (rootEdgeSq_pos flipped q he) v (b i) (b (finRotate _ i)) <;>
      rcases hi with hi | hi | hi <;>
      simp [b,hi,triangleVertexSet_eq]
  have hsum : ∑ i, angle (U i) (V i) = 2*Real.pi := by
    have h := hflat v
    rw [coneAngles_eq_linkSum] at h
    simpa only [b,Function.comp_apply,hang] using h
  exact vertex_motion_eq_one g C U V hfix hratio
    (fun i => edgeTransition_unit flipped q he v (b i)) hh hsum

end OrigamiTorus.Type7
