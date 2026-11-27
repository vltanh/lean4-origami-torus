module

public import OrigamiTorus.SevenVertex.Classification
public import OrigamiTorus.EightVertex.Type1.Nonexistence
import Mathlib.Tactic

/-! Nonexistence of seven-vertex paper tori in the barycentric realization model. -/

@[expose] public section

namespace OrigamiTorus.SevenVertex

open InnerProductGeometry

/-- The union of the barycentric simplices of the triangulation. -/
def weightSpace (fs : Faces) : Set (Label → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ ∃ f ∈ fs, ∀ i ∉ f, w i = 0}

/-- The piecewise-affine realization with the given vertex positions. -/
noncomputable def evaluate (fs : Faces) (q : Label → Point3)
    (w : weightSpace fs) : Point3 :=
  ∑ i, w.val i • q i

/-- The cone angle at a vertex. Each incident triangle contributes the angle
between its other two vertices. The inner sum counts both orders. -/
noncomputable def angleSum (fs : Faces) (q : Label → Point3) (v : Label) : ℝ :=
  let p := Type2.euclideanPoint ∘ q
  ∑ f ∈ fs, if v ∈ f then
    (∑ a ∈ f.erase v, ∑ b ∈ (f.erase v).erase a, angle (p a - p v) (p b - p v)) / (↑(2 : ℕ) : ℝ)
  else 0

end OrigamiTorus.SevenVertex

section

namespace OrigamiTorus.SevenVertex

open Finset InnerProductGeometry

private def pad {α : Type*} (z : α) (p : Label → α) : Vertex → α := Fin.cases z p

@[simp] private theorem pad_zero {α : Type*} (z : α) (p : Label → α) : pad z p 0 = z := rfl

@[simp] private theorem pad_succ {α : Type*} (z : α) (p : Label → α) (i : Label) :
    pad z p i.succ = p i := rfl

private theorem collapsed_faces_bridge :
    (Type1.collapsedFaces.map triangleVertexSet).toFinset =
      moebius.image (fun f => f.image Fin.succ) := by
  decide +kernel

private theorem collapsed_weight_zero (w : triangleWeightSpace Type1.collapsedFaces) :
    w.val 0 = 0 := by
  obtain ⟨f,hf,hw⟩ := w.property
  have h : ∀ f ∈ Type1.collapsedFaces, (0 : Vertex) ∉ triangleVertexSet f := by decide +kernel
  exact hw.2.2 _ (h f hf)

private def transportWeights (e : Equiv.Perm Label) (fs : Faces)
    (hfs : fs = moebius.image (fun f => f.image e))
    (w : triangleWeightSpace Type1.collapsedFaces) : weightSpace fs := by
  let W (i : Label) := w.val (e.symm i).succ
  refine ⟨W, ?_⟩
  obtain ⟨f,hf,hw⟩ := w.property
  have hface : triangleVertexSet f ∈ moebius.image (fun f => f.image Fin.succ) := by
    rw [← collapsed_faces_bridge, List.mem_toFinset]
    exact List.mem_map_of_mem hf
  obtain ⟨g,hg,heq⟩ := mem_image.mp hface
  refine ⟨fun i => hw.1 _, ?_, g.image e, ?_, ?_⟩
  · rw [← Equiv.sum_comp e W]
    have hmass := hw.2.1
    rw [Fin.sum_univ_succ, collapsed_weight_zero w, zero_add] at hmass
    simpa [W] using hmass
  · rw [hfs]
    exact mem_image_of_mem _ hg
  · intro i hi
    apply hw.2.2
    rw [← heq]
    intro hh
    obtain ⟨j,hj,hij⟩ := mem_image.mp hh
    have he := Fin.succ_injective _ hij
    exact hi (mem_image.mpr ⟨j,hj,by simp [he]⟩)

private theorem transportWeights_injective (e : Equiv.Perm Label) (fs : Faces)
    (hfs : fs = moebius.image (fun f => f.image e)) :
    Function.Injective (transportWeights e fs hfs) := by
  intro w w' h
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [collapsed_weight_zero, collapsed_weight_zero]
  · simpa [transportWeights] using
      congrArg (fun W : weightSpace fs => W.val (e j)) h

private theorem transport_evaluate (e : Equiv.Perm Label) (fs : Faces)
    (hfs : fs = moebius.image (fun f => f.image e)) (q : Label → Point3)
    (w : triangleWeightSpace Type1.collapsedFaces) :
    evaluate fs q (transportWeights e fs hfs w) =
      evaluateTriangles Type1.collapsedFaces (pad 0 (q ∘ e)) w := by
  unfold evaluate evaluateTriangles evaluateWeights
  rw [← Equiv.sum_comp e (fun i => (transportWeights e fs hfs w).val i • q i),
    Fin.sum_univ_succ (fun i : Vertex => w.val i • pad 0 (q ∘ e) i)]
  simp [transportWeights, Function.comp_apply, collapsed_weight_zero w]

private theorem angleSum_relabel (e : Equiv.Perm Label) (fs : Faces)
    (q : Label → Point3) (v : Label) :
    angleSum (fs.image (fun f => f.image e)) q (e v) = angleSum fs (q ∘ e) v := by
  let i := e.toEmbedding
  have hmap : (fs.image fun f => f.image e) = fs.map (mapEmbedding i).toEmbedding := by
    rw [map_eq_image]
    congr 1
    funext f
    exact (map_eq_image i f).symm
  unfold angleSum
  rw [hmap, sum_map]
  apply sum_congr rfl
  intro f _
  let p := Type2.euclideanPoint ∘ q
  change (if i v ∈ f.map i then
    (∑ a ∈ (f.map i).erase (i v), ∑ b ∈ ((f.map i).erase (i v)).erase a,
      angle (p a - p (i v)) (p b - p (i v))) / 2 else 0) = _
  simp only [mem_map' i, ← map_erase, sum_map]
  rfl

private def unpadLabel : Vertex → Label := Fin.cases 0 id

private def unpadFace (f : Triangle) : Finset Label :=
  {unpadLabel f.1, unpadLabel f.2.1, unpadLabel f.2.2}

private theorem unpad_faces :
    (Type1.collapsedFaces.map unpadFace).toFinset = moebius ∧
      (Type1.collapsedFaces.map unpadFace).Nodup := by decide +kernel

private theorem unpad_face_valid :
    ∀ f ∈ Type1.collapsedFaces,
      let a := unpadLabel f.1
      let b := unpadLabel f.2.1
      let c := unpadLabel f.2.2
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a.succ = f.1 ∧ b.succ = f.2.1 ∧ c.succ = f.2.2 := by
  decide +kernel

private theorem anglePair (p : Label → EuclideanSpace ℝ (Fin 3)) (v a b : Label) (h : a ≠ b) :
    (∑ x ∈ ({a,b} : Finset Label), ∑ y ∈ ({a,b} : Finset Label).erase x,
      angle (p x - p v) (p y - p v)) / 2 = angle (p a - p v) (p b - p v) := by
  rw [sum_pair h, erase_insert (by simpa using h), erase_insert_of_ne h, erase_singleton]
  simp only [sum_singleton, insert_empty_eq]
  rw [angle_comm (p b - p v)]
  ring

private theorem triangle_angle (p : Label → EuclideanSpace ℝ (Fin 3)) (v a b c : Label)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let s : Finset Label := {a,b,c}
    (if v ∈ s then
      (∑ x ∈ s.erase v, ∑ y ∈ (s.erase v).erase x, angle (p x - p v) (p y - p v)) / 2
    else 0) =
    if v = a then angle (p b - p v) (p c - p v)
    else if v = b then angle (p c - p v) (p a - p v)
    else if v = c then angle (p a - p v) (p b - p v) else 0 := by
  dsimp only
  by_cases hva : v = a
  · subst v
    have ha : a ∉ ({b,c} : Finset Label) := by simp [hab,hac]
    simp only [mem_insert_self, ite_true, erase_insert ha]
    exact anglePair p a b c hbc
  by_cases hvb : v = b
  · subst v
    have hb : b ∉ ({c} : Finset Label) := by simpa using hbc
    have hmem : b ∈ ({a,b,c} : Finset Label) := by simp
    simp only [hmem, ite_true, hva, ite_false, erase_insert_of_ne hab, erase_insert hb]
    exact (anglePair p b a c hac).trans (angle_comm _ _)
  by_cases hvc : v = c
  · subst v
    have hmem : c ∈ ({a,b,c} : Finset Label) := by simp
    simp only [hmem, ite_true, hva, hvb, ite_false, erase_insert_of_ne hac,
      erase_insert_of_ne hbc, erase_singleton, insert_empty_eq]
    exact anglePair p c a b hab
  · have hn : v ∉ ({a,b,c} : Finset Label) := by simp [hva,hvb,hvc]
    simp [hn,hva,hvb,hvc]

private theorem angleSum_moebius (q : Label → Point3) (v : Label) :
    angleSum moebius q v =
      coneAngles Type1.collapsedFaces (Type2.euclideanPoint ∘ pad 0 q) v.succ := by
  unfold angleSum coneAngles
  rw [← unpad_faces.1, List.sum_toFinset _ unpad_faces.2, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨a,b,c⟩ hf
  obtain ⟨hab,hac,hbc,ha,hb,hc⟩ := unpad_face_valid _ hf
  have position (j : Vertex) (hj : (unpadLabel j).succ = j) :
      pad 0 q j = q (unpadLabel j) := by rw [← congrArg (pad 0 q) hj, pad_succ]
  have index (j : Vertex) (hj : (unpadLabel j).succ = j) :
      v.succ = j ↔ v = unpadLabel j :=
    ⟨fun h => Fin.succ_injective _ (h.trans hj.symm), fun h => (congrArg Fin.succ h).trans hj⟩
  let p := Type2.euclideanPoint ∘ q
  let s : Finset Label := {unpadLabel a, unpadLabel b, unpadLabel c}
  change (if v ∈ s then
    (∑ x ∈ s.erase v, ∑ y ∈ (s.erase v).erase x, angle (p x - p v) (p y - p v)) / 2
    else 0) = _
  have hangle := triangle_angle p v (unpadLabel a) (unpadLabel b) (unpadLabel c) hab hac hbc
  dsimp only at hangle
  rw [show s = {unpadLabel a,unpadLabel b,unpadLabel c} from rfl, hangle]
  simp only [cornerRays, index _ ha, index _ hb, index _ hc]
  split_ifs <;> simp [p, position _ ha, position _ hb, position _ hc]

/-- **Schwartz, Theorem 1.1.** Every embedded seven-vertex torus
triangulation has a vertex whose cone angle differs from `2π`.
The proof transports the determinant-sign obstruction for the Möbius
triangulation along the checked combinatorial classification. -/
public theorem nonexistence (fs : Faces) (hf : IsTorusTriangulation fs)
    (q : Label → Point3) (he : Function.Injective (evaluate fs q)) :
    ¬ ∀ v, angleSum fs q v = 2 * Real.pi := by
  intro hflat
  obtain ⟨e, hfs⟩ := exists_relabel_moebius hf
  let Q := pad 0 (q ∘ e)
  have hQ : Function.Injective (evaluateTriangles Type1.collapsedFaces Q) := by
    intro w w' hw
    apply transportWeights_injective e fs hfs
    apply he
    simpa only [transport_evaluate] using hw
  have hcone : ∀ v : Vertex, v ≠ 0 →
      coneAngles Type1.collapsedFaces (Type2.euclideanPoint ∘ Q) v = 2 * Real.pi := by
    intro v
    refine Fin.cases (fun h => (h rfl).elim) (fun i _ => ?_) v
    rw [← angleSum_moebius, ← angleSum_relabel, ← hfs]
    exact hflat (e i)
  exact Type1.collapsed_hull_obstruction Q hQ (Type1.collapsed_strictSupport Q hQ hcone)

end OrigamiTorus.SevenVertex

end
