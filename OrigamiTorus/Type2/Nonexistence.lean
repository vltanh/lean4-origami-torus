module

public import OrigamiTorus.Type2.Projection
import OrigamiTorus.Type2.Certificate
import OrigamiTorus.Type2.CircuitSigns
import OrigamiTorus.Type2.MixedSigns
import OrigamiTorus.Type2.PluckerSigns
import Mathlib.Tactic

/-! The geometric reduction to the checked Type 2 sign refutation. -/

public section

namespace OrigamiTorus.Type2

private def natPlacement (r : Vertex → Point3) (i : ℕ) : Point3 := r (Fin.ofNat 8 i)

private theorem vertex_label_val {i : ℕ} (hi : i < 8) : (Fin.ofNat 8 i).val = i :=
  Nat.mod_eq_of_lt hi

private theorem natPlacement_val (r : Vertex → Point3) (v : Vertex) : natPlacement r v.val = r v := by
  simp only [natPlacement,Fin.ofNat_val_eq_self]

private theorem natPlacement_ordered_minors (r : Vertex → Point3)
    (h : GenericLift (fun v => ((r v).1,(r v).2.1)) (fun v => (r v).2.2))
    (a b c d : ℕ) (ha : a < b) (hb : b < c) (hc : c < d) (hd : d < 8) :
    affineBracket (natPlacement r a) (natPlacement r b) (natPlacement r c) (natPlacement r d) ≠ 0 := by
  have hab : Fin.ofNat 8 a < Fin.ofNat 8 b := by
    change (Fin.ofNat 8 a).val < (Fin.ofNat 8 b).val
    rwa [vertex_label_val (ha.trans (hb.trans (hc.trans hd))),vertex_label_val (hb.trans (hc.trans hd))]
  have hbc : Fin.ofNat 8 b < Fin.ofNat 8 c := by
    change (Fin.ofNat 8 b).val < (Fin.ofNat 8 c).val
    rwa [vertex_label_val (hb.trans (hc.trans hd)),vertex_label_val (hc.trans hd)]
  have hcd : Fin.ofNat 8 c < Fin.ofNat 8 d := by
    change (Fin.ofNat 8 c).val < (Fin.ofNat 8 d).val
    rwa [vertex_label_val (hc.trans hd),vertex_label_val hd]
  simpa only [volume_eq_affineBracket,natPlacement] using
    h (Fin.ofNat 8 a) (Fin.ofNat 8 b) (Fin.ofNat 8 c) (Fin.ofNat 8 d) hab hbc hcd

private theorem natPlacement_hull (r : Vertex → Point3) (s : Finset ℕ) :
    vertexHull (natPlacement r) s = vertexHull r (s.image (Fin.ofNat 8)) := by
  unfold vertexHull
  rw [Finset.coe_image,Set.image_image]
  rfl

private def faceLabels (f : Triangle) : List ℕ := (triangleVertices f).map Fin.val

private theorem faceLabels_mem {f : Triangle} (hf : f ∈ geometricFaces) : faceLabels f ∈ faces := by
  rw [← geometricFaces_labels]
  exact List.mem_map.mpr ⟨f,hf,rfl⟩

private theorem faceLabels_bounds {f : Triangle} {a : ℕ} (ha : a ∈ faceLabels f) : a < 8 := by
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
  exact v.isLt

private theorem faceLabels_toFinset (f : Triangle) :
    (faceLabels f).toFinset.image (Fin.ofNat 8) = triangleVertexSet f := by
  ext v
  simp only [Finset.mem_image,triangleVertexSet,List.mem_toFinset]
  constructor
  · rintro ⟨i,hi,he⟩
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
    rw [Fin.ofNat_val_eq_self] at he
    exact he ▸ hw
  · intro hv
    exact ⟨v.val,List.mem_map.mpr ⟨v,hv,rfl⟩,Fin.ofNat_val_eq_self v⟩

private theorem disjoint_fin_labels {s t : Finset ℕ} (hs : ∀ a ∈ s, a < 8) (ht : ∀ a ∈ t, a < 8)
    (hD : Disjoint s t) : Disjoint (s.image (Fin.ofNat 8)) (t.image (Fin.ofNat 8)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,he'⟩ := Finset.mem_image.mp hx'
  have heq := congrArg Fin.val (he.trans he'.symm)
  rw [vertex_label_val (hs a ha),vertex_label_val (ht b hb)] at heq
  exact Finset.disjoint_left.mp hD ha (heq.symm ▸ hb)

private theorem natPlacement_edge_face (r : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles geometricFaces r))
    (a b : ℕ) (f : List ℕ) (ha : a < 8) (hb : b < 8) (heAB : isEdge a b = true)
    (hf : f ∈ faces) (hdis : Disjoint ({a,b} : Finset ℕ) f.toFinset) :
    Disjoint (vertexHull (natPlacement r) {a,b}) (vertexHull (natPlacement r) f.toFinset) := by
  let A := Fin.ofNat 8 a
  let B := Fin.ofNat 8 b
  have hadj : Adjacent geometricFaces A B := by
    rw [adjacent_geometricFaces_iff]
    change isEdge (Fin.ofNat 8 a).val (Fin.ofNat 8 b).val = true
    rwa [vertex_label_val ha,vertex_label_val hb]
  obtain ⟨_,g,hg,hA,hB⟩ := hadj
  have hF : f ∈ geometricFaces.map faceLabels := geometricFaces_labels.symm ▸ hf
  obtain ⟨f',hf',hEq⟩ := List.mem_map.mp hF
  have hImage : f.toFinset.image (Fin.ofNat 8) = triangleVertexSet f' := hEq ▸ faceLabels_toFinset f'
  have hAB : ({a,b} : Finset ℕ).image (Fin.ofNat 8) = {A,B} := by simp [A,B]
  have hEdgeBounds (i : ℕ) (hi : i ∈ ({a,b} : Finset ℕ)) : i < 8 := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption
  have hFaceBounds (i : ℕ) (hi : i ∈ f.toFinset) : i < 8 := by
    rw [← hEq] at hi
    exact faceLabels_bounds (List.mem_toFinset.mp hi)
  have htyped := disjoint_fin_labels hEdgeBounds hFaceBounds hdis
  rw [hAB,hImage] at htyped
  have hedge : ({A,B} : Finset Vertex) ∈ (triangleComplex geometricFaces).faces :=
    ⟨by simp,g,hg,Finset.insert_subset_iff.mpr ⟨hA,Finset.singleton_subset_iff.mpr hB⟩⟩
  have hface : triangleVertexSet f' ∈ (triangleComplex geometricFaces).faces :=
    ⟨⟨f'.1,by simp [triangleVertexSet,triangleVertices]⟩,f',hf',le_rfl⟩
  rw [natPlacement_hull,natPlacement_hull,hAB,hImage]
  exact disjoint_vertexHull_of_injective_evaluateTriangles geometricFaces r he _ _ hedge hface htyped

private theorem natPlacement_strict_support (r : Vertex → Point3)
    (h : ∀ v, HasStrictSupport geometricFaces r v) (v : ℕ) (s : List ℕ) (hv : v < 8)
    (hs : ∀ w ∈ s, w < 8 ∧ isEdge v w = true) :
    natPlacement r v ∉ vertexHull (natPlacement r) s.toFinset := by
  rw [natPlacement_hull,natPlacement]
  apply strictSupport_not_mem_neighborHull geometricFaces r _ _ ?_ (h _)
  intro x hx
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hw₁,hw₂⟩ := hs w (List.mem_toFinset.mp hw)
  rw [adjacent_geometricFaces_iff,vertex_label_val hv,vertex_label_val hw₁]
  exact hw₂

private theorem faceSide_eq_bracketValue (r : Vertex → Point3) (f : Triangle) (w : Vertex) :
    bracketValue (natPlacement r) (faceLabels f ++ [w.val]) = faceSide r f w := by
  rcases f with ⟨a,b,c⟩
  simp only [faceLabels,triangleVertices,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    bracketValue,faceSide,natPlacement_val]

private theorem natPlacement_mixed_faces (r : Vertex → Point3)
    (h : ∀ v, HasMixedFace geometricFaces r v) :
    ∀ v ∈ ([0,1,2] : List ℕ), ∃ f ∈ faces.filter (·.contains v),
      (∃ a ∈ vertices.filter (fun w => isEdge v w && !f.contains w),
        0 < bracketValue (natPlacement r) (f ++ [a])) ∧
      (∃ b ∈ vertices.filter (fun w => isEdge v w && !f.contains w),
        bracketValue (natPlacement r) (f ++ [b]) < 0) := by
  intro v hv
  have hv₈ : v < 8 := by simp at hv; omega
  let V := Fin.ofNat 8 v
  obtain ⟨f,⟨hf,hVf⟩,a,b,⟨ha,ha',hb,hb'⟩,hpos,hneg⟩ := h V
  have hIn (w : Vertex) (hw : w ∈ triangleVertexSet f) : w.val ∈ faceLabels f :=
    List.mem_map.mpr ⟨w,List.mem_toFinset.mp hw,rfl⟩
  have hOut (w : Vertex) (hw : w ∉ triangleVertexSet f) : w.val ∉ faceLabels f := by
    intro he
    obtain ⟨z,hz,hzw⟩ := List.mem_map.mp he
    exact hw (Fin.val_injective hzw ▸ (List.mem_toFinset.mpr hz))
  have hvf : v ∈ faceLabels f := vertex_label_val hv₈ ▸ hIn V hVf
  have hEligible (w : Vertex) (hw : Adjacent geometricFaces V w) (hw' : w ∉ triangleVertexSet f) :
      w.val ∈ vertices.filter (fun x => isEdge v x && !(faceLabels f).contains x) := by
    rw [adjacent_geometricFaces_iff,vertex_label_val hv₈] at hw
    exact List.mem_filter.mpr ⟨List.mem_range.mpr w.isLt,by simp [hw,hOut w hw']⟩
  exact ⟨faceLabels f,List.mem_filter.mpr ⟨faceLabels_mem hf,by simpa using hvf⟩,
    ⟨a.val,hEligible a ha ha',by simpa only [faceSide_eq_bracketValue] using hpos⟩,
    ⟨b.val,hEligible b hb hb',by simpa only [faceSide_eq_bracketValue] using hneg⟩⟩

/-- The Lutz Type 2 triangulation has no embedded spatial realization
with cone angle `2π` at every vertex. The geometric reduction and the
finite propositional refutation are both proved in Lean. -/
theorem type2_nonexistence (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles geometricFaces q)) : ¬ HasFlatStars q := by
  intro hflat
  obtain ⟨r,hr,hg,hnorm,hs,hm⟩ := normalized_witnesses_of_flat_embedding q he hflat
  have hminors := natPlacement_ordered_minors r hg
  obtain ⟨mark,hM⟩ := exists_assignment_satisfying_mixedClauses _ hminors (natPlacement_mixed_faces r hm)
  have hP := determinantAssignment_satisfies_pluckerClauses _ mark hminors
  have hC := determinantAssignment_satisfies_circuitClauses _ mark hminors
    (natPlacement_edge_face r hr) (natPlacement_strict_support r hs)
  have hN : determinantAssignment (natPlacement r) mark 0 = true :=
    determinantAssignment_normalized _ mark hnorm
  apply type2_signsImpossible (determinantAssignment (natPlacement r) mark)
  intro C hc
  simp only [signClauses,List.append_assoc,List.mem_append] at hc
  rcases hc with hc | hc | hc | hc
  · obtain rfl := List.mem_singleton.mp hc
    exact ⟨(0,true),List.mem_cons_self,hN⟩
  · exact hP C hc
  · exact hC C hc
  · exact hM C hc

end OrigamiTorus.Type2
