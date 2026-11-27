module

public import OrigamiTorus.Type1.Star
import Mathlib.Tactic

/-! Removing the flat valence-three vertex of Type 1. -/

@[expose] public section

noncomputable section

open InnerProductGeometry
open scoped NNReal

namespace OrigamiTorus.Type1

open Type2 (euclideanPoint linkDirection)

/-- Replace the three triangles incident to 0 by the triangle on its
neighbors. The vertex type still includes the now-unused label 0. -/
def collapsedFaces : List Triangle := (1,2,3) :: faces.drop 3

private theorem rest_nozero {f : Triangle} (hf : f ∈ faces.drop 3) : 0 ∉ triangleVertexSet f := by
  have h : (faces.drop 3).all (fun f => !(triangleVertices f).contains 0) = true := by decide +kernel
  simpa using List.all_eq_true.mp h f hf

private theorem coarse_nozero {f : Triangle} (hf : f ∈ collapsedFaces) : 0 ∉ triangleVertexSet f := by
  change f ∈ (1,2,3) :: faces.drop 3 at hf
  rcases List.mem_cons.mp hf with rfl | hf
  · decide +kernel
  · exact rest_nozero hf

private def weightChange (a b c : ℝ) : Vertex → ℝ := ![1,-a,-b,-c,0,0,0,0]

private theorem weightChange_mass {a b c : ℝ} (h : a+b+c = 1) :
    ∑ i, weightChange a b c i = 0 := by
  norm_num [weightChange,Fin.sum_univ_succ]
  linarith

private theorem weightChange_evaluate (q : Vertex → Point3) {a b c : ℝ}
    (h : q 0 = a • q 1+b • q 2+c • q 3) : evaluateWeights q (weightChange a b c) = 0 := by
  norm_num [evaluateWeights,weightChange,Fin.sum_univ_succ]
  rw [h]
  abel

private theorem weightChange_preserves_evaluation (q : Vertex → Point3) {a b c : ℝ}
    (h : q 0 = a • q 1+b • q 2+c • q 3) (w : Vertex → ℝ) (t : ℝ) :
    evaluateWeights q (w+t • weightChange a b c) = evaluateWeights q w := by
  change (∑ i, (w i+t*weightChange a b c i) • q i) = ∑ i, w i • q i
  simp only [add_smul,Finset.sum_add_distrib,mul_smul,← Finset.smul_sum]
  change _ + t • evaluateWeights q (weightChange a b c) = _
  rw [weightChange_evaluate q h,smul_zero,add_zero]

private theorem weightChange_off_outer {a b c : ℝ} (i : Vertex) (hi : i ≠ 0)
    (h₀ : i ∉ triangleVertexSet (1,2,3)) : weightChange a b c i = 0 := by
  fin_cases i <;> simp [triangleVertexSet_eq,weightChange] at hi h₀ ⊢

private theorem outer_face_lift (w : Vertex → ℝ) (hw : w ∈ faceWeights (triangleVertexSet (1,2,3)))
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : a+b+c = 1) :
    ∃ t : ℝ, ∃ f ∈ faces, w+t • weightChange a b c ∈ faceWeights (triangleVertexSet f) := by
  let t := min (w 1/a) (min (w 2/b) (w 3/c))
  let W := w+t • weightChange a b c
  have h₁ := (le_div_iff₀ ha).mp (min_le_left _ _ : t ≤ w 1/a)
  have h₂ := (le_div_iff₀ hb).mp ((min_le_right _ _).trans (min_le_left _ _) : t ≤ w 2/b)
  have h₃ := (le_div_iff₀ hc).mp ((min_le_right _ _).trans (min_le_right _ _) : t ≤ w 3/c)
  change t*a ≤ w 1 at h₁
  change t*b ≤ w 2 at h₂
  change t*c ≤ w 3 at h₃
  have ht : 0 ≤ t := le_min (div_nonneg (hw.1 _) ha.le)
    (le_min (div_nonneg (hw.1 _) hb.le) (div_nonneg (hw.1 _) hc.le))
  have hpos (i : Vertex) : 0 ≤ W i := by
    fin_cases i
    · change 0 ≤ w 0+t*1
      linarith [hw.1 0]
    · change 0 ≤ w 1+t*(-a)
      linarith
    · change 0 ≤ w 2+t*(-b)
      linarith
    · change 0 ≤ w 3+t*(-c)
      linarith
    · change 0 ≤ w 4+t*0
      simpa only [mul_zero,add_zero] using hw.1 4
    · change 0 ≤ w 5+t*0
      simpa only [mul_zero,add_zero] using hw.1 5
    · change 0 ≤ w 6+t*0
      simpa only [mul_zero,add_zero] using hw.1 6
    · change 0 ≤ w 7+t*0
      simpa only [mul_zero,add_zero] using hw.1 7
  have hsum : ∑ i, W i = 1 := by
    simp only [W,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
      ← Finset.mul_sum,weightChange_mass hs,hw.2.1,mul_zero,add_zero]
  have hrest (i : Vertex) (hi : i ≠ 0) (h₀ : i ∉ triangleVertexSet (1,2,3)) : W i = 0 := by
    simp [W,hw.2.2 i h₀,weightChange_off_outer i hi h₀]
  refine ⟨t,?_⟩
  rcases min_choice (w 1/a) (min (w 2/b) (w 3/c)) with h₁' | hrest'
  · have hzero : W 1 = 0 := by
      have hh : w 1 = t*a := (div_eq_iff ha.ne').mp h₁'.symm
      change w 1+t*(-a) = 0
      linear_combination hh
    refine ⟨(0,2,3),by decide +kernel,hpos,hsum,?_⟩
    intro i hi
    by_cases h : i = 1
    · exact h ▸ hzero
    · exact hrest i (by simpa [triangleVertexSet_eq] using (fun hz => hi (by simp [triangleVertexSet_eq,hz])) :
        i ≠ 0) (by simp [triangleVertexSet_eq] at hi ⊢; tauto)
  · rcases min_choice (w 2/b) (w 3/c) with h₂' | h₃'
    · have hzero : W 2 = 0 := by
        have ht₂ : t = w 2/b := hrest'.trans h₂'
        have hh : w 2 = t*b := (div_eq_iff hb.ne').mp ht₂.symm
        change w 2+t*(-b) = 0
        linear_combination hh
      refine ⟨(0,3,1),by decide +kernel,hpos,hsum,?_⟩
      intro i hi
      by_cases h : i = 2
      · exact h ▸ hzero
      · exact hrest i (fun hz => hi (by simp [triangleVertexSet_eq,hz]))
          (by simp [triangleVertexSet_eq] at hi ⊢; tauto)
    · have hzero : W 3 = 0 := by
        have ht₃ : t = w 3/c := hrest'.trans h₃'
        have hh : w 3 = t*c := (div_eq_iff hc.ne').mp ht₃.symm
        change w 3+t*(-c) = 0
        linear_combination hh
      refine ⟨(0,1,2),by decide +kernel,hpos,hsum,?_⟩
      intro i hi
      by_cases h : i = 3
      · exact h ▸ hzero
      · exact hrest i (fun hz => hi (by simp [triangleVertexSet_eq,hz]))
          (by simp [triangleVertexSet_eq] at hi ⊢; tauto)

/-- Removal of a strictly interior valence-three vertex preserves the
spatial embedding, by lifting the coarse barycentric weights. -/
theorem collapsed_evaluation_injective_of_convex (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q))
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hs : a+b+c = 1)
    (hq : q 0 = a • q 1+b • q 2+c • q 3) :
    Function.Injective (evaluateTriangles collapsedFaces q) := by
  let η := weightChange a b c
  have hlift (w : triangleWeightSpace collapsedFaces) :
      ∃ W : triangleWeightSpace faces, W.val-W.val 0 • η = w.val ∧
        evaluateTriangles faces q W = evaluateTriangles collapsedFaces q w := by
    obtain ⟨f,hf,hw⟩ := w.property
    have hw₀ : w.val 0 = 0 := hw.2.2 0 (coarse_nozero hf)
    change f ∈ (1,2,3) :: faces.drop 3 at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · obtain ⟨t,g,hg,hW⟩ := outer_face_lift w.val hw ha hb hc hs
      let W : triangleWeightSpace faces := ⟨w.val+t • η,g,hg,hW⟩
      have h0 : W.val 0 = t := by simp [W,η,weightChange,hw₀]
      refine ⟨W,?_,?_⟩
      · rw [h0]
        exact add_sub_cancel_right w.val (t • η)
      · exact weightChange_preserves_evaluation q hq w.val t
    · let W : triangleWeightSpace faces := ⟨w.val,f,List.mem_of_mem_drop hf,hw⟩
      refine ⟨W,?_,rfl⟩
      change w.val-w.val 0 • η = w.val
      rw [hw₀,zero_smul,sub_zero]
  intro w w' h
  obtain ⟨W,hW,eW⟩ := hlift w
  obtain ⟨W',hW',eW'⟩ := hlift w'
  have heq : W = W' := he (eW.trans (h.trans eW'.symm))
  rw [heq,hW'] at hW
  exact Subtype.ext hW.symm

private theorem center_convex_weights (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q))
    (hf : coneAngles faces (euclideanPoint ∘ q) 0 = 2*Real.pi) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a+b+c = 1 ∧
      q 0 = a • q 1+b • q 2+c • q 3 := by
  obtain ⟨s,t,hs,ht,hq⟩ := center_strictly_inside q he hf
  let m := 1+s+t
  have hm : 0 < m := by dsimp [m]; linarith
  let a := 1/m
  let b := s/m
  let c := t/m
  have hm₁ : a+b+c = 1 := by
    dsimp only [a,b,c]
    rw [← add_div,← add_div]
    exact div_self hm.ne'
  have hm₂ : q 0 = a • q 1+b • q 2+c • q 3 := by
    have h := congrArg ((1/m) • ·) hq
    rw [smul_smul,one_div_mul_cancel hm.ne',one_smul] at h
    simpa [a,b,c,smul_add,smul_smul,div_eq_mul_inv,mul_comm] using h.symm
  exact ⟨a,b,c,div_pos one_pos hm,div_pos hs hm,div_pos ht hm,hm₁,hm₂⟩

/-- The flat valence-three vertex of Type 1 can be removed without
creating an intersection of the remaining triangles. -/
theorem collapsed_evaluation_injective (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q))
    (hf : coneAngles faces (euclideanPoint ∘ q) 0 = 2*Real.pi) :
    Function.Injective (evaluateTriangles collapsedFaces q) := by
  obtain ⟨a,b,c,ha,hb,hc,hm,hq⟩ := center_convex_weights q he hf
  exact collapsed_evaluation_injective_of_convex q he ha hb hc hm hq

private theorem angle_at_subdivision (q : Vertex → Point3)
    {v a b c : Vertex} {x y z : ℝ} (hy : 0 < y) (hz : 0 < z) (hs : x+y+z = 1)
    (hv : q v = x • q a + y • q b + z • q c) (hne : q v ≠ q a) :
    angle (linkDirection q a b) (linkDirection q a c) =
      angle (linkDirection q a b) (linkDirection q a v) +
      angle (linkDirection q a v) (linkDirection q a c) := by
  have hu : linkDirection q a v ≠ 0 := by
    intro he
    exact hne (sub_eq_zero.mp (Type2.euclideanPoint_injective (he.trans euclideanPoint.map_zero.symm)))
  apply (angle_eq_angle_add_angle_iff hu).mpr
  right
  apply Submodule.mem_span_pair.mpr
  refine ⟨⟨y,hy.le⟩,⟨z,hz.le⟩,?_⟩
  have he : y • (q b-q a)+z • (q c-q a) = q v-q a := by
    rw [hv]
    calc
      _ = (x • q a + y • q b + z • q c) - (x+y+z) • q a := by module
      _ = _ := by rw [hs,one_smul]
  change y • euclideanPoint (q b-q a) + z • euclideanPoint (q c-q a) = euclideanPoint (q v-q a)
  simpa only [map_add,map_smul] using congrArg euclideanPoint he

/-- Removing vertex 0 preserves the cone angle at every remaining vertex. -/
theorem collapsed_coneAngles (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q))
    (hf : coneAngles faces (euclideanPoint ∘ q) 0 = 2*Real.pi) (i : Vertex) (hi : i ≠ 0) :
    coneAngles collapsedFaces (euclideanPoint ∘ q) i = coneAngles faces (euclideanPoint ∘ q) i := by
  obtain ⟨a,b,c,ha,hb,hc,hm,hq⟩ := center_convex_weights q he hf
  have hcover (j : Vertex) : ∃ f ∈ faces, j ∈ triangleVertexSet f := by
    have H : ∀ j : Vertex, faces.any (fun f => (triangleVertices f).contains j) = true := by decide +kernel
    obtain ⟨f,hf,hj⟩ := List.any_eq_true.mp (H j)
    exact ⟨f,hf,by simpa using hj⟩
  have hqi := vertex_injective_of_injective_evaluateTriangles faces q hcover he
  have h1 := angle_at_subdivision q (v := 0) (a := 1) (b := 2) (c := 3) hb hc hm hq
    (hqi.ne (by decide))
  have h2 := angle_at_subdivision q (v := 0) (a := 2) (b := 3) (c := 1) hc ha
    (by linarith : b+c+a = 1) (by rw [hq]; abel) (hqi.ne (by decide))
  have h3 := angle_at_subdivision q (v := 0) (a := 3) (b := 1) (c := 2) ha hb
    (by linarith : c+a+b = 1) (by rw [hq]; abel) (hqi.ne (by decide))
  let e := euclideanPoint ∘ q
  let old : List Triangle := [(0,1,2),(0,3,1),(0,2,3)]
  let new : List Triangle := [(1,2,3)]
  have ho : coneAngles faces e i = coneAngles old e i+coneAngles (faces.drop 3) e i := by
    conv_lhs => rw [show faces = old ++ faces.drop 3 by decide +kernel]
    simp [coneAngles]
  have hn : coneAngles collapsedFaces e i = coneAngles new e i+coneAngles (faces.drop 3) e i := by
    conv_lhs => rw [show collapsedFaces = new ++ faces.drop 3 by rfl]
    simp [coneAngles]
  change coneAngles collapsedFaces e i = coneAngles faces e i
  rw [ho,hn]
  congr 1
  fin_cases i
  · exact (hi rfl).elim
  · simpa [coneAngles,old,new,cornerRays,linkDirection,map_sub,e,Function.comp_apply] using h1
  · simpa [coneAngles,old,new,cornerRays,linkDirection,map_sub,e,Function.comp_apply,add_comm] using h2
  · simpa [coneAngles,old,new,cornerRays,linkDirection,map_sub,e,Function.comp_apply] using h3
  all_goals simp [coneAngles,old,new,cornerRays]

/-- The star removal changes only the triangulation of the same spatial surface. -/
theorem collapsed_image (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q))
    (hf : coneAngles faces (euclideanPoint ∘ q) 0 = 2*Real.pi) :
    Set.range (evaluateTriangles collapsedFaces q) = Set.range (evaluateTriangles faces q) := by
  obtain ⟨a,b,c,ha,hb,hc,hm,hq⟩ := center_convex_weights q he hf
  apply Set.Subset.antisymm
  · rintro p ⟨w,rfl⟩
    obtain ⟨f,hf,hw⟩ := w.property
    change f ∈ (1,2,3) :: faces.drop 3 at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · obtain ⟨t,g,hg,hW⟩ := outer_face_lift w.val hw ha hb hc hm
      exact ⟨⟨w.val+t • weightChange a b c,g,hg,hW⟩,weightChange_preserves_evaluation q hq w.val t⟩
    · exact ⟨⟨w.val,f,List.mem_of_mem_drop hf,hw⟩,rfl⟩
  · rintro p ⟨w,rfl⟩
    obtain ⟨f,hf,hw⟩ := w.property
    by_cases hh : f ∈ faces.drop 3
    · exact ⟨⟨w.val,f,List.mem_cons_of_mem _ hh,hw⟩,rfl⟩
    have hsub : triangleVertexSet f ⊆ insert 0 (triangleVertexSet (1,2,3)) := by
      have hs : f ∈ [(0,1,2),(0,3,1),(0,2,3)] := by
        have heq : faces = [(0,1,2),(0,3,1),(0,2,3)] ++ faces.drop 3 := by decide +kernel
        exact (List.mem_append.mp (heq ▸ hf)).resolve_right hh
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
      rcases hs with rfl | rfl | rfl <;> decide +kernel
    let W : Vertex → ℝ := w.val+(-w.val 0) • weightChange a b c
    have hWpos (i : Vertex) : 0 ≤ W i := by
      fin_cases i
      · change 0 ≤ w.val 0+(-w.val 0)*1
        linarith
      · change 0 ≤ w.val 1+(-w.val 0)*(-a)
        simpa [neg_mul_neg] using add_nonneg (hw.1 1) (mul_nonneg (hw.1 0) ha.le)
      · change 0 ≤ w.val 2+(-w.val 0)*(-b)
        simpa [neg_mul_neg] using add_nonneg (hw.1 2) (mul_nonneg (hw.1 0) hb.le)
      · change 0 ≤ w.val 3+(-w.val 0)*(-c)
        simpa [neg_mul_neg] using add_nonneg (hw.1 3) (mul_nonneg (hw.1 0) hc.le)
      · change 0 ≤ w.val 4+(-w.val 0)*0
        simpa only [mul_zero,add_zero] using hw.1 4
      · change 0 ≤ w.val 5+(-w.val 0)*0
        simpa only [mul_zero,add_zero] using hw.1 5
      · change 0 ≤ w.val 6+(-w.val 0)*0
        simpa only [mul_zero,add_zero] using hw.1 6
      · change 0 ≤ w.val 7+(-w.val 0)*0
        simpa only [mul_zero,add_zero] using hw.1 7
    have hWsum : ∑ i, W i = 1 := by
      simp only [W,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
        ← Finset.mul_sum,weightChange_mass hm,hw.2.1,mul_zero,add_zero]
    have hWsupp (i : Vertex) (hi : i ∉ triangleVertexSet (1,2,3)) : W i = 0 := by
      by_cases hzero : i = 0
      · subst i
        change w.val 0+(-w.val 0)*1 = 0
        ring
      · have hnot : i ∉ triangleVertexSet f := fun h => (Finset.mem_insert.mp (hsub h)).elim hzero hi
        simp [W,hw.2.2 i hnot,weightChange_off_outer i hzero hi]
    refine ⟨⟨W,(1,2,3),List.mem_cons_self,hWpos,hWsum,hWsupp⟩,?_⟩
    exact weightChange_preserves_evaluation q hq w.val (-w.val 0)

/-- The collapsed and original face spaces are homeomorphic through their
common embedded image. -/
noncomputable def collapsedHomeomorph (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q))
    (hf : coneAngles faces (euclideanPoint ∘ q) 0 = 2*Real.pi) :
    triangleWeightSpace collapsedFaces ≃ₜ triangleWeightSpace faces := by
  let _ : CompactSpace (triangleWeightSpace collapsedFaces) :=
    isCompact_iff_compactSpace.mp (isCompact_triangleWeightSpace collapsedFaces)
  let _ : CompactSpace (triangleWeightSpace faces) :=
    isCompact_iff_compactSpace.mp (isCompact_triangleWeightSpace faces)
  have hnew := (continuous_evaluateTriangles collapsedFaces q).isClosedEmbedding
    (collapsed_evaluation_injective q he hf)
  have hold := (continuous_evaluateTriangles faces q).isClosedEmbedding he
  exact hnew.isEmbedding.toHomeomorph.trans
    ((Homeomorph.setCongr (collapsed_image q he hf)).trans hold.isEmbedding.toHomeomorph.symm)

theorem collapsed_vertex_count : (collapsedFaces.flatMap triangleVertices).toFinset.card = 7 := by
  decide +kernel

theorem collapsed_complete_graph (a b : Vertex) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Type2.Adjacent collapsedFaces a b := by
  refine ⟨hab,?_⟩
  have H : ∀ a b : Vertex, a ≠ 0 → b ≠ 0 → a ≠ b →
      collapsedFaces.any (fun f => (triangleVertices f).contains a &&
        (triangleVertices f).contains b) = true := by decide +kernel
  obtain ⟨f,hf,hm⟩ := List.any_eq_true.mp (H a b ha hb hab)
  exact ⟨f,hf,by simpa using hm⟩

/-- An embedded flat Type 1 placement yields an embedded flat placement on
the collapsed seven-vertex face list. -/
theorem collapse_flat_realization (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q))
    (hf : ∀ i, coneAngles faces (euclideanPoint ∘ q) i = 2*Real.pi) :
    Function.Injective (evaluateTriangles collapsedFaces q) ∧
      ∀ i : Vertex, i ≠ 0 → coneAngles collapsedFaces (euclideanPoint ∘ q) i = 2*Real.pi := by
  exact ⟨collapsed_evaluation_injective q he (hf 0),fun i hi =>
    (collapsed_coneAngles q he (hf 0) i hi).trans (hf i)⟩

end OrigamiTorus.Type1
