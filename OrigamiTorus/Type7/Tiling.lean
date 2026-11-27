module

public import OrigamiTorus.Lattice.LatticeTorus
public import OrigamiTorus.Geometry.TriangleMetric
public import OrigamiTorus.Type7.IntrinsicLifts
public import OrigamiTorus.Type7.Inflation
import Mathlib.Tactic

/-! The marked developed triangles give a piecewise-isometric embedding of the
intrinsic rectangular lattice quotient. -/

@[expose] public section

namespace OrigamiTorus.Type7

open Type5 (squared2 squared3)

/-- The embedding and facewise metric conditions on specified spatial and
intrinsic vertex data. -/
def ChartRealization (flipped : Bool) (a b : ℂ)
    (H : triangleWeightSpace (faceChoice flipped) ≃ₜ ComplexTorus a b)
    (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Fin 16 → Vertex → ℂ) : Prop :=
    Topology.IsClosedEmbedding F ∧
    (∀ u, F (H u) = evaluateTriangles (faceChoice flipped) Q u) ∧
    (∀ j u, u.val ∈ faceWeights (triangleVertexSet (markedFace flipped j)) →
      H u = complexTorusProjection a b (∑ i, u.val i • P j i)) ∧
    ∀ j u v,
      u.val ∈ faceWeights (triangleVertexSet (markedFace flipped j)) →
      v.val ∈ faceWeights (triangleVertexSet (markedFace flipped j)) →
      squared3 (F (H u) - F (H v)) =
        dist (∑ i, u.val i • P j i) (∑ i, v.val i • P j i)^2

/-- An embedding with the specified lattice, measured on the indicated planar
lift of each face. -/
def ChartRealizes (flipped : Bool) (a b : ℂ) : Prop :=
  ∃ (H : triangleWeightSpace (faceChoice flipped) ≃ₜ ComplexTorus a b)
    (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Fin 16 → Vertex → ℂ),
    ChartRealization flipped a b H F Q P

/-- A realization whose spatial placement also satisfies a given property. -/
def ChartRealizesWith (flipped : Bool) (a b : ℂ) (C : (Vertex → Point3) → Prop) : Prop :=
  ∃ (H : triangleWeightSpace (faceChoice flipped) ≃ₜ ComplexTorus a b)
    (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Fin 16 → Vertex → ℂ),
    ChartRealization flipped a b H F Q P ∧ C Q

theorem ChartRealizesWith.realizes {flipped : Bool} {a b : ℂ} {C : (Vertex → Point3) → Prop}
    (h : ChartRealizesWith flipped a b C) : ChartRealizes flipped a b := by
  obtain ⟨H,F,Q,P,he,_⟩ := h
  exact ⟨H,F,Q,P,he⟩

abbrev Realizes := ChartRealizes false

noncomputable def chartMarkedShape (flipped : Bool) (s : Vertex → Vertex → ℝ) : ℂ :=
  (chartMarkingDisplacements flipped s).2/(chartMarkingDisplacements flipped s).1

private theorem complex_of_translatePoint (x y : ℝ) (d : Period) (p : ℝ × ℝ) :
    Complex.equivRealProdCLM.symm (translatePoint x y d p) =
      Complex.equivRealProdCLM.symm p + (d.1 : ℂ) + (d.2 : ℂ)*((x : ℂ)+y*Complex.I) := by
  apply Complex.ext <;>
    simp [translatePoint,Complex.equivRealProdCLM_symm_apply,Complex.mul_re,Complex.mul_im] <;>
    ring

private theorem squared2_complex_pair (z : ℂ) :
    squared2 (Complex.equivRealProdCLM z) = Complex.normSq z := by
  simp only [squared2,Type5.dot,Complex.normSq_apply]
  rfl

/-- Develop and rescale a marked flat embedding, preserving any property
shared by its positive uniform rescalings. -/
theorem realizes_of_markedShape_with (flipped : Bool) (q : Vertex → Point3)
    (he : Topology.IsClosedEmbedding (evaluateTriangles (faceChoice flipped) q))
    (hflat : ∀ v, coneAngles (faceChoice flipped) (Type2.euclideanPoint ∘ q) v = 2*Real.pi)
    (x y : ℝ) (hy : 0 < y)
    (hshape : chartMarkedShape flipped (spatialEdgeSq q) = (x : ℂ)+y*Complex.I)
    (a b D : ℂ) (refl : Bool) (hD : D ≠ 0)
    (hL : complexSimilarity D refl '' complexLattice 1 (x+y*Complex.I) = complexLattice a b)
    {C : (Vertex → Point3) → Prop} (hC : ∀ r : ℝ, 0 < r → C (r • q)) :
    ChartRealizesWith flipped a b C := by
  classical
  let P (j : Fin 16) := (markedDevelopment flipped q he.injective j).point
  let U := (chartMarkingDisplacements flipped (spatialEdgeSq q)).1
  let V := (chartMarkingDisplacements flipped (spatialEdgeSq q)).2
  let k := rootEdgeSq flipped q
  have hk : 0 < k := rootEdgeSq_pos flipped q he.injective
  change V/U = (x : ℂ)+y*Complex.I at hshape
  have hU : U ≠ 0 := by
    intro h
    rw [h,div_zero] at hshape
    have hs := congrArg Complex.im hshape
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,Complex.I_re,
      Complex.I_im,zero_mul,one_mul,mul_one,add_zero,zero_add,Complex.zero_im] at hs
    exact hy.ne' hs.symm
  let p (i : Vertex) := Complex.equivRealProdCLM (P (representativeFace flipped i) i/U)
  let S (j : Fin 16) (i : Vertex) :=
    translatePoint x y (facePeriod (chartLifts flipped j) i) (p i)
  have hs (j : Fin 16) (i : Vertex) (hm : i ∈ triangleVertexSet (markedFace flipped j)) :
      Complex.equivRealProdCLM.symm (S j i) = P j i/U := by
    let d := facePeriod (chartLifts flipped j) i
    have hp : P j i = P (representativeFace flipped i) i+complexPeriod U V d :=
      markedDevelopment_periodic flipped q he.injective hflat j i hm
    change Complex.equivRealProdCLM.symm (translatePoint x y d (p i)) = _
    rw [complex_of_translatePoint,hp,add_div]
    simp only [p,ContinuousLinearEquiv.symm_apply_apply,complexPeriod,add_div,mul_div_assoc,
      div_self hU,mul_one,hshape,add_assoc]
  have hdiff (j : Fin 16) (i l : Vertex) :
      P j i/U-P j l/U = U⁻¹*(P j i-P j l) := by ring
  have hpos (j : Fin 16) : 0 < periodicFaceArea x y p (chartLifts flipped j) := by
    let f := chartLifts flipped j
    let i := f.1.1
    let l := f.2.1.1
    let m := f.2.2.1
    have hi : i ∈ triangleVertexSet (markedFace flipped j) := by simp [i,f,markedFace,liftedVertices,triangleVertexSet_eq]
    have hl : l ∈ triangleVertexSet (markedFace flipped j) := by simp [l,f,markedFace,liftedVertices,triangleVertexSet_eq]
    have hm : m ∈ triangleVertexSet (markedFace flipped j) := by simp [m,f,markedFace,liftedVertices,triangleVertexSet_eq]
    obtain ⟨hi',hl',hm'⟩ := facePeriod_correct f ((chartFaceSystem flipped).distinct j)
    change facePeriod (chartLifts flipped j) f.1.1 = f.1.2 at hi'
    change facePeriod (chartLifts flipped j) f.2.1.1 = f.2.1.2 at hl'
    change facePeriod (chartLifts flipped j) f.2.2.1 = f.2.2.2 at hm'
    have hh : periodicFaceArea x y p f =
        complexCross (Complex.equivRealProdCLM.symm (S j l)-Complex.equivRealProdCLM.symm (S j i))
          (Complex.equivRealProdCLM.symm (S j m)-Complex.equivRealProdCLM.symm (S j i)) := by
      simp only [periodicFaceArea,S,i,l,m,hi',hl',hm',complexCross_apply,Complex.sub_re,Complex.sub_im]
      rfl
    change 0 < periodicFaceArea x y p f
    rw [hh,hs j l hl,hs j m hm,hs j i hi,hdiff,hdiff,complexCross_mul]
    exact mul_pos (Complex.normSq_pos.mpr (inv_ne_zero hU)) (markedDevelopment flipped q he.injective j).orientation
  let H₀ := chartHomeomorph flipped x y hy p hpos
  obtain ⟨J,hJ⟩ := complexTorus_rebase a b x y hy.ne' D refl hD hL
  let H := H₀.trans J
  let r := ‖D‖/(Real.sqrt k*‖U‖)
  have hr : 0 < r := div_pos (norm_pos_iff.mpr hD)
    (mul_pos (Real.sqrt_pos.mpr hk) (norm_pos_iff.mpr hU))
  let Q (i : Vertex) := r • q i
  let E := evaluateTriangles (faceChoice flipped) Q
  let F := E ∘ H.symm
  let L := (complexSimilarityLinear D refl).comp Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap
  let W (j : Fin 16) (i : Vertex) := L (S j i)
  have hQ : Topology.IsClosedEmbedding E := by
    let M : Point3 →ₗ[ℝ] Point3 := r • LinearMap.id
    let T : Point3 ≃ₜ Point3 := Homeomorph.smulOfNeZero r hr.ne'
    have hm : E = T ∘ evaluateTriangles (faceChoice flipped) q :=
      evaluateTriangles_comp_linear (faceChoice flipped) q M
    rw [hm]
    exact T.isClosedEmbedding.comp he
  have hfold (u : triangleWeightSpace (faceChoice flipped)) : F (H u) = E u := by simp [F]
  have hscale : r^2*k = ‖D‖^2/Complex.normSq U := by
    dsimp only [r]
    rw [div_pow,mul_pow,Real.sq_sqrt hk.le,Complex.normSq_eq_norm_sq]
    field_simp [hk.ne',norm_ne_zero_iff.mpr hU]
  have hedge (j : Fin 16) (i l : Vertex)
      (hi : i ∈ triangleVertexSet (markedFace flipped j)) (hl : l ∈ triangleVertexSet (markedFace flipped j)) :
      squared3 (Q l-Q i) = Complex.normSq (W j l-W j i) := by
    have H₁ : W j i = complexSimilarity D refl (P j i/U) := by
      change complexSimilarity D refl (Complex.equivRealProdCLM.symm (S j i)) = _
      rw [hs j i hi]
    have H₂ : W j l = complexSimilarity D refl (P j l/U) := by
      change complexSimilarity D refl (Complex.equivRealProdCLM.symm (S j l)) = _
      rw [hs j l hl]
    have hnorm : Complex.normSq (W j l-W j i) =
        ‖D‖^2*Complex.normSq (P j l/U-P j i/U) := by
      simp only [Complex.normSq_eq_norm_sq,← dist_eq_norm,H₁,H₂,complexSimilarity,complex_similarity_dist,mul_pow]
    unfold Q
    rw [← smul_sub,squared3_smul,hnorm,← sub_div,Complex.normSq_div]
    change r^2*spatialEdgeSq q i l = _
    rw [← (markedDevelopment flipped q he.injective j).edge_metric i hi l hl,← mul_assoc,hscale]
    change ‖D‖^2/Complex.normSq U*Complex.normSq (P j l-P j i) = _
    ring
  refine ⟨H,F,Q,W,?_,hC r hr⟩
  refine ⟨hQ.comp H.symm.isClosedEmbedding,hfold,?_,?_⟩
  · intro j u hu
    let t := ∑ i, u.val i • S j i
    have hdevelopment : H₀ u = projectPeriods (periodCoordinates x y t) := by
      change chartHomeomorph flipped x y hy p hpos u = _
      rw [chartHomeomorph_apply,periodicDevelopment_on_face _ _ (chartFaceSystem flipped).shared _ _ _ j u hu,
        facePeriodPoint_eq_coordinates x y hy.ne' p (chartLifts flipped j) u.val]
    have ht : (∑ i, u.val i • W j i) = complexSimilarity D refl (Complex.equivRealProdCLM.symm t) := by
      change (∑ i, u.val i • L (S j i)) = L (∑ i, u.val i • S j i)
      simp only [map_sum,map_smul]
    change J (H₀ u) = _
    rw [hdevelopment,hJ t,ht]
  · intro j u v hu hv
    rw [hfold,hfold]
    let f := chartLifts flipped j
    let T (i : Vertex) := Complex.equivRealProdCLM (W j i)
    have ht : (∑ i, u.val i • T i) - (∑ i, v.val i • T i) =
        Complex.equivRealProdCLM ((∑ i, u.val i • W j i) - ∑ i, v.val i • W j i) := by
      simp only [T,map_sub,map_sum,map_smul]
    rw [dist_eq_norm,← Complex.normSq_eq_norm_sq,← squared2_complex_pair]
    change squared3 ((∑ i, u.val i • Q i) - ∑ i, v.val i • Q i) =
      squared2 (Complex.equivRealProdCLM ((∑ i, u.val i • W j i) - ∑ i, v.val i • W j i))
    rw [← ht]
    have hd := (chartFaceSystem flipped).distinct j
    rw [lifted_affine_difference f hd Q u.val v.val hu hv,
      lifted_affine_difference f hd T u.val v.val hu hv]
    have hi : f.1.1 ∈ triangleVertexSet (markedFace flipped j) := by simp [f,markedFace,liftedVertices,triangleVertexSet_eq]
    have hl : f.2.1.1 ∈ triangleVertexSet (markedFace flipped j) := by simp [f,markedFace,liftedVertices,triangleVertexSet_eq]
    have hm : f.2.2.1 ∈ triangleVertexSet (markedFace flipped j) := by simp [f,markedFace,liftedVertices,triangleVertexSet_eq]
    have hm' (i l : Vertex) (hi : i ∈ triangleVertexSet (markedFace flipped j)) (hl : l ∈ triangleVertexSet (markedFace flipped j)) :
        squared3 (Q l-Q i) = squared2 (T l-T i) := by
      rw [show T l-T i = Complex.equivRealProdCLM (W j l-W j i) by simp [T],
        squared2_complex_pair,hedge j i l hi hl]
    exact triangle_squared_metric (T f.1.1) (T f.2.1.1) (T f.2.2.1) (Q f.1.1) (Q f.2.1.1) (Q f.2.2.1)
      (hm' _ _ hi hl) (hm' _ _ hi hm) (hm' _ _ hl hm) _ _

/-- Develop and rescale a closed embedded flat placement to its target lattice. -/
theorem realizes_of_markedShape (flipped : Bool) (q : Vertex → Point3)
    (he : Topology.IsClosedEmbedding (evaluateTriangles (faceChoice flipped) q))
    (hflat : ∀ v, coneAngles (faceChoice flipped) (Type2.euclideanPoint ∘ q) v = 2*Real.pi)
    (x y : ℝ) (hy : 0 < y)
    (hshape : chartMarkedShape flipped (spatialEdgeSq q) = (x : ℂ)+y*Complex.I)
    (a b D : ℂ) (refl : Bool) (hD : D ≠ 0)
    (hL : complexSimilarity D refl '' complexLattice 1 (x+y*Complex.I) = complexLattice a b) :
    ChartRealizes flipped a b :=
  (realizes_of_markedShape_with flipped q he hflat x y hy hshape a b D refl hD hL
    (C := fun _ => True) (fun _ _ => trivial)).realizes

private theorem chart_embedded_flat_markedShape (flipped : Bool) (w : ℝ) (hw : 1 ≤ w) :
    ∃ q : Vertex → Point3, Topology.IsClosedEmbedding (evaluateTriangles (faceChoice flipped) q) ∧
      (∀ v, coneAngles (faceChoice flipped) (Type2.euclideanPoint ∘ q) v = 2*Real.pi) ∧
      chartMarkedShape flipped (spatialEdgeSq q) = ⟨0,Real.sqrt w⟩ := by
  cases flipped
  · exact rectangular_embedded_flat_markedShape w hw
  · exact Type4.rectangular_embedded_flat_markedShape w hw

private theorem rectangular_of_similarity (flipped : Bool) (y : ℝ) (hy : 1 ≤ y) (a b D : ℂ) (hD : D ≠ 0)
    (hL : complexSimilarity D false '' complexLattice 1 ((y : ℂ)*Complex.I) = complexLattice a b) :
    ChartRealizes flipped a b := by
  have hyp : 0 < y := by linarith
  have hy2 : 1 ≤ y^2 := by nlinarith [sq_nonneg (y-1)]
  obtain ⟨q,he,hflat,hshape⟩ := chart_embedded_flat_markedShape flipped (y^2) hy2
  refine realizes_of_markedShape flipped q he hflat 0 y hyp ?_ a b D false hD ?_
  · rw [Real.sqrt_sq hyp.le] at hshape
    rw [hshape]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  · simpa only [Complex.ofReal_zero,zero_add] using hL

/-- A rectangular torus with aspect ratio at least one has a Type 7 origami realization. -/
theorem rectangular_normalized (y : ℝ) (hy : 1 ≤ y) : Realizes 1 ((y : ℂ)*Complex.I) := by
  apply rectangular_of_similarity false y hy _ _ 1 one_ne_zero
  have he : complexSimilarity 1 false = (fun z : ℂ => 1*z) := funext fun _ => by simp [complexSimilarity]
  rw [he,complexLattice_mul,mul_one,one_mul]

private theorem rectangular_ratio (a b : ℂ) (ho : (b/a).re = 0) :
    b/a = ((b/a).im : ℂ)*Complex.I := by
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,ho]

private theorem lattice_of_rectangular_ratio (a b : ℂ) (ha : a ≠ 0) (ho : (b/a).re = 0) :
    complexSimilarity a false '' complexLattice 1 ((|(b/a).im| : ℝ)*Complex.I) = complexLattice a b := by
  let r := (b/a).im
  have hb : b = (r : ℂ)*Complex.I*a := (div_eq_iff ha).mp (rectangular_ratio a b ho)
  have hfun : complexSimilarity a false = (fun z : ℂ => a*z) := funext fun _ => by simp [complexSimilarity]
  rw [hfun,complexLattice_mul,mul_one]
  change complexLattice a (a*((|r| : ℝ)*Complex.I)) = _
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr]
    congr 1
    rw [hb]
    ring
  · rw [abs_of_neg (lt_of_not_ge hr)]
    have he : a*(((-r : ℝ) : ℂ)*Complex.I) = -b := by
      rw [Complex.ofReal_neg,hb]
      ring
    rw [he,complexLattice_neg_right]

/-- Every rectangular flat torus has an eight-vertex Type 7 origami embedding.
The condition on the real part says that the two nonzero generators are perpendicular. -/
theorem chart_rectangular (flipped : Bool) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (ho : (b/a).re = 0) :
    ChartRealizes flipped a b := by
  let r := (b/a).im
  by_cases hr : 1 ≤ |r|
  · exact rectangular_of_similarity flipped |r| hr a b a ha (lattice_of_rectangular_ratio a b ha ho)
  · have hr₀ : r ≠ 0 := by
      intro hz
      have hq := rectangular_ratio a b ho
      change b/a = (r : ℂ)*Complex.I at hq
      rw [hz,Complex.ofReal_zero,zero_mul] at hq
      exact (div_ne_zero hb ha) hq
    have hq : a/b = ((-r⁻¹ : ℝ) : ℂ)*Complex.I := by
      rw [← inv_div,rectangular_ratio a b ho]
      change ((r : ℂ)*Complex.I)⁻¹ = _
      rw [mul_inv_rev,Complex.inv_I,Complex.ofReal_neg,Complex.ofReal_inv]
      ring
    have ho' : (a/b).re = 0 := by rw [hq]; simp [Complex.mul_re]
    have hy : 1 ≤ |(a/b).im| := by
      rw [hq]
      simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
        mul_one,zero_mul,add_zero,abs_neg,abs_inv] using
        (one_le_inv₀ (abs_pos.mpr hr₀)).mpr (le_of_lt (lt_of_not_ge hr))
    have hswap : complexLattice b a = complexLattice a b := by
      ext z
      constructor <;> rintro ⟨m,n,h⟩ <;> exact ⟨n,m,(add_comm _ _).trans h⟩
    apply rectangular_of_similarity flipped |(a/b).im| hy a b b hb
    exact (lattice_of_rectangular_ratio b a hb ho').trans hswap

theorem rectangular (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (ho : (b/a).re = 0) :
    Realizes a b :=
  chart_rectangular false a b ha hb ho

/-- A chart realization indexed by its labeled faces. -/
theorem chart_by_faces (flipped : Bool) (a b : ℂ) (h : ChartRealizes flipped a b) :
    ∃ (H : triangleWeightSpace (faceChoice flipped) ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles (faceChoice flipped) Q u) ∧
      (∀ f ∈ faceChoice flipped, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ faceChoice flipped, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  classical
  obtain ⟨H,F,Q,P,hE,hfold,hproj,hmetric⟩ := h
  have exists_lift (f : Triangle) (hf : f ∈ faceChoice flipped) : ∃ j : Fin 16, markedFace flipped j = f := exists_markedFace flipped f hf
  let index (f : Triangle) := if hf : f ∈ faceChoice flipped then (exists_lift f hf).choose else 0
  have hindex (f : Triangle) (hf : f ∈ faceChoice flipped) : markedFace flipped (index f) = f := by
    simp only [index,dite_eq_left hf]
    exact (exists_lift f hf).choose_spec
  refine ⟨H,F,Q,P ∘ index,hE,hfold,?_,?_⟩
  · intro f hf u hu
    exact hproj (index f) u (by simpa only [hindex f hf] using hu)
  · intro f hf u v hu hv
    exact hmetric (index f) u v (by simpa only [hindex f hf] using hu)
      (by simpa only [hindex f hf] using hv)

/-- The rectangular embedding, with its specified lift indexed by each labeled face. -/
theorem rectangular_by_faces (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (ho : (b/a).re = 0) :
    ∃ (H : triangleWeightSpace faces ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles faces Q u) ∧
      (∀ f ∈ faces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ faces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 :=
  chart_by_faces false a b (rectangular a b ha hb ho)

end OrigamiTorus.Type7

namespace OrigamiTorus.Type4

/-- Every rectangular lattice has a Type 4 realization, in the labels of the flipped chart. -/
theorem rectangular (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (ho : (b/a).re = 0) :
    Type7.ChartRealizes true a b :=
  Type7.chart_rectangular true a b ha hb ho

end OrigamiTorus.Type4
