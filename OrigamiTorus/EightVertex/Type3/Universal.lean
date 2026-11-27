module

public import OrigamiTorus.EightVertex.Type3.Periodic
public import OrigamiTorus.EightVertex.Type6.Tiling
public import OrigamiTorus.Lattice.LatticeTorus
import OrigamiTorus.EightVertex.Type6.Signs
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Tactic

/-! The published Type 3 triangulation realizes every rank-two lattice torus.

The fixed-period length equations implement the inflation in Remark 5.4 of
Doyle–Lander–Schwartz–Trettel. The quotient is identified using its positive
oriented triangles and its total area.
-/

public section

open Filter Set
open scoped Topology

namespace OrigamiTorus.Type3

open Type5 (squared2 squared3)

private theorem edgeTriangleSeparated (p : Vertex → ℝ × ℝ) (z : Vertex → ℝ)
    (hg : GenericLift p z) (hs : ∀ pair ∈ disjointPairs, isSeparated p z pair) :
    EdgeTriangleSeparated (fun i => ((p i).1,(p i).2,z i)) type3Faces := by
  rintro ⟨a,b⟩ he ⟨c,d,e⟩ hf hi
  have hm : ((a,b),(c,d,e)) ∈ disjointPairs := mem_disjointTests he hf hi
  have hc : disjointPairs.all (fun ((a,b),c,d,e) =>
      decide ([a,b,c,d,e].Pairwise (· ≠ ·))) = true := by decide +kernel
  rw [vertexHull_pair,vertexHull_triangle]
  exact separated_segment_disjoint_triangle p z a b c d e hg
    (of_decide_eq_true (List.all_eq_true.mp hc _ hm)) (hs _ hm)

/-- Affine coordinates of the lifted triangle in ordinary Euclidean units. -/
noncomputable def facePoint (second : Bool) (x y : ℝ) (m : SheetMotion)
    (j : Fin 16) (u : Vertex → ℝ) : ℝ × ℝ :=
  ∑ i, u i • physicalIntrinsicCorner second x y m (i,facePeriod (faceLifts j) i)

private theorem project_facePoint (second : Bool) (x y : ℝ) (hy : y ≠ 0) (m : SheetMotion)
    (j : Fin 16) (u : triangleWeightSpace type3Faces)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (faceLifts j)))) :
    periodicDevelopment faceLifts periodicFaceSystem.cover x (y^2)
      (movedIntrinsicPoint second x (y^2) m) u =
      projectPeriods (periodCoordinates x y (facePoint second x y m j u.val)) := by
  let q := movedIntrinsicPoint second x (y^2) m
  let f := faceLifts j
  let L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun p => (p.1,p.2/y)
      map_add' := fun a b => Prod.ext rfl (add_div a.2 b.2 y)
      map_smul' := by
        intro r p
        change (r*p.1,(r*p.2)/y) = (r*p.1,r*(p.2/y))
        rw [mul_div_assoc] }
  have hP : facePoint second x y m j u.val =
      L (∑ i, u.val i • translatePoint x (y^2) (facePeriod f i) (q i)) := by
    change (∑ i, u.val i • L (translatePoint x (y^2) (facePeriod f i) (q i))) = _
    simp only [map_sum,map_smul]
  have hcoord (p : ℝ × ℝ) : periodCoordinates x y (L p) = periodCoordinates x (y^2) p := by
    have h (r : ℝ) : r/y/y = r/y^2 := by rw [div_div,pow_two]
    apply Prod.ext <;> simp only [periodCoordinates,L,LinearMap.coe_mk,AddHom.coe_mk,h]
  rw [periodicDevelopment_on_face faceLifts periodicFaceSystem.cover periodicFaceSystem.shared
    x (y^2) q j u hu, facePeriodPoint_eq_coordinates _ _ (pow_ne_zero 2 hy), hP,hcoord]

private theorem weighted_face_metric (second : Bool) (x y : ℝ) (hy : y ≠ 0) (m : SheetMotion)
    (z : Vertex → ℝ) (t : ℝ) (hlen : fixedPeriodResidual edgeTable second x (y^2) z (t,m) = 0)
    (j : Fin 16) (u v : triangleWeightSpace type3Faces)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (faceLifts j))))
    (hv : v.val ∈ faceWeights (triangleVertexSet (liftedVertices (faceLifts j)))) :
    let E := evaluateTriangles type3Faces (physicalFoldedVertex second x y m z t)
    squared3 (E u - E v) =
      squared2 (facePoint second x y m j u.val - facePoint second x y m j v.val) := by
  dsimp only
  unfold evaluateTriangles evaluateWeights facePoint
  have hd := periodicFaceSystem.distinct j
  rw [lifted_affine_difference (faceLifts j) hd _ _ _ hu hv,
    lifted_affine_difference (faceLifts j) hd _ _ _ hu hv]
  obtain ⟨ha,hb,hc⟩ := facePeriod_correct (faceLifts j) hd
  simp only [ha,hb,hc]
  apply fixedPeriod_face_metric edgeTable second x y m z t hy hlen (faceLifts j)
  intro k hk
  exact side_index j k hk

/-- The two charts produce piecewise-isometric Type 3 embeddings of all reduced moduli. -/
theorem origamiTorus (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hy : 0 < y) (hw : 1-x^2 ≤ y^2) :
    ∃ (second : Bool) (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion)
      (H : triangleWeightSpace type3Faces ≃ₜ MarkedTorus) (F : MarkedTorus → Point3),
      chartDomain second x (y^2) ∧ 0 < t ∧ Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type3Faces (physicalFoldedVertex second x y m z t) u) ∧
      (∀ j u, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (faceLifts j))) →
        H u = projectPeriods (periodCoordinates x y (facePoint second x y m j u.val))) ∧
      ∀ j u v,
        u.val ∈ faceWeights (triangleVertexSet (liftedVertices (faceLifts j))) →
        v.val ∈ faceWeights (triangleVertexSet (liftedVertices (faceLifts j))) →
        squared3 (F (H u) - F (H v)) =
          squared2 (facePoint second x y m j u.val - facePoint second x y m j v.val) := by
  obtain ⟨second,hd⟩ : ∃ second, chartDomain second x (y^2) := by
    rcases le_total x (1/6) with h | h
    · exact ⟨false,hx,h,hw⟩
    · exact ⟨true,h,hx',hw⟩
  let z : Vertex → ℝ := generalPositionDirection second
  have hgen : GenericLift (stripPoint second x (y^2)) z :=
    type6_nonzeroDirection second x (y^2) hd
  obtain ⟨U,hsub,hU,hzero⟩ := mem_nhds_iff.mp (eventually_intrinsicPositive second x (y^2) hd)
  obtain ⟨t,m,ht,hm,hlen,_,hg,hs⟩ := fixedPeriodMatchedLift edgeTable disjointPairs second x (y^2) z
    (planarLengthsMatch second x (y^2)) (edgeDerivative_injective second x (y^2) hd)
    hgen (type3_strictSeparation second x (y^2) hd) hU hzero
  let p := movedFoldedPoint second x (y^2) m
  have hE := fixedPeriod_physical_embedding type3Faces second x y z t m hy.ne'
    (spatialTriangles_isClosedEmbedding p (fun i => t * z i) _
      hg (edgeTriangleSeparated p _ hg hs))
  let q := movedIntrinsicPoint second x (y^2) m
  let H := periodicFaceSystem.homeomorph x (y^2) (sq_pos_of_pos hy) q (hsub hm)
    (latticeTotalArea x (y^2) (pow_ne_zero 2 hy.ne') q)
  let E := evaluateTriangles type3Faces (physicalFoldedVertex second x y m z t)
  refine ⟨second,z,t,m,H,E ∘ H.symm,hd,ht,hE.comp H.symm.isClosedEmbedding,?_,?_,?_⟩
  · intro u
    simp [E]
  · intro j u hu
    rw [show H u = periodicDevelopment faceLifts periodicFaceSystem.cover x (y^2) q u from
      periodicFaceSystem.homeomorph_apply _ _ _ _ _ _ u]
    exact project_facePoint second x y hy.ne' m j u hu
  · intro j u v hu hv
    simpa [E,Function.comp_apply] using weighted_face_metric second x y hy.ne' m z t hlen j u v hu hv

private theorem complex_plane_dist_sq (p q : ℝ × ℝ) :
    dist (Complex.equivRealProdCLM.symm p) (Complex.equivRealProdCLM.symm q)^2 = squared2 (p-q) := by
  rw [dist_eq_norm, ← map_sub, Complex.sq_norm, Complex.equivRealProdCLM_symm_apply]
  simp [Complex.normSq_apply,squared2,Type5.dot]

/-- Every flat lattice torus has a piecewise-isometric embedding with the
published Type 3 face list (Doyle–Lander–Schwartz–Trettel, Theorem 1.1). -/
theorem universal (a b : ℂ) (ha : a ≠ 0) (hb : (b/a).im ≠ 0) :
    ∃ (H : triangleWeightSpace type3Faces ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles type3Faces Q u) ∧
      (∀ f ∈ type3Faces, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ type3Faces, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  classical
  obtain ⟨x,y,D,refl,hx,hx',hy,hw,hD,hL⟩ := reduced_complex_lattice a b ha hb
  obtain ⟨J,hJ⟩ := complexTorus_rebase a b x y hy.ne' D refl hD hL
  obtain ⟨second,z,t,m,H₀,F₀,_,_,hE,hfold,hproj,hmetric⟩ := origamiTorus x y hx hx' hy hw
  let S : Point3 ≃ₜ Point3 := Homeomorph.smulOfNeZero ‖D‖ (norm_ne_zero_iff.mpr hD)
  let H := H₀.trans J
  let F := S ∘ F₀ ∘ J.symm
  let Q (i : Vertex) := ‖D‖ • physicalFoldedVertex second x y m z t i
  let index (f : Triangle) :=
    if hf : f ∈ type3Faces then ((has_faceLift f).mp hf).choose else 0
  have hindex (f : Triangle) (hf : f ∈ type3Faces) :
      liftedVertices (faceLifts (index f)) = f := by
    simp only [index,dite_eq_left hf]
    exact ((has_faceLift f).mp hf).choose_spec
  let P (f : Triangle) (i : Vertex) := complexSimilarity D refl
    (Complex.equivRealProdCLM.symm (physicalIntrinsicCorner second x y m
      (i,facePeriod (faceLifts (index f)) i)))
  have hP (f : Triangle) (u : Vertex → ℝ) : (∑ i, u i • P f i) =
      complexSimilarity D refl (Complex.equivRealProdCLM.symm (facePoint second x y m (index f) u)) := by
    let L := (complexSimilarityLinear D refl).comp Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap
    change (∑ i, u i • L (physicalIntrinsicCorner second x y m (i,facePeriod (faceLifts (index f)) i))) =
      L (∑ i, u i • physicalIntrinsicCorner second x y m (i,facePeriod (faceLifts (index f)) i))
    simp only [map_sum,map_smul]
  refine ⟨H,F,Q,P,S.isClosedEmbedding.comp (hE.comp J.symm.isClosedEmbedding),?_,?_,?_⟩
  · intro u
    change S (F₀ (J.symm (J (H₀ u)))) = _
    rw [J.symm_apply_apply,hfold]
    let L : Point3 →ₗ[ℝ] Point3 := ‖D‖ • LinearMap.id
    exact (congrFun (evaluateTriangles_comp_linear type3Faces
      (physicalFoldedVertex second x y m z t) L) u).symm
  · intro f hf u hu
    change J (H₀ u) = _
    rw [hP,hproj (index f) u (by simpa only [hindex f hf] using hu),hJ]
  · intro f hf u v hu hv
    change squared3 (S (F₀ (J.symm (J (H₀ u)))) - S (F₀ (J.symm (J (H₀ v))))) = _
    rw [J.symm_apply_apply,J.symm_apply_apply,hP,hP]
    change squared3 (‖D‖ • F₀ (H₀ u) - ‖D‖ • F₀ (H₀ v)) = _
    rw [← smul_sub,squared3_smul,hmetric (index f) u v
      (by simpa only [hindex f hf] using hu) (by simpa only [hindex f hf] using hv)]
    let p := Complex.equivRealProdCLM.symm (facePoint second x y m (index f) u.val)
    let q := Complex.equivRealProdCLM.symm (facePoint second x y m (index f) v.val)
    change _ = dist (complexSimilarity D refl p) (complexSimilarity D refl q)^2
    rw [show dist (complexSimilarity D refl p) (complexSimilarity D refl q) = ‖D‖*dist p q
      from complex_similarity_dist D refl p q, mul_pow,complex_plane_dist_sq]

end OrigamiTorus.Type3
