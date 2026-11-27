module

public import OrigamiTorus.Type5MarkedReduction
public import OrigamiTorus.FaceDevelopment
import Mathlib.Tactic

/-! Gauge the intrinsic lifts and put the spatial anchor triangle in its
intrinsic Euclidean coordinates before applying the finite reconstruction. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type5

open Type2 (euclideanPoint euclideanPoint_injective)

/-- The period shifts after changing the representatives so that all shifts
out of vertex 1 vanish. -/
def gaugedShifts (K : EdgeShifts) : EdgeShifts :=
  fun a b => K a b+K 1 a-K 1 b

/-- Representatives after the same change of lifts and translation of vertex 1
to the origin. -/
def gaugedPlacement (K : EdgeShifts) (p : Vertex → Plane ℝ) : Vertex → Plane ℝ :=
  fun a => p a+K 1 a-p 1

theorem gaugedRealization {K : EdgeShifts} {p : Vertex → Plane ℝ} {q : Vertex → Point3}
    (h : MarkedRealization K p q) (hK : ∀ a b, K b a = -K a b)
    (hc : ∀ f ∈ faces, K f.1 f.2.1+K f.2.1 f.2.2+K f.2.2 f.1 = 0) :
    GaugedShifts (gaugedShifts K) ∧ gaugedPlacement K p 1 = 0 ∧
      MarkedRealization (gaugedShifts K) (gaugedPlacement K p) q := by
  have h₁ : K 1 1 = 0 := by
    have hx := congrArg Prod.fst (hK 1 1)
    have hy := congrArg Prod.snd (hK 1 1)
    apply Prod.ext
    · change (K 1 1).1 = 0
      simp only [Prod.fst_neg] at hx
      linarith
    · change (K 1 1).2 = 0
      simp only [Prod.snd_neg] at hy
      linarith
  have hd (a b : Vertex) :
      gaugedPlacement K p b+gaugedShifts K a b-gaugedPlacement K p a = p b+K a b-p a := by
    simp only [gaugedPlacement,gaugedShifts]
    abel
  refine ⟨⟨?_,?_,?_⟩,?_,⟨h.embedding,h.flat,?_,?_⟩⟩
  · intro a b
    simp only [gaugedShifts,hK a b]
    abel
  · intro a
    simp [gaugedShifts,h₁]
  · intro f hf
    unfold gaugedShifts
    calc _ = _ := by abel
         _ = 0 := hc f hf
  · simp [gaugedPlacement,h₁]
  · intro a b hab
    rw [hd]
    exact h.edge_length a b hab
  · intro f hf
    unfold markedFaceCross
    rw [hd,hd]
    exact h.nondegenerate f hf

private def euclideanCoordinates : Point3 ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearEquiv.ofBijective euclideanPoint ⟨euclideanPoint_injective,by
    intro v
    let x := WithLp.ofLp v
    refine ⟨(x 0,x 1,x 2),?_⟩
    rw [← WithLp.toLp_ofLp (2 : ENNReal) v]
    apply congrArg (WithLp.toLp (2 : ENNReal))
    funext i
    fin_cases i <;> rfl⟩

private def spatialCombination (x y : Point3) : Plane ℝ →ₗ[ℝ] Point3 :=
  { toFun := fun t => smul3 t.1 x+smul3 t.2 y
    map_add' := by intros; ext <;> simp [smul3,smul2,atHeight,horizontal] <;> ring
    map_smul' := by intros; ext <;> simp [smul3,smul2,atHeight,horizontal] <;> ring }

private theorem spatialCombination_flat_injective {a b : Plane ℝ} (h : cross a b ≠ 0) :
    Function.Injective (spatialCombination (atHeight a 0) (atHeight b 0)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro t ht
  have hx := congrArg Prod.fst ht
  have hy := congrArg (fun r : Point3 => r.2.1) ht
  simp only [spatialCombination,LinearMap.coe_mk,AddHom.coe_mk,smul3,smul2,atHeight,horizontal,
    Prod.fst_add,Prod.snd_add,Prod.fst_zero,Prod.snd_zero] at hx hy
  apply Prod.ext
  · change t.1 = 0
    apply (mul_left_cancel₀ h)
    simp only [cross]
    linear_combination b.2*hx-b.1*hy
  · change t.2 = 0
    apply (mul_left_cancel₀ h)
    simp only [cross]
    linear_combination a.1*hy-a.2*hx

private theorem euclidean_isometry_of_anchor_lengths (x y : Point3) (a b : Plane ℝ)
    (h : cross a b ≠ 0) (hx : squared3 x = squared2 a) (hy : squared3 y = squared2 b)
    (hxy : squared3 (y-x) = squared2 (b-a)) :
    ∃ I : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      I (euclideanPoint x) = euclideanPoint (atHeight a 0) ∧
      I (euclideanPoint y) = euclideanPoint (atHeight b 0) := by
  let F := euclideanPoint.comp (spatialCombination x y)
  let G := euclideanPoint.comp (spatialCombination (atHeight a 0) (atHeight b 0))
  have hn (t : Plane ℝ) : ‖G t‖ = ‖F t‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖euclideanPoint (smul3 t.1 (atHeight a 0)+smul3 t.2 (atHeight b 0))‖^2 =
      ‖euclideanPoint (smul3 t.1 x+smul3 t.2 y)‖^2
    rw [euclideanPoint_norm_sq,euclideanPoint_norm_sq]
    have h₁ : squared3 (x-0) = squared2 (a-0) := by simpa only [sub_zero]
    have h₂ : squared3 (y-0) = squared2 (b-0) := by simpa only [sub_zero]
    have he := triangle_squared_metric 0 a b 0 x y h₁ h₂ hxy t.1 t.2
    simpa [sub_zero,squared3,horizontal,smul3,smul2,atHeight] using he.symm
  have hFi : Function.Injective F := by
    apply (injective_iff_map_eq_zero F).mpr
    intro t ht
    have hG := (norm_eq_zero.mp (by rw [hn,ht,norm_zero] : ‖G t‖ = 0))
    exact (euclideanPoint_injective.comp (spatialCombination_flat_injective h)) (hG.trans G.map_zero.symm)
  let E := LinearEquiv.ofInjective F hFi
  let I : F.range →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    { toLinearMap := G.comp E.symm.toLinearMap
      norm_map' := by
        intro r
        change ‖G (E.symm r)‖ = ‖(r : EuclideanSpace ℝ (Fin 3))‖
        rw [hn,LinearEquiv.ofInjective_symm_apply] }
  have hI (t : Plane ℝ) : I.extend (F t) = G t := by
    rw [← LinearEquiv.ofInjective_apply F (h := hFi) t,LinearIsometry.extend_apply]
    change G (E.symm (E t)) = G t
    rw [E.symm_apply_apply]
  refine ⟨I.extend,?_,?_⟩
  · simpa [F,G,spatialCombination,smul3,smul2,atHeight,horizontal] using hI (1,0)
  · simpa [F,G,spatialCombination,smul3,smul2,atHeight,horizontal] using hI (0,1)

/-- Congruent side vectors on the anchor plane extend to a rigid linear map
on the three spatial coordinates. -/
theorem rigid_map_of_triangle_lengths (x y : Point3) (a b : Plane ℝ)
    (h : cross a b ≠ 0) (hx : squared3 x = squared2 a) (hy : squared3 y = squared2 b)
    (hxy : squared3 (y-x) = squared2 (b-a)) :
    ∃ T : Point3 →ₗ[ℝ] Point3, Function.Injective T ∧ (∀ z, squared3 (T z) = squared3 z) ∧
      T x = atHeight a 0 ∧ T y = atHeight b 0 := by
  obtain ⟨I,hI₁,hI₂⟩ := euclidean_isometry_of_anchor_lengths x y a b h hx hy hxy
  let T := euclideanCoordinates.symm.toLinearMap.comp (I.toLinearMap.comp euclideanPoint)
  have hT (z : Point3) : euclideanPoint (T z) = I (euclideanPoint z) :=
    euclideanCoordinates.apply_symm_apply _
  refine ⟨T,euclideanCoordinates.symm.injective.comp (I.injective.comp euclideanPoint_injective),
    fun z => ?_,euclideanPoint_injective ((hT x).trans hI₁),
    euclideanPoint_injective ((hT y).trans hI₂)⟩
  rw [← euclideanPoint_norm_sq,← euclideanPoint_norm_sq,hT,I.norm_map]

/-- A rigid change of spatial coordinates puts the three anchors at their
specified intrinsic locations without changing any edge length or flatness. -/
theorem normalize_spatial_anchors {K : EdgeShifts} {p : Vertex → Plane ℝ} {q : Vertex → Point3}
    (hK : GaugedShifts K) (h : MarkedRealization K p q) (hp : p 1 = 0) :
    ∃ (T : Point3 →ₗ[ℝ] Point3) (r : Vertex → Point3),
      Function.Injective T ∧ (∀ x, squared3 (T x) = squared3 x) ∧
      (∀ i, r i = T (q i-q 1)) ∧
      MarkedRealization K p r ∧ r 1 = 0 ∧ r 2 = atHeight (p 2) 0 ∧ r 5 = atHeight (p 5) 0 ∧
      cross (p 2) (p 5) ≠ 0 := by
  have hface : (1,5,2) ∈ faces := by decide +kernel
  have hK₂₅ : K 2 5 = 0 := by
    have hc := hK.closed _ hface
    change K 1 5+K 5 2+K 2 1 = 0 at hc
    rw [hK.anchor,hK.skew 2 5,hK.skew 1 2,hK.anchor] at hc
    simpa using hc
  have hAB : cross (p 2) (p 5) ≠ 0 := by
    have hm := h.nondegenerate _ hface
    change cross (p 5+K 1 5-p 1) (p 2+K 1 2-p 1) ≠ 0 at hm
    rw [hK.anchor,hK.anchor,hp,add_zero,add_zero,sub_zero,sub_zero] at hm
    intro hz
    apply hm
    simp only [cross] at hz ⊢
    linear_combination -hz
  have h₂ : squared3 (q 2-q 1) = squared2 (p 2) := by
    simpa [hK.anchor,hp] using h.edge_length 1 2 ((adjacency_test 1 2).mpr (by decide +kernel))
  have h₅ : squared3 (q 5-q 1) = squared2 (p 5) := by
    simpa [hK.anchor,hp] using h.edge_length 1 5 ((adjacency_test 1 5).mpr (by decide +kernel))
  have h₂₅ : squared3 ((q 5-q 1)-(q 2-q 1)) = squared2 (p 5-p 2) := by
    rw [show (q 5-q 1)-(q 2-q 1) = q 5-q 2 by abel]
    simpa [hK₂₅] using h.edge_length 2 5 ((adjacency_test 2 5).mpr (by decide +kernel))
  obtain ⟨I,hI₂,hI₅⟩ := euclidean_isometry_of_anchor_lengths
    (q 2-q 1) (q 5-q 1) (p 2) (p 5) hAB h₂ h₅ h₂₅
  let T := euclideanCoordinates.symm.toLinearMap.comp (I.toLinearMap.comp euclideanPoint)
  have hT (x : Point3) : euclideanPoint (T x) = I (euclideanPoint x) :=
    euclideanCoordinates.apply_symm_apply _
  have hTi : Function.Injective T := euclideanCoordinates.symm.injective.comp
    (I.injective.comp euclideanPoint_injective)
  have hTnorm (x : Point3) : squared3 (T x) = squared3 x := by
    rw [← euclideanPoint_norm_sq,← euclideanPoint_norm_sq,hT,I.norm_map]
  let r (i : Vertex) := T (q i-q 1)
  have hr (i j : Vertex) : r j-r i = T (q j-q i) := by
    simp only [r,← map_sub]
    congr 1
    abel
  have hmap (w : triangleWeightSpace faces) :
      evaluateTriangles faces r w = T (evaluateTriangles faces q w-q 1) := by
    have hm : ∑ i, w.val i = 1 := by
      obtain ⟨f,hf,hfw⟩ := w.property
      exact hfw.2.1
    let q₀ (i : Vertex) := q i-q 1
    have ht : evaluateTriangles faces q₀ w = evaluateTriangles faces q w-q 1 := by
      simp only [evaluateTriangles,evaluateWeights,q₀,smul_sub,Finset.sum_sub_distrib,
        ← Finset.sum_smul,hm,one_smul]
    change evaluateTriangles faces (T ∘ q₀) w = _
    rw [evaluateTriangles_comp_linear,Function.comp_apply,ht]
  have hre : Function.Injective (evaluateTriangles faces r) := by
    intro u v he
    rw [hmap,hmap] at he
    have he' := hTi he
    exact h.embedding (sub_left_inj.mp he')
  have hFlat (v : Vertex) : FlatAt r v := by
    rw [flatAt_iff_coneAngles]
    have hd (a : Vertex) : euclideanPoint (r a)-euclideanPoint (r v) =
        I (euclideanPoint (q a)-euclideanPoint (q v)) := by
      rw [← map_sub,hr,hT,map_sub]
    have hθ : coneAngles faces (euclideanPoint ∘ r) v = coneAngles faces (euclideanPoint ∘ q) v := by
      unfold coneAngles
      apply congrArg List.sum
      apply List.map_congr_left
      intro f hf
      rcases cornerRays v f with _ | ⟨a,b⟩
      · rfl
      · change InnerProductGeometry.angle (euclideanPoint (r a)-euclideanPoint (r v))
          (euclideanPoint (r b)-euclideanPoint (r v)) = _
        rw [hd,hd,I.angle_map]
        rfl
    rw [hθ]
    exact (flatAt_iff_coneAngles q v).mp (h.flat v)
  have h₂' : r 2 = atHeight (p 2) 0 := euclideanPoint_injective ((hT _).trans hI₂)
  have h₅' : r 5 = atHeight (p 5) 0 := euclideanPoint_injective ((hT _).trans hI₅)
  exact ⟨T,r,hTi,hTnorm,fun _ => rfl,⟨hre,hFlat,
    fun a b hab => by rw [hr,hTnorm]; exact h.edge_length a b hab,h.nondegenerate⟩,
    by simp [r],h₂',h₅',hAB⟩

/-- After a change of lifts and a rigid spatial motion an arbitrary embedded
marked realization is among the at most 32 exact candidates for its four
gauged core points. -/
theorem marked_reduction_complete {K : EdgeShifts} {p : Vertex → Plane ℝ} {q : Vertex → Point3}
    (h : MarkedRealization K p q) (hK : ∀ a b, K b a = -K a b)
    (hc : ∀ f ∈ faces, K f.1 f.2.1+K f.2.1 f.2.2+K f.2.2 f.1 = 0) :
    let k := gaugedShifts K
    let u := gaugedPlacement K p
    let C := markedCandidates k (CorePositions.ofPlacement u)
    C.length ≤ 32 ∧
      ∃ (T : Point3 →ₗ[ℝ] Point3) (r : Vertex → Point3),
        Function.Injective T ∧ (∀ x, squared3 (T x) = squared3 x) ∧
        (∀ i, r i = T (q i-q 1)) ∧ MarkedRealization k u r ∧
        (r 3,r 4,(u 0,r 0),(u 6,r 6),(u 7,r 7)) ∈ C := by
  dsimp only
  obtain ⟨hk,hu,hr⟩ := gaugedRealization h hK hc
  obtain ⟨T,r,hTi,hT,hR,hM,h₁,h₂,h₅,hAB⟩ := normalize_spatial_anchors hk hr hu
  exact ⟨markedCandidates_length _ _,T,r,hTi,hT,hR,hM,
    markedCandidates_complete hk hM hu h₁ h₂ h₅ hAB⟩

end OrigamiTorus.Type5
