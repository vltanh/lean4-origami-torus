module

public import OrigamiTorus.Geometry.PlanarBoundary
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! The straight section of a compact convex body in an affine plane. -/

public section

open Filter Set
open scoped Topology

namespace OrigamiTorus

private theorem interior_point_same_side {K : Set Point3} (hK : Convex ℝ K)
    (L : Point3 →ₗ[ℝ] ℝ) {y x : Point3} (hy : y ∈ intrinsicInterior ℝ K)
    (hx : x ∈ K) (hxL : 0 < L x) : ∃ z ∈ intrinsicInterior ℝ K, 0 < L z := by
  let f : ℝ →ᵃ[ℝ] Point3 := AffineMap.lineMap y x
  have hf : Continuous (fun t : ℝ => L (f t)) :=
    L.continuous_of_finiteDimensional.comp AffineMap.lineMap_continuous
  have hfx : 0 < L (f 1) := by
    rw [show f 1 = x from AffineMap.lineMap_apply_one y x]
    exact hxL
  have hpos : ∀ᶠ t : ℝ in 𝓝 1, 0 < t := isOpen_Ioi.mem_nhds (zero_lt_one : (0 : ℝ) < 1)
  have hnear : ∀ᶠ t : ℝ in 𝓝 1, 0 < t ∧ 0 < L (f t) :=
    hpos.and ((isOpen_lt continuous_const hf).mem_nhds hfx)
  obtain ⟨t,ht₁,ht₀,htL⟩ := hnear.exists_lt
  have hseg : f t ∈ openSegment ℝ y x := lineMap_mem_openSegment ℝ y x ⟨ht₀,ht₁⟩
  exact ⟨f t,hK.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
    hy (subset_intrinsicClosure hx) hseg,htL⟩

/-- A genuine cutting line passes through the relative interior. -/
theorem exists_intrinsicInterior_on_cut {K : Set Point3} (hK : Convex ℝ K)
    (L : Point3 →ₗ[ℝ] ℝ) (hp : ∃ x ∈ K, 0 < L x) (hm : ∃ x ∈ K, L x < 0) :
    ∃ z ∈ intrinsicInterior ℝ K, L z = 0 := by
  obtain ⟨p,hp,hLp⟩ := hp
  obtain ⟨m,hm,hLm⟩ := hm
  obtain ⟨y,hy⟩ := Set.Nonempty.intrinsicInterior hK ⟨p,hp⟩
  obtain ⟨a,ha,hLa⟩ := interior_point_same_side hK L hy hp hLp
  obtain ⟨b,hb,hLb⟩ := interior_point_same_side hK (-L) hy hm (neg_pos.mpr hLm)
  have hLb' : L b < 0 := neg_pos.mp hLb
  let t := L a/(L a-L b)
  have hd : 0 < L a-L b := sub_pos.mpr (hLb'.trans hLa)
  have ht₀ : 0 < t := div_pos hLa hd
  have ht₁ : t < 1 := (div_lt_one hd).mpr (by linarith)
  refine ⟨AffineMap.lineMap a b t,
    hK.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior ha
      (subset_intrinsicClosure (intrinsicInterior_subset hb))
      (lineMap_mem_openSegment ℝ a b ⟨ht₀,ht₁⟩),?_⟩
  rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul]
  change (1-t)*L a+t*L b = 0
  dsimp [t]
  field_simp
  ring

private theorem exists_cut_parameter {A : AffineSubspace ℝ Point3}
    (hd : Module.finrank ℝ A.direction = 2) (L : Point3 →ₗ[ℝ] ℝ)
    {z p : Point3} (hz : z ∈ A) (hLz : L z = 0) (hp : p ∈ A) (hLp : L p ≠ 0) :
    ∃ f : ℝ →ᵃ[ℝ] Point3, f 0 = z ∧ Topology.IsClosedEmbedding f ∧
      Set.range f = (A : Set Point3) ∩ {x | L x = 0} := by
  let M := L.comp A.direction.subtype
  have hM : M ≠ 0 := by
    intro he
    have hmem : p-z ∈ A.direction := A.vsub_mem_direction hp hz
    have HH := congrFun (congrArg DFunLike.coe he) (⟨p-z,hmem⟩ : A.direction)
    change L (p-z) = 0 at HH
    rw [map_sub,hLz,sub_zero] at HH
    exact hLp HH
  have hr₁ : 1 ≤ Module.finrank ℝ M.range := Submodule.one_le_finrank_iff.mpr
    (fun he => hM (LinearMap.range_eq_bot.mp he))
  have hr₂ : Module.finrank ℝ M.range ≤ 1 := by simpa using Submodule.finrank_le M.range
  have hk := M.finrank_range_add_finrank_ker
  rw [hd,le_antisymm hr₂ hr₁] at hk
  have hk₁ : Module.finrank ℝ M.ker = 1 := by omega
  have hkne : M.ker ≠ ⊥ := Submodule.one_le_finrank_iff.mp hk₁.ge
  obtain ⟨w,hw,hwne⟩ := M.ker.ne_bot_iff.mp hkne
  let v : M.ker := ⟨w,hw⟩
  have hvne : v ≠ 0 := fun he => hwne (congrArg Subtype.val he)
  have hspan := (finrank_eq_one_iff_of_ne_zero' v hvne).mp hk₁
  let J : ℝ →ₗ[ℝ] Point3 := LinearMap.toSpanSingleton ℝ Point3 (w : Point3)
  let f : ℝ →ᵃ[ℝ] Point3 := (AffineEquiv.constVAdd ℝ Point3 z).toAffineMap.comp J.toAffineMap
  have hf (t : ℝ) : f t = z + J t := rfl
  have hw' : (w : Point3) ≠ 0 := fun he => hwne (Subtype.ext he)
  have hE : Topology.IsClosedEmbedding f :=
    (Homeomorph.addLeft z).isClosedEmbedding.comp
      (LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_toSpanSingleton ℝ hw'))
  refine ⟨f,by simp [hf],hE,Set.ext fun x => ?_⟩
  constructor
  · rintro ⟨t,rfl⟩
    have hdir : J t ∈ A.direction := A.direction.smul_mem t w.property
    have hk : L (J t) = 0 := by
      change L (t • (w : Point3)) = 0
      rw [map_smul,show L (w : Point3) = 0 from hw,smul_zero]
    refine ⟨?_,?_⟩
    · change f t ∈ A
      have hm : J t +ᵥ z ∈ A := A.vadd_mem_of_mem_direction hdir hz
      simpa only [hf, vadd_eq_add, add_comm] using hm
    · change L (f t) = 0
      rw [hf, map_add, hLz, hk, add_zero]
  · rintro ⟨hx,hLx⟩
    let u : A.direction := ⟨x-z,A.vsub_mem_direction hx hz⟩
    have hu : u ∈ M.ker := LinearMap.mem_ker.mpr (by change L (x-z) = 0; rw [map_sub,hLx,hLz,sub_zero])
    obtain ⟨t,he⟩ := hspan ⟨u,hu⟩
    have hJt : J t = x-z := congrArg (fun w : M.ker => (w.val : Point3)) he
    exact ⟨t,by rw [hf,hJt]; abel⟩

/-- A line cutting a compact convex planar set in both directions gives a
nondegenerate chord and meets the relative boundary only at its endpoints. -/
theorem planarCut_chord {K : Set Point3} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hd : Module.finrank ℝ (affineSpan ℝ K).direction = 2) (L : Point3 →ₗ[ℝ] ℝ)
    (hp : ∃ x ∈ K, 0 < L x) (hm : ∃ x ∈ K, L x < 0) :
    ∃ a b : Point3, a ≠ b ∧
      K ∩ {x | L x = 0} = segment ℝ a b ∧
      intrinsicFrontier ℝ K ∩ {x | L x = 0} = {a,b} := by
  obtain ⟨z,hz,hLz⟩ := exists_intrinsicInterior_on_cut hconv L hp hm
  obtain ⟨p,hpK,hpL⟩ := hp
  let A := affineSpan ℝ K
  obtain ⟨f,hf₀,hf,hRange⟩ := exists_cut_parameter hd L
    (subset_affineSpan ℝ K (intrinsicInterior_subset hz)) hLz (subset_affineSpan ℝ K hpK) hpL.ne'
  have hfA (t : ℝ) : f t ∈ A := (hRange ▸ mem_range_self t).1
  have hfL (t : ℝ) : L (f t) = 0 := (hRange ▸ mem_range_self t).2
  let g (t : ℝ) : A := ⟨f t,hfA t⟩
  have hg : Continuous g := hf.continuous.subtype_mk _
  let S : Set ℝ := f ⁻¹' K
  have hSc : IsCompact S := hf.isCompact_preimage hK
  have hSconv : Convex ℝ S := hconv.affine_preimage f
  have hint (t : ℝ) (ht : f t ∈ intrinsicInterior ℝ K) : t ∈ interior S := by
    obtain ⟨y,hy,he⟩ := mem_intrinsicInterior.mp ht
    have he' : y = g t := Subtype.ext he
    rw [he'] at hy
    rw [mem_interior_iff_mem_nhds]
    exact hg.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hy)
  have h0 : (0 : ℝ) ∈ interior S := hint 0 (hf₀.symm ▸ hz)
  have hS : S.Nonempty := ⟨0,interior_subset h0⟩
  obtain ⟨a,ha,hmin⟩ := hSc.exists_isMinOn hS continuousOn_id
  obtain ⟨b,hb,hmax⟩ := hSc.exists_isMaxOn hS continuousOn_id
  have hle : a ≤ b := hmin hb
  have he : S = Icc a b := Set.Subset.antisymm
    (fun t ht => ⟨hmin ht,hmax ht⟩) (segment_eq_Icc hle ▸ hSconv.segment_subset ha hb)
  have h0' : a < 0 ∧ 0 < b := by rwa [he, interior_Icc] at h0
  have hfrontSubset : intrinsicFrontier ℝ K ⊆ K := by
    rw [← closure_sdiff_intrinsicInterior,hK.isClosed.closure_eq]
    exact sdiff_subset
  have he₁ : f '' S = K ∩ {x | L x = 0} := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨ht,hfL t⟩
    · rintro ⟨hx,hLx⟩
      obtain ⟨t,rfl⟩ := hRange.symm ▸ (show x ∈ (A : Set Point3) ∩ {x | L x = 0} from
        ⟨subset_affineSpan ℝ K hx,hLx⟩)
      exact ⟨t,hx,rfl⟩
  have hmid (t : ℝ) (ht : t ∈ Ioo a b) : f t ∈ intrinsicInterior ℝ K := by
    rcases lt_trichotomy t 0 with hl | he | hr
    · have hseg : f t ∈ openSegment ℝ (f a) (f 0) := by
        rw [← image_openSegment, openSegment_eq_Ioo h0'.1]
        exact ⟨t,⟨ht.1,hl⟩,rfl⟩
      rw [openSegment_symm] at hseg
      exact hconv.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
        (hf₀.symm ▸ hz) (subset_intrinsicClosure (show f a ∈ K from ha)) hseg
    · exact he.symm ▸ (hf₀.symm ▸ hz)
    · have hseg : f t ∈ openSegment ℝ (f 0) (f b) := by
        rw [← image_openSegment, openSegment_eq_Ioo h0'.2]
        exact ⟨t,⟨hr,ht.2⟩,rfl⟩
      exact hconv.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior
        (hf₀.symm ▸ hz) (subset_intrinsicClosure (show f b ∈ K from hb)) hseg
  have hEnd (t : ℝ) (ht : t ∈ S) (hEnd : t = a ∨ t = b) : f t ∈ intrinsicFrontier ℝ K := by
    rw [← closure_sdiff_intrinsicInterior]
    refine ⟨subset_closure ht,fun hI => ?_⟩
    have hin := hint t hI
    rw [he,interior_Icc] at hin
    rcases hEnd with rfl | rfl
    · exact lt_irrefl _ hin.1
    · exact lt_irrefl _ hin.2
  refine ⟨f a,f b,fun hab => (h0'.1.trans h0'.2).ne (hf.injective hab),?_,?_⟩
  · rw [← he₁,he,← segment_eq_Icc hle,image_segment]
  · ext x
    constructor
    · rintro ⟨hx,hLx⟩
      obtain ⟨t,ht,rfl⟩ := he₁.symm ▸ (show x ∈ K ∩ {x | L x = 0} from ⟨hfrontSubset hx,hLx⟩)
      rw [he] at ht
      have hnot : t ∉ Ioo a b := fun h => by
        rw [← closure_sdiff_intrinsicInterior] at hx
        exact hx.2 (hmid t h)
      simp only [mem_insert_iff,mem_singleton_iff]
      rcases eq_or_lt_of_le ht.1 with e | hlt
      · exact Or.inl (congrArg f e.symm)
      · exact Or.inr (congrArg f (le_antisymm ht.2 (le_of_not_gt (fun h => hnot ⟨hlt,h⟩))))
    · simp only [mem_insert_iff,mem_singleton_iff]
      rintro (rfl | rfl)
      · exact ⟨hEnd a ha (Or.inl rfl),hfL a⟩
      · exact ⟨hEnd b hb (Or.inr rfl),hfL b⟩

private theorem affineSpan_cut_eq {K : Set Point3} (L : Point3 →ₗ[ℝ] ℝ)
    {z : Point3} (hz : z ∈ intrinsicInterior ℝ K) (hLz : 0 < L z) :
    affineSpan ℝ (K ∩ {x | 0 ≤ L x}) = affineSpan ℝ K := by
  obtain ⟨zA,hzA,rfl⟩ := mem_intrinsicInterior.mp hz
  let A := affineSpan ℝ K
  let _ : Nonempty A := ⟨zA⟩
  let C := K ∩ {x | 0 ≤ L x}
  apply le_antisymm (affineSpan_mono ℝ inter_subset_left)
  intro x hx
  let xA : A := ⟨x,hx⟩
  let f : ℝ →ᵃ[ℝ] A := AffineMap.lineMap zA xA
  have hf : Continuous f := AffineMap.lineMap_continuous
  have h₀ : f 0 = zA := AffineMap.lineMap_apply_zero _ _
  have hK : ∀ᶠ t : ℝ in 𝓝 0, (f t : Point3) ∈ K :=
    (hf.tendsto' _ _ h₀).eventually_mem (mem_interior_iff_mem_nhds.mp hzA)
  have hcont : Continuous (fun t : ℝ => L (f t : Point3)) :=
    L.continuous_of_finiteDimensional.comp (continuous_subtype_val.comp hf)
  have hL : ∀ᶠ t : ℝ in 𝓝 0, 0 < L (f t : Point3) :=
    (isOpen_lt continuous_const hcont).mem_nhds (by change 0 < L (f 0 : Point3); rwa [h₀])
  obtain ⟨t,ht,htK,htL⟩ := (hK.and hL).exists_gt
  have hzK : zA ∈ (Subtype.val ⁻¹' K : Set A) := interior_subset hzA
  have hzC : (zA : Point3) ∈ C := ⟨hzK,hLz.le⟩
  have htC : (f t : Point3) ∈ C := ⟨htK,htL.le⟩
  have hline := AffineMap.lineMap_mem t⁻¹ (subset_affineSpan ℝ C hzC) (subset_affineSpan ℝ C htC)
  have he : AffineMap.lineMap (zA : Point3) (f t : Point3) t⁻¹ = x := by
    change AffineMap.lineMap (zA : Point3) (AffineMap.lineMap zA xA t : Point3) t⁻¹ = x
    have hco : (AffineMap.lineMap zA xA t : Point3) = AffineMap.lineMap (zA : Point3) x t :=
      A.subtype.apply_lineMap zA xA t
    rw [hco,AffineMap.lineMap_apply_module',AffineMap.lineMap_apply_module']
    rw [add_sub_cancel_right,smul_smul, inv_mul_cancel₀ ht.ne',one_smul,sub_add_cancel]
  exact he ▸ hline

private theorem interior_affine_halfspace {A : AffineSubspace ℝ Point3} [Nonempty A]
    (L : Point3 →ₗ[ℝ] ℝ) (y : A) (hy : L (y : Point3) < 0) :
    interior {x : A | 0 ≤ L (x : Point3)} = {x : A | 0 < L (x : Point3)} := by
  have hc : Continuous (fun x : A => L (x : Point3)) :=
    L.continuous_of_finiteDimensional.comp continuous_subtype_val
  ext x
  constructor
  · intro hI
    have hm : 0 ≤ L (x : Point3) := interior_subset hI
    refine lt_of_le_of_ne hm (fun he => ?_)
    let f : ℝ →ᵃ[ℝ] A := AffineMap.lineMap x y
    have h₀ : f 0 = x := AffineMap.lineMap_apply_zero _ _
    have hf : Continuous f := AffineMap.lineMap_continuous
    have hn : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ L (f t : Point3) :=
      (hf.tendsto' _ _ h₀).eventually_mem (mem_interior_iff_mem_nhds.mp hI)
    obtain ⟨t,ht,h⟩ := hn.exists_gt
    have hline : (f t : Point3) = AffineMap.lineMap (x : Point3) (y : Point3) t :=
      A.subtype.apply_lineMap x y t
    rw [hline,AffineMap.lineMap_apply_module,map_add,map_smul,map_smul,← he,smul_zero,zero_add] at h
    exact (not_le_of_gt (mul_neg_of_pos_of_neg ht hy)) h
  · intro hx
    rw [mem_interior_iff_mem_nhds]
    exact mem_of_superset ((isOpen_lt continuous_const hc).mem_nhds hx) (fun _ h => h.le)

private theorem intrinsicInterior_in_same_span {K : Set Point3} {A : AffineSubspace ℝ Point3}
    (hA : affineSpan ℝ K = A) :
    intrinsicInterior ℝ K = Subtype.val '' interior (Subtype.val ⁻¹' K : Set A) := by
  subst A
  rfl

/-- The boundary after a genuine cut consists of the surviving old boundary
and the chord. The clipped body still has the original affine span. -/
theorem planarCut_frontier {K : Set Point3} (hK : IsClosed K) (hconv : Convex ℝ K)
    (L : Point3 →ₗ[ℝ] ℝ) (hp : ∃ x ∈ K, 0 < L x) (hm : ∃ x ∈ K, L x < 0) :
    let C := K ∩ {x | 0 ≤ L x}
    affineSpan ℝ C = affineSpan ℝ K ∧
      intrinsicFrontier ℝ C =
        (intrinsicFrontier ℝ K ∩ {x | 0 ≤ L x}) ∪ (K ∩ {x | L x = 0}) := by
  obtain ⟨p,hpK,hpL⟩ := hp
  obtain ⟨y,hyK,hyL⟩ := hm
  obtain ⟨z,hz⟩ := Set.Nonempty.intrinsicInterior hconv ⟨p,hpK⟩
  obtain ⟨u,hu,huL⟩ := interior_point_same_side hconv L hz hpK hpL
  let A := affineSpan ℝ K
  let uA : A := ⟨u,subset_affineSpan ℝ K (intrinsicInterior_subset hu)⟩
  let _ : Nonempty A := ⟨uA⟩
  let yA : A := ⟨y,subset_affineSpan ℝ K hyK⟩
  let C := K ∩ {x | 0 ≤ L x}
  change affineSpan ℝ C = A ∧ _
  have hA : affineSpan ℝ C = A := affineSpan_cut_eq L hu huL
  refine ⟨hA,?_⟩
  have hI : intrinsicInterior ℝ C = intrinsicInterior ℝ K ∩ {x | 0 < L x} := by
    rw [intrinsicInterior_in_same_span hA]
    unfold C
    rw [preimage_inter, interior_inter]
    change Subtype.val '' (interior (Subtype.val ⁻¹' K) ∩ interior {x : A | 0 ≤ L (x : Point3)}) = _
    rw [interior_affine_halfspace L yA hyL, intrinsicInterior_in_same_span (show affineSpan ℝ K = A from rfl)]
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha.1,rfl⟩,ha.2⟩
    · rintro ⟨⟨a,ha,rfl⟩,hx⟩
      exact ⟨a,⟨ha,hx⟩,rfl⟩
  have hC : IsClosed C := hK.inter (isClosed_le continuous_const L.continuous_of_finiteDimensional)
  rw [← closure_sdiff_intrinsicInterior, ← closure_sdiff_intrinsicInterior, hC.closure_eq, hK.closure_eq, hI]
  ext x
  change (x ∈ K ∧ 0 ≤ L x) ∧ ¬ (x ∈ intrinsicInterior ℝ K ∧ 0 < L x) ↔
    ((x ∈ K ∧ x ∉ intrinsicInterior ℝ K) ∧ 0 ≤ L x) ∨ (x ∈ K ∧ L x = 0)
  constructor
  · rintro ⟨⟨hx,hL⟩,hnot⟩
    rcases lt_or_eq_of_le hL with hpos | hzero
    · exact Or.inl ⟨⟨hx,fun h => hnot ⟨h,hpos⟩⟩,hL⟩
    · exact Or.inr ⟨hx,hzero.symm⟩
  · rintro (⟨⟨hx,hI⟩,hL⟩ | ⟨hx,hL⟩)
    · exact ⟨⟨hx,hL⟩,fun h => hI h.1⟩
    · exact ⟨⟨hx,hL.ge⟩,fun h => (ne_of_gt h.2) hL⟩

/-- The intersection with the cutting line, parameterized from the
nonnegative endpoint of a crossing edge. -/
@[expose] noncomputable def linearCutPoint (L : Point3 →ₗ[ℝ] ℝ) (a b : Point3) : Point3 :=
  AffineMap.lineMap a b (L a/(L a-L b))

theorem linearCutPoint_mem_segment (L : Point3 →ₗ[ℝ] ℝ) (a b : Point3)
    (ha : 0 ≤ L a) (hb : L b < 0) :
    linearCutPoint L a b ∈ segment ℝ a b ∧ L (linearCutPoint L a b) = 0 := by
  have hd : 0 < L a - L b := sub_pos.mpr (hb.trans_le ha)
  refine ⟨lineMap_mem_segment ℝ a b ⟨div_nonneg ha hd.le,(div_le_one hd).mpr (by linarith)⟩,?_⟩
  rw [linearCutPoint,AffineMap.lineMap_apply_module,map_add,map_smul,map_smul]
  change (1 - L a/(L a-L b))*L a + (L a/(L a-L b))*L b = 0
  field_simp
  ring

theorem linearCutPoint_mem_openSegment (L : Point3 →ₗ[ℝ] ℝ) (a b : Point3)
    (ha : 0 < L a) (hb : L b < 0) : linearCutPoint L a b ∈ openSegment ℝ a b := by
  have hd := sub_pos.mpr (hb.trans ha)
  exact lineMap_mem_openSegment ℝ a b ⟨div_pos ha hd,(div_lt_one hd).mpr (by linarith)⟩

private theorem segment_cut_from_nonnegative (L : Point3 →ₗ[ℝ] ℝ) (a b : Point3)
    (ha : 0 ≤ L a) (hb : L b < 0) :
    segment ℝ a b ∩ {x | 0 ≤ L x} = segment ℝ a (linearCutPoint L a b) := by
  let t := L a/(L a-L b)
  let f : ℝ →ᵃ[ℝ] Point3 := AffineMap.lineMap a b
  have hd : 0 < L a - L b := sub_pos.mpr (hb.trans_le ha)
  have ht : 0 ≤ t := div_nonneg ha hd.le
  have ht₁ : t ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hcoords (s : ℝ) : L (f s) = (1-s)*L a+s*L b := by
    change L (AffineMap.lineMap a b s) = _
    rw [AffineMap.lineMap_apply_module,map_add,map_smul,map_smul]
    rfl
  have htest (s : ℝ) : 0 ≤ L (f s) ↔ s ≤ t := by
    rw [hcoords,le_div_iff₀ hd]
    constructor <;> intro h <;> nlinarith
  have he : segment ℝ a (linearCutPoint L a b) = f '' Icc 0 t := by
    rw [← segment_eq_Icc ht,image_segment, show f 0 = a from AffineMap.lineMap_apply_zero a b]
    rfl
  rw [he, segment_eq_image_lineMap]
  ext x
  constructor
  · rintro ⟨⟨s,hs,rfl⟩,hL⟩
    exact ⟨s,⟨hs.1,(htest s).mp hL⟩,rfl⟩
  · rintro ⟨s,hs,rfl⟩
    exact ⟨⟨s,⟨hs.1,hs.2.trans ht₁⟩,rfl⟩,(htest s).mpr hs.2⟩

/-- Cutting a segment keeps it whole, truncates it, or removes it. A zero
endpoint is kept, even when the rest of the segment is removed. -/
theorem segment_inter_nonnegativeHalfspace (L : Point3 →ₗ[ℝ] ℝ) (a b : Point3) :
    segment ℝ a b ∩ {x | 0 ≤ L x} =
      if 0 ≤ L a then
        if 0 ≤ L b then segment ℝ a b else segment ℝ a (linearCutPoint L a b)
      else if 0 ≤ L b then segment ℝ (linearCutPoint L b a) b else ∅ := by
  by_cases ha : 0 ≤ L a <;> by_cases hb : 0 ≤ L b <;> simp only [ha,hb,ite_true,ite_false]
  · exact inter_eq_left.mpr ((convex_halfSpace_ge L.isLinear 0).segment_subset ha hb)
  · exact segment_cut_from_nonnegative L a b ha (lt_of_not_ge hb)
  · rw [segment_symm ℝ a b, segment_cut_from_nonnegative L b a hb (lt_of_not_ge ha),segment_symm]
  · apply Set.eq_empty_of_forall_notMem
    rintro x ⟨hx,hy⟩
    have hz : x ∈ {x | L x < 0} := (convex_halfSpace_lt L.isLinear 0).segment_subset
      (lt_of_not_ge ha) (lt_of_not_ge hb) hx
    change L x < 0 at hz
    change 0 ≤ L x at hy
    exact (not_lt_of_ge hy) hz

/-- The result of a planar cut has the clipped old segments and one new chord
as its relative boundary. -/
theorem planarCut_boundary_segments {K : Set Point3} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hd : Module.finrank ℝ (affineSpan ℝ K).direction = 2) (L : Point3 →ₗ[ℝ] ℝ)
    (hp : ∃ x ∈ K, 0 < L x) (hm : ∃ x ∈ K, L x < 0)
    {ι : Type*} (edge : ι → Point3 × Point3)
    (hF : intrinsicFrontier ℝ K = ⋃ i, segment ℝ (edge i).1 (edge i).2) :
    ∃ a b : Point3, a ≠ b ∧ intrinsicFrontier ℝ K ∩ {x | L x = 0} = {a,b} ∧
      intrinsicFrontier ℝ (K ∩ {x | 0 ≤ L x}) =
        (⋃ i, (segment ℝ (edge i).1 (edge i).2 ∩ {x | 0 ≤ L x})) ∪ segment ℝ a b := by
  obtain ⟨a,b,hab,hchord,hends⟩ := planarCut_chord hK hconv hd L hp hm
  refine ⟨a,b,hab,hends,?_⟩
  rw [(planarCut_frontier hK.isClosed hconv L hp hm).2,hF,hchord]
  congr 1
  ext x
  simp only [Set.mem_inter_iff,Set.mem_iUnion]
  exact ⟨fun ⟨⟨i,hi⟩,hx⟩ => ⟨i,hi,hx⟩,fun ⟨i,hi,hx⟩ => ⟨⟨i,hi⟩,hx⟩⟩

/-- With pairwise disjoint open edges, at most two edges can meet the
cutting line in their interiors with endpoints on opposite sides. -/
theorem planarCut_strictCrossings_card_le_two {K : Set Point3}
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (hd : Module.finrank ℝ (affineSpan ℝ K).direction = 2) (L : Point3 →ₗ[ℝ] ℝ)
    (hp : ∃ x ∈ K, 0 < L x) (hm : ∃ x ∈ K, L x < 0)
    {ι : Type*} (I : Finset ι) (edge : ι → Point3 × Point3)
    (hF : ∀ i ∈ I, segment ℝ (edge i).1 (edge i).2 ⊆ intrinsicFrontier ℝ K)
    (hsimple : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (openSegment ℝ (edge i).1 (edge i).2) (openSegment ℝ (edge j).1 (edge j).2)) :
    (I.filter fun i => L (edge i).1 * L (edge i).2 < 0).card ≤ 2 := by
  classical
  obtain ⟨a,b,_,_,hends⟩ := planarCut_chord hK hconv hd L hp hm
  let S := I.filter fun i => L (edge i).1 * L (edge i).2 < 0
  let f (i : ι) := if 0 ≤ L (edge i).1 then linearCutPoint L (edge i).1 (edge i).2
    else linearCutPoint L (edge i).2 (edge i).1
  have hpt (i : ι) (hi : i ∈ S) : f i ∈ openSegment ℝ (edge i).1 (edge i).2 ∧ L (f i) = 0 := by
    rcases mul_neg_iff.mp (Finset.mem_filter.mp hi).2 with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · simp only [f,ha.le,ite_true]
      exact ⟨linearCutPoint_mem_openSegment L _ _ ha hb,(linearCutPoint_mem_segment L _ _ ha.le hb).2⟩
    · simp only [f,not_le_of_gt ha,ite_false]
      refine ⟨?_,(linearCutPoint_mem_segment L _ _ hb.le ha).2⟩
      rw [openSegment_symm ℝ (edge i).1 (edge i).2]
      exact linearCutPoint_mem_openSegment L _ _ hb ha
  have hi : InjOn f (S : Set ι) := by
    intro i hi j hj hij
    by_contra hne
    exact Set.disjoint_left.mp
      (hsimple i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne)
      (hpt i hi).1 (hij.symm ▸ (hpt j hj).1)
  have hsub : S.image f ⊆ ({a,b} : Finset Point3) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hxi : f i ∈ intrinsicFrontier ℝ K ∩ {x | L x = 0} :=
      ⟨hF i (Finset.mem_filter.mp hi).1 (openSegment_subset_segment ℝ _ _ (hpt i hi).1),(hpt i hi).2⟩
    rw [hends] at hxi
    simpa using hxi
  have hcard := (Finset.card_le_card hsub).trans Finset.card_le_two
  rwa [Finset.card_image_of_injOn hi] at hcard

end OrigamiTorus
