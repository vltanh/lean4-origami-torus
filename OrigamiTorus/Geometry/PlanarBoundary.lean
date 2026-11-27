module

public import OrigamiTorus.Geometry.AffineDeterminants
public import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic

/-! Punctured relative boundaries of compact two-dimensional convex sets. -/

public section

open Metric Set

namespace OrigamiTorus

/-- Removing a point from the relative boundary of a compact convex set of
affine dimension two allows the remainder to be embedded in the real line. -/
theorem exists_injOn_punctured_intrinsicFrontier {K : Set Point3}
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (hd : Module.finrank ℝ (affineSpan ℝ K).direction = 2)
    {p : Point3} (hp : p ∈ intrinsicFrontier ℝ K) :
    ∃ f : Point3 → ℝ, ContinuousOn f (intrinsicFrontier ℝ K \ {p}) ∧
      Set.InjOn f (intrinsicFrontier ℝ K \ {p}) := by
  classical
  let A := affineSpan ℝ K
  let T : Set A := Subtype.val ⁻¹' K
  obtain ⟨pA,hpA,hpp⟩ := mem_intrinsicFrontier.mp hp
  let _ : Nonempty A := ⟨pA⟩
  let E := EuclideanSpace ℝ (Fin 2)
  let J : A.direction ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq
    (hd.trans (by simp [E]))
  let Q : A ≃ᵃ[ℝ] E := (AffineEquiv.vaddConst ℝ pA).symm.trans J.toLinearEquiv.toAffineEquiv
  let H : A ≃ₜ E := Q.toContinuousAffineEquiv.toHomeomorph
  let U : Set E := H.symm ⁻¹' T
  have hTc : IsCompact T := (A.isClosed_of_finiteDimensional.isClosedEmbedding_subtypeVal).isCompact_preimage hK
  have hUconv : Convex ℝ U := hconv.affine_preimage (A.subtype.comp Q.symm.toAffineMap)
  have hUc : IsCompact U := H.symm.isClosedEmbedding.isCompact_preimage hTc
  have hUi : (interior U).Nonempty := by
    have hne : K.Nonempty := ⟨p, hK.isClosed.closure_eq ▸ (by
      rw [← closure_sdiff_intrinsicInterior] at hp
      exact hp.1)⟩
    obtain ⟨x,hx⟩ := hne.intrinsicInterior hconv
    obtain ⟨xA,hxA,_⟩ := mem_intrinsicInterior.mp hx
    refine ⟨H xA,?_⟩
    change H xA ∈ interior (H.symm ⁻¹' T)
    rwa [← H.symm.preimage_interior, mem_preimage, Homeomorph.symm_apply_apply]
  obtain ⟨G,_,_,hG⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    hUconv hUi hUc.isBounded
  have hS (x : A) (hx : x ∈ frontier T) : G (H x) ∈ sphere (0 : E) 1 := by
    have hx' : H x ∈ frontier U := by
      change H x ∈ frontier (H.symm ⁻¹' T)
      rwa [← H.symm.preimage_frontier, mem_preimage, Homeomorph.symm_apply_apply]
    exact hG ▸ mem_image_of_mem G hx'
  let pole : sphere (0 : E) 1 := ⟨G (H pA), hS pA hpA⟩
  let _ : Fact (Module.finrank ℝ E = 1 + 1) := ⟨by simp [E]⟩
  let S := stereographic' 1 pole
  let X := intrinsicFrontier ℝ K \ {p}
  have hinA (x : X) : x.val ∈ A := by
    obtain ⟨y,_,hy⟩ := mem_intrinsicFrontier.mp x.property.1
    exact hy ▸ y.property
  let lift (x : X) : A := ⟨x.val,hinA x⟩
  have hF (x : X) : lift x ∈ frontier T := by
    obtain ⟨y,hy,he⟩ := mem_intrinsicFrontier.mp x.property.1
    have he' : y = lift x := Subtype.ext he
    exact he' ▸ hy
  let onSphere (x : X) : sphere (0 : E) 1 := ⟨G (H (lift x)),hS (lift x) (hF x)⟩
  have hsource (x : X) : onSphere x ∈ S.source := by
    rw [show S.source = {pole}ᶜ from stereographic'_source pole]
    intro he
    apply x.property.2
    have eq : lift x = pA := H.injective (G.injective (congrArg Subtype.val (show onSphere x = pole from he)))
    exact (congrArg Subtype.val eq).trans hpp
  have hcont₁ : Continuous onSphere := by
    have hl : Continuous lift := continuous_subtype_val.subtype_mk _
    exact (G.continuous.comp (H.continuous.comp hl)).subtype_mk _
  let out (x : X) : ℝ := (S (onSphere x)) 0
  have hcont : Continuous out := by
    have hC := S.continuousOn.comp_continuous hcont₁ hsource
    exact (PiLp.continuous_apply 2 _ 0).comp hC
  have hi : Function.Injective out := by
    intro x y hxy
    have eq : S (onSphere x) = S (onSphere y) := by
      ext i
      fin_cases i
      exact hxy
    have eq' := S.injOn (hsource x) (hsource y) eq
    have eq'' : lift x = lift y := H.injective (G.injective (congrArg Subtype.val eq'))
    exact Subtype.ext (congrArg (fun z : A => (z : Point3)) eq'')
  let f (x : Point3) : ℝ := if hx : x ∈ X then out ⟨x,hx⟩ else 0
  refine ⟨f, continuousOn_iff_continuous_domRestrict.mpr ?_, ?_⟩
  · change Continuous (X.domRestrict f)
    have he : X.domRestrict f = out := by funext x; exact dite_eq_left x.property
    rw [he]
    exact hcont
  · intro x hx y hy he
    change x ∈ X at hx
    change y ∈ X at hy
    have hxy : out ⟨x,hx⟩ = out ⟨y,hy⟩ := by simpa only [f,dite_eq_left hx,dite_eq_left hy] using he
    exact congrArg (fun z : X => (z : Point3)) (hi hxy)

private theorem box_subset_triangle (r : ℝ) (hr : 0 < r) (z : ℝ × ℝ)
    (hx : |z.1| ≤ r) (hy : |z.2| ≤ r) :
    z ∈ convexHull ℝ ({(-r,-r),(3*r,-r),(-r,3*r)} : Set (ℝ × ℝ)) := by
  let b := (z.1+r)/(4*r)
  let c := (z.2+r)/(4*r)
  have hd : 0 < 4*r := by positivity
  have hb : 0 ≤ b := div_nonneg (by linarith [(abs_le.mp hx).1]) hd.le
  have hc : 0 ≤ c := div_nonneg (by linarith [(abs_le.mp hy).1]) hd.le
  have h₁ : b+c ≤ 1 := by
    change (z.1+r)/(4*r) + (z.2+r)/(4*r) ≤ 1
    rw [← add_div, div_le_one hd]
    linarith [(abs_le.mp hx).2,(abs_le.mp hy).2]
  let w : Fin 3 → ℝ := ![1-b-c,b,c]
  let p : Fin 3 → ℝ × ℝ := ![(-r,-r),(3*r,-r),(-r,3*r)]
  have hp (i : Fin 3) : p i ∈ ({(-r,-r),(3*r,-r),(-r,3*r)} : Set (ℝ × ℝ)) := by
    fin_cases i <;> simp [p]
  have hw (i : Fin 3) : 0 ≤ w i := by
    fin_cases i
    · change 0 ≤ 1-b-c
      linarith
    · exact hb
    · exact hc
  have hw₁ : ∑ i, w i = 1 := by simp [w,Fin.sum_univ_succ]
  have he := Finset.univ.centerMass_mem_convexHull (fun i _ => hw i)
    (by rw [hw₁]; norm_num) (fun i _ => hp i)
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁] at he
  have hsum : ∑ i, w i • p i = z := by
    apply Prod.ext <;>
      simp [w,p,Fin.sum_univ_succ,smul_eq_mul] <;>
      dsimp only [b,c] <;> field_simp <;> ring
  rwa [hsum] at he

/-- A compact set of affine dimension two lies in a triangle in its own plane. -/
theorem exists_enclosing_triangle {K : Set Point3} (hK : IsCompact K) (hne : K.Nonempty)
    (hd : Module.finrank ℝ (affineSpan ℝ K).direction = 2) :
    ∃ a b c : Point3,
      a ∈ affineSpan ℝ K ∧ b ∈ affineSpan ℝ K ∧ c ∈ affineSpan ℝ K ∧ K ⊆ convexHull ℝ {a,b,c} := by
  obtain ⟨x,hx⟩ := hne
  let A := affineSpan ℝ K
  let xA : A := ⟨x,subset_affineSpan ℝ K hx⟩
  let _ : Nonempty A := ⟨xA⟩
  let J : A.direction ≃ₗ[ℝ] ℝ × ℝ := LinearEquiv.ofFinrankEq _ _
    (hd.trans (by simp [Module.finrank_prod]))
  let Q : A ≃ᵃ[ℝ] (ℝ × ℝ) := (AffineEquiv.vaddConst ℝ xA).symm.trans J.toAffineEquiv
  let H : A ≃ₜ (ℝ × ℝ) := Q.toContinuousAffineEquiv.toHomeomorph
  let S : Set (ℝ × ℝ) := H.symm ⁻¹' (Subtype.val ⁻¹' K : Set A)
  have hSc : IsCompact S := H.symm.isClosedEmbedding.isCompact_preimage
    (A.isClosed_of_finiteDimensional.isClosedEmbedding_subtypeVal.isCompact_preimage hK)
  obtain ⟨s,hs⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ × ℝ)).mp hSc.isBounded
  let r := |s|+1
  have hr : 0 < r := by dsimp [r]; positivity
  let a := (-r,-r)
  let b := (3*r,-r)
  let c := (-r,3*r)
  let F : (ℝ × ℝ) →ᵃ[ℝ] Point3 := A.subtype.comp Q.symm.toAffineMap
  refine ⟨F a,F b,F c,(Q.symm a).property,(Q.symm b).property,(Q.symm c).property,?_⟩
  intro y hy
  let yA : A := ⟨y,subset_affineSpan ℝ K hy⟩
  let z := H yA
  have hz : z ∈ S := by change ↑(H.symm (H yA)) ∈ K; simpa
  have hzn : ‖z‖ < r := by
    have hz' := Metric.mem_ball.mp (hs hz)
    rw [dist_zero_right] at hz'
    exact hz'.trans (by dsimp [r]; linarith [le_abs_self s])
  have hcoords : |z.1| ≤ r ∧ |z.2| ≤ r := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs] at hzn
    exact max_le_iff.mp hzn.le
  have htri : z ∈ convexHull ℝ ({a,b,c} : Set (ℝ × ℝ)) := box_subset_triangle r hr z hcoords.1 hcoords.2
  have hy' : F z = y := by
    change ↑(H.symm (H yA)) = y
    rw [H.symm_apply_apply]
  have hmem := Set.mem_image_of_mem F htri
  rw [F.image_convexHull, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hy'] at hmem
  exact hmem

end OrigamiTorus
