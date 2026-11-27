module

public import OrigamiTorus.PlanarPolygonCut
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-! The relative boundary of a nondegenerate planar triangle. -/

public section

open Set
open scoped BigOperators

namespace OrigamiTorus

private theorem affineBasis_frontier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : AffineBasis (Fin 3) ℝ E) :
    intrinsicFrontier ℝ (convexHull ℝ (range B)) =
      ⋃ i : Fin 3, convexHull ℝ (B '' {i}ᶜ) := by
  let S := convexHull ℝ (range B)
  let s : Affine.Simplex ℝ E 2 := ⟨B,B.ind⟩
  have hspan : affineSpan ℝ S = ⊤ := by rw [affineSpan_convexHull,B.tot]
  have htop : ((affineSpan ℝ S : AffineSubspace ℝ E) : Set E) = univ := by simp [hspan]
  let H := (Homeomorph.setCongr htop).trans (Homeomorph.Set.univ E)
  have hF : intrinsicFrontier ℝ S = frontier S := by
    change Subtype.val '' frontier (Subtype.val ⁻¹' S : Set (affineSpan ℝ S)) = frontier S
    change H '' frontier (H ⁻¹' S) = frontier S
    rw [← H.preimage_frontier, image_preimage_eq _ H.surjective]
  have hc : IsClosed S := ((finite_range B).isCompact_convexHull ℝ).isClosed
  have hS : S = s.closedInterior := Affine.Simplex.convexHull_eq_closedInterior s
  have hI : interior S = s.interior := by
    rw [B.interior_convexHull]
    ext x
    let w := fun i => B.coord i x
    have hsum : ∑ i, w i = 1 := B.sum_coord_apply_eq_one x
    have hw : (Finset.univ.affineCombination ℝ s.points) w = x :=
      B.affineCombination_coord_eq_self x
    have hm := Affine.Simplex.affineCombination_mem_interior_iff (s := s) hsum
    rw [hw] at hm
    rw [hm]
    change (∀ i, 0 < w i) ↔ ∀ i, w i ∈ Ioo 0 1
    refine ⟨fun hp i => ⟨hp i,?_⟩,fun hp i => (hp i).1⟩
    obtain ⟨j,hj⟩ := exists_ne i
    calc
      w i < ∑ k, w k := Finset.single_lt_sum hj (Finset.mem_univ i) (Finset.mem_univ j)
        (hp j) (fun k _ _ => (hp k).le)
      _ = 1 := hsum
  rw [hF,frontier,hc.closure_eq,hI,hS,s.closedInterior_sdiff_interior]
  simp_rw [← Affine.Simplex.convexHull_eq_closedInterior, Affine.Simplex.range_faceOpposite_points]
  rfl

set_option maxHeartbeats 600000 in
/-- The relative boundary of a nondegenerate triangle consists of its three edges. -/
theorem intrinsicFrontier_triangle (a b c : Point3)
    (hi : AffineIndependent ℝ (![a,b,c] : Fin 3 → Point3)) :
    intrinsicFrontier ℝ (convexHull ℝ {a,b,c}) = segmentCycle [a,b,c] := by
  let p : Fin 3 → Point3 := ![a,b,c]
  have hp : range p = {a,b,c} := by
    ext x
    simp [p,Matrix.range_cons]
    tauto
  let A := affineSpan ℝ (range p)
  let aA : A := ⟨a,subset_affineSpan ℝ _ ⟨0,rfl⟩⟩
  let _ : Nonempty A := ⟨aA⟩
  let e := AffineIsometryEquiv.vaddConst ℝ aA
  let F := A.subtypeₐᵢ.comp e.toAffineIsometry
  let q : Fin 3 → A.direction := fun i => e.symm ⟨p i,subset_affineSpan ℝ _ (mem_range_self i)⟩
  have hq : (F : A.direction → Point3) ∘ q = p := by
    funext i
    change ((e (e.symm ⟨p i,_⟩) : A) : Point3) = p i
    rw [e.apply_symm_apply]
  have hiq : AffineIndependent ℝ q := by
    apply AffineIndependent.of_comp F.toAffineMap
    change AffineIndependent ℝ (F ∘ q)
    rwa [hq]
  have htop : (affineSpan ℝ (range q)).map F.toAffineMap = A := by
    rw [AffineSubspace.map_span, show (F.toAffineMap : A.direction → Point3) = F from rfl,
      ← range_comp, hq]
  have hmap : A.comap F.toAffineMap = ⊤ := by
    apply top_unique
    intro x _
    change F x ∈ A
    exact (e x).property
  have hs : affineSpan ℝ (range q) = ⊤ := by
    rw [← AffineSubspace.comap_map_eq_of_injective F.injective (affineSpan ℝ (range q)),
      htop,hmap]
  let B : AffineBasis (Fin 3) ℝ A.direction := ⟨q,hiq,hs⟩
  have hImg : F '' convexHull ℝ (range B) = convexHull ℝ {a,b,c} := by
    change F.toAffineMap '' convexHull ℝ (range q) = _
    rw [F.toAffineMap.image_convexHull, ← range_comp]
    change convexHull ℝ (range (F ∘ q)) = _
    rw [hq,hp]
  rw [← hImg,F.intrinsicFrontier_image,affineBasis_frontier,image_iUnion]
  have hFace (i : Fin 3) : F '' convexHull ℝ (B '' {i}ᶜ) = convexHull ℝ (p '' {i}ᶜ) := by
    change F.toAffineMap '' convexHull ℝ (q '' {i}ᶜ) = _
    rw [F.toAffineMap.image_convexHull,image_image]
    change convexHull ℝ ((F ∘ q) '' {i}ᶜ) = _
    rw [hq]
  simp_rw [hFace]
  have h0 : p '' ({(0 : Fin 3)}ᶜ) = {b,c} := by
    ext x
    simp [p,Fin.exists_fin_succ]
    grind
  have h1 : p '' ({(1 : Fin 3)}ᶜ) = {c,a} := by
    ext x
    simp [p,Fin.exists_fin_succ]
    grind
  have h2 : p '' ({(2 : Fin 3)}ᶜ) = {a,b} := by
    ext x
    simp [p,Fin.exists_fin_succ]
    grind
  ext x
  simp only [mem_iUnion,segmentCycle,segmentPath,mem_union]
  constructor
  · rintro ⟨i,hi⟩
    fin_cases i
    · change x ∈ convexHull ℝ (p '' ({(0 : Fin 3)}ᶜ)) at hi
      exact Or.inr (Or.inl (by simpa only [h0,convexHull_pair] using hi))
    · change x ∈ convexHull ℝ (p '' ({(1 : Fin 3)}ᶜ)) at hi
      exact Or.inr (Or.inr (by simpa only [h1,convexHull_pair] using hi))
    · change x ∈ convexHull ℝ (p '' ({(2 : Fin 3)}ᶜ)) at hi
      exact Or.inl (by simpa only [h2,convexHull_pair] using hi)
  · rintro (hx | hx | hx)
    · exact ⟨2,by simpa only [h2,convexHull_pair] using hx⟩
    · exact ⟨0,by simpa only [h0,convexHull_pair] using hx⟩
    · exact ⟨1,by simpa only [h1,convexHull_pair] using hx⟩

/-- The cyclic list of the three vertices of a nondegenerate triangle is simple. -/
theorem simplePolygon_triangle (a b c : Point3)
    (hi : AffineIndependent ℝ (![a,b,c] : Fin 3 → Point3)) : SimplePolygon [a,b,c] := by
  classical
  let p : Fin 3 → Point3 := ![a,b,c]
  have hpi : Function.Injective p := hi.injective
  have hab : a ≠ b := fun h => (by decide : (0 : Fin 3) ≠ 1) (hpi h)
  have hbc : b ≠ c := fun h => (by decide : (1 : Fin 3) ≠ 2) (hpi h)
  have hca : c ≠ a := fun h => (by decide : (2 : Fin 3) ≠ 0) (hpi h)
  have hV {i j : Fin 3} (hij : i ≠ j) (k : Fin 3) :
      p k ∉ openSegment ℝ (p i) (p j) := by
    by_cases hki : k = i
    · subst k
      exact fun ho => hij (hpi (left_mem_openSegment_iff.mp ho))
    by_cases hkj : k = j
    · subst k
      exact fun ho => hij (hpi (right_mem_openSegment_iff.mp ho))
    intro hx
    have hx' : p k ∈ affineSpan ℝ (p '' {i,j}) := by
      rw [image_insert_eq,image_singleton,← affineSpan_convexHull,convexHull_pair]
      exact subset_affineSpan ℝ _ (openSegment_subset_segment ℝ _ _ hx)
    exact (hi.mem_affineSpan_iff k {i,j}).mp hx' |>.elim hki (fun he => hkj he)
  have hD {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
      Disjoint (openSegment ℝ (p i) (p j)) (openSegment ℝ (p j) (p k)) := by
    let L : Finset Point3 := {p i,p j}
    let R : Finset Point3 := {p j,p k}
    have hsub : (L : Set Point3) ∪ R ⊆ range p := by
      intro x hx
      simp only [L,R,Finset.coe_insert,Finset.coe_singleton,mem_union,mem_insert_iff,mem_singleton_iff] at hx
      rcases hx with (rfl | rfl) | (rfl | rfl)
      all_goals exact mem_range_self _
    have hsub' : (↑(L ∪ R) : Set Point3) ⊆ range p := by
      simpa only [Finset.coe_union] using hsub
    have hI := (hi.range.mono hsub').convexHull_inter' (t₁ := L) (t₂ := R)
    have hLR : (L : Set Point3) ∩ R = {p j} := by
      have hjk' := hpi.ne hjk
      have hki' := hpi.ne hki
      ext x
      simp only [L,R,Finset.coe_insert,Finset.coe_singleton,mem_inter_iff,mem_insert_iff,mem_singleton_iff]
      grind
    rw [hLR,convexHull_singleton] at hI
    simp only [L,R,Finset.coe_insert,Finset.coe_singleton] at hI
    rw [convexHull_pair,convexHull_pair] at hI
    apply disjoint_left.mpr
    intro x hx hx'
    have he : x ∈ ({p j} : Set Point3) := hI.symm ▸
      (show x ∈ segment ℝ (p i) (p j) ∩ segment ℝ (p j) (p k) from
        ⟨openSegment_subset_segment ℝ _ _ hx,openSegment_subset_segment ℝ _ _ hx'⟩)
    obtain rfl := mem_singleton_iff.mp he
    exact hV hij j hx
  have hmem (e : Point3 × Point3) : e ∈ polygonCycleEdges [a,b,c] ↔
      e = (a,b) ∨ e = (b,c) ∨ e = (c,a) := by simp [polygonCycleEdges,polygonPathEdges]
  refine ⟨by simp [hab,hbc,hca.symm],?_,?_⟩
  · intro e he x hx
    have hx' : ∃ k, p k = x := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
    obtain ⟨k,rfl⟩ := hx'
    rcases (hmem e).mp he with rfl | rfl | rfl
    · exact hV (i := 0) (j := 1) (by decide) k
    · exact hV (i := 1) (j := 2) (by decide) k
    · exact hV (i := 2) (j := 0) (by decide) k
  · have d₁ := hD (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
    have d₂ := hD (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide)
    have d₃ := hD (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide)
    intro e he g hg hne
    rcases (hmem e).mp he with rfl | rfl | rfl <;>
      rcases (hmem g).mp hg with rfl | rfl | rfl
    · exact (hne rfl).elim
    · exact d₁
    · exact d₃.symm
    · exact d₁.symm
    · exact (hne rfl).elim
    · exact d₂
    · exact d₃
    · exact d₂.symm
    · exact (hne rfl).elim

end OrigamiTorus
