module

public import OrigamiTorus.Lattice.PeriodicArea
public import Mathlib.Topology.LocallyFinite
import Mathlib.Tactic

/-! Connectivity of the overlap graph of a periodic tiling. -/

@[expose] public section

namespace OrigamiTorus

/-- Translate a compact piece by the integral vector in its label. -/
def translatedPiece {ι : Type*} (S : ι → Set (ℝ × ℝ)) (j : ι × Period) : Set (ℝ × ℝ) :=
  (fun p => p+realPeriod j.2) '' S j.1

theorem locallyFinite_translatedPieces {ι : Type*} [Finite ι] (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, IsCompact (S i)) : LocallyFinite (translatedPiece S) := by
  obtain ⟨R,hR⟩ := (isCompact_iUnion hS).isBounded.exists_norm_le
  intro x
  refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x (by norm_num),?_⟩
  let N : ℤ := ⌈1+‖x‖+R⌉
  have hNR : 1+‖x‖+R ≤ (N : ℝ) := Int.le_ceil _
  refine (Set.finite_univ.prod ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N))).subset ?_
  rintro ⟨i,d⟩ ⟨z,⟨p,hp,rfl⟩,hz⟩
  have hpR := hR p (Set.mem_iUnion.mpr ⟨i,hp⟩)
  have ht : ‖p+realPeriod d-x‖ < 1 := by
    simpa only [Metric.mem_ball,dist_eq_norm] using hz
  have hd : ‖realPeriod d‖ ≤ (N : ℝ) := by
    calc
      ‖realPeriod d‖ = ‖(p+realPeriod d-x)+x-p‖ := by congr 1; abel
      _ ≤ ‖p+realPeriod d-x‖+‖x‖+‖p‖ := by
        linarith only [norm_sub_le ((p+realPeriod d-x)+x) p,norm_add_le (p+realPeriod d-x) x]
      _ ≤ (N : ℝ) := by linarith only [hNR,ht,hpR]
  have ha : |(d.1 : ℝ)| ≤ (N : ℝ) := (norm_fst_le (realPeriod d)).trans hd
  have hb : |(d.2 : ℝ)| ≤ (N : ℝ) := (norm_snd_le (realPeriod d)).trans hd
  obtain ⟨ha₁,ha₂⟩ := abs_le.mp ha
  obtain ⟨hb₁,hb₂⟩ := abs_le.mp hb
  exact ⟨Set.mem_univ _,⟨⟨by exact_mod_cast ha₁,by exact_mod_cast ha₂⟩,
    ⟨by exact_mod_cast hb₁,by exact_mod_cast hb₂⟩⟩⟩

/-- The overlap graph of a locally finite closed cover of a preconnected
space connects any two nonempty pieces. -/
theorem overlap_connected_of_locallyFinite_cover {X ι : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (S : ι → Set X) (hlocal : LocallyFinite S) (hclosed : ∀ i, IsClosed (S i))
    (hcover : (⋃ i, S i) = Set.univ) {i j : ι} (hi : (S i).Nonempty) (hj : (S j).Nonempty) :
    Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j := by
  classical
  let R := {u : ι | Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i u}
  let U := ⋃ u : R, S u.val
  let V := ⋃ u : {a // a ∉ R}, S u.val
  have hU : IsClosed U :=
    (hlocal.comp_injective (Subtype.val_injective (p := fun u => u ∈ R))).isClosed_iUnion (fun u => hclosed u.val)
  have hV : IsClosed V :=
    (hlocal.comp_injective (Subtype.val_injective (p := fun u => u ∉ R))).isClosed_iUnion (fun u => hclosed u.val)
  have hUV (z : X) : z ∈ U ∨ z ∈ V := by
    have hz : z ∈ ⋃ i, S i := hcover.symm ▸ Set.mem_univ z
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hz
    by_cases h : k ∈ R
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨k,h⟩,hk⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k,h⟩,hk⟩)
  have hdisj : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro z hu hv
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hu
    obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hv
    exact b.property (a.property.tail ⟨z,ha,hb⟩)
  have hUC : U = Vᶜ := by
    ext z
    exact ⟨fun hu hv => Set.disjoint_left.mp hdisj hu hv,
      fun hv => (hUV z).resolve_right hv⟩
  have hVC : V = Uᶜ := by
    ext z
    exact ⟨fun hv hu => Set.disjoint_left.mp hdisj hu hv,
      fun hu => (hUV z).resolve_left hu⟩
  have hUopen : IsOpen U := hUC ▸ hV.isOpen_compl
  have hVopen : IsOpen V := hVC ▸ hU.isOpen_compl
  have hiU : (Set.univ ∩ U).Nonempty := by
    obtain ⟨z,hz⟩ := hi
    exact ⟨z,Set.mem_univ z,Set.mem_iUnion.mpr ⟨⟨i,Relation.ReflTransGen.refl⟩,hz⟩⟩
  have hsub : (Set.univ : Set X) ⊆ U := isPreconnected_univ.subset_left_of_subset_union
    hUopen hVopen hdisj (fun z _ => hUV z) hiU
  by_contra hjR
  obtain ⟨z,hz⟩ := hj
  have hzV : z ∈ V := Set.mem_iUnion.mpr ⟨⟨j,hjR⟩,hz⟩
  exact Set.disjoint_left.mp hdisj (hsub (Set.mem_univ z)) hzV

theorem overlap_connected_of_periodic_cover {ι : Type*} [Finite ι] (S : ι → Set (ℝ × ℝ))
    (hS : ∀ i, IsCompact (S i)) (hcover : (⋃ i, translatedPiece S i) = Set.univ)
    {i j : ι × Period} (hi : (translatedPiece S i).Nonempty) (hj : (translatedPiece S j).Nonempty) :
    Relation.ReflTransGen (fun a b => (translatedPiece S a ∩ translatedPiece S b).Nonempty) i j :=
  overlap_connected_of_locallyFinite_cover _ (locallyFinite_translatedPieces S hS)
    (fun i => ((hS i.1).image (continuous_id.add continuous_const)).isClosed) hcover hi hj

namespace PeriodicFaceSystem

noncomputable def weightTile {ι : Type*} (lift : ι → LiftedFace) (x w : ℝ)
    (q : Vertex → ℝ × ℝ) (j : ι) : Set (ℝ × ℝ) :=
  facePeriodPoint x w q (lift j) '' faceWeights (triangleVertexSet (liftedVertices (lift j)))

theorem weightTile_compact {ι : Type*} (lift : ι → LiftedFace) (x w : ℝ)
    (q : Vertex → ℝ × ℝ) (j : ι) : IsCompact (weightTile lift x w q j) := by
  apply (isCompact_faceWeights _).image
  unfold facePeriodPoint
  fun_prop

theorem weightTile_nonempty {ι : Type*} (lift : ι → LiftedFace) (x w : ℝ)
    (q : Vertex → ℝ × ℝ) (j : ι) : (weightTile lift x w q j).Nonempty := by
  let a := (lift j).1.1
  let u (b : Vertex) : ℝ := if b = a then 1 else 0
  have ha : a ∈ triangleVertexSet (liftedVertices (lift j)) := by
    rcases h : lift j with ⟨u,v,w⟩
    simp [a,h,liftedVertices,triangleVertexSet_eq]
  have hu : u ∈ faceWeights (triangleVertexSet (liftedVertices (lift j))) := by
    refine ⟨fun b => by unfold u; split <;> norm_num,by simp [u],?_⟩
    intro b hb
    have hne : b ≠ a := fun h => hb (h.symm ▸ ha)
    simp [u,hne]
  exact ⟨_,u,hu,rfl⟩

variable {ι : Type*} {fs : List Triangle} {lift : ι → LiftedFace}

theorem translatedWeightTiles_cover (S : PeriodicFaceSystem fs lift) (x w : ℝ) (q : Vertex → ℝ × ℝ)
    (F : triangleWeightSpace fs → MarkedTorus) (hf : Function.Surjective F)
    (hF : ∀ j u, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift j))) →
      F u = projectPeriods (facePeriodPoint x w q (lift j) u.val)) :
    (⋃ j, translatedPiece (weightTile lift x w q) j) = Set.univ := by
  ext z
  simp only [Set.mem_univ,iff_true]
  obtain ⟨u,hu⟩ := hf (projectPeriods z)
  obtain ⟨j,hj⟩ := S.cover u
  obtain ⟨d,hd⟩ := (projectPeriods_eq_iff _ _).mp ((hF j u hj).symm.trans hu)
  exact Set.mem_iUnion.mpr ⟨(j,d),_,⟨u.val,hj,rfl⟩,hd⟩

private theorem realPeriod_injective : Function.Injective realPeriod := by
  intro a b h
  apply Prod.ext
  · have he := congrArg Prod.fst h
    change (a.1 : ℝ) = (b.1 : ℝ) at he
    exact_mod_cast he
  · have he := congrArg Prod.snd h
    change (a.2 : ℝ) = (b.2 : ℝ) at he
    exact_mod_cast he

private theorem realPeriod_add (a b : Period) : realPeriod (a+b) = realPeriod a+realPeriod b := by
  apply Prod.ext <;> simp [realPeriod]

private theorem pointDifference (hshare : SharedFacePeriods lift) (x w : ℝ) (q : Vertex → ℝ × ℝ)
    {j l : ι} {u : Vertex → ℝ} (hj : u ∈ faceWeights (triangleVertexSet (liftedVertices (lift j))))
    (hl : u ∈ faceWeights (triangleVertexSet (liftedVertices (lift l)))) {a : Vertex} (ha : u a ≠ 0) :
    facePeriodPoint x w q (lift j) u = facePeriodPoint x w q (lift l) u +
      realPeriod (facePeriod (lift j) a-facePeriod (lift l) a) := by
  let d := facePeriod (lift j) a-facePeriod (lift l) a
  have hm {f : ι} (hf : u ∈ faceWeights (triangleVertexSet (liftedVertices (lift f))))
      {b : Vertex} (hb : u b ≠ 0) : b ∈ triangleVertexSet (liftedVertices (lift f)) := by
    by_contra hn
    exact hb (hf.2.2 b hn)
  have hp (b : Vertex) : u b • (periodCoordinates x w (q b) + realPeriod (facePeriod (lift j) b)) =
      u b • (periodCoordinates x w (q b) + realPeriod (facePeriod (lift l) b)) + u b • realPeriod d := by
    by_cases hb : u b = 0
    · simp [hb]
    have he : facePeriod (lift j) b-facePeriod (lift l) b = d :=
      hshare j l b a (hm hj hb) (hm hl hb) (hm hj ha) (hm hl ha)
    have hs : facePeriod (lift j) b = facePeriod (lift l) b+d := by
      rw [← he]
      abel
    rw [hs,realPeriod_add,← add_assoc,smul_add]
  change (∑ i, u i • (periodCoordinates x w (q i) + realPeriod (facePeriod (lift j) i))) =
    (∑ i, u i • (periodCoordinates x w (q i) + realPeriod (facePeriod (lift l) i))) + realPeriod d
  simp only [hp,Finset.sum_add_distrib,← Finset.sum_smul,hj.2.1,one_smul]

/-- Overlapping translated lifts share a vertex with the same label and
the same lifted period. -/
theorem common_lifted_vertex (S : PeriodicFaceSystem fs lift) (x w : ℝ) (q : Vertex → ℝ × ℝ)
    (F : triangleWeightSpace fs → MarkedTorus) (hf : Function.Injective F)
    (hF : ∀ j u, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift j))) →
      F u = projectPeriods (facePeriodPoint x w q (lift j) u.val)) {j l : ι × Period}
    (hover : (translatedPiece (weightTile lift x w q) j ∩ translatedPiece (weightTile lift x w q) l).Nonempty) :
    ∃ a : Vertex, a ∈ triangleVertexSet (liftedVertices (lift j.1)) ∧
      a ∈ triangleVertexSet (liftedVertices (lift l.1)) ∧
      facePeriod (lift j.1) a+j.2 = facePeriod (lift l.1) a+l.2 := by
  obtain ⟨z,⟨_,⟨u,hu,rfl⟩,eu⟩,⟨_,⟨v,hv,rfl⟩,ev⟩⟩ := hover
  let U : triangleWeightSpace fs := ⟨u,_,S.mem j.1,hu⟩
  let V : triangleWeightSpace fs := ⟨v,_,S.mem l.1,hv⟩
  have heU : F U = projectPeriods z := (hF j.1 U hu).trans ((projectPeriods_eq_iff _ _).mpr ⟨j.2,eu⟩)
  have heV : F V = projectPeriods z := (hF l.1 V hv).trans ((projectPeriods_eq_iff _ _).mpr ⟨l.2,ev⟩)
  have hUV : u = v := congrArg Subtype.val (hf (heU.trans heV.symm))
  subst v
  have hne : ∃ a, u a ≠ 0 := by
    by_contra! h
    have hsum := hu.2.1
    simp [h] at hsum
  obtain ⟨a,ha⟩ := hne
  have hs := pointDifference S.shared x w q hu hv ha
  rw [hs] at eu
  have hh : facePeriod (lift j.1) a-facePeriod (lift l.1) a+j.2 = l.2 := by
    apply realPeriod_injective
    rw [realPeriod_add]
    exact add_left_cancel (by simpa only [add_assoc] using eu.trans ev.symm)
  refine ⟨a,Classical.not_not.mp (fun h => ha (hu.2.2 a h)),
    Classical.not_not.mp (fun h => ha (hv.2.2 a h)),?_⟩
  calc
    facePeriod (lift j.1) a+j.2 = facePeriod (lift l.1) a+
        (facePeriod (lift j.1) a-facePeriod (lift l.1) a+j.2) := by abel
    _ = _ := by rw [hh]

/-- A quotient triangulation lifts to a connected chain of tiles sharing
labeled vertices in the covering plane. -/
theorem translated_tiles_connected [Finite ι] (S : PeriodicFaceSystem fs lift)
    (x w : ℝ) (q : Vertex → ℝ × ℝ) (F : triangleWeightSpace fs → MarkedTorus)
    (hf : Function.Bijective F)
    (hF : ∀ j u, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift j))) →
      F u = projectPeriods (facePeriodPoint x w q (lift j) u.val)) (j l : ι × Period) :
    Relation.ReflTransGen (fun p r : ι × Period =>
      ∃ a : Vertex, a ∈ triangleVertexSet (liftedVertices (lift p.1)) ∧
        a ∈ triangleVertexSet (liftedVertices (lift r.1)) ∧
        facePeriod (lift p.1) a+p.2 = facePeriod (lift r.1) a+r.2) j l := by
  have hn (r : ι × Period) : (translatedPiece (weightTile lift x w q) r).Nonempty :=
    (weightTile_nonempty lift x w q r.1).image _
  have h := overlap_connected_of_periodic_cover (weightTile lift x w q) (weightTile_compact lift x w q)
    (S.translatedWeightTiles_cover x w q F hf.2 hF) (hn j) (hn l)
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (S.common_lifted_vertex x w q F hf.1 hF hstep)

end PeriodicFaceSystem

end OrigamiTorus
