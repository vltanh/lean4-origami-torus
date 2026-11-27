module

public import OrigamiTorus.Type5Geometry
public import OrigamiTorus.Type5LeafRank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! A flat embedded Type 5 leaf has no common nonzero face-plane direction. -/

@[expose] public section

open InnerProductGeometry

namespace OrigamiTorus.Type5

open Type2 (Adjacent euclideanPoint linkDirection)

def leafRay (q : Vertex → Point3) (v : Vertex) (i : Fin 5) : Point3 :=
  q (leafNeighbor v i)-q v

def leafPlane (q : Vertex → Point3) (v : Vertex) (i : Fin 5) : Submodule ℝ Point3 :=
  Submodule.span ℝ {leafRay q v i,leafRay q v (finRotate 5 i)}

private theorem leaf_other_pair_roots (v : Vertex) (hv : v ∈ leaves) (i j : Fin 5) (hne : i ≠ j)
    (h : ¬ Adjacent faces (leafNeighbor v i) (leafNeighbor v j)) :
    (leafNeighbor v i,leafNeighbor v j) ∈ ([(3,4),(4,3)] : List Edge) := by
  rw [adjacency_test] at h
  revert hv i j
  fin_cases v <;> decide +kernel

private theorem leaf_angle_ne_pi (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (v : Vertex) (hv : v ∈ leaves)
    (hflat : FlatAt q v) {i j : Fin 5} (hij : i ≠ j) :
    angle (linkDirection q v (leafNeighbor v i)) (linkDirection q v (leafNeighbor v j)) ≠ Real.pi := by
  let a := leafNeighbor v i
  let b := leafNeighbor v j
  change angle (linkDirection q v a) (linkDirection q v b) ≠ Real.pi
  intro hπ
  have hna := no_edge_of_opposite_rays_of_embedding q he
    (leaf_center_adjacent v hv i) (leaf_center_adjacent v hv j) hπ
  have hroots := leaf_other_pair_roots v hv i j hij hna
  have hno := roots_not_opposite_at_flat_star q he v (Or.inl hv) hflat
  change (a,b) ∈ ([(3,4),(4,3)] : List Edge) at hroots
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hroots
  obtain ⟨ha,hb⟩ | ⟨ha,hb⟩ := hroots <;> rw [ha,hb] at hπ
  · exact hno hπ
  · exact hno ((angle_comm _ _).trans hπ)

private theorem leafRay_ne_zero (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (v : Vertex) (hv : v ∈ leaves) (i : Fin 5) :
    leafRay q v i ≠ 0 := by
  intro h
  exact (leaf_center_adjacent v hv i).1
    ((vertex_injective_of_injective_evaluateTriangles faces q type5_covers he) (sub_eq_zero.mp h)).symm

private theorem leafRays_not_proportional (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (v : Vertex) (hv : v ∈ leaves)
    (hflat : FlatAt q v) {i j : Fin 5} (hij : i ≠ j) (s : ℝ) :
    s • leafRay q v j ≠ leafRay q v i := by
  intro h
  let d := linkDirection q v
  let a := leafNeighbor v i
  let b := leafNeighbor v j
  have hne : d b ≠ 0 := fun h =>
    leafRay_ne_zero q he v hv j (Type2.euclideanPoint_injective (h.trans euclideanPoint.map_zero.symm))
  have hsm : d a = s • d b := by
    change euclideanPoint (leafRay q v i) = s • euclideanPoint (leafRay q v j)
    rw [← h,map_smul]
  rcases lt_trichotomy s 0 with hn | hz | hp
  · exact leaf_angle_ne_pi q he v hv hflat hij.symm (angle_eq_pi_iff.mpr ⟨hne,s,hn,hsm⟩)
  · simp [hz] at h
    exact leafRay_ne_zero q he v hv i h.symm
  · exact distinct_rays_of_embedding q he (leaf_center_adjacent v hv j) (leaf_center_adjacent v hv i)
      ((leafNeighbor_injective v hv).ne hij.symm) (angle_eq_zero_iff.mpr ⟨hne,s,hp,hsm⟩)

private theorem finrank_span_pair_of_not_proportional {x y : Point3} (hy : y ≠ 0)
    (h : ∀ t : ℝ, t • y ≠ x) : Module.finrank ℝ (Submodule.span ℝ ({x,y} : Set Point3)) = 2 := by
  let f : Fin 2 → Point3 := ![x,y]
  have hi : LinearIndependent ℝ f := linearIndependent_fin2.mpr ⟨hy,h⟩
  have hr : Set.range f = {x,y} := by simp [f,Matrix.range_cons,Set.pair_comm]
  rw [← hr,finrank_span_eq_card hi,Fintype.card_fin]

theorem leafPlane_finrank (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (v : Vertex) (hv : v ∈ leaves)
    (hflat : FlatAt q v) (i : Fin 5) :
    Module.finrank ℝ (leafPlane q v i) = 2 := by
  have hnext : ∀ i : Fin 5, i ≠ finRotate 5 i := by decide +kernel
  exact finrank_span_pair_of_not_proportional (leafRay_ne_zero q he v hv _)
    (leafRays_not_proportional q he v hv hflat (hnext i))

private theorem cycle_constant_of_at_most_one_change {A : Type*} (p : Fin 5 → A)
    (h : ∀ i j : Fin 5, p i ≠ p (finRotate 5 i) → p j ≠ p (finRotate 5 j) → i = j) :
    ∀ i, p i = p 0 := by
  classical
  have hsteps : ∀ i : Fin 5,
      finRotate 5 i = i+1 ∧ finRotate 5 (i+1) = i+2 ∧ finRotate 5 (i+2) = i+3 ∧
      finRotate 5 (i+3) = i+4 ∧ finRotate 5 (i+4) = i := by decide +kernel
  have hne : ∀ i : Fin 5, i ≠ i+1 ∧ i ≠ i+2 ∧ i ≠ i+3 ∧ i ≠ i+4 := by decide +kernel
  have hall (i : Fin 5) : p i = p (finRotate 5 i) := by
    by_contra hi
    have hh (j : Fin 5) (hij : i ≠ j) : p j = p (finRotate 5 j) := by
      by_contra hj
      exact hij (h i j hi hj)
    obtain ⟨e0,e1,e2,e3,e4⟩ := hsteps i
    obtain ⟨n1,n2,n3,n4⟩ := hne i
    have h1 := hh (i+1) n1
    have h2 := hh (i+2) n2
    have h3 := hh (i+3) n3
    have h4 := hh (i+4) n4
    rw [e1] at h1
    rw [e2] at h2
    rw [e3] at h3
    rw [e4] at h4
    rw [e0] at hi
    exact hi (h1.trans (h2.trans (h3.trans h4))).symm
  have e01 : p 0 = p 1 := hall 0
  have e12 : p 1 = p 2 := hall 1
  have e23 : p 2 = p 3 := hall 2
  have e34 : p 3 = p 4 := hall 3
  intro i
  fin_cases i
  · rfl
  · exact e01.symm
  · exact (e01.trans e12).symm
  · exact (e01.trans (e12.trans e23)).symm
  · exact (e01.trans (e12.trans (e23.trans e34))).symm

/-- A flat embedded leaf cannot have a nonzero vector in every incident
face plane. This rules out the common direction from a degenerate norm equation. -/
theorem leaf_no_common_plane_direction (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (v : Vertex) (hv : v ∈ leaves)
    (hflat : FlatAt q v) (e : Point3) (hne : e ≠ 0)
    (heP : ∀ i : Fin 5, e ∈ leafPlane q v i) : False := by
  let P := leafPlane q v
  let R := leafRay q v
  let ρ := finRotate 5
  have hP : ∀ i, Module.finrank ℝ (P i) = 2 := leafPlane_finrank q he v hv hflat
  have hlines (i j : Fin 5) (hi : R i ∈ Submodule.span ℝ {e})
      (hj : R j ∈ Submodule.span ℝ {e}) : i = j := by
    by_contra hij
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hi
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hj
    have hbne : b ≠ 0 := by
      intro hzero
      simp [hzero] at hb
      exact leafRay_ne_zero q he v hv j hb.symm
    apply leafRays_not_proportional q he v hv hflat hij (a/b)
    change (a/b) • R j = R i
    rw [← hb,smul_smul,div_mul_cancel₀ _ hbne,ha]
  have hstep (i : Fin 5) (hn : P i ≠ P (ρ i)) : R (ρ i) ∈ Submodule.span ℝ {e} := by
    by_contra hi
    let D := Submodule.span ℝ ({R (ρ i),e} : Set Point3)
    have hD : Module.finrank ℝ D = 2 :=
      finrank_span_pair_of_not_proportional hne
        (fun t ht => hi (Submodule.mem_span_singleton.mpr ⟨t,ht⟩))
    have ha : R (ρ i) ∈ P i := Submodule.subset_span
      (show R (ρ i) ∈ ({R i,R (ρ i)} : Set Point3) from Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hb : R (ρ i) ∈ P (ρ i) := Submodule.subset_span
      (show R (ρ i) ∈ ({R (ρ i),R (ρ (ρ i))} : Set Point3) from Set.mem_insert _ _)
    have hle (j : Fin 5) (hmem : R (ρ i) ∈ P j) : D ≤ P j := by
      apply Submodule.span_le.mpr
      intro x hx
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hmem
      · exact heP j
    have h₁ := Submodule.eq_of_le_of_finrank_le (hle i ha) (by rw [hP,hD])
    have h₂ := Submodule.eq_of_le_of_finrank_le (hle (ρ i) hb) (by rw [hP,hD])
    exact hn (h₁.symm.trans h₂)
  have hun (i : Fin 5) : P i = P 0 := cycle_constant_of_at_most_one_change P
    (fun i j hi hj => ρ.injective (hlines _ _ (hstep i hi) (hstep j hj))) i
  apply core_not_in_plane_of_embedding q he (q v) (P 0) (hP 0).le
  intro i
  obtain ⟨k,hk⟩ := core_mem_leafNeighbor v hv i
  rw [← hk]
  change R k ∈ P 0
  rw [← hun k]
  exact Submodule.subset_span (show R k ∈ ({R k,R (ρ k)} : Set Point3) from Set.mem_insert _ _)

end OrigamiTorus.Type5
