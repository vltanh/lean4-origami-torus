module

public import OrigamiTorus.Type5Reduction
import Mathlib.Tactic

/-! The finite reconstruction for a fixed Type 5 marking, measured in
Euclidean coordinates on the lifted triangles. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type5

open Type2 (Adjacent)

abbrev EdgeShifts := Vertex → Vertex → Plane ℝ

/-- The shifts have been gauged to zero at the anchor vertex 1. -/
structure GaugedShifts (K : EdgeShifts) : Prop where
  skew : ∀ a b, K b a = -K a b
  anchor : ∀ b, K 1 b = 0
  closed : ∀ f ∈ faces, K f.1 f.2.1+K f.2.1 f.2.2+K f.2.2 f.1 = 0

/-- The signed double area of the lifted triangle. -/
def markedFaceCross (K : EdgeShifts) (p : Vertex → Plane ℝ) (f : Triangle) : ℝ :=
  cross (p f.2.1+K f.1 f.2.1-p f.1) (p f.2.2+K f.1 f.2.2-p f.1)

/-- The Euclidean lifted-face data used by reconstruction. -/
structure MarkedRealization (K : EdgeShifts) (p : Vertex → Plane ℝ) (q : Vertex → Point3) : Prop where
  embedding : Function.Injective (evaluateTriangles faces q)
  flat : ∀ v, FlatAt q v
  edge_length : ∀ a b, Adjacent faces a b → squared3 (q b-q a) = squared2 (p b+K a b-p a)
  nondegenerate : ∀ f ∈ faces, markedFaceCross K p f ≠ 0

private theorem shift_comp_of_closed (K : EdgeShifts) (hK : GaugedShifts K) (a b c : Vertex)
    (h : K a b+K b c+K c a = 0) : K a b+K b c = K a c := by
  rw [hK.skew a c,← sub_eq_add_neg,sub_eq_zero] at h
  exact h

private theorem markedFaceCross_rotate (K : EdgeShifts) (p : Vertex → Plane ℝ)
    (hK : GaugedShifts K) (a b c : Vertex) (h : K a b+K b c+K c a = 0) :
    markedFaceCross K p (b,c,a) = markedFaceCross K p (a,b,c) := by
  have hc := shift_comp_of_closed K hK a b c h
  have he : p c+K b c-p b = (p c+K a c-p a)-(p b+K a b-p a) := by rw [← hc]; abel
  have hf : p a+K b a-p b = -(p b+K a b-p a) := by rw [hK.skew]; abel
  change cross (p c+K b c-p b) (p a+K b a-p b) = _
  rw [he,hf]
  simp [markedFaceCross,cross]
  ring

private theorem leaf_face_order (v : Vertex) (hv : v ∈ leaves) (i : Fin 5) :
    let a := leafNeighbor v i
    let b := leafNeighbor v (finRotate 5 i)
    (v,a,b) ∈ faces ∨ (a,b,v) ∈ faces ∨ (b,v,a) ∈ faces := by
  revert hv i
  fin_cases v <;> decide +kernel

private def liftedLeafRays (K : EdgeShifts) (p : Vertex → Plane ℝ) (v : Vertex) (i : Fin 5) : Plane ℝ :=
  p (leafNeighbor v i)+K v (leafNeighbor v i)-p v

private theorem MarkedRealization.leafMetric {K : EdgeShifts} {p : Vertex → Plane ℝ} {q : Vertex → Point3}
    (hK : GaugedShifts K) (h : MarkedRealization K p q) (v : Vertex) (hv : v ∈ leaves) :
    LeafMetric q v (liftedLeafRays K p v) := by
  have hrow (i : Fin 5) :
      let a := leafNeighbor v i
      let b := leafNeighbor v (finRotate 5 i)
      K v a+K a b+K b v = 0 ∧ markedFaceCross K p (v,a,b) ≠ 0 := by
    obtain hd | hd | hd := leaf_face_order v hv i
    · exact ⟨hK.closed _ hd,h.nondegenerate _ hd⟩
    · let a := leafNeighbor v i
      let b := leafNeighbor v (finRotate 5 i)
      have hh : K a b+K b v+K v a = 0 := hK.closed _ hd
      have hc : K v a+K a b+K b v = 0 := by rw [← hh]; abel
      exact ⟨hc,markedFaceCross_rotate K p hK v a b hc ▸ h.nondegenerate _ hd⟩
    · let a := leafNeighbor v i
      let b := leafNeighbor v (finRotate 5 i)
      have hh : K b v+K v a+K a b = 0 := hK.closed _ hd
      have hc : K v a+K a b+K b v = 0 := by rw [← hh]; abel
      exact ⟨hc,(markedFaceCross_rotate K p hK b v a hh).symm ▸ h.nondegenerate _ hd⟩
  refine ⟨fun i => h.edge_length v _ (leaf_center_adjacent v hv i),?_,?_⟩
  · intro i
    let a := leafNeighbor v i
    let b := leafNeighbor v (finRotate 5 i)
    have hc := shift_comp_of_closed K hK v a b (hrow i).1
    have hspatial : (q b-q v)-(q a-q v) = q b-q a := by abel
    have hintrinsic : (p b+K v b-p v)-(p a+K v a-p v) = p b+K a b-p a := by rw [← hc]; abel
    change squared3 ((q b-q v)-(q a-q v)) = squared2 ((p b+K v b-p v)-(p a+K v a-p v))
    rw [hspatial,hintrinsic]
    exact h.edge_length a b (leaf_consecutive_adjacent v hv i)
  · intro i
    exact (hrow i).2

/-- The four two-dimensional inputs to the fixed-marking reconstruction. -/
structure CorePositions where
  p₂ : Plane ℝ
  p₃ : Plane ℝ
  p₄ : Plane ℝ
  p₅ : Plane ℝ

/-- The eight real parameters read from any intrinsic vertex placement. -/
def CorePositions.ofPlacement (p : Vertex → Plane ℝ) : CorePositions := ⟨p 2,p 3,p 4,p 5⟩

def firstRootCandidates (K : EdgeShifts) (c : CorePositions) : List Point3 :=
  [makeRoot c.p₂ c.p₅ (c.p₂-K 2 3) (c.p₅-K 5 3) c.p₃ false,
   makeRoot c.p₂ c.p₅ (c.p₂-K 2 3) (c.p₅-K 5 3) c.p₃ true]

def secondRootCandidates (K : EdgeShifts) (c : CorePositions) : List Point3 :=
  [makeRoot c.p₂ c.p₅ (c.p₂-K 2 4) (c.p₅-K 5 4) c.p₄ false,
   makeRoot c.p₂ c.p₅ (c.p₂-K 2 4) (c.p₅-K 5 4) c.p₄ true]

def markedLeafData (K : EdgeShifts) (c : CorePositions) (r₃ r₄ : Point3) (v : Vertex) : LeafData ℝ :=
  if r₃.2.2 ≠ 0 then
    normalizedLeafData c.p₂ c.p₅ r₃ r₄ (c.p₂-K 2 v) (c.p₅-K 5 v) (c.p₃-K 3 v) (c.p₄-K 4 v)
  else
    normalizedLeafData c.p₂ c.p₅ r₄ r₃ (c.p₂-K 2 v) (c.p₅-K 5 v) (c.p₄-K 4 v) (c.p₃-K 3 v)

def markedLeafCandidates (K : EdgeShifts) (c : CorePositions) (r₃ r₄ : Point3) (v : Vertex) :
    List (Plane ℝ × Point3) :=
  (markedLeafData K c r₃ r₄ v).candidates

abbrev Reconstruction := Point3 × Point3 × (Plane ℝ × Point3) × (Plane ℝ × Point3) × (Plane ℝ × Point3)

/-- The finite choices determined by a fixed marking and the four core points. -/
def markedCandidates (K : EdgeShifts) (c : CorePositions) : List Reconstruction :=
  (firstRootCandidates K c).flatMap fun r₃ =>
    (secondRootCandidates K c).flatMap fun r₄ =>
    (markedLeafCandidates K c r₃ r₄ 0).flatMap fun a =>
      (markedLeafCandidates K c r₃ r₄ 6).flatMap fun b =>
        (markedLeafCandidates K c r₃ r₄ 7).map fun d => (r₃,r₄,a,b,d)

theorem markedCandidates_length (K : EdgeShifts) (c : CorePositions) :
    (markedCandidates K c).length ≤ 32 :=
  branch_count (firstRootCandidates K c) (fun _ => secondRootCandidates K c)
    (fun x y => markedLeafCandidates K c x y 0)
    (fun x y => markedLeafCandidates K c x y 6)
    (fun x y => markedLeafCandidates K c x y 7) (by rfl) (by intro; rfl)
    (fun x y => (markedLeafData K c x y 0).candidates_length)
    (fun x y => (markedLeafData K c x y 6).candidates_length)
    (fun x y => (markedLeafData K c x y 7).candidates_length)

private theorem marked_root_mem_candidates {K : EdgeShifts} {p : Vertex → Plane ℝ} {q : Vertex → Point3}
    (hK : GaugedShifts K) (h : MarkedRealization K p q)
    (hp : p 1 = 0) (hq : q 1 = 0)
    (hq₂ : q 2 = atHeight (p 2) 0) (hq₅ : q 5 = atHeight (p 5) 0)
    (hAB : cross (p 2) (p 5) ≠ 0) (r : Vertex) (hr : r = 3 ∨ r = 4) :
    q r ∈ [makeRoot (p 2) (p 5) (p 2-K 2 r) (p 5-K 5 r) (p r) false,
      makeRoot (p 2) (p 5) (p 2-K 2 r) (p 5-K 5 r) (p r) true] := by
  have h₁ : Adjacent faces 1 r := by
    rw [adjacency_test]
    rcases hr with rfl | rfl <;> decide +kernel
  have h₂ : Adjacent faces 2 r := by
    rw [adjacency_test]
    rcases hr with rfl | rfl <;> decide +kernel
  have h₅ : Adjacent faces 5 r := by
    rw [adjacency_test]
    rcases hr with rfl | rfl <;> decide +kernel
  apply normalized_root_complete hAB
  · simpa [hp,hq,hK.anchor] using h.edge_length 1 r h₁
  · rw [← hq₂,show p r-(p 2-K 2 r) = p r+K 2 r-p 2 by abel]
    exact h.edge_length 2 r h₂
  · rw [← hq₅,show p r-(p 5-K 5 r) = p r+K 5 r-p 5 by abel]
    exact h.edge_length 5 r h₅

private theorem exists_core_order (v : Vertex) (hv : v ∈ leaves) :
    ∃ e : Fin 5 ≃ Fin 5, ∀ i, leafNeighbor v (e i) = coreLabels i := by
  classical
  have H : ∀ i, ∃ j, leafNeighbor v j = coreLabels i := core_mem_leafNeighbor v hv
  choose e he using H
  have hi : Function.Injective e := by
    intro i j hij
    exact coreLabels_injective ((he i).symm.trans (hij ▸ he j))
  exact ⟨Equiv.ofBijective e ⟨hi,Finite.surjective_of_injective hi⟩,he⟩

private theorem marked_leaf_mem_branch {K : EdgeShifts} {p : Vertex → Plane ℝ} {q : Vertex → Point3}
    (hK : GaugedShifts K) (h : MarkedRealization K p q)
    (hp : p 1 = 0) (hq : q 1 = 0)
    (hq₂ : q 2 = atHeight (p 2) 0) (hq₅ : q 5 = atHeight (p 5) 0)
    (hAB : cross (p 2) (p 5) ≠ 0) (v : Vertex) (hv : v ∈ leaves)
    (e : Fin 5 ≃ Fin 5) (h0 : e 0 = 0) (h1 : e 1 = 1) (h2 : e 2 = 2)
    (hz : (q (coreLabels (e 3))).2.2 ≠ 0) :
    (p v,q v) ∈ (normalizedLeafData (p 2) (p 5) (q (coreLabels (e 3))) (q (coreLabels (e 4)))
      (p 2-K 2 v) (p 5-K 5 v) (p (coreLabels (e 3))-K (coreLabels (e 3)) v)
      (p (coreLabels (e 4))-K (coreLabels (e 4)) v)).candidates := by
  obtain ⟨j,hj⟩ := exists_core_order v hv
  let O := e.trans j
  have hO (i : Fin 5) : leafNeighbor v (O i) = coreLabels (e i) := hj (e i)
  have ha : leafNeighbor v (O 0) = 1 := by rw [hO,h0]; rfl
  let s := liftedLeafRays K p v
  have hs₀ : s (O 0) = -p v := by
    change p (leafNeighbor v (O 0))+K v (leafNeighbor v (O 0))-p v = _
    rw [ha,hp,hK.skew 1 v,hK.anchor]
    abel
  have hr₀ : leafRay q v (O 0) = -q v := by simp [leafRay,ha,hq]
  have hs (i : Fin 5) : s (O i)-s (O 0) = p (coreLabels (e i))-K (coreLabels (e i)) v := by
    rw [hs₀]
    change p (leafNeighbor v (O i))+K v (leafNeighbor v (O i))-p v-(-p v) = _
    rw [hO,hK.skew]
    abel
  have hr (i : Fin 5) : leafRay q v (O i)-leafRay q v (O 0) = q (coreLabels (e i)) := by
    rw [hr₀]
    change q (leafNeighbor v (O i))-q v-(-q v) = _
    rw [hO]
    abel
  have hA : leafRay q v (O 1)-leafRay q v (O 0) = atHeight (p 2) 0 := by rw [hr,h1]; exact hq₂
  have hB : leafRay q v (O 2)-leafRay q v (O 0) = atHeight (p 5) 0 := by rw [hr,h2]; exact hq₅
  have hmetric : LeafMetric q v s := h.leafMetric hK v hv
  have hmem := (hmetric.normalized_candidates_complete h.embedding hv (h.flat v)
    (fun a _ => h.flat a) O (p 2) (p 5) hAB hA hB (by rwa [hr])).2.2
  dsimp only at hmem
  rw [hr 3,hr 4,hs 1,hs 2,hs 3,hs 4,h1,h2,hs₀,hr₀,neg_neg,neg_neg] at hmem
  exact hmem

private theorem marked_leaf_mem_candidates {K : EdgeShifts} {p : Vertex → Plane ℝ} {q : Vertex → Point3}
    (hK : GaugedShifts K) (h : MarkedRealization K p q)
    (hp : p 1 = 0) (hq : q 1 = 0)
    (hq₂ : q 2 = atHeight (p 2) 0) (hq₅ : q 5 = atHeight (p 5) 0)
    (hAB : cross (p 2) (p 5) ≠ 0) (v : Vertex) (hv : v ∈ leaves) :
    (p v,q v) ∈ markedLeafCandidates K (CorePositions.ofPlacement p) (q 3) (q 4) v := by
  unfold markedLeafCandidates markedLeafData CorePositions.ofPlacement
  by_cases hz : (q 3).2.2 ≠ 0
  · rw [ite_eq_left hz]
    exact marked_leaf_mem_branch hK h hp hq hq₂ hq₅ hAB v hv (Equiv.refl _) rfl rfl rfl hz
  · rw [ite_eq_right hz]
    have h₄ := (core_some_height_ne_zero q h.embedding (by simp [hq]) (by simp [hq₂,atHeight])
      (by simp [hq₅,atHeight])).resolve_left hz
    exact marked_leaf_mem_branch hK h hp hq hq₂ hq₅ hAB v hv (Equiv.swap 3 4)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) h₄

/-- In normalized coordinates, every embedded flat realization with this
marking occurs on the list of at most 32 reconstructions for its four core
positions. Membership is a necessary algebraic test for a realization. -/
theorem markedCandidates_complete {K : EdgeShifts} {p : Vertex → Plane ℝ} {q : Vertex → Point3}
    (hK : GaugedShifts K) (h : MarkedRealization K p q)
    (hp : p 1 = 0) (hq : q 1 = 0)
    (hq₂ : q 2 = atHeight (p 2) 0) (hq₅ : q 5 = atHeight (p 5) 0)
    (hAB : cross (p 2) (p 5) ≠ 0) :
    (q 3,q 4,(p 0,q 0),(p 6,q 6),(p 7,q 7)) ∈ markedCandidates K (CorePositions.ofPlacement p) := by
  have h₃ := marked_root_mem_candidates hK h hp hq hq₂ hq₅ hAB 3 (Or.inl rfl)
  have h₄ := marked_root_mem_candidates hK h hp hq hq₂ hq₅ hAB 4 (Or.inr rfl)
  have hl (v : Vertex) (hv : v ∈ leaves) := marked_leaf_mem_candidates hK h hp hq hq₂ hq₅ hAB v hv
  exact List.mem_flatMap.mpr ⟨q 3,h₃,List.mem_flatMap.mpr ⟨q 4,h₄,
    List.mem_flatMap.mpr ⟨(p 0,q 0),hl 0 (by decide +kernel),
    List.mem_flatMap.mpr ⟨(p 6,q 6),hl 6 (by decide +kernel),
    List.mem_map.mpr ⟨(p 7,q 7),hl 7 (by decide +kernel),rfl⟩⟩⟩⟩⟩

end OrigamiTorus.Type5
