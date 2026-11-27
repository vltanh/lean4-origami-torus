module

public import OrigamiTorus.TetrahedralAnchors
public import OrigamiTorus.TetrahedronFromDistances
import Mathlib.Tactic

/-! Fourteen continuous coordinates and at most eighty radical branches
for each marked Type 4 or Type 7 realization. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.AnchorType

open Type2 (Adjacent)
open Type5 (Plane EdgeShifts squared2 squared3)

/-- Seven planar representatives after fixing the representative of vertex 0. -/
def intrinsicPlacement (p : Fin 7 → Plane ℝ) : Vertex → Plane ℝ := Fin.cases 0 p

/-- Read the fourteen coordinates from any intrinsic representatives. -/
def intrinsicParameters (p : Vertex → Plane ℝ) (i : Fin 7) : Plane ℝ := p i.succ-p 0

theorem intrinsicPlacement_parameters (p : Vertex → Plane ℝ) (i : Vertex) :
    intrinsicPlacement (intrinsicParameters p) i = p i-p 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [intrinsicPlacement]
  · rfl

/-- Squared edge length prescribed by the marking and the fourteen coordinates. -/
def markedDistance (K : EdgeShifts) (p : Fin 7 → Plane ℝ) (a b : Vertex) : ℝ :=
  if a = b then 0 else squared2 (intrinsicPlacement p b+K a b-intrinsicPlacement p a)

def anchorDistances (k : AnchorType) (K : EdgeShifts) (p : Fin 7 → Plane ℝ) (a : Fin 5) :
    Fin 4 → Fin 4 → ℝ :=
  fun i j => markedDistance K p (k.anchor a i) (k.anchor a j)

/-- The two choices at one outside vertex, determined by three centers in the
canonical tetrahedron. -/
def outsideCandidates (k : AnchorType) (K : EdgeShifts) (p : Fin 7 → Plane ℝ) (a : Fin 5) (i : Fin 4) :
    List Point3 :=
  let q := tetrahedronFromDistances (k.anchorDistances K p a)
  let s := k.center a i
  let d (j : Fin 3) := markedDistance K p (k.anchor a (s j)) (k.outside a i)
  threeSphereCandidates (q (s 0)) (q (s 1)) (q (s 2)) (d 0) (d 1) (d 2)

/-- Each branch specifies an anchor and four positions outside that anchor. -/
abbrev Branch := Fin 5 × (Fin 4 → Point3)

def branchesAt (k : AnchorType) (K : EdgeShifts) (p : Fin 7 → Plane ℝ) (a : Fin 5) :
    List (Fin 4 → Point3) :=
  let C := k.outsideCandidates K p a
  (C 0).flatMap fun x =>
    (C 1).flatMap fun y =>
      (C 2).flatMap fun z =>
        (C 3).map fun w => ![x,y,z,w]

def reconstructionBranches (k : AnchorType) (K : EdgeShifts) (p : Fin 7 → Plane ℝ) : List Branch :=
  (List.finRange 5).flatMap fun a => (k.branchesAt K p a).map fun r => (a,r)

private theorem length_flatMap_le {α β : Type*} (l : List α) (f : α → List β) (n : ℕ)
    (hn : ∀ i ∈ l, (f i).length ≤ n) : (l.flatMap f).length ≤ l.length*n := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h₁ := hn a (by simp)
    have h₂ : ∀ i ∈ l, (f i).length ≤ n := fun i hi => hn i (by simp [hi])
    have ih' := ih h₂
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,one_mul]
    omega

theorem branchesAt_length (k : AnchorType) (K : EdgeShifts) (p : Fin 7 → Plane ℝ) (a : Fin 5) :
    (k.branchesAt K p a).length ≤ 16 := by
  let C := k.outsideCandidates K p a
  have hC (i : Fin 4) : (C i).length = 2 := rfl
  unfold branchesAt
  change ((C 0).flatMap fun x => (C 1).flatMap fun y => (C 2).flatMap fun z =>
    (C 3).map fun w => (![x,y,z,w] : Fin 4 → Point3)).length ≤ 16
  calc
    _ ≤ (C 0).length*8 := by
      apply length_flatMap_le
      intro x hx
      calc _ ≤ (C 1).length*4 := by
             apply length_flatMap_le
             intro y hy
             calc _ ≤ (C 2).length*2 :=
                    length_flatMap_le _ _ _ (fun _ _ => by simp [hC])
                _ = 4 := by rw [hC]
           _ = 8 := by rw [hC]
    _ = 16 := by rw [hC]

theorem reconstructionBranches_length (k : AnchorType) (K : EdgeShifts) (p : Fin 7 → Plane ℝ) :
    (k.reconstructionBranches K p).length ≤ 80 := by
  exact length_flatMap_le _ _ 16 (fun a _ => by
    rw [List.length_map]
    exact k.branchesAt_length K p a)

def listLabelIndex (xs : List Vertex) (v : Vertex) : Fin 4 :=
  Fin.ofNat 4 (xs.idxOf v)

theorem anchor_mem_its_labels (k : AnchorType) (a : Fin 5) (i : Fin 4) :
    k.anchor a i ∈ List.ofFn (k.anchor a) := by
  revert a i
  cases k <;> decide +kernel

private theorem anchor_index (k : AnchorType) (a : Fin 5) (i : Fin 4) :
    listLabelIndex (List.ofFn (k.anchor a)) (k.anchor a i) = i := by
  revert a i
  cases k <;> decide +kernel

private theorem outside_index (k : AnchorType) (a : Fin 5) (i : Fin 4) :
    listLabelIndex (List.ofFn (k.outside a)) (k.outside a i) = i := by
  revert a i
  cases k <;> decide +kernel

private theorem outside_not_mem_anchor (k : AnchorType) (a : Fin 5) (i : Fin 4) :
    k.outside a i ∉ List.ofFn (k.anchor a) := by
  revert a i
  cases k <;> decide +kernel

/-- Decode a branch into the eight labeled points. -/
def branchPlacement (k : AnchorType) (K : EdgeShifts) (p : Fin 7 → Plane ℝ) (b : Branch) (v : Vertex) : Point3 :=
  let anchorLabels := List.ofFn (k.anchor b.1)
  if v ∈ anchorLabels then
    tetrahedronFromDistances (k.anchorDistances K p b.1) (listLabelIndex anchorLabels v)
  else b.2 (listLabelIndex (List.ofFn (k.outside b.1)) v)

theorem branchPlacement_anchor (k : AnchorType) (K : EdgeShifts) (p : Fin 7 → Plane ℝ)
    (b : Branch) (i : Fin 4) :
    k.branchPlacement K p b (k.anchor b.1 i) = tetrahedronFromDistances (k.anchorDistances K p b.1) i := by
  unfold branchPlacement
  rw [ite_eq_left (k.anchor_mem_its_labels b.1 i),k.anchor_index]

theorem branchPlacement_outside (k : AnchorType) (K : EdgeShifts) (p : Fin 7 → Plane ℝ)
    (b : Branch) (i : Fin 4) :
    k.branchPlacement K p b (k.outside b.1 i) = b.2 i := by
  unfold branchPlacement
  rw [ite_eq_right (k.outside_not_mem_anchor b.1 i),k.outside_index]

/-- Every embedded spatial placement with the prescribed marked edge lengths
occurs among the radical branches, up to a rigid motion. -/
theorem reconstruction_complete (k : AnchorType) (K : EdgeShifts)
    (p : Vertex → Plane ℝ) (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles k.faces q))
    (hl : ∀ a b, Adjacent k.faces a b → squared3 (q b-q a) = squared2 (p b+K a b-p a)) :
    let u := intrinsicParameters p
    ∃ b ∈ k.reconstructionBranches K u, ∃ T : Point3 →ₗ[ℝ] Point3,
      Function.Injective T ∧ (∀ z, squared3 (T z) = squared3 z) ∧
      ∀ i, k.branchPlacement K u b i = T (q i-q (k.anchor b.1 0)) := by
  let u := intrinsicParameters p
  have hdist (a b : Vertex) (hab : Adjacent k.faces a b) :
      squared3 (q b-q a) = markedDistance K u a b := by
    rw [markedDistance,ite_eq_right hab.1,intrinsicPlacement_parameters,intrinsicPlacement_parameters]
    rw [show p b-p 0+K a b-(p a-p 0) = p b+K a b-p a by abel]
    exact hl a b hab
  obtain ⟨a,ha⟩ := k.exists_independent_anchor q he
  let f := q ∘ k.anchor a
  let d := k.anchorDistances K u a
  have hD (i j : Fin 4) : squared3 (f j-f i) = d i j := by
    by_cases hij : i = j
    · subst j
      simp [d,f,anchorDistances,markedDistance,(squared3_eq_zero_iff _).mpr rfl]
    · exact hdist _ _ (k.anchor_adjacent a i j hij)
  obtain ⟨T,hTi,hT,hmodel⟩ := tetrahedronFromDistances_congruent f d ha hD
  let m := tetrahedronFromDistances d
  let r (v : Vertex) := T (q v-q (k.anchor a 0))
  have hra (i : Fin 4) : r (k.anchor a i) = m i := hmodel i
  have hmr (v₁ v₂ : Vertex) :
      squared3 (r v₂-r v₁) = squared3 (q v₂-q v₁) := by
    rw [show r v₂-r v₁ = T (q v₂-q v₁) by
      simp only [r,← map_sub]; congr 1; abel]
    exact hT _
  let L := T.toAffineMap.comp (AffineEquiv.constVAdd ℝ Point3 (-(q (k.anchor a 0)))).toAffineMap
  have hLi : Function.Injective L :=
    hTi.comp (AffineEquiv.constVAdd ℝ Point3 (-(q (k.anchor a 0)))).injective
  have hL (i : Fin 4) : L (f i) = m i := by
    rw [← hra]
    change T (-(q (k.anchor a 0))+q (k.anchor a i)) = T (q (k.anchor a i)-q (k.anchor a 0))
    congr 1
    abel
  have hm : AffineIndependent ℝ m := by
    rw [← show L ∘ f = m from funext hL]
    exact ha.map' L hLi
  have hmem (i : Fin 4) : r (k.outside a i) ∈ k.outsideCandidates K u a i := by
    let e : Fin 3 ↪ Fin 4 := ⟨k.center a i,k.center_injective a i⟩
    have hm' := hm.comp_embedding e
    have hv : m ∘ e = ![m (k.center a i 0),m (k.center a i 1),m (k.center a i 2)] := by
      funext j
      fin_cases j <;> rfl
    rw [hv] at hm'
    have hnc := affineIndependent_iff_not_collinear_set.mp hm'
    have hs (j : Fin 3) : squared3 (r (k.outside a i)-m (k.center a i j)) =
        markedDistance K u (k.anchor a (k.center a i j)) (k.outside a i) := by
      rw [← hra,hmr]
      exact hdist _ _ (k.center_adjacent a i j)
    exact threeSphereCandidates_complete _ _ _ _ _ _ _ hnc (hs 0) (hs 1) (hs 2)
  let out : Fin 4 → Point3 := r ∘ k.outside a
  have hout : out ∈ k.branchesAt K u a := by
    exact List.mem_flatMap.mpr ⟨out 0,hmem 0,List.mem_flatMap.mpr ⟨out 1,hmem 1,
      List.mem_flatMap.mpr ⟨out 2,hmem 2,List.mem_map.mpr ⟨out 3,hmem 3,by
        funext i
        fin_cases i <;> rfl⟩⟩⟩⟩
  refine ⟨(a,out),List.mem_flatMap.mpr ⟨a,by simp,List.mem_map.mpr ⟨out,hout,rfl⟩⟩,
    T,hTi,hT,fun i => ?_⟩
  change k.branchPlacement K u (a,out) i = r i
  obtain ⟨j,rfl⟩ | ⟨j,rfl⟩ := k.anchor_outside_cover a i
  · rw [branchPlacement_anchor]
    exact (hra j).symm
  · rw [branchPlacement_outside]
    rfl

/-- A candidate passes the spatial tests if it matches every marked edge
and all convex hulls of disjoint labeled subfaces are disjoint. -/
def PassesSpatialTests (k : AnchorType) (K : EdgeShifts) (p : Fin 7 → Plane ℝ) (q : Vertex → Point3) : Prop :=
  (∀ a b, Adjacent k.faces a b → squared3 (q b-q a) = markedDistance K p a b) ∧
    ∀ s t : Finset Vertex, s ∈ (triangleComplex k.faces).faces → t ∈ (triangleComplex k.faces).faces →
      Disjoint s t → Disjoint (vertexHull q s) (vertexHull q t)

/-- For fixed marked distances, an embedding exists exactly when one of the
radical branches passes the exact spatial tests. -/
theorem exists_placement_iff_branch (k : AnchorType) (K : EdgeShifts) (p : Fin 7 → Plane ℝ) :
    (∃ q : Vertex → Point3, k.PassesSpatialTests K p q) ↔
      ∃ b ∈ k.reconstructionBranches K p, k.PassesSpatialTests K p (k.branchPlacement K p b) := by
  constructor
  · rintro ⟨q,hl,hd⟩
    have he := (evaluateTriangles_injective_iff_disjoint_subfaces k.faces q).mpr hd
    let u := intrinsicPlacement p
    have hu : intrinsicParameters u = p := by
      funext i
      simp [u,intrinsicParameters,intrinsicPlacement]
    have hlen (a b : Vertex) (hab : Adjacent k.faces a b) :
        squared3 (q b-q a) = squared2 (u b+K a b-u a) := by
      rw [hl a b hab,markedDistance,ite_eq_right hab.1]
    obtain ⟨b,hb,T,hTi,hT,hq⟩ := k.reconstruction_complete K u q he hlen
    rw [hu] at hb hq
    let r := k.branchPlacement K p b
    let o := q (k.anchor b.1 0)
    have hr : r = (fun i => T (q i-o)) := funext hq
    refine ⟨b,hb,?_,(evaluateTriangles_injective_iff_disjoint_subfaces k.faces r).mp ?_⟩
    · intro a c hac
      change squared3 (r c-r a) = _
      rw [hr,← map_sub,show (q c-o)-(q a-o) = q c-q a by abel,hT]
      exact hl a c hac
    · intro w w' h
      rw [hr,show (fun i => T (q i-o)) = T ∘ (fun i => q i-o) by rfl,
        evaluateTriangles_comp_linear] at h
      change T (evaluateTriangles k.faces (fun i => q i-o) w) =
        T (evaluateTriangles k.faces (fun i => q i-o) w') at h
      rw [evaluateTriangles_sub_origin,evaluateTriangles_sub_origin] at h
      have h' := hTi h
      exact he (sub_left_inj.mp h')
  · rintro ⟨b,_,h⟩
    exact ⟨k.branchPlacement K p b,h⟩

end OrigamiTorus.AnchorType
