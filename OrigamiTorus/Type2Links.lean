module

public import OrigamiTorus.Type2Perturbation
public import OrigamiTorus.SphericalPerimeter
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.List.NodupEquivFin
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

/-! Cyclic links and the strict support condition in the Type 2 reduction. -/

namespace OrigamiTorus.Type2

@[expose] public section

/-- The neighbors in cyclic link order, up to reversal and the starting vertex. -/
def linkCycle : Vertex → List Vertex :=
  ![[4,6,5,7], [3,5,4,7,6], [3,4,5,6,7], [1,5,7,2,4,6],
    [0,6,3,2,5,1,7], [0,6,2,4,1,3,7], [0,4,3,1,7,2,5], [0,4,1,6,2,3,5]]

def linkEdges (v : Vertex) : List Edge :=
  let ns := linkCycle v
  ns.zip (ns.drop 1 ++ ns.take 1)

def incidentCorners (v : Vertex) : List Edge :=
  geometricFaces.filterMap fun f =>
    let a := f.1
    let b := f.2.1
    let c := f.2.2
    if v = a then some (b,c) else if v = b then some (a,c) else
      if v = c then some (a,b) else none

theorem linkCycle_checked (v : Vertex) :
    (linkCycle v).Nodup ∧ 3 ≤ (linkCycle v).length ∧
      ((linkEdges v).map fun e => orderedEdge e.1 e.2).Perm (incidentCorners v) := by
  fin_cases v <;> decide +kernel

theorem mem_linkCycle_iff (v w : Vertex) : w ∈ linkCycle v ↔ Adjacent geometricFaces v w := by
  rw [adjacent_geometricFaces_iff]
  fin_cases v <;> revert w <;> decide +kernel

/-- View the three spatial coordinates in Euclidean space for angle measurements. -/
def euclideanPoint : Point3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun p := WithLp.toLp _ ![p.1,p.2.1,p.2.2]
  map_add' p q := by ext i; fin_cases i <;> rfl
  map_smul' r p := by ext i; fin_cases i <;> rfl

theorem euclideanPoint_injective : Function.Injective euclideanPoint := by
  intro p q h
  have coord (i : Fin 3) := congrFun (congrArg WithLp.ofLp h) i
  exact Prod.ext (coord 0) (Prod.ext (coord 1) (coord 2))

def linkDirection (q : Vertex → Point3) (v w : Vertex) : EuclideanSpace ℝ (Fin 3) :=
  euclideanPoint (q w - q v)

theorem linkDirection_ne_zero (q : Vertex → Point3) (hq : Function.Injective q)
    (v w : Vertex) (h : w ∈ linkCycle v) : linkDirection q v w ≠ 0 := by
  intro hz
  have he := euclideanPoint_injective (hz.trans euclideanPoint.map_zero.symm)
  exact ((mem_linkCycle_iff v w).mp h).1 (hq (sub_eq_zero.mp he)).symm

noncomputable def cornerAngle (q : Vertex → Point3) (v : Vertex) (e : Edge) : ℝ :=
  InnerProductGeometry.angle (linkDirection q v e.1) (linkDirection q v e.2)

noncomputable def linkPerimeter (q : Vertex → Point3) (v : Vertex) : ℝ :=
  ((linkEdges v).map (cornerAngle q v)).sum

/-- The sum over the link cycle is precisely the sum of the incident face angles. -/
theorem linkPerimeter_eq_coneAngle (q : Vertex → Point3) (v : Vertex) :
    linkPerimeter q v = ((incidentCorners v).map (cornerAngle q v)).sum := by
  have he (e : Edge) : cornerAngle q v (orderedEdge e.1 e.2) = cornerAngle q v e := by
    rcases e with ⟨a,b⟩
    rcases le_total a b with hab | hba
    · simp [orderedEdge, min_eq_left hab, max_eq_right hab]
    · simp [orderedEdge, min_eq_right hba, max_eq_left hba, cornerAngle,
        InnerProductGeometry.angle_comm]
  have h := ((linkCycle_checked v).2.2.map (cornerAngle q v)).sum_eq
  simpa only [linkPerimeter, List.map_map, Function.comp_def, he] using h

theorem linkPerimeter_eq_angularCycleLength (q : Vertex → Point3) (v : Vertex) :
    linkPerimeter q v = angularCycleLength ((linkCycle v).map (linkDirection q v)) := by
  rw [angularCycleLength_eq_sum_zip]
  simp only [← List.map_drop, ← List.map_take, ← List.map_append, List.zip_map, List.map_map]
  rfl

/-- The intrinsic flatness condition at the eight spatial vertex stars. -/
def HasFlatStars (q : Vertex → Point3) : Prop := ∀ v, linkPerimeter q v = 2 * Real.pi

end

public section

theorem singleton_face (a : Vertex) : {a} ∈ (triangleComplex geometricFaces).faces := by
  have hcover : ∀ a : Vertex, ∃ f ∈ geometricFaces, a ∈ triangleVertexSet f := by decide +kernel
  obtain ⟨f,hf,ha⟩ := hcover a
  exact ⟨Finset.singleton_nonempty a,f,hf,Finset.singleton_subset_iff.mpr ha⟩

theorem vertex_injective_of_embedding (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q)) : Function.Injective q := by
  exact vertex_injective_of_injective_evaluateTriangles geometricFaces q (by decide +kernel) h

private theorem strongDual_eq_normalDot (L : StrongDual ℝ Point3) (p : Point3) :
    L p = normalDot (L (1,0,0), L (0,1,0), L (0,0,1)) p := by
  have he : p = p.1 • (1,0,0) + p.2.1 • (0,1,0) + p.2.2 • (0,0,1) := by
    apply Prod.ext
    · norm_num [Prod.fst_add, Prod.fst_smul, smul_eq_mul]
    · apply Prod.ext <;> norm_num [Prod.snd_add, Prod.snd_smul, Prod.fst_add,
        Prod.fst_smul, smul_eq_mul]
  conv_lhs => rw [he]
  simp only [map_add, map_smul, smul_eq_mul, normalDot]
  ring

/-- The strict supporting plane exists exactly when the vertex is outside
the convex hull of its neighboring vertices. -/
theorem strictSupport_iff_not_mem_neighborHull (q : Vertex → Point3) (v : Vertex) :
    HasStrictSupport geometricFaces q v ↔ q v ∉ vertexHull q (linkCycle v).toFinset := by
  let s := (linkCycle v).toFinset
  have hs (w : Vertex) : w ∈ s ↔ Adjacent geometricFaces v w := by
    simpa only [s, List.mem_toFinset] using mem_linkCycle_iff v w
  refine ⟨strictSupport_not_mem_neighborHull _ q v s (fun w => (hs w).mp), ?_⟩
  intro h
  change q v ∉ convexHull ℝ (q '' (s : Set Vertex)) at h
  have hc := ((s.finite_toSet).image q).isCompact_convexHull ℝ
  obtain ⟨L,t,hv,ht⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _) hc.isClosed h
  refine ⟨(L (1,0,0), L (0,1,0), L (0,0,1)), fun w hw => ?_⟩
  rw [← strongDual_eq_normalDot, map_sub, sub_pos]
  exact hv.trans (ht _ (subset_convexHull ℝ _ ⟨w,(hs w).mpr hw,rfl⟩))

/-- Failure of strict support gives a positive dependence on at most four directions. -/
theorem small_positive_dependence_of_no_support (q : Vertex → Point3) (v : Vertex)
    (h : ¬ HasStrictSupport geometricFaces q v) :
    ∃ (ι : Type) (_inst : Fintype ι),
      ∃ (z : ι → Point3) (w : ι → ℝ),
        Fintype.card ι ≤ 4 ∧ AffineIndependent ℝ z ∧
        (∀ i, ∃ a ∈ linkCycle v, z i = q a - q v) ∧
        (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • z i = 0 := by
  have hv : q v ∈ vertexHull q (linkCycle v).toFinset :=
    Classical.not_not.mp ((strictSupport_iff_not_mem_neighborHull q v).not.mp h)
  change q v ∈ convexHull ℝ (q '' (↑(linkCycle v).toFinset : Set Vertex)) at hv
  obtain ⟨ι,inst,p,w,hp,hi,hw,ht,hs⟩ := eq_pos_convex_span_of_mem_convexHull hv
  let z (i : ι) := p i - q v
  have hcard := hi.card_le_finrank_succ
  have hdim : Module.finrank ℝ Point3 = 3 := by simp [Point3, Module.finrank_prod]
  have hspan : Module.finrank ℝ (vectorSpan ℝ (Set.range p)) ≤ 3 :=
    hdim ▸ Submodule.finrank_le _
  refine ⟨ι,inst,z,w,hcard.trans (Nat.succ_le_succ hspan),?_,?_,hw,ht,?_⟩
  · let T : Point3 ≃ᵃ[ℝ] Point3 := AffineEquiv.constVAdd ℝ Point3 (-q v)
    have he : T.toAffineMap ∘ p = z := by
      funext i
      change -q v + p i = p i - q v
      abel
    rw [← he]
    exact hi.map' T.toAffineMap T.injective
  · intro i
    obtain ⟨a,ha,he⟩ := hp (Set.mem_range_self i)
    exact ⟨a,List.mem_toFinset.mp ha,congrArg (· - q v) he.symm⟩
  · simp only [z, smul_sub, Finset.sum_sub_distrib, hs, ← Finset.sum_smul, ht, one_smul, sub_self]

/-- The directions in the positive dependence can be listed in their actual
order on the link, with the weights transported along the same reindexing. -/
theorem ordered_positive_dependence_of_no_support (q : Vertex → Point3) (v : Vertex)
    (h : ¬ HasStrictSupport geometricFaces q v) :
    ∃ s : List Vertex, s.Sublist (linkCycle v) ∧ s.length ≤ 4 ∧
      ∃ w : Fin s.length → ℝ,
        (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
        AffineIndependent ℝ (linkDirection q v ∘ s.get) ∧
        ∑ i, w i • linkDirection q v (s.get i) = 0 := by
  classical
  obtain ⟨ι,inst,z,w,hcard,hi,hn,hp,hs,hz⟩ := small_positive_dependence_of_no_support q v h
  choose label hl hzl using hn
  have hlInj : Function.Injective label := by
    intro i j e
    exact hi.injective (by rw [hzl, hzl, e])
  let s := (linkCycle v).filter fun a => decide (a ∈ Set.range label)
  have hsub : s.Sublist (linkCycle v) := List.filter_sublist
  have hm (a : Vertex) : a ∈ s ↔ a ∈ Set.range label := by
    change a ∈ (linkCycle v).filter _ ↔ _
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ⟨i,hi⟩ => ⟨hi ▸ hl i,⟨i,hi⟩⟩⟩
  let g (i : ι) : {a // a ∈ s} := ⟨label i,(hm _).mpr (Set.mem_range_self i)⟩
  let e := Equiv.ofBijective g
    ⟨fun _ _ he => hlInj (congrArg Subtype.val he), fun a => by
      obtain ⟨i,hi⟩ := (hm a).mp a.property
      exact ⟨i,Subtype.ext hi⟩⟩
  let f := (List.Nodup.getEquiv s (hsub.nodup (linkCycle_checked v).1)).trans e.symm
  have hf (i : Fin s.length) : label (f i) = s.get i :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have hc : s.length = Fintype.card ι := by
    simpa only [Fintype.card_fin] using Fintype.card_congr f
  have hd : linkDirection q v ∘ s.get = euclideanPoint ∘ z ∘ f := by
    funext i
    change euclideanPoint (q (s.get i) - q v) = euclideanPoint (z (f i))
    rw [hzl, hf]
  refine ⟨s,hsub,hc.trans_le hcard,w ∘ f,fun i => hp (f i),?_,?_,?_⟩
  · exact (f.sum_comp w).trans hs
  · rw [hd]
    exact (hi.map' euclideanPoint.toAffineMap euclideanPoint_injective).comp_embedding f.toEmbedding
  · have he := f.sum_comp (fun i => euclideanPoint (w i • z i))
    rw [← map_sum euclideanPoint (fun i : ι => w i • z i), hz, map_zero] at he
    have hpoint (i : Fin s.length) : linkDirection q v (s.get i) = euclideanPoint (z (f i)) :=
      congrFun hd i
    simpa only [Function.comp_apply, hpoint, map_smul] using he

/-- A linear relation among affinely independent points with a normalized
dependence is a multiple of that dependence. -/
theorem linear_relation_eq_multiple {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (z : ι → E) (w r : ι → ℝ)
    (ha : AffineIndependent ℝ z) (hw : ∑ i, w i = 1) (hz : ∑ i, w i • z i = 0)
    (hr : ∑ i, r i • z i = 0) (i : ι) : r i = (∑ j, r j) * w i := by
  let c := ∑ j, r j
  let d (j : ι) := r j - c * w j
  have hs : ∑ j, d j = 0 := by simp [d, Finset.sum_sub_distrib, ← Finset.mul_sum, hw, c]
  have hv : ∑ j, d j • z j = 0 := by
    simp [d, sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hr, hz]
  have h := (affineIndependent_iff_of_fintype ℝ z).mp ha d hs
    ((Finset.weightedVSub_eq_linear_combination _ hs).trans hv) i
  exact sub_eq_zero.mp h

/-- A relation that omits one direction of a positive dependence is trivial. -/
theorem linear_relation_eq_zero_of_omitted {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (z : ι → E) (w r : ι → ℝ) (ha : AffineIndependent ℝ z)
    (hw : ∑ i, w i = 1) (hz : ∑ i, w i • z i = 0) (hr : ∑ i, r i • z i = 0)
    (j : ι) (hwj : w j ≠ 0) (hrj : r j = 0) (i : ι) : r i = 0 := by
  have he := linear_relation_eq_multiple z w r ha hw hz hr j
  rw [hrj] at he
  have hc := (mul_eq_zero.mp he.symm).resolve_right hwj
  rw [linear_relation_eq_multiple z w r ha hw hz hr i, hc, zero_mul]

/-- Four positively dependent directions in their order on the link force
cone angle strictly greater than `2π`. -/
theorem linkPerimeter_gt_of_ordered_positive_four (q : Vertex → Point3) (v a b c d : Vertex)
    (horder : [a,b,c,d].Sublist (linkCycle v)) (w : Fin 4 → ℝ)
    (hp : ∀ i, 0 < w i) (hw : ∑ i, w i = 1) :
    let z : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
      ![linkDirection q v a,linkDirection q v b,linkDirection q v c,linkDirection q v d]
    AffineIndependent ℝ z → ∑ i, w i • z i = 0 → 2 * Real.pi < linkPerimeter q v := by
  intro z hA hz
  let x := linkDirection q v a
  let y := linkDirection q v b
  let t := linkDirection q v c
  let u := linkDirection q v d
  have hLin : LinearIndependent ℝ (fun i : Fin 3 => z i.castSucc) := by
    rw [Fintype.linearIndependent_iff]
    intro r hr i
    let s : Fin 4 → ℝ := Fin.lastCases 0 r
    have hs : ∑ j, s j • z j = 0 := by
      simpa only [s, Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last,
        zero_smul, add_zero] using hr
    have he := linear_relation_eq_zero_of_omitted z w s hA hw hz hs
      (Fin.last 3) (hp _).ne' Fin.lastCases_last i.castSucc
    simpa only [s, Fin.lastCases_castSucc] using he
  have he : (fun i : Fin 3 => z i.castSucc) = ![x,y,t] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at hLin
  have hr : w 0 • x + w 1 • y + w 2 • t + w 3 • u = 0 := by
    simpa [z,x,y,t,u,Fin.sum_univ_succ,add_assoc] using hz
  have hquad := quadrilateral_perimeter_gt_of_positive_relation x y t u
    (w 0) (w 1) (w 2) (w 3) (hp 0) (hp 1) (hp 2) (hp 3) hr hLin
  have hcyc := angularCycleLength_mono (horder.map (linkDirection q v))
  rw [linkPerimeter_eq_angularCycleLength]
  apply hquad.trans_le
  simpa [angularCycleLength_four, x, y, t, u] using hcyc

/-- A flat link without strict support has either an antipodal pair or a
positive affine-independent triple, in link order. -/
theorem ordered_pair_or_triple_of_flat_no_support (q : Vertex → Point3) (v : Vertex)
    (hflat : linkPerimeter q v = 2 * Real.pi) (hq : Function.Injective q)
    (h : ¬ HasStrictSupport geometricFaces q v) :
    (∃ a b : Vertex, [a,b].Sublist (linkCycle v) ∧
      InnerProductGeometry.angle (linkDirection q v a) (linkDirection q v b) = Real.pi) ∨
    ∃ a b c : Vertex, [a,b,c].Sublist (linkCycle v) ∧
      ∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧
        let z := ![linkDirection q v a,linkDirection q v b,linkDirection q v c]
        AffineIndependent ℝ z ∧ ∑ i, w i • z i = 0 := by
  obtain ⟨s,hsub,hcard,w,hpos,hmass,hi,hrel⟩ := ordered_positive_dependence_of_no_support q v h
  have htwo : 2 ≤ s.length := by
    by_contra! hn
    cases s with
    | nil => simp at hmass
    | cons a s =>
      cases s with
      | nil =>
        have hz : w 0 • linkDirection q v a = 0 := by simpa [Fin.sum_univ_succ] using hrel
        exact linkDirection_ne_zero q hq v a (hsub.subset (by simp))
          ((smul_eq_zero.mp hz).resolve_left (hpos 0).ne')
      | cons b s => simp at hn
  have hcases : s.length = 2 ∨ s.length = 3 ∨ s.length = 4 := by omega
  rcases hcases with hlen | hlen | hlen
  · obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hlen
    have hzero : w 0 • linkDirection q v a + w 1 • linkDirection q v b = 0 := by
      simpa [Fin.sum_univ_succ] using hrel
    have he : w 1 • linkDirection q v b = -(w 0 • linkDirection q v a) := by
      apply eq_neg_iff_add_eq_zero.mpr
      rwa [add_comm]
    have hc : linkDirection q v b = (-w 0 / w 1) • linkDirection q v a := by
      calc
        _ = (w 1)⁻¹ • (w 1 • linkDirection q v b) := by
          rw [smul_smul, inv_mul_cancel₀ (hpos 1).ne', one_smul]
        _ = _ := by rw [he, smul_neg, smul_smul, neg_div, div_eq_inv_mul, neg_smul]
    exact Or.inl ⟨a,b,hsub,InnerProductGeometry.angle_eq_pi_iff.mpr
      ⟨linkDirection_ne_zero q hq v a (hsub.subset (by simp)),
        -w 0 / w 1,div_neg_of_neg_of_pos (neg_neg_of_pos (hpos 0)) (hpos 1),hc⟩⟩
  · obtain ⟨a,b,c,rfl⟩ := List.length_eq_three.mp hlen
    have he : linkDirection q v ∘ [a,b,c].get =
        ![linkDirection q v a,linkDirection q v b,linkDirection q v c] := by
      funext i
      fin_cases i <;> rfl
    change (∑ i : Fin 3, w i • (linkDirection q v ∘ [a,b,c].get) i) = 0 at hrel
    rw [he] at hi
    rw [he] at hrel
    exact Or.inr ⟨a,b,c,hsub,w,hpos,hmass,hi,hrel⟩
  · obtain ⟨a,b,c,d,rfl⟩ := List.length_eq_four.mp hlen
    have he : linkDirection q v ∘ [a,b,c,d].get =
        ![linkDirection q v a,linkDirection q v b,linkDirection q v c,linkDirection q v d] := by
      funext i
      fin_cases i <;> rfl
    change (∑ i : Fin 4, w i • (linkDirection q v ∘ [a,b,c,d].get) i) = 0 at hrel
    rw [he] at hi
    rw [he] at hrel
    have hgt := linkPerimeter_gt_of_ordered_positive_four q v a b c d hsub w hpos hmass hi hrel
    exact False.elim (hgt.ne hflat.symm)

end

end OrigamiTorus.Type2
