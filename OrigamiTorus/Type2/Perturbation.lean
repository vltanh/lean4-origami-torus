module

public import OrigamiTorus.Geometry.TriangleIntersections
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-! Generic perturbations of embedded labeled triangles, including coplanar initial data. -/

public section

open Filter Polynomial
open scoped Topology

namespace OrigamiTorus

private def momentCurve (v : Vertex) : Point3 :=
  let r := (v.val : ℝ)
  (r,r^2,r^3)

private theorem bracket_momentCurve (a b c d : Vertex) (hab : a < b) (hbc : b < c)
    (hcd : c < d) : affineBracket (momentCurve a) (momentCurve b) (momentCurve c) (momentCurve d) ≠ 0 := by
  let A : ℝ := a.val
  let B : ℝ := b.val
  let C : ℝ := c.val
  let D : ℝ := d.val
  have hAB : A < B := Nat.cast_lt.mpr hab
  have hBC : B < C := Nat.cast_lt.mpr hbc
  have hCD : C < D := Nat.cast_lt.mpr hcd
  have h :
      affineBracket (momentCurve a) (momentCurve b) (momentCurve c) (momentCurve d) =
        (B-A)*(C-A)*(D-A)*(C-B)*(D-B)*(D-C) := by
    simp only [affineBracket, determinant3, momentCurve, Prod.fst_sub, Prod.snd_sub, A, B, C, D]
    ring
  rw [h]
  exact ne_of_gt (mul_pos (mul_pos (mul_pos (mul_pos (mul_pos
    (sub_pos.mpr hAB) (sub_pos.mpr (hAB.trans hBC))) (sub_pos.mpr (hAB.trans (hBC.trans hCD))))
    (sub_pos.mpr hBC)) (sub_pos.mpr (hBC.trans hCD))) (sub_pos.mpr hCD))

private noncomputable def determinantAlong (p q r u v w : Point3) : ℝ[X] :=
  monomial 0 (determinant3 p q r) +
  monomial 1 (determinant3 u q r + determinant3 p v r + determinant3 p q w) +
  monomial 2 (determinant3 u v r + determinant3 u q w + determinant3 p v w) +
  monomial 3 (determinant3 u v w)

private theorem determinantAlong_eval (p q r u v w : Point3) (t : ℝ) :
    (determinantAlong p q r u v w).eval t =
      determinant3 (p + t • u) (q + t • v) (r + t • w) := by
  have h (a : Point3) : t • a = (t*a.1, t*a.2.1, t*a.2.2) := rfl
  simp only [determinantAlong, eval_add, eval_monomial, determinant3, Prod.fst_add, Prod.snd_add,
    h]
  ring

private theorem eventually_generic_line (q : Vertex → Point3) :
    ∀ᶠ t : ℝ in cofinite, GenericLift
      (fun i => ((q i + t • momentCurve i).1,(q i + t • momentCurve i).2.1))
      (fun i => (q i + t • momentCurve i).2.2) := by
  unfold GenericLift
  simp only [eventually_all, volume_eq_affineBracket]
  intro a b c d hab hbc hcd
  let f := determinantAlong (q b-q a) (q c-q a) (q d-q a)
    (momentCurve b-momentCurve a) (momentCurve c-momentCurve a) (momentCurve d-momentCurve a)
  have hcoeff : f.coeff 3 =
      affineBracket (momentCurve a) (momentCurve b) (momentCurve c) (momentCurve d) := by
    simp [f, determinantAlong, coeff_monomial, affineBracket]
  have hf : f ≠ 0 := by
    intro hz
    exact bracket_momentCurve a b c d hab hbc hcd (by simpa [hz] using hcoeff.symm)
  filter_upwards [eventually_eval_ne_zero_cofinite hf] with t ht
  have H (i : Vertex) :
      (q i + t • momentCurve i) - (q a + t • momentCurve a) =
        (q i - q a) + t • (momentCurve i - momentCurve a) := by
    rw [smul_sub]
    abel
  simpa only [f, determinantAlong_eval, affineBracket, H] using ht

/-- General position is available in every neighborhood of any labeled placement. -/
theorem exists_generic_placement (q : Vertex → Point3) {U : Set (Vertex → Point3)}
    (hU : IsOpen U) (hq : q ∈ U) :
    ∃ v ∈ U, GenericLift (fun i => ((v i).1,(v i).2.1)) (fun i => (v i).2.2) := by
  have hc : Continuous (fun t : ℝ => q + t • momentCurve) := by fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝 0, q + t • momentCurve ∈ U := by
    have hm := hc.continuousAt (x := (0 : ℝ))
    exact hm.preimage_mem_nhds (hU.mem_nhds (by simpa using hq))
  obtain ⟨t,ht,hgt⟩ := ((he.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).and
    ((eventually_generic_line q).filter_mono (nhdsNE_le_cofinite 0))).exists
  exact ⟨q + t • momentCurve, ht, hgt⟩

/-- Any small open system of strict constraints on an embedding admits a generic
perturbation which is still an embedding of the same face list. -/
theorem exists_generic_embedded_placement (fs : List Triangle) (q : Vertex → Point3)
    {U : Set (Vertex → Point3)} (hU : IsOpen U) (hq : q ∈ U)
    (h : Function.Injective (evaluateTriangles fs q)) :
    ∃ v ∈ U, Function.Injective (evaluateTriangles fs v) ∧
      GenericLift (fun i => ((v i).1,(v i).2.1)) (fun i => (v i).2.2) := by
  obtain ⟨v,hv,hg⟩ := exists_generic_placement q (hU.inter (isOpen_injective_evaluateTriangles fs))
    ⟨hq,h⟩
  exact ⟨v,hv.1,hv.2,hg⟩

end OrigamiTorus

namespace OrigamiTorus.Type2

@[expose] public section

/-- The neighbors of a label in the triangle list. -/
def Adjacent (fs : List Triangle) (v w : Vertex) : Prop :=
  v ≠ w ∧ ∃ f ∈ fs, v ∈ triangleVertexSet f ∧ w ∈ triangleVertexSet f

def normalDot (n p : Point3) : ℝ := n.1*p.1 + n.2.1*p.2.1 + n.2.2*p.2.2

/-- A plane through the vertex strictly supports its link. -/
def HasStrictSupport (fs : List Triangle) (q : Vertex → Point3) (v : Vertex) : Prop :=
  ∃ n : Point3, ∀ w, Adjacent fs v w → 0 < normalDot n (q w - q v)

def faceSide (q : Vertex → Point3) (f : Triangle) (w : Vertex) : ℝ :=
  affineBracket (q f.1) (q f.2.1) (q f.2.2) (q w)

/-- Some face at the vertex has two neighbor vertices on opposite strict sides. -/
def HasMixedFace (fs : List Triangle) (q : Vertex → Point3) (v : Vertex) : Prop :=
  ∃ (f : Triangle) (_ : f ∈ fs ∧ v ∈ triangleVertexSet f) (a b : Vertex),
    (Adjacent fs v a ∧ a ∉ triangleVertexSet f ∧
      Adjacent fs v b ∧ b ∉ triangleVertexSet f) ∧
    0 < faceSide q f a ∧ faceSide q f b < 0

theorem vertexCount_neZero : NeZero 8 := @Nat.instNeZeroSucc 7

/-- The geometric face list with the labels used by the Type 2 sign formula. -/
def geometricFaces : List Triangle :=
  let v := @Fin.ofNat 8 vertexCount_neZero
  [(v 0,v 4,v 6), (v 0,v 4,v 7), (v 0,v 5,v 6), (v 0,v 5,v 7),
   (v 1,v 3,v 5), (v 1,v 3,v 6), (v 1,v 4,v 5), (v 1,v 4,v 7),
   (v 1,v 6,v 7), (v 2,v 3,v 4), (v 2,v 3,v 7), (v 2,v 4,v 5),
   (v 2,v 5,v 6), (v 2,v 6,v 7), (v 3,v 4,v 6), (v 3,v 5,v 7)]

theorem geometricFaces_labels :
    geometricFaces.map (fun f => (triangleVertices f).map Fin.val) = faces := by
  decide +kernel

theorem adjacent_geometricFaces_iff (u v : Vertex) :
    Adjacent geometricFaces u v ↔ isEdge u.val v.val = true := by
  have H : ∀ a b : Vertex, isEdge a.val b.val =
      ((a != b) && geometricFaces.any (fun f => (triangleVertices f).contains a &&
        (triangleVertices f).contains b)) := by
    decide +kernel
  rw [H, Bool.and_eq_true, List.any_eq_true]
  simp [Adjacent]

end

public section

theorem normalDot_linear (n : Point3) : IsLinearMap ℝ (normalDot n) := by
  constructor
  · intro a b
    simp only [normalDot, Prod.fst_add, Prod.snd_add]
    ring
  · intro r a
    have h : r • a = (r*a.1,r*a.2.1,r*a.2.2) := rfl
    simp only [h, normalDot, smul_eq_mul]
    ring

/-- The singleton side of an affine circuit cannot be a strictly supported vertex
when every label on the other side is its neighbor. -/
theorem strictSupport_not_mem_neighborHull (fs : List Triangle) (q : Vertex → Point3)
    (v : Vertex) (s : Finset Vertex) (hs : ∀ w ∈ s, Adjacent fs v w)
    (h : HasStrictSupport fs q v) : q v ∉ vertexHull q s := by
  obtain ⟨n,hn⟩ := h
  have hsubset : q '' (s : Set Vertex) ⊆ {p | normalDot n (q v) < normalDot n p} := by
    rintro _ ⟨w,hw,rfl⟩
    have H := hn w (hs w hw)
    have he : normalDot n (q w - q v) = normalDot n (q w) - normalDot n (q v) := by
      simp only [normalDot, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [he] at H
    exact sub_pos.mp H
  intro he
  have hp := convexHull_min hsubset (convex_halfSpace_gt (normalDot_linear n) _) he
  exact (lt_irrefl (normalDot n (q v))) hp

private theorem isOpen_support (fs : List Triangle) (v : Vertex) :
    IsOpen {q | HasStrictSupport fs q v} := by
  have h : {q | HasStrictSupport fs q v} =
      ⋃ n : Point3, ⋂ w : Vertex, ⋂ _ : Adjacent fs v w, {q | 0 < normalDot n (q w-q v)} := by
    ext q
    simp [HasStrictSupport]
  rw [h]
  refine isOpen_iUnion fun n => isOpen_iInter_of_finite fun w => isOpen_iInter_of_finite fun _ => ?_
  apply isOpen_lt continuous_const
  unfold normalDot
  fun_prop

private theorem isOpen_mixed (fs : List Triangle) (v : Vertex) :
    IsOpen {q | HasMixedFace fs q v} := by
  have h : {q | HasMixedFace fs q v} =
      ⋃ (f : Triangle) (_ : f ∈ fs ∧ v ∈ triangleVertexSet f) (a : Vertex) (b : Vertex)
        (_ : Adjacent fs v a ∧ a ∉ triangleVertexSet f ∧ Adjacent fs v b ∧ b ∉ triangleVertexSet f),
        {q | 0 < faceSide q f a} ∩ {q | faceSide q f b < 0} := by
    ext q
    simp only [HasMixedFace, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
  rw [h]
  have hc (f : Triangle) (w : Vertex) : Continuous (fun q => faceSide q f w) := by
    unfold faceSide affineBracket determinant3
    fun_prop
  exact isOpen_iUnion fun f => isOpen_iUnion fun _ => isOpen_iUnion fun a => isOpen_iUnion fun b =>
    isOpen_iUnion fun _ => (isOpen_lt continuous_const (hc f a)).inter (isOpen_lt (hc f b) continuous_const)

/-- An embedded configuration with strict support and mixed-side witnesses
can be made generic while retaining all those witnesses. -/
theorem exists_generic_with_strict_witnesses (fs : List Triangle) (required : Finset Vertex)
    (q : Vertex → Point3) (h : Function.Injective (evaluateTriangles fs q))
    (hs : ∀ v, HasStrictSupport fs q v) (hm : ∀ v ∈ required, HasMixedFace fs q v) :
    ∃ r : Vertex → Point3, Function.Injective (evaluateTriangles fs r) ∧
      GenericLift (fun v => ((r v).1,(r v).2.1)) (fun v => (r v).2.2) ∧
      (∀ v, HasStrictSupport fs r v) ∧ ∀ v ∈ required, HasMixedFace fs r v := by
  let U := (⋂ v : Vertex, {p | HasStrictSupport fs p v}) ∩
    (⋂ v : Vertex, ⋂ _ : v ∈ required, {p | HasMixedFace fs p v})
  have hU : IsOpen U := (isOpen_iInter_of_finite (isOpen_support fs)).inter
    (isOpen_iInter_of_finite fun v => isOpen_iInter_of_finite fun _ => isOpen_mixed fs v)
  have hq : q ∈ U := by simpa [U] using And.intro hs hm
  obtain ⟨r,hr,he,hg⟩ := exists_generic_embedded_placement fs q hU hq h
  exact ⟨r,he,hg,by simpa [U] using hr⟩

private noncomputable def reflectFirst : Point3 →ₗ[ℝ] Point3 where
  toFun p := (-p.1, p.2)
  map_add' a b := by simp [add_comm]
  map_smul' r p := by
    have h (a : Point3) : r • a = (r*a.1,r*a.2.1,r*a.2.2) := rfl
    simp [h]

private theorem reflected_bracket (a b c d : Point3) :
    affineBracket (reflectFirst a) (reflectFirst b) (reflectFirst c) (reflectFirst d) =
      -affineBracket a b c d := by
  simp only [reflectFirst, LinearMap.coe_mk, AddHom.coe_mk, affineBracket, determinant3,
    Prod.fst_sub, Prod.snd_sub]
  ring

/-- The placement can be put in the normalization used by the sign formula. -/
theorem exists_normalized_with_strict_witnesses (fs : List Triangle) (required : Finset Vertex)
    (q : Vertex → Point3) (h : Function.Injective (evaluateTriangles fs q))
    (hs : ∀ v, HasStrictSupport fs q v) (hm : ∀ v ∈ required, HasMixedFace fs q v) :
    ∃ r : Vertex → Point3, Function.Injective (evaluateTriangles fs r) ∧
      GenericLift (fun v => ((r v).1,(r v).2.1)) (fun v => (r v).2.2) ∧
      0 < affineBracket (r 0) (r 1) (r 2) (r 3) ∧
      (∀ v, HasStrictSupport fs r v) ∧ ∀ v ∈ required, HasMixedFace fs r v := by
  obtain ⟨r,he,hg,hss,hmm⟩ := exists_generic_with_strict_witnesses fs required q h hs hm
  have hz : affineBracket (r 0) (r 1) (r 2) (r 3) ≠ 0 := by
    simpa only [volume_eq_affineBracket] using hg 0 1 2 3 (by decide) (by decide) (by decide)
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · refine ⟨reflectFirst ∘ r, ?_, ?_, ?_, ?_, ?_⟩
    · rw [evaluateTriangles_comp_linear]
      have hinj : Function.Injective reflectFirst := by
        intro a b e
        change (-a.1,a.2) = (-b.1,b.2) at e
        obtain ⟨h₁,h₂⟩ := Prod.mk.inj e
        exact Prod.ext (neg_injective h₁) h₂
      exact hinj.comp he
    · intro a b c d hab hbc hcd
      rw [volume_eq_affineBracket]
      change affineBracket (reflectFirst (r a)) (reflectFirst (r b))
        (reflectFirst (r c)) (reflectFirst (r d)) ≠ 0
      rw [reflected_bracket, neg_ne_zero]
      simpa only [volume_eq_affineBracket] using hg a b c d hab hbc hcd
    · simpa only [Function.comp_apply, reflected_bracket] using neg_pos.mpr hneg
    · intro v
      obtain ⟨n,hn⟩ := hss v
      refine ⟨reflectFirst n,fun w hw => ?_⟩
      change 0 < normalDot (reflectFirst n) (reflectFirst (r w) - reflectFirst (r v))
      rw [← map_sub]
      have hd (p : Point3) : normalDot (reflectFirst n) (reflectFirst p) = normalDot n p := by
        simp [normalDot,reflectFirst]
      rw [hd]
      exact hn w hw
    · intro v hv
      obtain ⟨f,hf,a,b,⟨ha,ha',hb,hb'⟩,hpos,hneg⟩ := hmm v hv
      refine ⟨f,hf,b,a,⟨hb,hb',ha,ha'⟩,?_,?_⟩
      · simpa only [faceSide, Function.comp_apply, reflected_bracket] using neg_pos.mpr hneg
      · simpa only [faceSide, Function.comp_apply, reflected_bracket] using neg_neg_of_pos hpos
  · exact ⟨r,he,hg,hpos,hss,hmm⟩

end

end OrigamiTorus.Type2
