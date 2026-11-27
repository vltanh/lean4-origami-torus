module

public import OrigamiTorus.MarkedShape
import Mathlib.Analysis.Convex.Between
import Mathlib.Tactic

/-! The metric and orientation of a face developed from its three squared side lengths. -/

@[expose] public section

namespace OrigamiTorus

open InnerProductGeometry
open scoped InnerProductSpace

/-- A face of an injective affine realization has three noncollinear vertices. -/
theorem not_collinear_of_injective_face (fs : List Triangle) (q : Vertex → Point3)
    (hq : Function.Injective (evaluateTriangles fs q)) (a b c : Vertex)
    (hf : ∃ f ∈ fs, triangleVertexSet (a,b,c) ⊆ triangleVertexSet f)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Collinear ℝ ({q a,q b,q c} : Set Point3) := by
  let S := triangleVertexSet (a,b,c)
  obtain ⟨f,hf,hsub⟩ := hf
  have hface (T : Finset Vertex) (hT : T.Nonempty) (hsub : T ⊆ S) :
      T ∈ (triangleComplex fs).faces := ⟨hT,f,hf,hsub.trans ‹S ⊆ triangleVertexSet f›⟩
  have hmiddle (i j k : Vertex) (hji : j ≠ i) (hjk : j ≠ k)
      (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S) : ¬ Wbtw ℝ (q i) (q j) (q k) := by
    intro h
    have hj' := hface {j} (by simp) (Finset.singleton_subset_iff.mpr hj)
    have hik := hface {i,k} (by simp) (by
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      exact hv.elim (fun he => he ▸ hi) (fun he => he ▸ hk))
    have hd : Disjoint ({j} : Finset Vertex) {i,k} := by simp [hji,hjk]
    have hh := disjoint_vertexHull_of_injective_evaluateTriangles fs q hq {j} {i,k} hj' hik hd
    apply Set.disjoint_left.mp hh (subset_convexHull ℝ _ ⟨j,by simp,rfl⟩)
    rw [vertexHull_pair]
    exact h.mem_segment
  have ha : a ∈ S := by simp [S,triangleVertexSet_eq]
  have hb : b ∈ S := by simp [S,triangleVertexSet_eq]
  have hc : c ∈ S := by simp [S,triangleVertexSet_eq]
  intro h
  rcases h.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact hmiddle a b c hab.symm hbc ha hb hc h
  · exact hmiddle b c a hbc.symm hac.symm hb hc ha h
  · exact hmiddle c a b hac hab hc ha hb h

/-- The spatial squared length agrees with the squared norm in Euclidean coordinates. -/
theorem euclideanPoint_norm_sq (p : Point3) :
    ‖Type2.euclideanPoint p‖^2 = Type5.squared3 p := by
  rw [EuclideanSpace.real_norm_sq_eq]
  norm_num [Type2.euclideanPoint, Fin.sum_univ_succ, Type5.squared3,Type5.squared2,
    Type5.horizontal,Type5.dot,pow_two,add_assoc]

theorem spatialEdgeSq_euclidean (q : Vertex → Point3) (a b : Vertex) :
    Type7.spatialEdgeSq q a b = ‖Type2.euclideanPoint (q b) - Type2.euclideanPoint (q a)‖^2 := by
  rw [← map_sub,euclideanPoint_norm_sq]
  rfl

/-- Squared spatial distances are symmetric, including for degenerate placements. -/
theorem spatialEdgeSq_comm (q : Vertex → Point3) (a b : Vertex) :
    Type7.spatialEdgeSq q a b = Type7.spatialEdgeSq q b a := by
  simp only [spatialEdgeSq_euclidean]
  rw [norm_sub_rev]

@[simp] theorem spatialEdgeSq_same (q : Vertex → Point3) (a : Vertex) :
    Type7.spatialEdgeSq q a a = 0 := by simp [spatialEdgeSq_euclidean]

/-- Both denominators and developed heights are positive on a noncollinear spatial face. -/
theorem spatial_triangle_regular (q : Vertex → Point3) (a b c : Vertex)
    (habc : ¬ Collinear ℝ ({q a,q b,q c} : Set Point3)) :
    0 < Type7.spatialEdgeSq q a b ∧
      0 < developedHeightSq (Type7.spatialEdgeSq q a b) (Type7.spatialEdgeSq q a c)
        (Type7.spatialEdgeSq q b c) := by
  let T := Type2.euclideanPoint
  let u := T (q b)-T (q a)
  let v := T (q c)-T (q a)
  have hdir (r : ℝ) : v-r • u ≠ 0 := by
    intro he
    have hs : q c-q a = r • (q b-q a) := by
      apply Type2.euclideanPoint_injective
      simpa only [map_sub,map_smul] using sub_eq_zero.mp he
    have hline : q c ∈ line[ℝ,q a,q b] := by
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      refine ⟨r,?_⟩
      rw [AffineMap.lineMap_apply]
      change r • (q b-q a)+q a = q c
      rw [← hs,sub_add_cancel]
    have hc := collinear_insert_of_mem_affineSpan_pair hline
    apply habc
    convert hc using 1
    ext p
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    tauto
  have hu : u ≠ 0 := by
    intro hz
    have he := Type2.euclideanPoint_injective (sub_eq_zero.mp hz)
    apply habc
    simp [he,collinear_pair]
  have hU : 0 < ‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hbc : T (q c)-T (q b) = v-u := by dsimp only [v,u]; abel
  simp only [spatialEdgeSq_euclidean]
  change 0 < ‖u‖^2 ∧ 0 < developedHeightSq (‖u‖^2) (‖v‖^2) (‖T (q c)-T (q b)‖^2)
  rw [hbc]
  refine ⟨hU,?_⟩
  let r := ⟪v,u⟫_ℝ/‖u‖^2
  have hr : developedRe (‖u‖^2) (‖v‖^2) (‖v-u‖^2) = r := by
    rw [developedRe,norm_sub_sq_real v u]
    unfold r
    field_simp [hU.ne']
    ring
  have hh : ‖v-r • u‖^2/‖u‖^2 = ‖v‖^2/‖u‖^2-r^2 := by
    rw [norm_sub_sq_real v (r • u),norm_smul,Real.norm_eq_abs,real_inner_smul_right,mul_pow,sq_abs]
    unfold r
    field_simp [hU.ne']
    <;> ring
  rw [developedHeightSq,hr,← hh]
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr (hdir r))) hU

/-- The developed third corner has the selected orientation and the two required
squared distances in the normalized chart. -/
theorem developedCorner_metric (ab ac bc : ℝ) (sign : Bool) (hab : ab ≠ 0)
    (hh : 0 < developedHeightSq ab ac bc) :
    let z := developedCorner sign ab ac bc
    (if sign then 0 < z.im else z.im < 0) ∧
      Complex.normSq z = ac/ab ∧ Complex.normSq (z-1) = bc/ab := by
  let z := developedCorner sign ab ac bc
  let r := developedRe ab ac bc
  let h := developedHeightSq ab ac bc
  have hre : z.re = r := by simp [z,r,developedCorner]
  have him : z.im = (if sign then 1 else -1)*Real.sqrt h := by simp [z,h,developedCorner]
  have hs : z.im*z.im = h := by
    rw [him]
    cases sign <;> simp only [Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,neg_mul_neg] <;>
      exact Real.mul_self_sqrt hh.le
  have hpos : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  refine ⟨?_,?_,?_⟩
  · rw [him]
    cases sign <;> simp [hpos]
  · rw [Complex.normSq_apply,hre,hs]
    unfold h developedHeightSq r
    ring
  · simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
      sub_zero]
    change (z.re-1)*(z.re-1)+z.im*z.im = bc/ab
    rw [hre,hs]
    unfold h developedHeightSq r developedRe
    field_simp [hab]
    <;> ring

/-- The complex cross product of two planar vectors. -/
def complexCross (u v : ℂ) : ℝ := ((starRingEnd ℂ) u * v).im

theorem complexCross_apply (u v : ℂ) : complexCross u v = u.re*v.im-u.im*v.re := by
  simp [complexCross,Complex.mul_im,sub_eq_add_neg]

theorem complexCross_swap (u v : ℂ) : complexCross u v = -complexCross v u := by
  simp only [complexCross_apply]
  ring

theorem complexCross_mul (m u v : ℂ) :
    complexCross (m*u) (m*v) = Complex.normSq m * complexCross u v := by
  simp only [complexCross_apply,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring

theorem complexCross_cycle (A B C : ℂ) :
    complexCross (C-B) (A-B) = complexCross (B-A) (C-A) := by
  simp only [complexCross_apply,Complex.sub_re,Complex.sub_im]
  ring

theorem normSq_sub_rev (A B : ℂ) : Complex.normSq (A-B) = Complex.normSq (B-A) := by
  rw [← neg_sub,Complex.normSq_neg]

/-- Gluing the next triangle to its developed edge preserves the scale on its
three lengths and gives the requested orientation. -/
theorem develop_face_on_edge (ab ac bc k : ℝ) (A B : ℂ) (sign : Bool)
    (hk : 0 < k) (hab : 0 < ab) (hh : 0 < developedHeightSq ab ac bc)
    (hAB : k*Complex.normSq (B-A) = ab) :
    let C := A+(B-A)*developedCorner sign ab ac bc
    (if sign then 0 < complexCross (B-A) (C-A) else complexCross (B-A) (C-A) < 0) ∧
      k*Complex.normSq (C-A) = ac ∧ k*Complex.normSq (C-B) = bc := by
  let z := developedCorner sign ab ac bc
  let C := A+(B-A)*z
  obtain ⟨hi,hac,hbc⟩ := developedCorner_metric ab ac bc sign hab.ne' hh
  have hCA : C-A = (B-A)*z := by unfold C; ring
  have hCB : C-B = (B-A)*(z-1) := by unfold C; ring
  have hcross : complexCross (B-A) (C-A) = Complex.normSq (B-A)*z.im := by
    calc
      _ = complexCross ((B-A)*1) ((B-A)*z) := by rw [hCA,mul_one]
      _ = _ := by rw [complexCross_mul]; simp [complexCross]
  have hn : 0 < Complex.normSq (B-A) := by
    have he : Complex.normSq (B-A) = ab/k := (eq_div_iff hk.ne').mpr (by rw [mul_comm,hAB])
    rw [he]
    exact div_pos hab hk
  change (if sign then 0 < complexCross (B-A) (C-A) else complexCross (B-A) (C-A) < 0) ∧
      k*Complex.normSq (C-A) = ac ∧ k*Complex.normSq (C-B) = bc
  rw [hcross,hCA,hCB,Complex.normSq_mul,Complex.normSq_mul,← mul_assoc,← mul_assoc,hAB,hac,hbc]
  refine ⟨?_,mul_div_cancel₀ _ hab.ne',mul_div_cancel₀ _ hab.ne'⟩
  cases sign
  · exact mul_neg_of_pos_of_neg hn hi
  · exact mul_pos hn hi

theorem angle_eq_of_scaled_lengths {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (u v : E) (U V : F) {k : ℝ} (hk : 0 < k)
    (hu : ‖u‖^2 = k*‖U‖^2) (hv : ‖v‖^2 = k*‖V‖^2)
    (hw : ‖v-u‖^2 = k*‖V-U‖^2) : angle u v = angle U V := by
  have hnorm (w : E) (W : F) (he : ‖w‖^2 = k*‖W‖^2) :
      ‖w‖ = Real.sqrt k*‖W‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rwa [mul_pow,Real.sq_sqrt hk.le]
  have hinner : ⟪u,v⟫_ℝ = k*⟪U,V⟫_ℝ := by
    rw [norm_sub_sq_real v u,norm_sub_sq_real V U,hu,hv] at hw
    rw [real_inner_comm v u,real_inner_comm V U]
    linarith only [hw]
  apply Real.injOn_cos ⟨angle_nonneg _ _,angle_le_pi _ _⟩ ⟨angle_nonneg _ _,angle_le_pi _ _⟩
  rw [cos_angle,cos_angle,hinner,hnorm u U hu,hnorm v V hv]
  have hden : (Real.sqrt k*‖U‖)*(Real.sqrt k*‖V‖) = k*(‖U‖*‖V‖) := by
    calc
      _ = (Real.sqrt k)^2*(‖U‖*‖V‖) := by ring
      _ = _ := by rw [Real.sq_sqrt hk.le]
  rw [hden,mul_div_mul_left _ _ hk.ne']

/-- An oriented planar chart of the three spatial vertices, in a common
length scale for the entire development. -/
structure DevelopedFace (q : Vertex → Point3) (scaleSq : ℝ) (f : Triangle) (positive : Bool) where
  point : Vertex → ℂ
  orientation : let D := complexCross (point f.2.1-point f.1) (point f.2.2-point f.1)
    if positive then 0 < D else D < 0
  edge_metric : ∀ a ∈ triangleVertexSet f, ∀ b ∈ triangleVertexSet f,
    scaleSq*Complex.normSq (point b-point a) = Type7.spatialEdgeSq q a b

namespace DevelopedFace

variable {q : Vertex → Point3} {k : ℝ} {s : Bool}

/-- Cyclic relabeling preserves the planar chart and its orientation. -/
def rotate {a b c : Vertex} (P : DevelopedFace q k (a,b,c) s) :
    DevelopedFace q k (b,c,a) s where
  point := P.point
  orientation := by
    change (if s then 0 < complexCross (P.point c-P.point b) (P.point a-P.point b)
      else complexCross (P.point c-P.point b) (P.point a-P.point b) < 0)
    rw [complexCross_cycle]
    exact P.orientation
  edge_metric i hi j hj := by
    apply P.edge_metric i _ j <;>
      simp only [triangleVertexSet_eq,Finset.mem_insert,Finset.mem_singleton] at hi hj ⊢ <;>
      tauto

/-- Reversing the face order reverses the orientation sign. -/
def swapLast {a b c : Vertex} (P : DevelopedFace q k (a,b,c) s) :
    DevelopedFace q k (a,c,b) (!s) where
  point := P.point
  orientation := by
    change (if !s then 0 < complexCross (P.point c-P.point a) (P.point b-P.point a)
      else complexCross (P.point c-P.point a) (P.point b-P.point a) < 0)
    rw [complexCross_swap]
    cases s
    · exact neg_pos.mpr P.orientation
    · exact neg_neg_of_pos P.orientation
  edge_metric i hi j hj := by
    apply P.edge_metric i _ j <;>
      simp only [triangleVertexSet_eq,Finset.mem_insert,Finset.mem_singleton] at hi hj ⊢ <;>
      tauto

/-- Construct the oriented chart of a spatial triangle from the positions of
the two vertices on the incoming edge. -/
noncomputable def onEdge (q : Vertex → Point3) (k : ℝ) (a b c : Vertex) (positive : Bool)
    (A B : ℂ) (hk : 0 < k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hr : ¬ Collinear ℝ ({q a,q b,q c} : Set Point3))
    (hAB : k*Complex.normSq (B-A) = Type7.spatialEdgeSq q a b) :
    DevelopedFace q k (a,b,c) positive where
  point v := if v = a then A else if v = b then B
    else if v = c then A+(B-A)*Type7.triangleCorner (Type7.spatialEdgeSq q) positive a b c else 0
  orientation := by
    obtain ⟨hl,hh⟩ := spatial_triangle_regular q a b c hr
    have h := (develop_face_on_edge _ _ _ k A B positive hk hl hh hAB).1
    simpa only [ite_true,ite_false,hab.symm,hac.symm,hbc.symm,Type7.triangleCorner] using h
  edge_metric i hi j hj := by
    let C := A+(B-A)*Type7.triangleCorner (Type7.spatialEdgeSq q) positive a b c
    obtain ⟨hl,hh⟩ := spatial_triangle_regular q a b c hr
    obtain ⟨_,hAC,hBC⟩ := develop_face_on_edge _ _ _ k A B positive hk hl hh hAB
    change k*Complex.normSq (C-A) = Type7.spatialEdgeSq q a c at hAC
    change k*Complex.normSq (C-B) = Type7.spatialEdgeSq q b c at hBC
    have hBA : k*Complex.normSq (A-B) = Type7.spatialEdgeSq q b a := by
      rwa [normSq_sub_rev,spatialEdgeSq_comm]
    have hCA : k*Complex.normSq (A-C) = Type7.spatialEdgeSq q c a := by
      rwa [normSq_sub_rev,spatialEdgeSq_comm]
    have hCB : k*Complex.normSq (B-C) = Type7.spatialEdgeSq q c b := by
      rwa [normSq_sub_rev,spatialEdgeSq_comm]
    simp only [triangleVertexSet_eq,Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      simp only [ite_true,ite_false,hab.symm,hac.symm,hbc.symm] <;>
      first | assumption | simp

theorem angle_at {f : Triangle} (P : DevelopedFace q k f s) (hk : 0 < k)
    (a b c : Vertex) (ha : a ∈ triangleVertexSet f)
    (hb : b ∈ triangleVertexSet f) (hc : c ∈ triangleVertexSet f) :
    angle (Type2.euclideanPoint (q b)-Type2.euclideanPoint (q a))
      (Type2.euclideanPoint (q c)-Type2.euclideanPoint (q a)) =
    angle (P.point b-P.point a) (P.point c-P.point a) := by
  have hl (i j : Vertex) (hi : i ∈ triangleVertexSet f) (hj : j ∈ triangleVertexSet f) :
      ‖Type2.euclideanPoint (q j)-Type2.euclideanPoint (q i)‖^2 = k*‖P.point j-P.point i‖^2 := by
    rw [← spatialEdgeSq_euclidean,← Complex.normSq_eq_norm_sq]
    exact (P.edge_metric i hi j hj).symm
  apply angle_eq_of_scaled_lengths _ _ _ _ hk (hl a b ha hb) (hl a c ha hc)
  rw [sub_sub_sub_cancel_right,sub_sub_sub_cancel_right]
  exact hl b c hb hc

end DevelopedFace

end OrigamiTorus
