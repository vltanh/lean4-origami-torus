module

public import OrigamiTorus.Type2Links
public import OrigamiTorus.PlanarTriangle
public import Mathlib.Analysis.Convex.Intrinsic
import OrigamiTorus.Type2StrictSupport
import OrigamiTorus.PlanarBoundary
import OrigamiTorus.PolygonPerimeter
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! Central projection of a strictly supported Type 2 link to an affine plane. -/

public section

open Filter InnerProductGeometry Set

namespace OrigamiTorus.Type2

/-- The point on the ray from the star center through the neighbor, in the
affine section at height one above the center. -/
@[expose] noncomputable def radialPoint (q : Vertex → Point3) (n : Point3) (v w : Vertex) : Point3 :=
  (normalDot n (q w-q v))⁻¹ • (q w-q v)

private theorem smul_coordinates (c : ℝ) (p : Point3) : c • p = (c*p.1,c*p.2.1,c*p.2.2) := rfl

theorem normalDot_radialPoint (q : Vertex → Point3) (n : Point3) (v w : Vertex)
    (h : 0 < normalDot n (q w-q v)) : normalDot n (radialPoint q n v w) = 1 := by
  have he (c : ℝ) (p : Point3) : normalDot n (c • p) = c * normalDot n p := by
    simpa only [smul_eq_mul] using (normalDot_linear n).2 c p
  rw [radialPoint, he, inv_mul_cancel₀ h.ne']

/-- Central projection preserves the angular length of any link edge. -/
theorem angle_radialPoint (q : Vertex → Point3) (n : Point3) (v a b : Vertex)
    (ha : 0 < normalDot n (q a-q v)) (hb : 0 < normalDot n (q b-q v)) :
    angle (euclideanPoint (radialPoint q n v a)) (euclideanPoint (radialPoint q n v b)) =
      cornerAngle q v (a,b) := by
  rw [radialPoint, radialPoint, map_smul, map_smul,
    angle_smul_left_of_pos _ _ (inv_pos.mpr ha), angle_smul_right_of_pos _ _ (inv_pos.mpr hb)]
  rfl

private theorem determinant3_radialPoint (q : Vertex → Point3) (n : Point3) (v a b c : Vertex) :
    determinant3 (radialPoint q n v a) (radialPoint q n v b) (radialPoint q n v c) =
      (normalDot n (q a-q v))⁻¹ * (normalDot n (q b-q v))⁻¹ * (normalDot n (q c-q v))⁻¹ *
        affineBracket (q v) (q a) (q b) (q c) := by
  simp only [radialPoint, affineBracket, determinant3, smul_coordinates]
  ring

/-- Central projection preserves the strict side of the plane through the two rays. -/
theorem radialPoint_side_pos_iff (q : Vertex → Point3) (n : Point3) (v a b c : Vertex)
    (ha : 0 < normalDot n (q a-q v)) (hb : 0 < normalDot n (q b-q v))
    (hc : 0 < normalDot n (q c-q v)) :
    0 < determinant3 (radialPoint q n v a) (radialPoint q n v b) (radialPoint q n v c) ↔
      0 < affineBracket (q v) (q a) (q b) (q c) := by
  rw [determinant3_radialPoint]
  exact mul_pos_iff_of_pos_left (mul_pos (mul_pos (inv_pos.mpr ha) (inv_pos.mpr hb)) (inv_pos.mpr hc))

private theorem faceSide_eq_zero_of_mem (q : Vertex → Point3) (f : Triangle) (w : Vertex)
    (hw : w ∈ triangleVertexSet f) : faceSide q f w = 0 := by
  rcases f with ⟨a,b,c⟩
  simp only [triangleVertexSet_eq,Finset.mem_insert,Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl <;>
    simp only [faceSide,affineBracket,determinant3,sub_self,Prod.fst_zero,Prod.snd_zero] <;> ring

/-- In the absence of a mixed face at the center, every incident face plane
has all the neighboring rays in one of its two closed half-spaces. -/
theorem faceSide_one_sided_of_noMixedFace (q : Vertex → Point3) (v : Vertex)
    (h : ¬ HasMixedFace geometricFaces q v) (f : Triangle) (hf : f ∈ geometricFaces)
    (hv : v ∈ triangleVertexSet f) :
    (∀ w ∈ linkCycle v, 0 ≤ faceSide q f w) ∨ (∀ w ∈ linkCycle v, faceSide q f w ≤ 0) := by
  by_contra! he
  obtain ⟨⟨b,hb,hneg⟩,⟨a,ha,hpos⟩⟩ := he
  apply h
  have han : a ∉ triangleVertexSet f := fun ha => (ne_of_gt hpos) (faceSide_eq_zero_of_mem q f a ha)
  have hbn : b ∉ triangleVertexSet f := fun hb => (ne_of_lt hneg) (faceSide_eq_zero_of_mem q f b hb)
  exact ⟨f,⟨hf,hv⟩,a,b,⟨(mem_linkCycle_iff v a).mp ha,han,(mem_linkCycle_iff v b).mp hb,hbn⟩,hpos,hneg⟩

private theorem face_of_linkEdge (v a b : Vertex) (h : (a,b) ∈ linkEdges v) :
    a ∈ linkCycle v ∧ b ∈ linkCycle v ∧
      ∃ f ∈ geometricFaces, v ∈ triangleVertexSet f ∧
        (f = (v,a,b) ∨ f = (a,b,v) ∨ f = (b,v,a) ∨
          f = (v,b,a) ∨ f = (b,a,v) ∨ f = (a,v,b)) := by
  revert h
  fin_cases v <;> revert a b <;> decide +kernel

/-- Projection preserves the common subface of any two subfaces in the link
of an injectively realized star. -/
theorem radialHull_inter_of_embedding (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v)) (s t : Finset Vertex)
    (hs : ∀ w ∈ s, w ∈ linkCycle v) (ht : ∀ w ∈ t, w ∈ linkCycle v)
    (hsface : insert v s ∈ (triangleComplex geometricFaces).faces)
    (htface : insert v t ∈ (triangleComplex geometricFaces).faces) :
    vertexHull (radialPoint q n v) s ∩ vertexHull (radialPoint q n v) t =
      vertexHull (radialPoint q n v) (s ∩ t) := by
  apply Set.Subset.antisymm ?_ (Set.subset_inter
    (vertexHull_mono _ Finset.inter_subset_left) (vertexHull_mono _ Finset.inter_subset_right))
  rintro x ⟨hxs,hxt⟩
  obtain ⟨u,hu,hu₁,hux⟩ := weights_of_mem_vertexHull _ s hxs
  obtain ⟨w,hw,hw₁,hwx⟩ := weights_of_mem_vertexHull _ t hxt
  let depth (i : Vertex) : ℝ := normalDot n (q i-q v)
  let rayWeights (r : Finset Vertex) (c : Vertex → ℝ) (i : Vertex) : ℝ :=
    if i ∈ r then c i * (depth i)⁻¹ else 0
  let U := rayWeights s u
  let W := rayWeights t w
  have hnonneg (r : Finset Vertex) (hr : ∀ i ∈ r, i ∈ linkCycle v) (c : Vertex → ℝ)
      (hc : ∀ i ∈ r, 0 ≤ c i) (i : Vertex) : 0 ≤ rayWeights r c i := by
    unfold rayWeights
    split_ifs with hi
    · exact mul_nonneg (hc i hi) (inv_nonneg.mpr (hn i (hr i hi)).le)
    · exact le_rfl
  have hU := hnonneg s hs u hu
  have hW := hnonneg t ht w hw
  let M := ∑ i, U i
  let N := ∑ i, W i
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => hU i)
  have hN : 0 ≤ N := Finset.sum_nonneg (fun i _ => hW i)
  let c : ℝ := (1+M+N)⁻¹
  have hden : 0 < 1+M+N := by linarith
  have hc : 0 < c := inv_pos.mpr hden
  have hcM : c*M ≤ 1 := by
    rw [show c*M = M/(1+M+N) by simp [c, div_eq_inv_mul], div_le_one hden]
    linarith
  have hcN : c*N ≤ 1 := by
    rw [show c*N = N/(1+M+N) by simp [c, div_eq_inv_mul], div_le_one hden]
    linarith
  let lift (r : Finset Vertex) (f : Vertex → ℝ) (i : Vertex) : ℝ :=
    c * rayWeights r f i + (Pi.single v (1-c*(∑ j, rayWeights r f j)) : Vertex → ℝ) i
  have hweights (r : Finset Vertex) (f : Vertex → ℝ) (hr : ∀ i, 0 ≤ rayWeights r f i)
      (hm : c*(∑ i, rayWeights r f i) ≤ 1) : lift r f ∈ faceWeights (insert v r) := by
    refine ⟨fun i => ?_, ?_, fun i hi => ?_⟩
    · apply add_nonneg (mul_nonneg hc.le (hr i))
      simp only [Pi.single_apply]
      split_ifs <;> linarith
    · simp only [lift, Finset.sum_add_distrib, ← Finset.mul_sum, Pi.single_apply,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    · have hn : i ≠ v ∧ i ∉ r := by simpa only [Finset.mem_insert, not_or] using hi
      simp [lift,rayWeights,hn.1,hn.2]
  have heval (r : Finset Vertex) (f : Vertex → ℝ)
      (hr : ∑ i ∈ r, f i • radialPoint q n v i = x) :
      evaluateWeights q (lift r f) = q v + c • x := by
    have hx : (∑ i, rayWeights r f i • (q i-q v)) = x := by
      simpa only [rayWeights, ite_smul, zero_smul, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter, radialPoint, depth, mul_smul] using hr
    have hx' : (∑ i, rayWeights r f i • q i) = x + (∑ i, rayWeights r f i) • q v := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul] at hx
      exact eq_add_of_sub_eq hx
    unfold evaluateWeights
    simp only [lift, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, Pi.single_apply,
      ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [hx']
    module
  obtain ⟨_,f,hf,hsub⟩ := hsface
  obtain ⟨_,g,hg,hsub'⟩ := htface
  let a : triangleWeightSpace geometricFaces := ⟨lift s u, f,hf,
    faceWeights_mono hsub (hweights s u hU hcM)⟩
  let b : triangleWeightSpace geometricFaces := ⟨lift t w, g,hg,
    faceWeights_mono hsub' (hweights t w hW hcN)⟩
  have he : lift s u = lift t w := congrArg Subtype.val
    (h (show evaluateWeights q (lift s u) = evaluateWeights q (lift t w) from
      (heval s u hux).trans (heval t w hwx).symm) : a = b)
  have hz (i : Vertex) (hi : i ∈ s) (hit : i ∉ s ∩ t) : u i = 0 := by
    have hne : i ≠ v := ((mem_linkCycle_iff v i).mp (hs i hi)).1.symm
    have hnt : i ∉ t := fun ht' => hit (Finset.mem_inter.mpr ⟨hi,ht'⟩)
    have H := congrFun he i
    simp [lift,rayWeights,hi,hnt,hne, hc.ne', inv_ne_zero (hn i (hs i hi)).ne', depth] at H
    exact H
  have hmass : ∑ i ∈ s ∩ t, u i = 1 := by
    rw [Finset.sum_subset Finset.inter_subset_left hz, hu₁]
  rw [← hux, ← Finset.sum_subset Finset.inter_subset_left
    (by intro i hi hit; rw [hz i hi hit, zero_smul])]
  exact weighted_mem_vertexHull _ _ u (fun i hi => hu i (Finset.mem_inter.mp hi).1) hmass

private theorem linkEdge_subface (v a b : Vertex) (h : (a,b) ∈ linkEdges v) :
    insert v ({a,b} : Finset Vertex) ∈ (triangleComplex geometricFaces).faces := by
  obtain ⟨_,_,f,hf,_,he⟩ := face_of_linkEdge v a b h
  refine ⟨by simp, f,hf,?_⟩
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [triangleVertexSet_eq, Finset.insert_subset_iff]

/-- The segments of the projected vertex link meet exactly at their shared
labeled endpoints. -/
theorem radialLinkEdge_inter (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v)) (a b c d : Vertex)
    (hab : (a,b) ∈ linkEdges v) (hcd : (c,d) ∈ linkEdges v) :
    segment ℝ (radialPoint q n v a) (radialPoint q n v b) ∩
      segment ℝ (radialPoint q n v c) (radialPoint q n v d) =
        vertexHull (radialPoint q n v) ({a,b} ∩ {c,d}) := by
  obtain ⟨ha,hb,_⟩ := face_of_linkEdge v a b hab
  obtain ⟨hc,hd,_⟩ := face_of_linkEdge v c d hcd
  rw [← vertexHull_pair, ← vertexHull_pair]
  exact radialHull_inter_of_embedding q v n h hn {a,b} {c,d}
    (by simp [Finset.mem_insert,ha,hb]) (by simp [Finset.mem_insert,hc,hd])
    (linkEdge_subface v a b hab) (linkEdge_subface v c d hcd)

theorem radialPoint_injOn_linkCycle (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v)) :
    Set.InjOn (radialPoint q n v) {w | w ∈ linkCycle v} := by
  intro a ha b hb he
  change a ∈ linkCycle v at ha
  change b ∈ linkCycle v at hb
  by_contra hne
  have hr (w : Vertex) (hw : w ∈ linkCycle v) :
      insert v ({w} : Finset Vertex) ∈ (triangleComplex geometricFaces).faces := by
    obtain ⟨_,f,hf,hv,hw⟩ := (mem_linkCycle_iff v w).mp hw
    exact ⟨by simp,f,hf,by simp [Finset.insert_subset_iff,hv,hw]⟩
  have hs : ({a} : Finset Vertex) ∩ {b} = ∅ := by simp [hne]
  have hi := radialHull_inter_of_embedding q v n h hn {a} {b}
    (by simpa) (by simpa) (hr a ha) (hr b hb)
  simp only [hs,vertexHull,Finset.coe_empty,Set.image_empty,convexHull_empty] at hi
  have hm : radialPoint q n v a ∈
      convexHull ℝ (radialPoint q n v '' (↑({a} : Finset Vertex) : Set Vertex)) ∩
        convexHull ℝ (radialPoint q n v '' (↑({b} : Finset Vertex) : Set Vertex)) :=
    ⟨subset_convexHull ℝ _ ⟨a,by simp,rfl⟩,subset_convexHull ℝ _ ⟨b,by simp,he.symm⟩⟩
  rw [hi] at hm
  exact hm

private def determinantLine (a b : Point3) : Point3 →ₗ[ℝ] ℝ where
  toFun := determinant3 a b
  map_add' x y := by
    simp only [determinant3,Prod.fst_add,Prod.snd_add]
    ring
  map_smul' c x := by
    simp only [determinant3,smul_coordinates,smul_eq_mul,RingHom.id_apply]
    ring

private def normalFunctional (n : Point3) : Point3 →ₗ[ℝ] ℝ :=
  ⟨⟨normalDot n,(normalDot_linear n).1⟩,(normalDot_linear n).2⟩

private theorem determinantLine_ne_zero (n a b : Point3) (ha : normalDot n a = 1)
    (hb : normalDot n b = 1) (hne : a ≠ b) : determinantLine a b ≠ 0 := by
  intro hz
  have h₁ : a.2.1*b.2.2 - a.2.2*b.2.1 = 0 := by
    have he := congrFun (congrArg DFunLike.coe hz) ((1,0,0) : Point3)
    norm_num [determinantLine,determinant3] at he
    exact he
  have h₂ : a.1*b.2.2 - a.2.2*b.1 = 0 := by
    have he := congrFun (congrArg DFunLike.coe hz) ((0,1,0) : Point3)
    norm_num [determinantLine,determinant3] at he
    linear_combination -he
  have h₃ : a.1*b.2.1 - a.2.1*b.1 = 0 := by
    have he := congrFun (congrArg DFunLike.coe hz) ((0,0,1) : Point3)
    norm_num [determinantLine,determinant3] at he
    exact he
  simp only [normalDot] at ha hb
  apply hne
  apply Prod.ext
  · linear_combination b.1*ha-a.1*hb+n.2.1*h₃+n.2.2*h₂
  · apply Prod.ext
    · linear_combination b.2.1*ha-a.2.1*hb-n.1*h₃+n.2.2*h₁
    · linear_combination b.2.2*ha-a.2.2*hb-n.1*h₂-n.2.1*h₁

/-- The line through two different projected vertices misses at least one
projected neighbor. Otherwise the spatial star would be planar. -/
theorem radialLine_proper (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v))
    (a b : Vertex) (ha : a ∈ linkCycle v) (hb : b ∈ linkCycle v) (hab : a ≠ b) :
    ∃ w ∈ linkCycle v,
      determinant3 (radialPoint q n v a) (radialPoint q n v b) (radialPoint q n v w) ≠ 0 := by
  by_contra! hz
  let L := determinantLine (radialPoint q n v a) (radialPoint q n v b)
  have hne : L ≠ 0 := determinantLine_ne_zero n _ _ (normalDot_radialPoint q n v a (hn a ha))
    (normalDot_radialPoint q n v b (hn b hb))
    (fun h' => hab (radialPoint_injOn_linkCycle q v n h hn ha hb h'))
  have hr : 1 ≤ Module.finrank ℝ L.range := Submodule.one_le_finrank_iff.mpr
    (fun h' => hne (LinearMap.range_eq_bot.mp h'))
  have hd := L.finrank_range_add_finrank_ker
  have hdim : Module.finrank ℝ Point3 = 3 := by simp [Point3, Module.finrank_prod]
  rw [hdim] at hd
  have hdimK : Module.finrank ℝ L.ker ≤ 2 := by omega
  apply not_planar_of_embedding q h v (L.ker.map euclideanPoint)
    ((Submodule.finrank_map_le _ _).trans hdimK)
  intro w hw
  refine ⟨q w-q v,LinearMap.mem_ker.mpr ?_,rfl⟩
  have hzero : L (radialPoint q n v w) = 0 := hz w hw
  rw [radialPoint, map_smul, smul_eq_mul, mul_eq_zero] at hzero
  exact hzero.resolve_left (inv_ne_zero (hn w hw).ne')

private theorem bracket_rotate (a b c d : Point3) : affineBracket b c a d = affineBracket a b c d := by
  simp only [affineBracket,determinant3,Prod.fst_sub,Prod.snd_sub]
  ring

private theorem bracket_reverse (a b c d : Point3) : affineBracket a c b d = -affineBracket a b c d := by
  simp only [affineBracket,determinant3]
  ring

/-- In the absence of a mixed face, each projected link edge has a common
weak side sign for all projected neighbors. -/
theorem radialEdge_one_sided_of_noMixedFace (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v))
    (hm : ¬ HasMixedFace geometricFaces q v) (a b : Vertex) (hab : (a,b) ∈ linkEdges v) :
    let d (w : Vertex) := determinant3 (radialPoint q n v a) (radialPoint q n v b) (radialPoint q n v w)
    (∀ w ∈ linkCycle v, 0 ≤ d w) ∨ (∀ w ∈ linkCycle v, d w ≤ 0) := by
  obtain ⟨ha,hb,f,hf,hvf,hord⟩ := face_of_linkEdge v a b hab
  let raw (w : Vertex) := affineBracket (q v) (q a) (q b) (q w)
  have hs : (∀ w, faceSide q f w = raw w) ∨ (∀ w, faceSide q f w = -raw w) := by
    rcases hord with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl fun _ => rfl
    · exact Or.inl fun _ => bracket_rotate _ _ _ _
    · exact Or.inl fun _ => (bracket_rotate _ _ _ _).trans (bracket_rotate _ _ _ _)
    · exact Or.inr fun _ => bracket_reverse _ _ _ _
    · exact Or.inr fun _ => (bracket_rotate _ _ _ _).trans (bracket_reverse _ _ _ _)
    · exact Or.inr fun _ => (bracket_rotate _ _ _ _).trans
        ((bracket_rotate _ _ _ _).trans (bracket_reverse _ _ _ _))
  have hraw : (∀ w ∈ linkCycle v, 0 ≤ raw w) ∨ (∀ w ∈ linkCycle v, raw w ≤ 0) := by
    have he := faceSide_one_sided_of_noMixedFace q v hm f hf hvf
    rcases hs with hs | hs <;> simp_rw [hs] at he
    · exact he
    · simpa only [neg_nonneg, neg_nonpos, or_comm] using he
  have hp (w : Vertex) (hw : w ∈ linkCycle v) :
      0 ≤ (normalDot n (q a-q v))⁻¹ * (normalDot n (q b-q v))⁻¹ * (normalDot n (q w-q v))⁻¹ :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (hn a ha).le) (inv_nonneg.mpr (hn b hb).le))
      (inv_nonneg.mpr (hn w hw).le)
  rcases hraw with hpos | hneg
  · left
    intro w hw
    simp only [determinant3_radialPoint]
    exact mul_nonneg (hp w hw) (hpos w hw)
  · right
    intro w hw
    simp only [determinant3_radialPoint]
    exact mul_nonpos_of_nonneg_of_nonpos (hp w hw) (hneg w hw)

private theorem mem_frontier_of_proper_support {K : Set Point3} (L : Point3 →ₗ[ℝ] ℝ)
    (hn : ∀ y ∈ K, 0 ≤ L y) {x y : Point3} (hx : x ∈ K) (hzero : L x = 0)
    (hy : y ∈ K) (hpos : 0 < L y) : x ∈ intrinsicFrontier ℝ K := by
  rw [← closure_sdiff_intrinsicInterior]
  refine ⟨subset_closure hx,?_⟩
  rintro ⟨x',hx',rfl⟩
  let _ : Nonempty (affineSpan ℝ K) := ⟨x'⟩
  let y' : affineSpan ℝ K := ⟨y,subset_affineSpan ℝ K hy⟩
  let g : ℝ →ᵃ[ℝ] (affineSpan ℝ K) := AffineMap.lineMap y' x'
  have hg : Continuous g := AffineMap.lineMap_continuous
  have h1 : g 1 = x' := AffineMap.lineMap_apply_one y' x'
  obtain ⟨t,ht,htK⟩ :=
    (hg.tendsto' _ _ h1).eventually_mem
      (mem_interior_iff_mem_nhds.mp hx') |>.exists_gt
  have he := hn _ htK
  change 0 ≤ L ((AffineMap.lineMap y' x' t : affineSpan ℝ K) : Point3) at he
  rw [AffineMap.lineMap_apply] at he
  change 0 ≤ L (t • ((x' : Point3)-y) + y) at he
  rw [map_add,map_smul,map_sub,hzero,smul_eq_mul,zero_sub] at he
  nlinarith [mul_pos (sub_pos.mpr ht) hpos]

/-- If there is no mixed face, the line of every projected link edge is a
proper supporting line of the projected convex hull. -/
private theorem radialEdge_support_of_noMixedFace (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v))
    (hm : ¬ HasMixedFace geometricFaces q v) (a b : Vertex) (hab : (a,b) ∈ linkEdges v) :
    let p := radialPoint q n v
    let K := vertexHull p (linkCycle v).toFinset
    ∃ L : Point3 →ₗ[ℝ] ℝ,
      (∀ y ∈ K, 0 ≤ L y) ∧ (∃ y ∈ K, 0 < L y) ∧ ∀ y ∈ segment ℝ (p a) (p b), L y = 0 := by
  let p := radialPoint q n v
  let D := determinantLine (p a) (p b)
  obtain ⟨ha,hb,_⟩ := face_of_linkEdge v a b hab
  have hne : a ≠ b := by
    have he : ∀ v a : Vertex, (a,a) ∉ linkEdges v := by decide +kernel
    intro heq
    subst b
    exact he v a hab
  obtain ⟨w,hw,hwne⟩ := radialLine_proper q v n h hn a b ha hb hne
  have hzA : D (p a) = 0 := by change determinant3 (p a) (p b) (p a) = 0; unfold determinant3; ring
  have hzB : D (p b) = 0 := by change determinant3 (p a) (p b) (p b) = 0; unfold determinant3; ring
  obtain ⟨L,hside,hLw,hLa,hLb⟩ : ∃ L : Point3 →ₗ[ℝ] ℝ,
      (∀ i ∈ linkCycle v, 0 ≤ L (p i)) ∧ 0 < L (p w) ∧ L (p a) = 0 ∧ L (p b) = 0 := by
    rcases radialEdge_one_sided_of_noMixedFace q v n hn hm a b hab with hpos | hneg
    · exact ⟨D,hpos,lt_of_le_of_ne (hpos w hw) hwne.symm,hzA,hzB⟩
    · exact ⟨-D,fun i hi => neg_nonneg.mpr (hneg i hi),neg_pos.mpr (lt_of_le_of_ne (hneg w hw) hwne),
        by simp [hzA],by simp [hzB]⟩
  let K := vertexHull p (linkCycle v).toFinset
  have hnK : ∀ y ∈ K, 0 ≤ L y := by
    apply convexHull_min ?_ (convex_halfSpace_ge L.isLinear 0)
    rintro _ ⟨i,hi,rfl⟩
    exact hside i (List.mem_toFinset.mp hi)
  have hwK : p w ∈ K := subset_convexHull ℝ _ ⟨w,List.mem_toFinset.mpr hw,rfl⟩
  refine ⟨L,hnK,⟨p w,hwK,hLw⟩,?_⟩
  rintro _ ⟨s,t,_,_,_,rfl⟩
  change L (s • p a + t • p b) = 0
  simp [hLa,hLb]

/-- Every projected link segment lies in the intrinsic boundary of the
projected convex hull if the star has no mixed face. -/
theorem radialEdge_subset_frontier_of_noMixedFace (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v))
    (hm : ¬ HasMixedFace geometricFaces q v) (a b : Vertex) (hab : (a,b) ∈ linkEdges v) :
    segment ℝ (radialPoint q n v a) (radialPoint q n v b) ⊆
      intrinsicFrontier ℝ (vertexHull (radialPoint q n v) (linkCycle v).toFinset) := by
  let p := radialPoint q n v
  let K := vertexHull p (linkCycle v).toFinset
  obtain ⟨ha,hb,_⟩ := face_of_linkEdge v a b hab
  have hsegK : segment ℝ (p a) (p b) ⊆ K := segment_subset_convexHull
    ⟨a,List.mem_toFinset.mpr ha,rfl⟩ ⟨b,List.mem_toFinset.mpr hb,rfl⟩
  obtain ⟨L,hnK,⟨w,hwK,hLw⟩,hzero⟩ := radialEdge_support_of_noMixedFace q v n h hn hm a b hab
  intro x hx
  exact mem_frontier_of_proper_support L hnK (hsegK hx) (hzero x hx) hwK hLw

private theorem link_has_two_incident_edges (v i : Vertex) (hi : i ∈ linkCycle v) :
    ∃ a b : Vertex, a ≠ i ∧ i ≠ b ∧ a ≠ b ∧ (a,i) ∈ linkEdges v ∧ (i,b) ∈ linkEdges v := by
  revert hi
  fin_cases v <;> revert i <;> decide +kernel

/-- No subset of space containing the projected link admits a continuous
injection into the real line. At a vertex of maximal image, the images of
its two incident segments would overlap beyond the vertex. -/
theorem no_continuous_injection_on_radialLink (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v)) {X : Set Point3}
    (hX : ∀ a b : Vertex, (a,b) ∈ linkEdges v → segment ℝ (radialPoint q n v a) (radialPoint q n v b) ⊆ X)
    (f : Point3 → ℝ) (hf : ContinuousOn f X) (hfi : Set.InjOn f X) : False := by
  let p := radialPoint q n v
  have hx (i : Vertex) (hi : i ∈ linkCycle v) : p i ∈ X := by
    obtain ⟨a,b,_,_,_,hai,_⟩ := link_has_two_incident_edges v i hi
    exact hX a i hai (right_mem_segment ℝ _ _)
  have H : ∀ v : Vertex, (linkCycle v).toFinset.Nonempty := by decide +kernel
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image (linkCycle v).toFinset (f ∘ p) (H v)
  obtain ⟨a,b,hai,hib,hab,hl,hr⟩ := link_has_two_incident_edges v i (List.mem_toFinset.mp hi)
  let L := segment ℝ (p a) (p i)
  let R := segment ℝ (p i) (p b)
  have hLX : L ⊆ X := hX a i hl
  have hRX : R ⊆ X := hX i b hr
  have hpair : ({a,i} : Finset Vertex) ∩ {i,b} = {i} := by
    ext j
    simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    grind
  have hinter : L ∩ R = {p i} := by
    change segment ℝ (p a) (p i) ∩ segment ℝ (p i) (p b) = _
    rw [radialLinkEdge_inter q v n h hn a i i b hl hr,hpair]
    simp [vertexHull,p]
  obtain ⟨ha,hi',_⟩ := face_of_linkEdge v a i hl
  obtain ⟨_,hb,_⟩ := face_of_linkEdge v i b hr
  have ha_le : f (p a) ≤ f (p i) := hmax a (List.mem_toFinset.mpr ha)
  have hb_le : f (p b) ≤ f (p i) := hmax b (List.mem_toFinset.mpr hb)
  have hbetween {S : Set Point3} (hS : S ⊆ X) (hc : Convex ℝ S) {x y z : Point3}
      (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ X) (h1 : f x ≤ f z) (h2 : f z ≤ f y) : z ∈ S := by
    have hc' := hc.isPreconnected.image f (hf.mono hS)
    obtain ⟨w,hw,hwz⟩ := hc'.Icc_subset ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩ ⟨h1,h2⟩
    exact hfi (hS hw) hz hwz ▸ hw
  rcases le_total (f (p a)) (f (p b)) with he | he
  · have hL : p b ∈ L := hbetween hLX (convex_segment _ _) (left_mem_segment ℝ _ _)
      (right_mem_segment ℝ _ _) (hx b hb) he hb_le
    have hbI : p b ∈ L ∩ R := ⟨hL,right_mem_segment ℝ _ _⟩
    rw [hinter] at hbI
    exact hib (radialPoint_injOn_linkCycle q v n h hn hb hi' hbI).symm
  · have hR : p a ∈ R := hbetween hRX (convex_segment _ _) (right_mem_segment ℝ _ _)
      (left_mem_segment ℝ _ _) (hx a ha) he ha_le
    have haI : p a ∈ L ∩ R := ⟨left_mem_segment ℝ _ _,hR⟩
    rw [hinter] at haI
    exact hai (radialPoint_injOn_linkCycle q v n h hn ha hi' haI)

private theorem radialHull_affine_dimension (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v)) :
    Module.finrank ℝ (affineSpan ℝ (vertexHull (radialPoint q n v) (linkCycle v).toFinset)).direction = 2 := by
  let p := radialPoint q n v
  let K := vertexHull p (linkCycle v).toFinset
  have hex : ∀ v : Vertex, ∃ a b : Vertex, a ≠ b ∧ (a,b) ∈ linkEdges v := by decide +kernel
  obtain ⟨a,b,hab,hE⟩ := hex v
  obtain ⟨ha,hb,_⟩ := face_of_linkEdge v a b hE
  obtain ⟨c,hc,hdet⟩ := radialLine_proper q v n h hn a b ha hb hab
  have hmem (i : Vertex) (hi : i ∈ linkCycle v) : p i ∈ K :=
    subset_convexHull ℝ _ ⟨i,List.mem_toFinset.mpr hi,rfl⟩
  let L := normalFunctional n
  have hnorm : ∀ x ∈ K, L x = 1 := by
    apply convexHull_min ?_ (convex_hyperplane L.isLinear 1)
    rintro _ ⟨i,hi,rfl⟩
    exact normalDot_radialPoint q n v i (hn i (List.mem_toFinset.mp hi))
  have hL : L ≠ 0 := by
    intro he
    have ho := hnorm (p a) (hmem a ha)
    simp [he] at ho
  have hr : 1 ≤ Module.finrank ℝ L.range := Submodule.one_le_finrank_iff.mpr
    (fun he => hL (LinearMap.range_eq_bot.mp he))
  have hk := L.finrank_range_add_finrank_ker
  have hdim : Module.finrank ℝ Point3 = 3 := by simp [Point3, Module.finrank_prod]
  rw [hdim] at hk
  have hk₂ : Module.finrank ℝ L.ker ≤ 2 := by omega
  have hdir : (affineSpan ℝ K).direction ≤ L.ker := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ (hmem a ha), Submodule.span_le]
    rintro _ ⟨y,hy,rfl⟩
    change L (y-p a) = 0
    rw [map_sub, hnorm y hy, hnorm _ (hmem a ha), sub_self]
  have hup : Module.finrank ℝ (affineSpan ℝ K).direction ≤ 2 :=
    (Submodule.finrank_mono hdir).trans hk₂
  have h4 : AffineIndependent ℝ (![0,p a,p b,p c] : Fin 4 → Point3) :=
    affineIndependent_of_bracket_ne_zero _ _ _ _ (by simpa [affineBracket,p] using hdet)
  let e : Fin 3 ↪ Fin 4 := ⟨Fin.succ,Fin.succ_injective _⟩
  have hj : (![0,p a,p b,p c] : Fin 4 → Point3) ∘ e = ![p a,p b,p c] := by
    funext i
    fin_cases i <;> rfl
  have h3 := h4.comp_embedding e
  rw [hj] at h3
  have hsub : Set.range (![p a,p b,p c] : Fin 3 → Point3) ⊆ K := by
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact hmem a ha
    · exact hmem b hb
    · exact hmem c hc
  have hlower := h3.card_le_finrank_succ
  rw [Fintype.card_fin] at hlower
  have hm := Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  change Module.finrank ℝ (affineSpan ℝ K).direction = 2
  apply le_antisymm hup
  rw [direction_affineSpan]
  exact (by omega : 2 ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range ![p a,p b,p c]))).trans hm

/-- A projected link has an enclosing triangle whose angular perimeter is
strictly below one great circle. -/
theorem radialHull_enclosing_triangle (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v)) :
    let K := vertexHull (radialPoint q n v) (linkCycle v).toFinset
    ∃ a b c : Point3, a ∈ affineSpan ℝ K ∧ b ∈ affineSpan ℝ K ∧ c ∈ affineSpan ℝ K ∧
      normalDot n a = 1 ∧ normalDot n b = 1 ∧ normalDot n c = 1 ∧
      K ⊆ convexHull ℝ {a,b,c} ∧
        angle (euclideanPoint a) (euclideanPoint b) + angle (euclideanPoint b) (euclideanPoint c) +
          angle (euclideanPoint c) (euclideanPoint a) < 2 * Real.pi := by
  let p := radialPoint q n v
  let K := vertexHull p (linkCycle v).toFinset
  have hc : IsCompact K := ((linkCycle v).toFinset.finite_toSet.image p).isCompact_convexHull ℝ
  have H : ∀ v : Vertex, (linkCycle v).toFinset.Nonempty := by decide +kernel
  obtain ⟨i,hi⟩ := H v
  have hiK : p i ∈ K := subset_convexHull ℝ _ ⟨i,hi,rfl⟩
  obtain ⟨a,b,c,ha,hb,hc',htri⟩ := exists_enclosing_triangle hc ⟨p i,hiK⟩
    (radialHull_affine_dimension q v n h hn)
  let N := normalFunctional n
  have hnorm : ∀ x ∈ K, N x = 1 := by
    apply convexHull_min ?_ (convex_hyperplane N.isLinear 1)
    rintro _ ⟨j,hj,rfl⟩
    exact normalDot_radialPoint q n v j (hn j (List.mem_toFinset.mp hj))
  have hplane : affineSpan ℝ K ≤ AffineSubspace.mk' (p i) N.ker := by
    rw [affineSpan_le]
    intro x hx
    change x ∈ AffineSubspace.mk' (p i) N.ker
    apply AffineSubspace.mem_mk'.mpr
    exact LinearMap.mem_ker.mpr (by change N (x-p i) = 0; rw [map_sub,hnorm x hx,hnorm _ hiK,sub_self])
  have hN (x : Point3) (hx : x ∈ affineSpan ℝ K) : normalDot n x = 1 := by
    have hp := LinearMap.mem_ker.mp (AffineSubspace.mem_mk'.mp (hplane hx))
    change N (x-p i) = 0 at hp
    rw [map_sub,hnorm _ hiK,sub_eq_zero] at hp
    exact hp
  have hdim : Module.finrank ℝ Point3 = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp [Point3,Module.finrank_prod]
  let e := LinearEquiv.ofInjectiveOfFinrankEq euclideanPoint euclideanPoint_injective hdim
  let l := N.comp e.symm.toLinearMap
  have hl (x : Point3) : l (euclideanPoint x) = normalDot n x := by
    change N (e.symm (e x)) = N x
    rw [e.symm_apply_apply]
  exact ⟨a,b,c,ha,hb,hc',hN a ha,hN b hb,hN c hc',htri,
    triangle_perimeter_lt_two_pi l _ _ _ (by rw [hl,hN a ha]; norm_num)
      (by rw [hl,hN b hb]; norm_num) (by rw [hl,hN c hc']; norm_num)⟩

/-- If no face at the vertex has neighbors on opposite strict sides, the
projected link is the entire relative boundary of its convex hull. -/
theorem radialLink_eq_frontier_of_noMixedFace (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v)) (hm : ¬ HasMixedFace geometricFaces q v) :
    (⋃ e ∈ linkEdges v, segment ℝ (radialPoint q n v e.1) (radialPoint q n v e.2)) =
      intrinsicFrontier ℝ (vertexHull (radialPoint q n v) (linkCycle v).toFinset) := by
  let p := radialPoint q n v
  let K := vertexHull p (linkCycle v).toFinset
  let B := ⋃ e ∈ linkEdges v, segment ℝ (p e.1) (p e.2)
  have hsub (a b : Vertex) (hab : (a,b) ∈ linkEdges v) : segment ℝ (p a) (p b) ⊆ B :=
    fun x hx => Set.mem_iUnion.mpr ⟨(a,b),Set.mem_iUnion.mpr ⟨hab,hx⟩⟩
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨⟨a,b⟩,hab,hx'⟩ := Set.mem_iUnion₂.mp hx
    exact radialEdge_subset_frontier_of_noMixedFace q v n h hn hm a b hab hx'
  · intro x hx
    by_contra hnot
    have hc : IsCompact K := ((linkCycle v).toFinset.finite_toSet.image p).isCompact_convexHull ℝ
    obtain ⟨f,hf,hfi⟩ := exists_injOn_punctured_intrinsicFrontier hc (convex_convexHull ℝ _)
      (radialHull_affine_dimension q v n h hn) hx
    apply no_continuous_injection_on_radialLink q v n h hn (X := intrinsicFrontier ℝ K \ {x}) _ f hf hfi
    intro a b hab y hy
    exact ⟨radialEdge_subset_frontier_of_noMixedFace q v n h hn hm a b hab hy,
      fun he => hnot ((Set.mem_singleton_iff.mp he) ▸ hsub a b hab hy)⟩

private theorem exists_frontier_between {K : Set Point3} (hK : IsClosed K) {y x : Point3}
    (hy : y ∈ intrinsicInterior ℝ K) (hxA : x ∈ affineSpan ℝ K) (hx : x ∉ K) :
    ∃ t ∈ Set.Ico (0 : ℝ) 1, ((1-t) • y + t • x) ∈ intrinsicFrontier ℝ K := by
  obtain ⟨yA,hyA,rfl⟩ := mem_intrinsicInterior.mp hy
  let A := affineSpan ℝ K
  let _ : Nonempty A := ⟨yA⟩
  let xA : A := ⟨x,hxA⟩
  let T : Set A := Subtype.val ⁻¹' K
  let g : ℝ →ᵃ[ℝ] A := AffineMap.lineMap yA xA
  have hg : Continuous g := AffineMap.lineMap_continuous
  let D := Set.Icc (0 : ℝ) 1 ∩ g ⁻¹' T
  have hDc : IsCompact D := isCompact_Icc.inter_right ((hK.preimage continuous_subtype_val).preimage hg)
  have h0 : (0 : ℝ) ∈ D := ⟨⟨le_rfl,zero_le_one⟩,by
    change g 0 ∈ T
    rw [show g 0 = yA from AffineMap.lineMap_apply_zero yA xA]
    exact interior_subset hyA⟩
  obtain ⟨t,ht,hmax⟩ := hDc.exists_isMaxOn ⟨0,h0⟩ continuousOn_id
  have ht₁ : t < 1 := by
    refine lt_of_le_of_ne ht.1.2 (fun he => hx ?_)
    have htT : g t ∈ T := ht.2
    rw [he,show g 1 = xA from AffineMap.lineMap_apply_one yA xA] at htT
    exact htT
  have htT : g t ∈ T := ht.2
  have hF : g t ∈ frontier T := (mem_frontier_iff_notMem_interior htT).mpr (by
    intro hI
    have hnear : ∀ᶠ s in nhds t, g s ∈ T :=
      hg.continuousAt.preimage_mem_nhds (mem_interior_iff_mem_nhds.mp hI)
    have hlt : ∀ᶠ s in nhds t, s < 1 := isOpen_Iio.mem_nhds ht₁
    obtain ⟨s,hs,hst,hs₁⟩ := (hnear.and hlt).exists_gt
    exact (not_lt_of_ge (hmax (show s ∈ D from ⟨⟨ht.1.1.trans hs.le,hs₁.le⟩,hst⟩))) hs)
  refine ⟨t,⟨ht.1.1,ht₁⟩,mem_intrinsicFrontier.mpr ⟨g t,hF,?_⟩⟩
  change ((AffineMap.lineMap yA xA t : A) : Point3) = (1-t) • (yA : Point3) + t • x
  rw [AffineMap.lineMap_apply]
  change t • ((x : Point3) - (yA : Point3)) + (yA : Point3) = _
  module

/-- In the absence of a mixed face, the projected convex hull is cut out in
its affine plane by the finitely many supporting half-planes of its edges. -/
theorem radialHull_eq_inter_halfSpaces_of_noMixedFace (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v)) (hm : ¬ HasMixedFace geometricFaces q v) :
    let p := radialPoint q n v
    let K := vertexHull p (linkCycle v).toFinset
    ∃ L : {e : Edge // e ∈ linkEdges v} → (Point3 →ₗ[ℝ] ℝ),
      (∀ e, ∀ y ∈ segment ℝ (p e.val.1) (p e.val.2), L e y = 0) ∧
        (∀ e, ∃ y ∈ K, 0 < L e y) ∧
        K = (affineSpan ℝ K : Set Point3) ∩ ⋂ e, {x | 0 ≤ L e x} := by
  let p := radialPoint q n v
  let K := vertexHull p (linkCycle v).toFinset
  have hdata (e : {e : Edge // e ∈ linkEdges v}) :
      ∃ L : Point3 →ₗ[ℝ] ℝ, (∀ y ∈ K, 0 ≤ L y) ∧ (∃ y ∈ K, 0 < L y) ∧
        ∀ y ∈ segment ℝ (p e.val.1) (p e.val.2), L y = 0 :=
    radialEdge_support_of_noMixedFace q v n h hn hm e.val.1 e.val.2 e.property
  choose L hL hpos hzero using hdata
  refine ⟨L,hzero,hpos,Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨subset_affineSpan ℝ K hx,Set.mem_iInter.mpr (fun e => hL e x hx)⟩
  · rintro x ⟨hxA,hx⟩
    by_contra hbad
    have hc : IsCompact K := ((linkCycle v).toFinset.finite_toSet.image p).isCompact_convexHull ℝ
    have hnK : K.Nonempty := by
      have H : ∀ v : Vertex, (linkCycle v).toFinset.Nonempty := by decide +kernel
      obtain ⟨a,ha⟩ := H v
      exact ⟨p a,subset_convexHull ℝ _ ⟨a,ha,rfl⟩⟩
    obtain ⟨y,hy⟩ := hnK.intrinsicInterior (convex_convexHull ℝ _)
    obtain ⟨t,ht,hF⟩ := exists_frontier_between hc.isClosed hy hxA hbad
    rw [← radialLink_eq_frontier_of_noMixedFace q v n h hn hm] at hF
    obtain ⟨e,he,hseg⟩ := Set.mem_iUnion₂.mp hF
    let E : {e : Edge // e ∈ linkEdges v} := ⟨e,he⟩
    have hLy : 0 < L E y := by
      obtain ⟨z,hz,hzPos⟩ := hpos E
      refine lt_of_le_of_ne (hL E y (intrinsicInterior_subset hy)) (fun he => ?_)
      have hF' := mem_frontier_of_proper_support (L E) (hL E) (intrinsicInterior_subset hy) he.symm hz hzPos
      rw [← closure_sdiff_intrinsicInterior] at hF'
      exact hF'.2 hy
    have hz := hzero E _ hseg
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hz
    have hx' : 0 ≤ L E x := Set.mem_iInter.mp hx E
    nlinarith [mul_pos (sub_pos.mpr ht.2) hLy, mul_nonneg ht.1 hx']

/-- Clipping an enclosing triangle by the projected link's supporting
half-planes gives a boundary cycle with angular perimeter less than a full turn. -/
theorem radialHull_exists_short_boundary_of_noMixedFace (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v)) (hm : ¬ HasMixedFace geometricFaces q v) :
    let K := vertexHull (radialPoint q n v) (linkCycle v).toFinset
    ∃ ys : List Point3, SimplePolygon ys ∧ intrinsicFrontier ℝ K = segmentCycle ys ∧
      angularCycleLength (ys.map euclideanPoint) < 2 * Real.pi := by
  let K := vertexHull (radialPoint q n v) (linkCycle v).toFinset
  obtain ⟨a,b,c,ha,hb,hc,hNa,hNb,hNc,hTK,hP⟩ := radialHull_enclosing_triangle q v n h hn
  let T := convexHull ℝ ({a,b,c} : Set Point3)
  have hTA : T ⊆ (affineSpan ℝ K : Set Point3) := by
    apply convexHull_min ?_ (affineSpan ℝ K).convex
    intro x hx
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hspan : affineSpan ℝ T = affineSpan ℝ K :=
    le_antisymm (affineSpan_le.mpr hTA) (affineSpan_mono ℝ hTK)
  have hd := radialHull_affine_dimension q v n h hn
  have hdT : Module.finrank ℝ (affineSpan ℝ T).direction = 2 := hspan.symm ▸ hd
  have hi : AffineIndependent ℝ (![a,b,c] : Fin 3 → Point3) := by
    apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ _ (show Fintype.card (Fin 3) = 2 + 1 by decide)).mpr
    have he : range (![a,b,c] : Fin 3 → Point3) = {a,b,c} := by
      ext x
      simp [Matrix.range_cons]
      tauto
    rw [he,← direction_affineSpan,← affineSpan_convexHull]
    exact hdT
  have hcT : IsCompact T := (((finite_singleton c).insert b).insert a).isCompact_convexHull ℝ
  have hnT : ∀ x ∈ T, euclideanPoint x ≠ 0 := by
    have hz : T ⊆ {x | normalFunctional n x = 1} := by
      apply convexHull_min ?_ (convex_hyperplane (normalFunctional n).isLinear 1)
      intro x hx
      simp only [mem_insert_iff,mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    intro x hx he
    have hzero : x = 0 := euclideanPoint_injective ((map_zero euclideanPoint).symm ▸ he)
    have hz' : normalFunctional n x = 1 := hz hx
    simp [hzero] at hz'
  obtain ⟨L,_,hpos,hK⟩ := radialHull_eq_inter_halfSpaces_of_noMixedFace q v n h hn hm
  change K = (affineSpan ℝ K : Set Point3) ∩ ⋂ e, {x | 0 ≤ L e x} at hK
  let cuts := (linkEdges v).attach.map L
  have hkeep : ∀ M ∈ cuts, ∀ x ∈ K, 0 ≤ M x := by
    intro M hM x hx
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hM
    have hx' : x ∈ (affineSpan ℝ K : Set Point3) ∩ ⋂ e, {x | 0 ≤ L e x} := by
      rwa [← hK]
    exact Set.mem_iInter.mp hx'.2 e
  have hp : ∀ M ∈ cuts, ∃ x ∈ K, 0 < M x := by
    intro M hM
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp hM
    exact hpos e
  have he : T ∩ ⋂ M ∈ cuts, {x | 0 ≤ M x} = K := by
    apply Set.Subset.antisymm ?_ ?_
    · intro x hx
      rw [hK]
      refine ⟨hTA hx.1,mem_iInter.mpr (fun e => ?_)⟩
      have hMe : L e ∈ cuts := List.mem_map.mpr ⟨e,List.mem_attach _ _,rfl⟩
      exact mem_iInter.mp (mem_iInter.mp hx.2 (L e)) hMe
    · intro x hx
      exact ⟨hTK hx,mem_iInter.mpr (fun M => mem_iInter.mpr (fun hM => hkeep M hM x hx))⟩
  obtain ⟨_,ys,hys,hF,hY⟩ := polygonCut_list hcT (convex_convexHull ℝ _) hdT [a,b,c]
    (intrinsicFrontier_triangle a b c hi) (simplePolygon_triangle a b c hi) cuts hTK hkeep hp
    euclideanPoint hnT
  have hF' : intrinsicFrontier ℝ K = segmentCycle ys := by
    rw [← he]
    exact hF
  refine ⟨ys,hys,hF',hY.trans_lt ?_⟩
  simpa only [List.map_cons,List.map_nil,angularCycleLength,angularPathLength,add_assoc] using hP

private theorem polygonCycleEdges_radialLink (q : Vertex → Point3) (v : Vertex) (n : Point3) :
    polygonCycleEdges ((linkCycle v).map (radialPoint q n v)) =
      (linkEdges v).map (fun e => (radialPoint q n v e.1,radialPoint q n v e.2)) := by
  rw [polygonCycleEdges_eq_zip]
  simp only [← List.map_drop,← List.map_take,← List.map_append,List.zip_map]
  rfl

private theorem radialLink_segmentCycle (q : Vertex → Point3) (v : Vertex) (n : Point3) :
    segmentCycle ((linkCycle v).map (radialPoint q n v)) =
      ⋃ e ∈ linkEdges v, segment ℝ (radialPoint q n v e.1) (radialPoint q n v e.2) := by
  rw [segmentCycle_eq_iUnion_edges,polygonCycleEdges_radialLink]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨e,he,hx⟩
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp he
    exact ⟨g,hg,hx⟩
  · rintro ⟨g,hg,hx⟩
    exact ⟨_,List.mem_map.mpr ⟨g,hg,rfl⟩,hx⟩

private theorem radialLink_simplePolygon (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q))
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v)) :
    SimplePolygon ((linkCycle v).map (radialPoint q n v)) := by
  let p := radialPoint q n v
  have hInj := radialPoint_injOn_linkCycle q v n h hn
  have hne : ∀ v a : Vertex, (a,a) ∉ linkEdges v := by decide +kernel
  have hrev : ∀ v a b : Vertex, (a,b) ∈ linkEdges v → (b,a) ∉ linkEdges v := by decide +kernel
  have hneL {a b : Vertex} (he : (a,b) ∈ linkEdges v) : a ≠ b :=
    fun hab => hne v a (hab ▸ he)
  have hneP {a b : Vertex} (he : (a,b) ∈ linkEdges v) : p a ≠ p b := by
    obtain ⟨ha,hb,_⟩ := face_of_linkEdge v a b he
    exact fun hab => hneL he (hInj ha hb hab)
  have hsingleton (x : Vertex) (hx : x ∈ linkCycle v) :
      insert v ({x} : Finset Vertex) ∈ (triangleComplex geometricFaces).faces := by
    obtain ⟨_,f,hf,hv,hw⟩ := (mem_linkCycle_iff v x).mp hx
    exact ⟨by simp,f,hf,by simp [Finset.insert_subset_iff,hv,hw]⟩
  refine ⟨(linkCycle_checked v).1.map_on (fun a ha b hb hp => hInj ha hb hp),?_,?_⟩
  · intro e he x hx
    rw [polygonCycleEdges_radialLink] at he
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := List.mem_map.mp he
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hx
    by_cases hca : c = a
    · subst c
      exact fun hx => hneP hab (left_mem_openSegment_iff.mp hx)
    by_cases hcb : c = b
    · subst c
      exact fun hx => hneP hab (right_mem_openSegment_iff.mp hx)
    intro hx
    obtain ⟨ha,hb,_⟩ := face_of_linkEdge v a b hab
    have hI := radialHull_inter_of_embedding q v n h hn {a,b} {c}
      (by simp [ha,hb]) (by simp [hc]) (linkEdge_subface v a b hab) (hsingleton c hc)
    have hEmpty : ({a,b} : Finset Vertex) ∩ {c} = ∅ := by
      ext x
      simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty]
      grind
    have hxI : p c ∈ vertexHull p {a,b} ∩ vertexHull p {c} :=
      ⟨vertexHull_pair p a b ▸ openSegment_subset_segment ℝ _ _ hx,
        subset_convexHull ℝ _ ⟨c,by simp,rfl⟩⟩
    change vertexHull p {a,b} ∩ vertexHull p {c} = vertexHull p ({a,b} ∩ {c}) at hI
    rw [hI,hEmpty] at hxI
    simp [vertexHull] at hxI
  · intro e he g hg hne'
    rw [polygonCycleEdges_radialLink] at he hg
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := List.mem_map.mp he
    obtain ⟨⟨c,d⟩,hcd,rfl⟩ := List.mem_map.mp hg
    have hPair : ¬ (a ∈ ({c,d} : Finset Vertex) ∧ b ∈ ({c,d} : Finset Vertex)) := by
      rintro ⟨ha,hb⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact hneL hab rfl
      · exact hne' rfl
      · exact hrev v _ _ hab hcd
      · exact hneL hab rfl
    have hI := radialLinkEdge_inter q v n h hn a b c d hab hcd
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hxI : x ∈ vertexHull p ({a,b} ∩ {c,d}) := hI ▸
      (show x ∈ segment ℝ (p a) (p b) ∩ segment ℝ (p c) (p d) from
        ⟨openSegment_subset_segment ℝ _ _ hx,openSegment_subset_segment ℝ _ _ hy⟩)
    have hSame (j : Vertex) (hj : ({a,b} : Finset Vertex) ∩ {c,d} ⊆ {j}) : x = p j := by
      have hx' := vertexHull_mono p hj hxI
      simpa [vertexHull] using hx'
    by_cases ha' : a ∈ ({c,d} : Finset Vertex)
    · have hb' : b ∉ ({c,d} : Finset Vertex) := fun hh => hPair ⟨ha',hh⟩
      have he := hSame a (by
        intro j hj
        simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
        exact hj.1.resolve_right (fun hjb => hb' (hjb ▸
          (show j ∈ ({c,d} : Finset Vertex) from by simpa using hj.2))))
      exact hneP hab (left_mem_openSegment_iff.mp (he ▸ hx))
    · have he := hSame b (by
        intro j hj
        simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton] at hj ⊢
        exact hj.1.resolve_left (fun hja => ha' (hja ▸
          (show j ∈ ({c,d} : Finset Vertex) from by simpa using hj.2))))
      exact hneP hab (right_mem_openSegment_iff.mp (he ▸ hx))

private theorem radialLink_perimeter (q : Vertex → Point3) (v : Vertex) (n : Point3)
    (hn : ∀ w ∈ linkCycle v, 0 < normalDot n (q w-q v)) :
    angularCycleLength (((linkCycle v).map (radialPoint q n v)).map euclideanPoint) = linkPerimeter q v := by
  rw [List.map_map,angularCycleLength_eq_sum_zip]
  simp only [← List.map_drop,← List.map_take,← List.map_append,List.zip_map,List.map_map]
  unfold linkPerimeter
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  obtain ⟨ha,hb,_⟩ := face_of_linkEdge v e.1 e.2 he
  exact angle_radialPoint q n v e.1 e.2 (hn _ ha) (hn _ hb)

/-- An embedded flat Type 2 vertex has an incident face whose plane has
neighbors on both strict sides. -/
theorem mixedFace_of_flat_embedding (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q)) (v : Vertex)
    (hflat : linkPerimeter q v = 2 * Real.pi) : HasMixedFace geometricFaces q v := by
  by_contra hm
  obtain ⟨n,hn⟩ := strictSupport_of_flat_embedding q h v hflat
  have hs (w : Vertex) (hw : w ∈ linkCycle v) := hn w ((mem_linkCycle_iff v w).mp hw)
  let xs := (linkCycle v).map (radialPoint q n v)
  let K := vertexHull (radialPoint q n v) (linkCycle v).toFinset
  obtain ⟨ys,hy,hF,hP⟩ := radialHull_exists_short_boundary_of_noMixedFace q v n h hs hm
  have hB : segmentCycle xs = intrinsicFrontier ℝ K :=
    (radialLink_segmentCycle q v n).trans (radialLink_eq_frontier_of_noMixedFace q v n h hs hm)
  have hnorm : K ⊆ {x | normalFunctional n x = 1} := by
    apply convexHull_min ?_ (convex_hyperplane (normalFunctional n).isLinear 1)
    rintro _ ⟨w,hw,rfl⟩
    exact normalDot_radialPoint q n v w (hs w (List.mem_toFinset.mp hw))
  have hK : IsCompact K := ((linkCycle v).toFinset.finite_toSet.image _).isCompact_convexHull ℝ
  have hnz (x : Point3) (hx : x ∈ segmentCycle xs) : euclideanPoint x ≠ 0 := by
    intro he
    have hzero : x = 0 := euclideanPoint_injective (he.trans euclideanPoint.map_zero.symm)
    have h1 : normalFunctional n x = 1 :=
      hnorm (intrinsicFrontier_subset hK.isClosed (hB ▸ hx))
    simp [hzero] at h1
  have he := angularCycleLength_eq_of_same_simple_boundary
    (radialLink_simplePolygon q v n h hs) hy (hB.trans hF) euclideanPoint hnz
  rw [← he,radialLink_perimeter q v n hs,hflat] at hP
  exact (lt_irrefl _ hP)

/-- Any embedded flat Type 2 realization supplies a normalized generic
placement that retains embeddedness and both kinds of strict witness. -/
theorem normalized_witnesses_of_flat_embedding (q : Vertex → Point3)
    (h : Function.Injective (evaluateTriangles geometricFaces q)) (hflat : HasFlatStars q) :
    ∃ r : Vertex → Point3, Function.Injective (evaluateTriangles geometricFaces r) ∧
      GenericLift (fun v => ((r v).1,(r v).2.1)) (fun v => (r v).2.2) ∧
      0 < affineBracket (r 0) (r 1) (r 2) (r 3) ∧
      (∀ v, HasStrictSupport geometricFaces r v) ∧ ∀ v, HasMixedFace geometricFaces r v := by
  obtain ⟨r,he,hg,hpos,hs,hm⟩ := exists_normalized_with_strict_witnesses geometricFaces Finset.univ q h
    (fun v => strictSupport_of_flat_embedding q h v (hflat v))
    (fun v _ => mixedFace_of_flat_embedding q h v (hflat v))
  exact ⟨r,he,hg,hpos,hs,fun v => hm v (Finset.mem_univ v)⟩

end OrigamiTorus.Type2
