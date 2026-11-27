module

public import OrigamiTorus.Type5.LeafPlanes
import Mathlib.Tactic

/-! The geometric exclusions remove rank loss and a direction on which the
Type 5 norm equation could vanish identically. -/

@[expose] public section

namespace OrigamiTorus.Type5

/-- Intrinsic vectors from the center of a lifted leaf star, in cyclic order.
The three edge lengths of each incident face agree with the spatial lengths. -/
structure LeafMetric (q : Vertex → Point3) (v : Vertex) (s : Fin 5 → Plane ℝ) : Prop where
  norm_eq : ∀ i, squared3 (leafRay q v i) = squared2 (s i)
  edge_eq : ∀ i, squared3 (leafRay q v (finRotate 5 i)-leafRay q v i) =
    squared2 (s (finRotate 5 i)-s i)
  oriented_nondegenerate : ∀ i, cross (s i) (s (finRotate 5 i)) ≠ 0

theorem LeafMetric.dot_eq {q : Vertex → Point3} {v : Vertex} {s : Fin 5 → Plane ℝ}
    (h : LeafMetric q v s) (i : Fin 5) :
    dot3 (leafRay q v i) (leafRay q v (finRotate 5 i)) = dot (s i) (s (finRotate 5 i)) := by
  have h₁ := h.norm_eq i
  have h₂ := h.norm_eq (finRotate 5 i)
  have h₁₂ := h.edge_eq i
  simp only [squared3,squared2,dot3,dot,horizontal,Prod.fst_sub,Prod.snd_sub] at h₁ h₂ h₁₂ ⊢
  linear_combination (h₁+h₂-h₁₂)/2

/-- No nonzero spatial variation at a flat embedded leaf preserves the
intrinsic norm and all five incident inner products. -/
theorem LeafMetric.no_norm_preserving_direction {q : Vertex → Point3} {v : Vertex} {s : Fin 5 → Plane ℝ}
    (h : LeafMetric q v s) (he : Function.Injective (evaluateTriangles faces q))
    (hv : v ∈ leaves) (hf : FlatAt q v) (e : Point3) (d : Plane ℝ)
    (hn : squared3 e = squared2 d)
    (hd : ∀ i, dot3 e (leafRay q v i) = dot d (s i)) : e = 0 := by
  by_contra hne
  apply leaf_no_common_plane_direction q he v hv hf e hne
  intro i
  obtain ⟨a,b,hab⟩ := leafDirection_in_facePlane _ _ e _ _ d (h.oriented_nondegenerate i)
    (h.norm_eq i) (h.norm_eq (finRotate 5 i)) (h.edge_eq i) hn (hd i) (hd (finRotate 5 i))
  apply Submodule.mem_span_pair.mpr
  exact ⟨a,b,hab.symm⟩

private def polarDifference (L : Point3 →ₗ[ℝ] Plane ℝ) : Point3 →ₗ[ℝ] Point3 →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => dot3 x y-dot (L x) (L y))
    (by intros; simp [dot3,dot,horizontal,map_add]; ring)
    (by intros; simp [dot3,dot,horizontal,map_smul]; ring)
    (by intros; simp [dot3,dot,horizontal,map_add]; ring)
    (by intros; simp [dot3,dot,horizontal,map_smul]; ring)

private theorem polarDifference_apply (L : Point3 →ₗ[ℝ] Plane ℝ) (x y : Point3) :
    polarDifference L x y = dot3 x y-dot (L x) (L y) := rfl

private theorem polarDifference_comm (L : Point3 →ₗ[ℝ] Plane ℝ) (x y : Point3) :
    polarDifference L x y = polarDifference L y x := by
  simp only [polarDifference_apply,dot3,dot,horizontal]
  ring

private theorem polarDifference_self (L : Point3 →ₗ[ℝ] Plane ℝ) (x : Point3) :
    polarDifference L x x = squared3 x-squared2 (L x) := by
  simp only [polarDifference_apply,dot3,dot,horizontal,squared3,squared2,pow_two]

/-- A bilinear form on a three-dimensional space that vanishes on a
two-dimensional subspace has a nonzero left radical. -/
private theorem exists_radical_of_null_plane
    (B : Point3 →ₗ[ℝ] Point3 →ₗ[ℝ] ℝ) (P : Submodule ℝ Point3)
    (hP : Module.finrank ℝ P = 2) (hBP : ∀ x ∈ P, ∀ y ∈ P, B x y = 0) :
    ∃ e : Point3, e ≠ 0 ∧ ∀ x : Point3, B e x = 0 := by
  have hdim : Module.finrank ℝ Point3 = 3 := by simp [Point3,Module.finrank_prod]
  have hne : P ≠ ⊤ := by
    intro he
    rw [he] at hP
    simp [hdim] at hP
  obtain ⟨z,hz⟩ : ∃ z : Point3, z ∉ P := by
    by_contra! h
    exact hne (Submodule.eq_top_iff'.mpr h)
  let T := Submodule.span ℝ ({z} : Set Point3)
  have hzs : z ∈ T := Submodule.subset_span (Set.mem_singleton _)
  have hlt : P < P ⊔ T :=
    lt_of_le_of_ne le_sup_left (fun h => hz (h ▸ Submodule.mem_sup_right hzs))
  have htop : P ⊔ T = ⊤ := by
    have hle := Submodule.finrank_le (P ⊔ T)
    have hge := Submodule.finrank_lt_finrank_of_lt hlt
    apply Submodule.eq_top_of_finrank_eq
    omega
  let K : P →ₗ[ℝ] ℝ := (LinearMap.applyₗ (R := ℝ) (M₂ := ℝ) z).comp (B.comp P.subtype)
  have hK : ¬ Function.Injective K := by
    intro hi
    have h := LinearMap.finrank_le_finrank_of_injective hi
    simp [hP] at h
  rw [← LinearMap.ker_eq_bot,Submodule.eq_bot_iff] at hK
  push Not at hK
  obtain ⟨e,he,hene⟩ := hK
  have hez : B e.val z = 0 := LinearMap.mem_ker.mp he
  have hne' : e.val ≠ 0 := fun h => hene (Subtype.ext h)
  refine ⟨e.val,hne',fun x => ?_⟩
  have hx : x ∈ P ⊔ T := by rw [htop]; exact Submodule.mem_top
  obtain ⟨y,hy,w,hw,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp hw
  simp [hBP e.val e.property y hy,hez]

private theorem LeafMetric.no_linear_graph {q : Vertex → Point3} {v : Vertex} {s : Fin 5 → Plane ℝ}
    (h : LeafMetric q v s) (he : Function.Injective (evaluateTriangles faces q))
    (hv : v ∈ leaves) (hf : FlatAt q v) (L : Point3 →ₗ[ℝ] Plane ℝ)
    (hL : ∀ i, s i = L (leafRay q v i)) : False := by
  let B := polarDifference L
  let x := leafRay q v 0
  let y := leafRay q v 1
  let P := leafPlane q v 0
  have hP : Module.finrank ℝ P = 2 := leafPlane_finrank q he v hv hf 0
  have hxx : B x x = 0 := by
    change polarDifference L x x = 0
    rw [polarDifference_self,← hL 0,h.norm_eq 0,sub_self]
  have hyy : B y y = 0 := by
    change polarDifference L y y = 0
    rw [polarDifference_self,← hL 1,h.norm_eq 1,sub_self]
  have hxy : B x y = 0 := by
    change polarDifference L x y = 0
    rw [polarDifference_apply,← hL 0,← hL 1]
    exact sub_eq_zero.mpr (h.dot_eq 0)
  have hyx : B y x = 0 := (polarDifference_comm L y x).trans hxy
  have hBP : ∀ u ∈ P, ∀ w ∈ P, B u w = 0 := by
    intro u hu w hw
    change u ∈ Submodule.span ℝ {x,y} at hu
    change w ∈ Submodule.span ℝ {x,y} at hw
    obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hu
    obtain ⟨c,d,rfl⟩ := Submodule.mem_span_pair.mp hw
    simp [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,hxx,hxy,hyx,hyy]
  obtain ⟨e,hene,hRad⟩ := exists_radical_of_null_plane B P hP hBP
  apply hene (h.no_norm_preserving_direction he hv hf e (L e) ?_ ?_)
  · have H := hRad e
    change polarDifference L e e = 0 at H
    exact sub_eq_zero.mp ((polarDifference_self L e).symm.trans H)
  · intro i
    rw [hL i]
    exact sub_eq_zero.mp (hRad (leafRay q v i))

/-- At a flat embedded leaf the two-dimensional intrinsic neighbor vectors
cannot be affine functions of the spatial neighbor vectors. Thus the two
intrinsic columns do not both lie in the span of the three spatial columns. -/
theorem LeafMetric.no_affine_graph {q : Vertex → Point3} {v : Vertex} {s : Fin 5 → Plane ℝ}
    (h : LeafMetric q v s) (he : Function.Injective (evaluateTriangles faces q))
    (hv : v ∈ leaves) (hf : FlatAt q v) (ha : ∀ u ∈ anchors, FlatAt q u)
    (L : Point3 →ₗ[ℝ] Plane ℝ) (b : Plane ℝ)
    (hL : ∀ i, s i = L (leafRay q v i)+b) : False := by
  by_cases hb : b = 0
  · exact h.no_linear_graph he hv hf L (fun i => by simpa [hb] using hL i)
  obtain ⟨i,c,hc,hm,hw⟩ := leafAffineRank_three_dependent (leafRay q v) s L hb hL h.norm_eq h.dot_eq
  let n := leafNeighbor v
  let a := i
  let b := finRotate 5 i
  let c' := finRotate 5 b
  let p : Fin 3 → Point3 := ![leafRay q v a,leafRay q v b,leafRay q v c']
  let T := (AffineEquiv.constVAdd ℝ Point3 (q v)).toAffineMap
  have hAi : AffineIndependent ℝ p := by
    apply AffineIndependent.of_comp T
    have heta : T ∘ p = ![q (n a),q (n b),q (n c')] := by
      funext j
      fin_cases j <;> simp [T,p,leafRay,n,sub_eq_add_neg,add_comm]
    rw [heta,affineIndependent_iff_not_collinear_set]
    exact leaf_link_triple_not_collinear q he ha v hv i
  have hval : ∀ j, c j = 0 := by
    apply ((affineIndependent_iff_of_fintype ℝ _).mp hAi) c hm
    rw [Finset.weightedVSub_eq_linear_combination _ hm]
    exact hw
  obtain ⟨j,hj⟩ := hc
  exact hj (hval j)

/-- The two independent intrinsic coordinate directions cannot both be
matched by spatial variations in all four subtracted length equations. -/
theorem LeafMetric.no_two_intrinsic_directions {q : Vertex → Point3} {v : Vertex}
    {s : Fin 5 → Plane ℝ} (h : LeafMetric q v s)
    (he : Function.Injective (evaluateTriangles faces q)) (hv : v ∈ leaves)
    (hf : FlatAt q v) (ha : ∀ u ∈ anchors, FlatAt q u) (a : Fin 5)
    (e₁ e₂ : Point3)
    (hx : ∀ i, dot3 e₁ (leafRay q v i-leafRay q v a) = (s i).1-(s a).1)
    (hy : ∀ i, dot3 e₂ (leafRay q v i-leafRay q v a) = (s i).2-(s a).2) : False := by
  let L : Point3 →ₗ[ℝ] Plane ℝ :=
    { toFun := fun x => (dot3 e₁ x,dot3 e₂ x)
      map_add' := by intros; ext <;> simp [dot3,dot,horizontal] <;> ring
      map_smul' := by intros; ext <;> simp [dot3,dot,horizontal] <;> ring }
  let b := s a-L (leafRay q v a)
  apply h.no_affine_graph he hv hf ha L b
  intro i
  have h₁ := hx i
  have h₂ := hy i
  apply Prod.ext
  · simp only [L,b,LinearMap.coe_mk,AddHom.coe_mk,Prod.fst_add,Prod.fst_sub,dot3,dot,horizontal,
      Prod.snd_sub] at h₁ ⊢
    linear_combination -h₁
  · simp only [L,b,LinearMap.coe_mk,AddHom.coe_mk,Prod.snd_add,Prod.fst_sub,dot3,dot,horizontal,
      Prod.snd_sub] at h₂ ⊢
    linear_combination -h₂

private theorem plane_eq_zero_of_squared {d : Plane ℝ} (h : squared2 d = 0) : d = 0 := by
  have h₁ := sq_nonneg d.1
  have h₂ := sq_nonneg d.2
  simp only [squared2,dot,← pow_two] at h
  exact Prod.ext (by nlinarith : d.1 = 0) (by nlinarith : d.2 = 0)

/-- A nonzero direction preserving the four subtracted linear equations
cannot make the norm equation vanish identically along a solution line. -/
theorem LeafMetric.norm_not_identically_zero {q : Vertex → Point3} {v : Vertex}
    {s : Fin 5 → Plane ℝ} (h : LeafMetric q v s)
    (he : Function.Injective (evaluateTriangles faces q)) (hv : v ∈ leaves) (hf : FlatAt q v)
    (a : Fin 5) (e : Point3) (d : Plane ℝ) (hd : d ≠ 0)
    (hlin : ∀ i, dot3 e (leafRay q v i-leafRay q v a) = dot d (s i-s a)) :
    ∃ t : ℝ, squared3 (-leafRay q v a+t • e) ≠ squared2 (-s a+t • d) := by
  by_contra! hall
  have h₀ := h.norm_eq a
  have h₁ := hall 1
  have h₂ := hall (-1)
  simp only [one_smul,neg_smul,Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg,
    squared3,squared2,dot,horizontal] at h₀ h₁ h₂
  have hn : squared3 e = squared2 d := by
    simp only [squared3,squared2,dot,horizontal]
    linear_combination (h₁+h₂)/2-h₀
  have hm : dot3 e (leafRay q v a) = dot d (s a) := by
    simp only [dot3,dot,horizontal]
    linear_combination (h₂-h₁)/4
  have hz := h.no_norm_preserving_direction he hv hf e d hn (fun i => by
    have h₃ := hlin i
    simp only [dot3,dot,horizontal,Prod.fst_sub,Prod.snd_sub] at hm h₃ ⊢
    linear_combination h₃+hm)
  exact hd (plane_eq_zero_of_squared (by simpa [hz,squared3,squared2,dot,horizontal] using hn.symm))

end OrigamiTorus.Type5
