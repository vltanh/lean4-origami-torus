module

public import OrigamiTorus.Type5Nondegenerate
import Mathlib.Tactic

/-! Completeness of the radical leaf candidates for an embedded Type 5 star.
The row equations are given in normalized coordinates with a nonzero height
at the root used as the vertical pivot. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type5

/-- The reduced leaf equations with their constant terms. -/
def LeafData.Satisfies (p : LeafData ℝ) (u : Plane ℝ) (w : Point3) : Prop :=
  horizontal w = p.planarLin u+p.base ∧
    p.z₃*w.2.2 = dot p.a₃ u+p.b₃ ∧ p.z₄*w.2.2 = dot p.a₄ u+p.b₄

/-- The homogeneous part of the reduced leaf equations. -/
def LeafData.Direction (p : LeafData ℝ) (d : Plane ℝ) (e : Point3) : Prop :=
  horizontal e = p.planarLin d ∧ p.z₃*e.2.2 = dot p.a₃ d ∧ p.z₄*e.2.2 = dot p.a₄ d

private theorem LeafData.direction_of_sub {p : LeafData ℝ} {u u' : Plane ℝ} {w w' : Point3}
    (h : p.Satisfies u w) (h' : p.Satisfies u' w') : p.Direction (u'-u) (w'-w) := by
  obtain ⟨ha,hb,hc⟩ := h
  obtain ⟨ha',hb',hc'⟩ := h'
  have hx := congrArg Prod.fst ha
  have hy := congrArg Prod.snd ha
  have hx' := congrArg Prod.fst ha'
  have hy' := congrArg Prod.snd ha'
  unfold LeafData.Direction
  refine ⟨Prod.ext ?_ ?_,?_,?_⟩
  all_goals
    simp only [horizontal,LeafData.planarLin,smul2,dot,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub] at *
  · linear_combination hx'-hx
  · linear_combination hy'-hy
  · linear_combination hb'-hb
  · linear_combination hc'-hc

private theorem LeafData.direction_of_lost_rank {p : LeafData ℝ} (hz : p.z₃ ≠ 0)
    (hn : squared2 p.lineNormal = 0) (d : Plane ℝ) : ∃ e : Point3, p.Direction d e := by
  let e := atHeight (p.planarLin d) (dot p.a₃ d/p.z₃)
  have hd : dot p.lineNormal d = 0 := by
    have hx := sq_nonneg p.lineNormal.1
    have hy := sq_nonneg p.lineNormal.2
    simp only [squared2,dot,← pow_two] at hn
    have h₁ : p.lineNormal.1 = 0 := by nlinarith
    have h₂ : p.lineNormal.2 = 0 := by nlinarith
    simp [dot,h₁,h₂]
  refine ⟨e,rfl,?_,?_⟩
  · change p.z₃*(dot p.a₃ d/p.z₃) = dot p.a₃ d
    field_simp [hz]
  · change p.z₄*(dot p.a₃ d/p.z₃) = dot p.a₄ d
    rw [← mul_div_assoc]
    apply (div_eq_iff hz).mpr
    simp [LeafData.lineNormal,smul2,dot] at hd ⊢
    linear_combination hd

private theorem LeafData.direction_eq (p : LeafData ℝ) (t k : ℝ) :
    p.intrinsicAt (t+k) = p.intrinsicAt t+k • p.intrinsicDirection ∧
    p.extrinsicAt (t+k) = p.extrinsicAt t+k • p.extrinsicDirection := by
  constructor <;> ext <;>
    simp [LeafData.intrinsicAt,LeafData.extrinsicAt,smul2,smul3,atHeight,horizontal] <;> ring

private theorem intrinsicDirection_ne_zero (p : LeafData ℝ) (hn : squared2 p.lineNormal ≠ 0) :
    p.intrinsicDirection ≠ 0 := by
  intro h
  have hx := congrArg Prod.snd h
  have hy := congrArg Prod.fst h
  change p.lineNormal.1 = 0 at hx
  change -p.lineNormal.2 = 0 at hy
  exact hn (by simp [squared2,dot,hx,neg_eq_zero.mp hy])

/-- The radical candidate list contains the actual leaf in an embedded flat
star. The row compatibility identifies the homogeneous reduced rows with
the four length differences from a common anchor. -/
theorem LeafMetric.complete_leaf_candidates {q : Vertex → Point3} {v : Vertex}
    {s : Fin 5 → Plane ℝ} (h : LeafMetric q v s)
    (he : Function.Injective (evaluateTriangles faces q)) (hv : v ∈ leaves)
    (hf : FlatAt q v) (ha : ∀ u ∈ anchors, FlatAt q u) (a : Fin 5)
    (p : LeafData ℝ) (hz : p.z₃ ≠ 0)
    (hpoint : p.Satisfies (-s a) (-leafRay q v a))
    (hrows : ∀ d e, p.Direction d e →
      ∀ i, dot3 e (leafRay q v i-leafRay q v a) = dot d (s i-s a)) :
    squared2 p.lineNormal ≠ 0 ∧ p.quadratic ≠ (0,0,0) ∧
      (-s a,-leafRay q v a) ∈ p.candidates := by
  have hn : squared2 p.lineNormal ≠ 0 := by
    intro hn
    obtain ⟨e₁,h₁⟩ := p.direction_of_lost_rank hz hn (1,0)
    obtain ⟨e₂,h₂⟩ := p.direction_of_lost_rank hz hn (0,1)
    apply h.no_two_intrinsic_directions he hv hf ha a e₁ e₂
    · intro i
      simpa [dot] using hrows _ _ h₁ i
    · intro i
      simpa [dot] using hrows _ _ h₂ i
  obtain ⟨t,hu,hw⟩ := p.parameterization hz hn _ _ hpoint.1 hpoint.2.1 hpoint.2.2
  have hb : p.quadratic ≠ (0,0,0) := by
    intro hzero
    obtain ⟨hdu,hdw⟩ := p.direction_eq t 1
    have hdir : p.Direction p.intrinsicDirection p.extrinsicDirection := by
      have hd := p.direction_of_sub (p.linear_equations hz hn t) (p.linear_equations hz hn (t+1))
      rw [hdu,hdw,one_smul,one_smul,add_sub_cancel_left,add_sub_cancel_left] at hd
      exact hd
    obtain ⟨k,hk⟩ := h.norm_not_identically_zero he hv hf a p.extrinsicDirection p.intrinsicDirection
      (intrinsicDirection_ne_zero p hn) (hrows _ _ hdir)
    apply hk
    obtain ⟨hdk₁,hdk₂⟩ := p.direction_eq t k
    rw [hu,hw,← hdk₁,← hdk₂,← sub_eq_zero,p.quadratic_eq,hzero]
    simp
  have hnorm : squared3 (-leafRay q v a) = squared2 (-s a) := by
    have hn' := h.norm_eq a
    simp [squared3,squared2,dot,horizontal,pow_two] at hn' ⊢
    exact hn'
  have hq : p.quadratic.1 ≠ 0 ∨ p.quadratic.2.1 ≠ 0 ∨ p.quadratic.2.2 ≠ 0 := by
    by_contra! h
    exact hb (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
  exact ⟨hn,hb,p.candidates_complete hz hn hq (-s a) (-leafRay q v a)
    hnorm hpoint.1 hpoint.2.1 hpoint.2.2⟩

def leafRootCoefficient {R : Type*} [Ring R] (r : Space R) (s X Y : Plane R) : Plane R :=
  (s.1-dot (horizontal r) X,s.2-dot (horizontal r) Y)

def leafRootConstant {R : Type*} [Field R] (r : Space R) (s b : Plane R) : R :=
  (squared3 r-squared2 s)/2-dot (horizontal r) b

/-- The normalized leaf data determined by the core and its intrinsic shifts.
The first two spatial anchors have height zero. Either root with nonzero
height can be the vertical pivot. -/
def normalizedLeafData {R : Type*} [Field R] (a b : Plane R) (r₃ r₄ : Space R)
    (s₂ s₅ s₃ s₄ : Plane R) : LeafData R :=
  let f := projection a b s₂ s₅
  let c := f (0,0)
  let X := f (1,0)-c
  let Y := f (0,1)-c
  ⟨c,X,Y,leafRootCoefficient r₃ s₃ X Y,leafRootCoefficient r₄ s₄ X Y,
    leafRootConstant r₃ s₃ c,leafRootConstant r₄ s₄ c,r₃.2.2,r₄.2.2⟩

private theorem normalizedLeafData_planarLin (a b : Plane ℝ) (r₃ r₄ : Point3)
    (s₂ s₅ s₃ s₄ u : Plane ℝ) :
    (normalizedLeafData a b r₃ r₄ s₂ s₅ s₃ s₄).planarLin u =
      linearSolve a b (dot s₂ u) (dot s₅ u) := by
  ext <;> simp [normalizedLeafData,LeafData.planarLin,projection,linearSolve,anchorRhs,smul2,dot] <;> ring

private theorem normalizedLeafData_projection (a b : Plane ℝ) (r₃ r₄ : Point3)
    (s₂ s₅ s₃ s₄ u : Plane ℝ) :
    let p := normalizedLeafData a b r₃ r₄ s₂ s₅ s₃ s₄
    p.planarLin u+p.base = projection a b s₂ s₅ u := by
  dsimp only
  rw [normalizedLeafData_planarLin]
  ext <;> simp [normalizedLeafData,projection,linearSolve,anchorRhs,dot] <;> ring

private theorem linearSolve_unique {a b : Plane ℝ} (hn : cross a b ≠ 0) {x : Plane ℝ} {c d : ℝ}
    (hc : dot a x = c) (hd : dot b x = d) : x = linearSolve a b c d := by
  obtain ⟨he,hf⟩ := linearSolve_spec hn c d
  let y := linearSolve a b c d
  change dot a y = c at he
  change dot b y = d at hf
  have h₁ := hc.trans he.symm
  have h₂ := hd.trans hf.symm
  apply Prod.ext
  · apply (mul_left_cancel₀ hn)
    simp only [cross,dot] at h₁ h₂ ⊢
    linear_combination b.2*h₁-a.2*h₂
  · apply (mul_left_cancel₀ hn)
    simp only [cross,dot] at h₁ h₂ ⊢
    linear_combination -b.1*h₁+a.1*h₂

private theorem root_reduced_row (r w : Point3) (s u b X Y : Plane ℝ)
    (hxy : horizontal w = smul2 u.1 X+smul2 u.2 Y+b)
    (hrow : dot3 r w-dot s u = (squared3 r-squared2 s)/2) :
    r.2.2*w.2.2 = dot (leafRootCoefficient r s X Y) u+leafRootConstant r s b := by
  have hx := congrArg Prod.fst hxy
  have hy := congrArg Prod.snd hxy
  simp only [leafRootCoefficient,leafRootConstant,dot3,dot,horizontal,smul2,Prod.fst_add,Prod.snd_add]
    at hx hy hrow ⊢
  linear_combination hrow-r.1*hx-r.2.1*hy

private theorem normalizedLeafData_satisfies {a b : Plane ℝ} (hn : cross a b ≠ 0)
    (r₃ r₄ w : Point3) (s₂ s₅ s₃ s₄ u : Plane ℝ)
    (h₂ : dot3 (atHeight a 0) w-dot s₂ u = (squared3 (atHeight a 0)-squared2 s₂)/2)
    (h₅ : dot3 (atHeight b 0) w-dot s₅ u = (squared3 (atHeight b 0)-squared2 s₅)/2)
    (h₃ : dot3 r₃ w-dot s₃ u = (squared3 r₃-squared2 s₃)/2)
    (h₄ : dot3 r₄ w-dot s₄ u = (squared3 r₄-squared2 s₄)/2) :
    (normalizedLeafData a b r₃ r₄ s₂ s₅ s₃ s₄).Satisfies u w := by
  let p := normalizedLeafData a b r₃ r₄ s₂ s₅ s₃ s₄
  have hA : dot a (horizontal w) = anchorRhs a s₂ u := by
    simp [dot3,atHeight,squared3,horizontal,anchorRhs] at h₂ ⊢
    linarith
  have hB : dot b (horizontal w) = anchorRhs b s₅ u := by
    simp [dot3,atHeight,squared3,horizontal,anchorRhs] at h₅ ⊢
    linarith
  have hxy : horizontal w = p.planarLin u+p.base :=
    (linearSolve_unique hn hA hB).trans (normalizedLeafData_projection a b r₃ r₄ s₂ s₅ s₃ s₄ u).symm
  exact ⟨hxy,root_reduced_row r₃ w s₃ u p.base p.colX p.colY hxy h₃,
    root_reduced_row r₄ w s₄ u p.base p.colX p.colY hxy h₄⟩

/-- The reduced leaf rows and the origin distance give the four remaining
distances to the core. -/
theorem normalizedLeafData_distances {a b : Plane ℝ} (hn : cross a b ≠ 0)
    {r₃ r₄ w : Point3} {s₂ s₅ s₃ s₄ u : Plane ℝ}
    (h₀ : squared3 w = squared2 u)
    (h : (normalizedLeafData a b r₃ r₄ s₂ s₅ s₃ s₄).Satisfies u w) :
    squared3 (w-atHeight a 0) = squared2 (u-s₂) ∧
    squared3 (w-atHeight b 0) = squared2 (u-s₅) ∧
    squared3 (w-r₃) = squared2 (u-s₃) ∧ squared3 (w-r₄) = squared2 (u-s₄) := by
  let p := normalizedLeafData a b r₃ r₄ s₂ s₅ s₃ s₄
  have hxy : horizontal w = p.planarLin u+p.base := h.1
  have hproj : horizontal w = projection a b s₂ s₅ u :=
    hxy.trans (normalizedLeafData_projection a b r₃ r₄ s₂ s₅ s₃ s₄ u)
  obtain ⟨hA,hB⟩ := linearSolve_spec hn (anchorRhs a s₂ u) (anchorRhs b s₅ u)
  change dot a (projection a b s₂ s₅ u) = _ at hA
  change dot b (projection a b s₂ s₅ u) = _ at hB
  rw [← hproj] at hA hB
  have root_sound (r : Point3) (s : Plane ℝ)
      (hr : r.2.2*w.2.2 = dot (leafRootCoefficient r s p.colX p.colY) u+leafRootConstant r s p.base) :
      squared3 (w-r) = squared2 (u-s) := by
    apply (edgeEquation_iff _ _ _ _ h₀).mpr
    have hx := congrArg Prod.fst hxy
    have hy := congrArg Prod.snd hxy
    simp only [leafRootCoefficient,leafRootConstant,LeafData.planarLin,dot3,dot,horizontal,smul2,
      Prod.fst_add,Prod.snd_add] at hx hy hr ⊢
    linear_combination hr+r.1*hx+r.2.1*hy
  refine ⟨(edgeEquation_iff _ _ _ _ h₀).mpr ?_,(edgeEquation_iff _ _ _ _ h₀).mpr ?_,
    root_sound r₃ s₃ h.2.1,root_sound r₄ s₄ h.2.2⟩
  · change dot a (horizontal w)+0*w.2.2-dot s₂ u = (squared2 a+0^2-squared2 s₂)/2
    rw [hA]
    unfold anchorRhs
    ring
  · change dot b (horizontal w)+0*w.2.2-dot s₅ u = (squared2 b+0^2-squared2 s₅)/2
    rw [hB]
    unfold anchorRhs
    ring

private theorem root_direction_row (r e : Point3) (s d X Y : Plane ℝ)
    (hxy : horizontal e = smul2 d.1 X+smul2 d.2 Y)
    (hz : r.2.2*e.2.2 = dot (leafRootCoefficient r s X Y) d) :
    dot3 e r = dot d s := by
  have hx := congrArg Prod.fst hxy
  have hy := congrArg Prod.snd hxy
  simp only [leafRootCoefficient,dot3,dot,horizontal,smul2,Prod.fst_add,Prod.snd_add]
    at hx hy hz ⊢
  linear_combination hz+r.1*hx+r.2.1*hy

private theorem normalizedLeafData_direction {a b : Plane ℝ} (hn : cross a b ≠ 0)
    (r₃ r₄ e : Point3) (s₂ s₅ s₃ s₄ d : Plane ℝ)
    (h : (normalizedLeafData a b r₃ r₄ s₂ s₅ s₃ s₄).Direction d e) :
    dot3 e (atHeight a 0) = dot d s₂ ∧ dot3 e (atHeight b 0) = dot d s₅ ∧
      dot3 e r₃ = dot d s₃ ∧ dot3 e r₄ = dot d s₄ := by
  let p := normalizedLeafData a b r₃ r₄ s₂ s₅ s₃ s₄
  obtain ⟨hxy,h₃,h₄⟩ := h
  have he : horizontal e = linearSolve a b (dot s₂ d) (dot s₅ d) :=
    hxy.trans (normalizedLeafData_planarLin a b r₃ r₄ s₂ s₅ s₃ s₄ d)
  obtain ⟨hA,hB⟩ := linearSolve_spec hn (dot s₂ d) (dot s₅ d)
  rw [← he] at hA hB
  refine ⟨?_,?_,root_direction_row r₃ e s₃ d p.colX p.colY hxy h₃,
    root_direction_row r₄ e s₄ d p.colX p.colY hxy h₄⟩
  · simp [dot3,atHeight,dot,horizontal] at hA ⊢
    linear_combination hA
  · simp [dot3,atHeight,dot,horizontal] at hB ⊢
    linear_combination hB

/-- A flat embedded leaf occurs on the radical list generated explicitly by
the normalized core coordinates. The ordering places the origin first, the
two horizontal anchors next and the root used as pivot fourth. -/
theorem LeafMetric.normalized_candidates_complete {q : Vertex → Point3} {v : Vertex}
    {s : Fin 5 → Plane ℝ} (h : LeafMetric q v s)
    (he : Function.Injective (evaluateTriangles faces q)) (hv : v ∈ leaves)
    (hf : FlatAt q v) (ha : ∀ u ∈ anchors, FlatAt q u) (order : Fin 5 ≃ Fin 5)
    (A B : Plane ℝ) (hAB : cross A B ≠ 0)
    (hA : leafRay q v (order 1)-leafRay q v (order 0) = atHeight A 0)
    (hB : leafRay q v (order 2)-leafRay q v (order 0) = atHeight B 0)
    (hz : (leafRay q v (order 3)-leafRay q v (order 0)).2.2 ≠ 0) :
    let R i := leafRay q v (order i)-leafRay q v (order 0)
    let S i := s (order i)-s (order 0)
    let p := normalizedLeafData A B (R 3) (R 4) (S 1) (S 2) (S 3) (S 4)
    squared2 p.lineNormal ≠ 0 ∧ p.quadratic ≠ (0,0,0) ∧
      (-s (order 0),-leafRay q v (order 0)) ∈ p.candidates := by
  let a := order 0
  let R i := leafRay q v (order i)-leafRay q v a
  let S i := s (order i)-s a
  let u := -s a
  let w := -leafRay q v a
  let p := normalizedLeafData A B (R 3) (R 4) (S 1) (S 2) (S 3) (S 4)
  have hnorm (i : Fin 5) : squared3 (-leafRay q v i) = squared2 (-s i) := by
    have hh := h.norm_eq i
    simp [squared3,squared2,dot,horizontal,pow_two] at hh ⊢
    exact hh
  have hrow (i : Fin 5) : dot3 (R i) w-dot (S i) u = (squared3 (R i)-squared2 (S i))/2 := by
    apply (edgeEquation_iff u (S i) w (R i) (hnorm a)).mp
    have h₁ : w-R i = -leafRay q v (order i) := by dsimp [w,R]; abel
    have h₂ : u-S i = -s (order i) := by dsimp [u,S]; abel
    rw [h₁,h₂]
    exact hnorm (order i)
  have h₁ := hrow 1
  have h₂ := hrow 2
  change R 1 = atHeight A 0 at hA
  change R 2 = atHeight B 0 at hB
  rw [hA] at h₁
  rw [hB] at h₂
  have hfit : p.Satisfies u w :=
    normalizedLeafData_satisfies hAB _ _ _ _ _ _ _ _ h₁ h₂ (hrow 3) (hrow 4)
  apply h.complete_leaf_candidates he hv hf ha a p hz hfit
  intro d e hh i
  obtain ⟨k,rfl⟩ := order.surjective i
  change dot3 e (R k) = dot d (S k)
  obtain ⟨h₁,h₂,h₃,h₄⟩ := normalizedLeafData_direction hAB _ _ _ _ _ _ _ _ hh
  fin_cases k
  · simp [R,S,a,dot3,dot,horizontal]
  · exact hA.symm ▸ h₁
  · exact hB.symm ▸ h₂
  · exact h₃
  · exact h₄

/-- Both signed roots are sufficient for any normalized spatial point
whose three anchor distances match. -/
theorem normalized_root_complete {a b : Plane ℝ} (hab : cross a b ≠ 0)
    (s₂ s₅ u : Plane ℝ) (r : Point3) (h₀ : squared3 r = squared2 u)
    (h₂ : squared3 (r-atHeight a 0) = squared2 (u-s₂))
    (h₅ : squared3 (r-atHeight b 0) = squared2 (u-s₅)) :
    r ∈ [makeRoot a b s₂ s₅ u false,makeRoot a b s₂ s₅ u true] := by
  have hrow₂ := (edgeEquation_iff u s₂ r (atHeight a 0) h₀).mp h₂
  have hrow₅ := (edgeEquation_iff u s₅ r (atHeight b 0) h₀).mp h₅
  have hA : dot a (horizontal r) = anchorRhs a s₂ u := by
    simp [dot3,atHeight,squared3,horizontal,anchorRhs] at hrow₂ ⊢
    linarith
  have hB : dot b (horizontal r) = anchorRhs b s₅ u := by
    simp [dot3,atHeight,squared3,horizontal,anchorRhs] at hrow₅ ⊢
    linarith
  have hxy : horizontal r = projection a b s₂ s₅ u := linearSolve_unique hab hA hB
  have hz : rootRadicand a b s₂ s₅ u = r.2.2^2 := by
    rw [rootRadicand,← hxy,← h₀,squared3]
    ring
  have hrt : Real.sqrt (rootRadicand a b s₂ s₅ u) = |r.2.2| := by
    rw [hz, Real.sqrt_sq_eq_abs]
  have hx := congrArg Prod.fst hxy
  have hy := congrArg Prod.snd hxy
  by_cases hpos : 0 ≤ r.2.2
  · apply List.mem_cons_of_mem
    apply List.mem_singleton.mpr
    exact Prod.ext hx (Prod.ext hy (by simp [makeRoot,atHeight,signedRoot,hrt,abs_of_nonneg hpos]))
  · apply List.mem_cons.mpr
    exact Or.inl (Prod.ext hx (Prod.ext hy (by simp [makeRoot,atHeight,signedRoot,hrt,abs_of_neg (lt_of_not_ge hpos)])))

theorem core_some_height_ne_zero (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q))
    (h₁ : (q 1).2.2 = 0) (h₂ : (q 2).2.2 = 0) (h₅ : (q 5).2.2 = 0) :
    (q 3).2.2 ≠ 0 ∨ (q 4).2.2 ≠ 0 := by
  by_contra! h
  let L : Plane ℝ →ₗ[ℝ] Point3 :=
    { toFun := fun p => atHeight p 0
      map_add' := by intros; ext <;> simp [atHeight]
      map_smul' := by intros; ext <;> simp [atHeight] }
  have hLi : Function.Injective L := by
    intro x y hq
    exact Prod.ext (congrArg (fun x : Point3 => x.1) hq) (congrArg (fun x : Point3 => x.2.1) hq)
  have hdim : Module.finrank ℝ L.range = 2 := by
    rw [LinearMap.finrank_range_of_inj hLi]
    simp [Plane,Module.finrank_prod]
  apply core_not_in_plane_of_embedding q he 0 L.range hdim.le
  intro i
  have hz : (q (coreLabels i)).2.2 = 0 := by
    fin_cases i <;> first | exact h₁ | exact h₂ | exact h₅ | exact h.1 | exact h.2
  refine ⟨horizontal (q (coreLabels i)),?_⟩
  rw [sub_zero]
  exact Prod.ext rfl (Prod.ext rfl hz.symm)

end OrigamiTorus.Type5
