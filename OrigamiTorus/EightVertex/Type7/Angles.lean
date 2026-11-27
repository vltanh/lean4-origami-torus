module

public import OrigamiTorus.EightVertex.Type7.Rectangular
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Tactic

/-! The positive rectangular corner product makes its argument sum an integral turn. -/

@[expose] public section

namespace OrigamiTorus.Type7

theorem complex_arg_list_product (l : List ℂ) (hn : ∀ a ∈ l, a ≠ 0) :
    ((l.prod.arg : ℝ) : Real.Angle) = (l.map fun a => (a.arg : Real.Angle)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h : ∀ b ∈ l, b ≠ 0 := fun b hb => hn b (List.mem_cons_of_mem _ hb)
    have hall : l.prod ≠ 0 := List.prod_ne_zero (fun hz => h 0 hz rfl)
    simp only [List.prod_cons,List.map_cons,List.sum_cons]
    rw [Complex.arg_mul_coe_angle (hn a List.mem_cons_self) hall, ih h]

noncomputable def physicalComplex (w : ℝ) (a : ℝ × ℝ) : ℂ := ⟨a.1,Real.sqrt w*a.2⟩

theorem physicalComplex_mul (w : ℝ) (hw : 0 ≤ w) (a b : ℝ × ℝ) :
    physicalComplex w (multiplyComplex w a b) = physicalComplex w a * physicalComplex w b := by
  apply Complex.ext
  · simp only [physicalComplex,multiplyComplex,Complex.mul_re]
    linear_combination a.2*b.2*Real.sq_sqrt hw
  · simp only [physicalComplex,multiplyComplex,Complex.mul_im]
    ring

theorem physicalComplex_one (w : ℝ) : physicalComplex w (1,0) = 1 := by
  apply Complex.ext <;> simp [physicalComplex]

private theorem physical_fold_product (w : ℝ) (hw : 0 ≤ w) (i : Vertex)
    (l : List (Triangle × Bool)) (acc : ℝ × ℝ) :
    physicalComplex w (l.foldl (fun c f => multiplyComplex w c (cornerFactor w i f)) acc) =
      physicalComplex w acc * (l.map (fun f => physicalComplex w (cornerFactor w i f))).prod := by
  induction l generalizing acc with
  | nil => simp
  | cons f l ih =>
    simp only [List.foldl_cons,List.map_cons,List.prod_cons]
    rw [ih,physicalComplex_mul w hw,mul_assoc]

private theorem physical_corner_product (w : ℝ) (hw : 0 ≤ w) (i : Vertex) :
    physicalComplex w (rectangularCornerProduct w i) =
      (orientedFaces.map fun f => physicalComplex w (cornerFactor w i f)).prod := by
  rw [rectangularCornerProduct,physical_fold_product w hw,physicalComplex_one,one_mul]

private theorem cross_area (p : Vertex → ℝ × ℝ) (a b c : Vertex) :
    Type5.cross (p b-p a) (p c-p a) = area p a b c := by
  simp only [area,Type5.cross,Prod.fst_sub,Prod.snd_sub]
  ring

private theorem cyc_area (p : Vertex → ℝ × ℝ) (a b c : Vertex) :
    area p b c a = area p a b c := by
  unfold area
  ring

private theorem physical_corner_positive_or_one (w : ℝ) (hw : 1 ≤ w) (i : Vertex) (f : Triangle × Bool)
    (hf : f ∈ orientedFaces) :
    let z := physicalComplex w (cornerFactor w i f)
    0 < z.im ∨ z = 1 := by
  rcases f with ⟨⟨a,b,c⟩,s⟩
  have ha : 0 < (if s then area (rectangularPoint w) a b c else -area (rectangularPoint w) a b c) := by
    have h := rectangular_face_orientation w hw (a,b,c) s hf
    cases s
    · exact neg_pos.mpr h
    · exact h
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 (by linarith)
  have hb := mul_pos hs ha
  by_cases ia : i=a
  · subst i
    left
    simpa [physicalComplex,cornerFactor,cross_area] using hb
  by_cases ib : i=b
  · subst i
    left
    simpa [physicalComplex,cornerFactor,ia,cross_area,cyc_area (rectangularPoint w) a b c] using hb
  by_cases ic : i=c
  · subst i
    left
    simpa [physicalComplex,cornerFactor,ia,ib,cross_area,cyc_area (rectangularPoint w) b c a,
      cyc_area (rectangularPoint w) a b c] using hb
  · right
    simpa [cornerFactor,ia,ib,ic] using physicalComplex_one w

noncomputable def rectangularAngleSum (w : ℝ) (i : Vertex) : ℝ :=
  (orientedFaces.map fun f => (physicalComplex w (cornerFactor w i f)).arg).sum

theorem coe_list_sum (l : List ℝ) :
    ((l.sum : ℝ) : Real.Angle) = (l.map fun a => (a : Real.Angle)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Real.Angle.coe_add,ih]

/-- Every rectangular vertex angle sum is an integer multiple of one full turn. -/
theorem rectangular_angle_sum_integral (w : ℝ) (hw : 1 ≤ w) (i : Vertex) :
    ∃ n : ℤ, n • (2 * Real.pi) = rectangularAngleSum w i := by
  let l := orientedFaces.map fun f => physicalComplex w (cornerFactor w i f)
  have hpos : 0 < (rectangularCornerProduct w i).1 := rectangular_corner_product_positive w hw i
  have hzero : (rectangularCornerProduct w i).2 = 0 := rectangular_corner_product_real w i
  have hpan : l.prod.arg = 0 := by
    rw [← physical_corner_product w (by linarith) i]
    exact Complex.arg_eq_zero_iff.mpr ⟨hpos.le,by simp [physicalComplex,hzero]⟩
  have hn : ∀ z ∈ l, z ≠ 0 := by
    intro z hz
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hz
    rcases physical_corner_positive_or_one w hw i f hf with hp | he
    · intro h
      rw [h,Complex.zero_im] at hp
      exact (lt_irrefl _ hp)
    · rw [he]
      exact one_ne_zero
  apply Real.Angle.coe_eq_zero_iff.mp
  have hh := complex_arg_list_product l hn
  rw [hpan,Real.Angle.coe_zero] at hh
  have ht : ((l.map Complex.arg).sum : Real.Angle) = 0 := by
    rw [coe_list_sum,List.map_map]
    exact hh.symm
  exact ht

theorem positiveArg {z : ℂ} (h : 0 < z.im) : 0 < z.arg := by
  apply lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr h.le)
  intro he
  exact h.ne' (Complex.arg_eq_zero_iff.mp he.symm).2

private theorem rectangular_factor_im (w : ℝ) (hw : 1 ≤ w) (i : Vertex)
    (f : Triangle × Bool) (hf : f ∈ orientedFaces) (hi : i ∈ triangleVertices f.1) :
    0 < (physicalComplex w (cornerFactor w i f)).im := by
  have ht := physical_corner_positive_or_one w hw i f hf
  rcases ht with ht | ht
  · exact ht
  · rcases f with ⟨⟨a,b,c⟩,s⟩
    have ha : 0 < (if s then area (rectangularPoint w) a b c else -area (rectangularPoint w) a b c) := by
      have h := rectangular_face_orientation w hw (a,b,c) s hf
      cases s
      · exact neg_pos.mpr h
      · exact h
    have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 (by linarith)
    have hb := mul_pos hs ha
    have he := congrArg Complex.im ht
    by_cases ia : i = a
    · subst i
      simp [physicalComplex,cornerFactor,cross_area] at he
      exact (hb.ne' (by cases s <;> simpa using he)).elim
    by_cases ib : i = b
    · subst i
      simp [physicalComplex,cornerFactor,ia,cross_area,cyc_area (rectangularPoint w) a b c] at he
      exact (hb.ne' (by cases s <;> simpa using he)).elim
    have ic : i = c := by simpa [triangleVertices,ia,ib] using hi
    subst i
    simp [physicalComplex,cornerFactor,ia,ib,cross_area,cyc_area (rectangularPoint w) b c a,
      cyc_area (rectangularPoint w) a b c] at he
    exact (hb.ne' (by cases s <;> simpa using he)).elim

theorem rectangular_angle_sum_lower (w : ℝ) (hw : 1 ≤ w) (i : Vertex) :
    2*Real.pi ≤ rectangularAngleSum w i := by
  have incident : ∀ j : Vertex, ∃ f ∈ orientedFaces, j ∈ triangleVertices f.1 := by
    decide +kernel
  have hn (f : Triangle × Bool) (hf : f ∈ orientedFaces) :
      0 ≤ (physicalComplex w (cornerFactor w i f)).arg := by
    rcases physical_corner_positive_or_one w hw i f hf with h | h
    · exact (positiveArg h).le
    · simp [h]
  obtain ⟨f,hf,hi⟩ := incident i
  have hpos : 0 < rectangularAngleSum w i := by
    unfold rectangularAngleSum
    let a (g : Triangle × Bool) := (physicalComplex w (cornerFactor w i g)).arg
    have sumpositive (l : List (Triangle × Bool)) (hl : ∀ g ∈ l, 0 ≤ a g)
        (hm : f ∈ l) : 0 < (l.map a).sum := by
      induction l with
      | nil => simp at hm
      | cons h l ih =>
        simp only [List.map_cons,List.sum_cons]
        rcases List.mem_cons.mp hm with rfl | hm
        · apply add_pos_of_pos_of_nonneg (positiveArg (rectangular_factor_im w hw i f hf hi))
          apply List.sum_nonneg
          intro x hx
          obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hx
          exact hl g (List.mem_cons_of_mem _ hg)
        · exact add_pos_of_nonneg_of_pos (hl h List.mem_cons_self)
            (ih (fun g hg => hl g (List.mem_cons_of_mem _ hg)) hm)
    exact sumpositive orientedFaces hn hf
  obtain ⟨n,h⟩ := rectangular_angle_sum_integral w hw i
  rw [← h] at hpos ⊢
  rw [zsmul_eq_mul] at hpos ⊢
  have hn : 0 < (n : ℝ) := pos_of_mul_pos_left hpos Real.two_pi_pos.le
  have hone : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by exact_mod_cast hn)
  nlinarith only [mul_nonneg (sub_nonneg.mpr hone) Real.two_pi_pos.le]

noncomputable def complexCorner (positive : Bool) (a b c : ℂ) : ℂ :=
  if positive then (starRingEnd ℂ) (b-a)*(c-a) else (b-a)*(starRingEnd ℂ) (c-a)

theorem physical_complex_corner (w : ℝ) (hw : 0 ≤ w) (s : Bool)
    (a b c : ℝ × ℝ) :
    physicalComplex w (weightedDot w (b-a) (c-a),
      if s then Type5.cross (b-a) (c-a) else -Type5.cross (b-a) (c-a)) =
    complexCorner s (physicalComplex w a) (physicalComplex w b) (physicalComplex w c) := by
  cases s <;> apply Complex.ext <;>
    simp only [complexCorner,ite_true,Bool.false_eq_true,ite_false,physicalComplex,weightedDot,
      Type5.cross,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      Complex.sub_re,Complex.sub_im,Prod.fst_sub,Prod.snd_sub] <;>
    ring_nf <;> rw [Real.sq_sqrt hw] <;> ring

theorem complexCorner_total (s : Bool) (a b c : ℂ)
    (h₁ : 0 < (complexCorner s a b c).im) (h₂ : 0 < (complexCorner s b c a).im)
    (h₃ : 0 < (complexCorner s c a b).im) :
    (complexCorner s a b c).arg+(complexCorner s b c a).arg+(complexCorner s c a b).arg =
      Real.pi := by
  let A := complexCorner s a b c
  let B := complexCorner s b c a
  let C := complexCorner s c a b
  have hu : b-a ≠ 0 := by
    intro hz
    simp [complexCorner,hz] at h₁
  have hv : c-b ≠ 0 := by
    intro hz
    simp [complexCorner,hz] at h₂
  have hw : a-c ≠ 0 := by
    intro hz
    simp [complexCorner,hz] at h₃
  let M := Complex.normSq (b-a)*Complex.normSq (c-b)*Complex.normSq (a-c)
  have hM : 0 < M := mul_pos (mul_pos (Complex.normSq_pos.mpr hu) (Complex.normSq_pos.mpr hv))
    (Complex.normSq_pos.mpr hw)
  have hprod : A*B*C = ((-M : ℝ) : ℂ) := by
    simp only [A,B,C,M,Complex.ofReal_neg,Complex.ofReal_mul,Complex.normSq_eq_conj_mul_self]
    have e₁ : c-a = -(a-c) := by abel
    have e₂ : a-b = -(b-a) := by abel
    have e₃ : b-c = -(c-b) := by abel
    cases s <;> simp only [complexCorner,ite_true,Bool.false_eq_true,ite_false] <;>
      rw [e₁,e₂,e₃] <;> (try simp only [map_neg]) <;> ring
  have hnA : A ≠ 0 := by intro h; exact h₁.ne' (congrArg Complex.im h)
  have hnB : B ≠ 0 := by intro h; exact h₂.ne' (congrArg Complex.im h)
  have hnC : C ≠ 0 := by intro h; exact h₃.ne' (congrArg Complex.im h)
  have harg : (A*B*C).arg = Real.pi := by rw [hprod,Complex.arg_ofReal_of_neg (neg_neg_of_pos hM)]
  let θ := A.arg+B.arg+C.arg
  have hang : (θ : Real.Angle) = (Real.pi : Real.Angle) := by
    have h := Complex.arg_mul_coe_angle (mul_ne_zero hnA hnB) hnC
    rw [harg,Complex.arg_mul_coe_angle hnA hnB] at h
    simpa only [θ,Real.Angle.coe_add] using h.symm
  have hzero : ((θ-Real.pi : ℝ) : Real.Angle) = 0 := by
    rw [Real.Angle.coe_sub,hang,sub_self]
  obtain ⟨n,hn⟩ := Real.Angle.coe_eq_zero_iff.mp hzero
  rw [zsmul_eq_mul] at hn
  have hθ₀ : 0 < θ := add_pos (add_pos (positiveArg h₁) (positiveArg h₂)) (positiveArg h₃)
  have hθ₁ : θ < 3*Real.pi := by
    have ha := Complex.arg_lt_pi_iff.mpr (Or.inr h₁.ne')
    have hb := Complex.arg_lt_pi_iff.mpr (Or.inr h₂.ne')
    have hc := Complex.arg_lt_pi_iff.mpr (Or.inr h₃.ne')
    dsimp [θ,A,B,C]
    linarith only [ha,hb,hc]
  have n₀ : ¬ n ≤ -1 := by
    intro h
    have h' : (n : ℝ) ≤ -1 := by exact_mod_cast h
    linarith only [hn,hθ₀,Real.pi_pos,mul_le_mul_of_nonneg_right h' Real.two_pi_pos.le]
  have n₁ : ¬ 1 ≤ n := by
    intro h
    have h' : (1 : ℝ) ≤ n := by exact_mod_cast h
    linarith only [hn,hθ₁,mul_le_mul_of_nonneg_right h' Real.two_pi_pos.le]
  have hn' : n = 0 := by omega
  change θ = Real.pi
  simpa [hn'] using (eq_of_sub_eq_zero (by simpa [hn'] using hn.symm) : θ = Real.pi)

private theorem rectangular_triangle_angle_sum (w : ℝ) (hw : 1 ≤ w) (f : Triangle × Bool)
    (hf : f ∈ orientedFaces) : ∑ i : Vertex, (physicalComplex w (cornerFactor w i f)).arg = Real.pi := by
  rcases f with ⟨⟨a,b,c⟩,s⟩
  have distinct : ∀ f : Triangle × Bool, f ∈ orientedFaces →
      f.1.1 ≠ f.1.2.1 ∧ f.1.1 ≠ f.1.2.2 ∧ f.1.2.1 ≠ f.1.2.2 := by decide +kernel
  obtain ⟨hab,hac,hbc⟩ := distinct ((a,b,c),s) hf
  let g (i : Vertex) := physicalComplex w (cornerFactor w i ((a,b,c),s))
  change ∑ i : Vertex, (g i).arg = Real.pi
  have ha : g a = complexCorner s (physicalComplex w (rectangularPoint w a))
      (physicalComplex w (rectangularPoint w b)) (physicalComplex w (rectangularPoint w c)) := by
    simpa [g,cornerFactor] using physical_complex_corner w (by linarith) s
      (rectangularPoint w a) (rectangularPoint w b) (rectangularPoint w c)
  have hb : g b = complexCorner s (physicalComplex w (rectangularPoint w b))
      (physicalComplex w (rectangularPoint w c)) (physicalComplex w (rectangularPoint w a)) := by
    simpa [g,cornerFactor,hab.symm] using physical_complex_corner w (by linarith) s
      (rectangularPoint w b) (rectangularPoint w c) (rectangularPoint w a)
  have hc : g c = complexCorner s (physicalComplex w (rectangularPoint w c))
      (physicalComplex w (rectangularPoint w a)) (physicalComplex w (rectangularPoint w b)) := by
    simpa [g,cornerFactor,hac.symm,hbc.symm] using physical_complex_corner w (by linarith) s
      (rectangularPoint w c) (rectangularPoint w a) (rectangularPoint w b)
  have ht : (g a).arg+(g b).arg+(g c).arg = Real.pi := by
    have ha₀ := rectangular_factor_im w hw a ((a,b,c),s) hf (by simp [triangleVertices])
    have hb₀ := rectangular_factor_im w hw b ((a,b,c),s) hf (by simp [triangleVertices])
    have hc₀ := rectangular_factor_im w hw c ((a,b,c),s) hf (by simp [triangleVertices])
    change 0 < (g a).im at ha₀
    change 0 < (g b).im at hb₀
    change 0 < (g c).im at hc₀
    rw [ha] at ha₀
    rw [hb] at hb₀
    rw [hc] at hc₀
    rw [ha,hb,hc]
    exact complexCorner_total s _ _ _ ha₀ hb₀ hc₀
  let vertices : Finset Vertex := {a,b,c}
  rw [← Finset.sum_subset (Finset.subset_univ vertices)]
  · have hs : ∑ i ∈ vertices, (g i).arg = (g a).arg+((g b).arg+(g c).arg) := by
      simp [vertices,Finset.sum_insert,hab,hac,hbc]
    rw [hs, ← add_assoc]
    exact ht
  · intro i _ hi
    have hn : i ≠ a ∧ i ≠ b ∧ i ≠ c := by simpa [vertices] using hi
    simp [g,cornerFactor,hn.1,hn.2.1,hn.2.2,physicalComplex_one]

private theorem sum_rectangular_angles (w : ℝ) (hw : 1 ≤ w) :
    ∑ i : Vertex, rectangularAngleSum w i = 16*Real.pi := by
  let g (i : Vertex) (f : Triangle × Bool) := (physicalComplex w (cornerFactor w i f)).arg
  have hsum (l : List (Triangle × Bool)) :
      ∑ i : Vertex, (l.map (g i)).sum = (l.map (fun f => ∑ i : Vertex, g i f)).sum := by
    induction l with
    | nil => simp
    | cons f l ih => simp [Finset.sum_add_distrib,ih]
  have hfaces : (orientedFaces.map (fun f => ∑ i : Vertex, g i f)) =
      orientedFaces.map (fun _ => Real.pi) := by
    apply List.map_congr_left
    exact rectangular_triangle_angle_sum w hw
  change ∑ i : Vertex, (orientedFaces.map (g i)).sum = _
  rw [hsum,hfaces]
  have hlen : orientedFaces.length = 16 := by decide +kernel
  rw [List.map_const',hlen,List.sum_replicate,nsmul_eq_mul]
  norm_num

/-- The certified base at every rectangular modulus has a full turn at each vertex. -/
theorem rectangular_cone_angle (w : ℝ) (hw : 1 ≤ w) (i : Vertex) :
    rectangularAngleSum w i = 2*Real.pi := by
  apply le_antisymm _ (rectangular_angle_sum_lower w hw i)
  by_contra! h
  have hs : ∑ _i : Vertex, (2*Real.pi) < ∑ j : Vertex, rectangularAngleSum w j :=
    Finset.sum_lt_sum (fun j _ => rectangular_angle_sum_lower w hw j) ⟨i,Finset.mem_univ _,h⟩
  rw [sum_rectangular_angles w hw] at hs
  norm_num [Finset.sum_const,nsmul_eq_mul] at hs
  linarith

open scoped InnerProductSpace

theorem complexCorner_arg_angle (s : Bool) (a b c : ℂ)
    (h : 0 < (complexCorner s a b c).im) :
    (complexCorner s a b c).arg = InnerProductGeometry.angle (b-a) (c-a) := by
  rw [Complex.arg_of_im_pos h]
  unfold InnerProductGeometry.angle
  congr 1
  cases s <;> simp only [complexCorner,Bool.false_eq_true,ite_false,ite_true,norm_mul,Complex.norm_conj] <;>
    congr 1 <;> simp only [Complex.inner,Complex.mul_re,Complex.conj_re,Complex.conj_im,
      Complex.sub_re,Complex.sub_im] <;> ring

/-- The Euclidean angle at the given corner of a rectangular base face, or zero
for a vertex absent from that face. -/
noncomputable def rectangularEuclideanCorner (w : ℝ) (i : Vertex) (f : Triangle) : ℝ :=
  let (a,b,c) := f
  let p v := physicalComplex w (rectangularPoint w v)
  if i = a then InnerProductGeometry.angle (p b-p a) (p c-p a)
  else if i = b then InnerProductGeometry.angle (p c-p b) (p a-p b)
  else if i = c then InnerProductGeometry.angle (p a-p c) (p b-p c)
  else 0

private theorem euclideanCorner_eq_arg (w : ℝ) (hw : 1 ≤ w) (i : Vertex) (f : Triangle × Bool)
    (hf : f ∈ orientedFaces) : rectangularEuclideanCorner w i f.1 =
      (physicalComplex w (cornerFactor w i f)).arg := by
  rcases f with ⟨⟨a,b,c⟩,s⟩
  have hco (u v t : Vertex) := physical_complex_corner w (by linarith) s
    (rectangularPoint w u) (rectangularPoint w v) (rectangularPoint w t)
  by_cases ha : i = a
  · subst i
    have h := rectangular_factor_im w hw a ((a,b,c),s) hf (by simp [triangleVertices])
    simp only [cornerFactor,ite_true] at h
    rw [hco a b c] at h
    simpa [rectangularEuclideanCorner,cornerFactor,hco a b c] using
      (complexCorner_arg_angle s _ _ _ h).symm
  by_cases hb : i = b
  · subst i
    have h := rectangular_factor_im w hw b ((a,b,c),s) hf (by simp [triangleVertices])
    simp [cornerFactor,ha] at h
    rw [hco b c a] at h
    simpa [rectangularEuclideanCorner,cornerFactor,ha,hco b c a] using
      (complexCorner_arg_angle s _ _ _ h).symm
  by_cases hc : i = c
  · subst i
    have h := rectangular_factor_im w hw c ((a,b,c),s) hf (by simp [triangleVertices])
    simp [cornerFactor,ha,hb] at h
    rw [hco c a b] at h
    simpa [rectangularEuclideanCorner,cornerFactor,ha,hb,hco c a b] using
      (complexCorner_arg_angle s _ _ _ h).symm
  · simp [rectangularEuclideanCorner,cornerFactor,ha,hb,hc,physicalComplex_one]

/-- The sum of the six Euclidean corner angles at every vertex is exactly two pi. -/
theorem rectangular_euclidean_cone_angle (w : ℝ) (hw : 1 ≤ w) (i : Vertex) :
    (orientedFaces.map fun f => rectangularEuclideanCorner w i f.1).sum = 2*Real.pi := by
  have he : (orientedFaces.map fun f => rectangularEuclideanCorner w i f.1) =
      orientedFaces.map fun f => (physicalComplex w (cornerFactor w i f)).arg := by
    apply List.map_congr_left
    exact euclideanCorner_eq_arg w hw i
  rw [he]
  exact rectangular_cone_angle w hw i

end OrigamiTorus.Type7
