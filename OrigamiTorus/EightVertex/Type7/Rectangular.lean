module

public import OrigamiTorus.EightVertex.Type6.Data
public import OrigamiTorus.Geometry.GenericLift
public import OrigamiTorus.Lattice.PlanarDevelopment
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

/-! The rational Type 7 planar family and its strict lift certificate at rectangular moduli. -/

@[expose] public section

namespace OrigamiTorus.Type7

def faces : List Triangle :=
  [(3,5,6), (3,2,5), (3,6,4), (3,0,2), (3,4,1), (3,1,0), (5,0,6), (5,2,4),
    (5,4,7), (5,7,0), (6,7,4), (6,0,1), (6,1,7), (2,1,4), (2,0,7), (2,7,1)]

def flippedFaces : List Triangle :=
  faces.filter (fun f => f != (3,5,6) && f != (3,2,5)) ++ [(6,3,2), (6,2,5)]

def type4Faces : List Triangle :=
  [(0,1,2), (0,3,1), (0,2,4), (0,5,3), (0,4,5), (1,5,2), (1,3,4), (1,4,6),
   (1,6,5), (2,6,4), (2,5,7), (2,7,6), (3,7,4), (3,5,6), (3,6,7), (4,7,5)]

def flipRelabeling : Vertex → Vertex := ![2,1,4,0,3,7,5,6]

def labelCode (f : Triangle) : Nat := 2^f.1.val + 2^f.2.1.val + 2^f.2.2.val

theorem flip_is_type4 :
    Function.Injective flipRelabeling ∧
    let after := flippedFaces.map (fun (a,b,c) =>
      2^(flipRelabeling a).val + 2^(flipRelabeling b).val + 2^(flipRelabeling c).val)
    let target := type4Faces.map labelCode
    after.all target.contains = true ∧ target.all after.contains = true := by
  decide +kernel

def disjointPairs (fs : List Triangle) : List (Edge × Triangle) :=
  (fs.flatMap faceEdges).eraseDups.flatMap fun e =>
    (fs.filter fun f => !(triangleVertices f).contains e.1 && !(triangleVertices f).contains e.2)
      |>.map (e, ·)

/-- The (x=0) bases from the PR, multiplied by the positive common denominator.
The physical second coordinate has the additional factor (y>0), where (w=y^2). -/
def rectangularPoint {R : Type*} [Field R] (w : R) : Vertex → R × R :=
  let H : R := 33 / 20
  let q : R := 33 / 13
  let d := 1 + q^2*w
  let t₃ := 73 / 40 - H*q*w
  let t₅ := H*q*w - 1
  ![(0,0), (73/60*d,11/10*d), (d/2,0), (t₃,H*d+q*t₃), (d,0),
    (d+t₅,q*t₅), (0,H*d), (d,H*d)]

def rectangularHeights {R : Type*} [Field R] : Vertex → R :=
  ![3/13,-3/8,-3/7,12/13,1,-1,1,0]

private abbrev Linear := ℚ × ℚ
private abbrev Quadratic := ℚ × ℚ × ℚ

private def eval1 (p : Linear) (h : ℝ) : ℝ := p.1 + p.2*h

private def eval2 (p : Quadratic) (h : ℝ) : ℝ := p.1 + p.2.1*h + p.2.2*h^2

private def times (p q : Linear) : Quadratic :=
  (p.1*q.1, p.1*q.2+p.2*q.1, p.2*q.2)

private theorem eval_times (p q : Linear) (h : ℝ) : eval2 (times p q) h = eval1 p h * eval1 q h := by
  simp [eval2, times, eval1]
  ring

private theorem eval_add (p q : Quadratic) (h : ℝ) : eval2 (p+q) h = eval2 p h + eval2 q h := by
  simp [eval2]
  ring

private theorem eval_sub (p q : Linear) (h : ℝ) : eval1 (p-q) h = eval1 p h - eval1 q h := by
  simp [eval1]
  ring

private def scale (a : ℚ) (p : Quadratic) : Quadratic :=
  (a*p.1, a*p.2.1, a*p.2.2)

private theorem eval_scale (a : ℚ) (p : Quadratic) (h : ℝ) : eval2 (scale a p) h = a * eval2 p h := by
  simp [eval2, scale]
  ring

private def xyCoeffs (v : Vertex) : Linear × Linear :=
  let atOne := rectangularPoint (1 : ℚ) v
  let atTwo := rectangularPoint (2 : ℚ) v
  ((atOne.1,atTwo.1-atOne.1), (atOne.2,atTwo.2-atOne.2))

set_option maxHeartbeats 1000000 in
private theorem rectangularPoint_eval (v : Vertex) (h : ℝ) :
    rectangularPoint (1+h) v = (eval1 (xyCoeffs v).1 h, eval1 (xyCoeffs v).2 h) := by
  fin_cases v <;> apply Prod.ext <;>
    norm_num [rectangularPoint, xyCoeffs, eval1] <;> ring

private def areaCoeffs (a b c : Vertex) : Quadratic :=
  times (xyCoeffs b).1 ((xyCoeffs c).2 - (xyCoeffs a).2) +
  times (xyCoeffs c).1 ((xyCoeffs a).2 - (xyCoeffs b).2) +
  times (xyCoeffs a).1 ((xyCoeffs b).2 - (xyCoeffs c).2)

private theorem area_eval (a b c : Vertex) (h : ℝ) :
    area (rectangularPoint (1+h)) a b c = eval2 (areaCoeffs a b c) h := by
  simp only [area, areaCoeffs, eval_add, eval_times, eval_sub, rectangularPoint_eval]

private def volCoeffs (z : Vertex → ℚ) (a b c d : Vertex) : Quadratic :=
  scale (-z a) (areaCoeffs b c d) + scale (z b) (areaCoeffs a c d) +
  scale (-z c) (areaCoeffs a b d) + scale (z d) (areaCoeffs a b c)

private theorem volume_eval (z : Vertex → ℚ) (a b c d : Vertex) (h : ℝ) :
    volume (rectangularPoint (1+h)) (fun v => (z v : ℝ)) a b c d =
      eval2 (volCoeffs z a b c d) h := by
  simp only [volume, volCoeffs, eval_add, eval_scale, area_eval, Rat.cast_neg]
  ring

private def coeffPositive (p : Quadratic) : Bool := decide (0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2)

private theorem coeffPositive_sound {p : Quadratic} (hp : coeffPositive p = true)
    {h : ℝ} (hh : 0 ≤ h) : 0 < eval2 p h := by
  simp only [coeffPositive, decide_eq_true_eq] at hp
  have h₀ : 0 < (p.1 : ℝ) := by exact_mod_cast hp.1
  have h₁ : 0 ≤ (p.2.1 : ℝ) := by exact_mod_cast hp.2.1
  have h₂ : 0 ≤ (p.2.2 : ℝ) := by exact_mod_cast hp.2.2
  unfold eval2
  positivity

private def signCert (p : Quadratic) : ℤ :=
  if coeffPositive p then 1 else if coeffPositive (scale (-1) p) then -1 else 0

private theorem pos_sound {p : Quadratic} (hp : 0 < signCert p)
    {h : ℝ} (hh : 0 ≤ h) : 0 < eval2 p h := by
  unfold signCert at hp
  split at hp
  · exact coeffPositive_sound ‹_› hh
  · split at hp <;> omega

private theorem neg_sound {p : Quadratic} (hp : signCert p < 0)
    {h : ℝ} (hh : 0 ≤ h) : eval2 p h < 0 := by
  unfold signCert at hp
  split at hp
  · omega
  · split at hp
    · have hf := coeffPositive_sound ‹coeffPositive (scale (-1) p) = true› hh
      simpa [eval_scale] using hf
    · omega

private theorem mul_pos_sound {p q : Quadratic} (hp : 0 < signCert p * signCert q)
    {h : ℝ} (hh : 0 ≤ h) : 0 < eval2 p h * eval2 q h := by
  rcases mul_pos_iff.mp hp with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · exact mul_pos (pos_sound hp hh) (pos_sound hq hh)
  · exact mul_pos_of_neg_of_neg (neg_sound hp hh) (neg_sound hq hh)

private theorem mul_neg_sound {p q : Quadratic} (hp : signCert p * signCert q < 0)
    {h : ℝ} (hh : 0 ≤ h) : eval2 p h * eval2 q h < 0 := by
  rcases mul_neg_iff.mp hp with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · exact mul_neg_of_pos_of_neg (pos_sound hp hh) (neg_sound hq hh)
  · exact mul_neg_of_neg_of_pos (neg_sound hp hh) (pos_sound hq hh)

private def sepCheck (pair : Edge × Triangle) : Bool :=
  let ((a,b), (c,d,e)) := pair
  let v a b c d := signCert (volCoeffs rectangularHeights a b c d)
  @decide (separates (v b c d e) (v a c d e) (v a b d e) (v a b c e) (v a b c d))
    (by unfold separates; infer_instance)

def faceChoice (flipped : Bool) : List Triangle := if flipped then flippedFaces else faces

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sepChecklist (flipped : Bool) : (disjointPairs (faceChoice flipped)).all sepCheck = true := by
  cases flipped <;> decide +kernel

private theorem height_cast (v : Vertex) :
    ((rectangularHeights v : ℚ) : ℝ) = rectangularHeights v := by
  fin_cases v <;> norm_num [rectangularHeights]

/-- Every disjoint edge and face admit a strict separating determinant witness at every
rectangular modulus, both with the original Type 7 faces and after the Type 4 flip. -/
theorem rectangular_separation (flipped : Bool) (w : ℝ) (hw : 1 ≤ w) :
    ∀ pair ∈ disjointPairs (faceChoice flipped), isSeparated (rectangularPoint w) rectangularHeights pair := by
  have hh : 0 ≤ w - 1 := sub_nonneg.mpr hw
  have he : 1 + (w-1) = w := by ring
  rintro ⟨⟨a,b⟩,c,d,e⟩ hpair
  have hc := (List.all_eq_true.mp (sepChecklist flipped)) _ hpair
  simp only [sepCheck, decide_eq_true_eq, separates] at hc
  have hv (i j k l : Vertex) := volume_eval rectangularHeights i j k l (w-1)
  simp only [height_cast, he] at hv
  simp only [isSeparated, separates, hv]
  rcases hc with hc | hc | hc | hc
  · exact Or.inl (mul_pos_sound hc hh)
  · exact Or.inr (Or.inl (mul_pos_sound hc hh))
  · exact Or.inr (Or.inr (Or.inl (mul_pos_sound hc hh)))
  · exact Or.inr (Or.inr (Or.inr (mul_neg_sound hc hh)))

private theorem flip_check :
    0 < signCert (areaCoeffs 3 5 6) ∧ signCert (areaCoeffs 3 5 2) < 0 ∧
      signCert (areaCoeffs 6 2 3) < 0 ∧ 0 < signCert (areaCoeffs 6 2 5) := by
  decide +kernel

theorem rectangular_flipSigns (w : ℝ) (hw : 1 ≤ w) :
    let p := rectangularPoint w
    0 < area p 3 5 6 ∧ area p 3 5 2 < 0 ∧ area p 6 2 3 < 0 ∧ 0 < area p 6 2 5 := by
  have hh : 0 ≤ w - 1 := sub_nonneg.mpr hw
  have he : 1 + (w-1) = w := by ring
  obtain ⟨ha,hb,hc,hd⟩ := flip_check
  have hv (i j k : Vertex) := area_eval i j k (w-1)
  simp only [he] at hv
  simp only [hv]
  exact ⟨pos_sound ha hh, neg_sound hb hh, neg_sound hc hh, pos_sound hd hh⟩


private def sortedTetrahedra : List Tetrahedron :=
  (List.finRange 8).flatMap fun a =>
    (List.finRange 8).flatMap fun b =>
      (List.finRange 8).flatMap fun c =>
        ((List.finRange 8).filter fun d => decide (a < b ∧ b < c ∧ c < d)).map (a,b,c,·)

private def areaCheck (q : Tetrahedron) : Bool :=
  let (a,b,c,d) := q
  [areaCoeffs b c d, areaCoeffs a c d, areaCoeffs a b d, areaCoeffs a b c].any
    (fun poly => signCert poly != 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem allAreaCheck : sortedTetrahedra.all areaCheck = true := by decide +kernel

private theorem areaCert_nonzero {a b c : Vertex} {w : ℝ} (hw : 1 ≤ w)
    (hc : signCert (areaCoeffs a b c) ≠ 0) : area (rectangularPoint w) a b c ≠ 0 := by
  have hh : 0 ≤ w - 1 := sub_nonneg.mpr hw
  have he : 1 + (w-1) = w := by ring
  rw [← he, area_eval]
  rcases lt_or_gt_of_ne hc with hn | hp
  · exact ne_of_lt (neg_sound hn hh)
  · exact ne_of_gt (pos_sound hp hh)

theorem rectangular_noncollinear (w : ℝ) (hw : 1 ≤ w) (a b c d : Vertex)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    let p := rectangularPoint w
    area p b c d ≠ 0 ∨ area p a c d ≠ 0 ∨ area p a b d ≠ 0 ∨ area p a b c ≠ 0 := by
  have hm : (a,b,c,d) ∈ sortedTetrahedra := by simp [sortedTetrahedra, hab,hbc,hcd]
  have hh := (List.all_eq_true.mp allAreaCheck) _ hm
  change ([areaCoeffs b c d, areaCoeffs a c d, areaCoeffs a b d, areaCoeffs a b c].any
    (fun poly => signCert poly != 0)) = true at hh
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, bne_iff_ne] at hh
  rcases hh with hh | hh | hh | hh
  · exact Or.inl (areaCert_nonzero hw hh)
  · exact Or.inr (Or.inl (areaCert_nonzero hw hh))
  · exact Or.inr (Or.inr (Or.inl (areaCert_nonzero hw hh)))
  · exact Or.inr (Or.inr (Or.inr (areaCert_nonzero hw hh)))

/-- At every rectangular modulus, the Type 7 and flipped Type 4 planar bases
have generic lifts with strict separation of disjoint edges and faces. -/
theorem rectangular_generic_lift (flipped : Bool) (w : ℝ) (hw : 1 ≤ w) :
    let p := rectangularPoint w
    ∃ z : Vertex → ℝ, GenericLift p z ∧
      ∀ pair ∈ disjointPairs (faceChoice flipped), isSeparated p z pair := by
  obtain ⟨z',h'⟩ := exists_generic_lift_of_noncollinear _ (rectangular_noncollinear w hw)
  exact exists_generic_separating_lift _ rectangularHeights z' _ h' (rectangular_separation flipped w hw)

def orientedFaces : List (Triangle × Bool) :=
  faces.zip [true,true,false,true,true,false,false,true,false,true,false,true,true,false,false,false]

private def faceRegularity (f : Triangle × Bool) : Bool :=
  let ((a,b,c),positive) := f
  signCert (areaCoeffs a b c) == (if positive then 1 else -1)

private theorem rectangular_face_orientation_of_check (w : ℝ) (hw : 1 ≤ w) (f : Triangle)
    (positive : Bool) (hh : faceRegularity (f,positive) = true) :
    let p := rectangularPoint w
    let a := area p f.1 f.2.1 f.2.2
    if positive then 0 < a else a < 0 := by
  rcases f with ⟨a,b,c⟩
  have he : 1+(w-1) = w := by ring
  have hp := area_eval a b c (w-1)
  rw [he] at hp
  cases positive
  · have hn : signCert (areaCoeffs a b c) = -1 := by simpa [faceRegularity] using hh
    simp only [Bool.false_eq_true,ite_false]
    rw [hp]
    exact neg_sound (by rw [hn]; norm_num) (sub_nonneg.mpr hw)
  · have hpos : signCert (areaCoeffs a b c) = 1 := by simpa [faceRegularity] using hh
    simp only [ite_true]
    rw [hp]
    exact pos_sound (by rw [hpos]; norm_num) (sub_nonneg.mpr hw)

theorem rectangular_face_orientation (w : ℝ) (hw : 1 ≤ w) (f : Triangle)
    (positive : Bool) (hm : (f,positive) ∈ orientedFaces) :
    let p := rectangularPoint w
    let a := area p f.1 f.2.1 f.2.2
    if positive then 0 < a else a < 0 := by
  have hc : orientedFaces.all faceRegularity = true := by decide +kernel
  exact rectangular_face_orientation_of_check w hw f positive ((List.all_eq_true.mp hc) _ hm)

def orientedFlippedFaces : List (Triangle × Bool) :=
  orientedFaces.filter (fun f => f.1 != (3,5,6) && f.1 != (3,2,5)) ++
    [((6,3,2),true),((6,2,5),true)]

theorem rectangular_flipped_face_orientation (w : ℝ) (hw : 1 ≤ w) (f : Triangle)
    (positive : Bool) (hm : (f,positive) ∈ orientedFlippedFaces) :
    let p := rectangularPoint w
    let a := area p f.1 f.2.1 f.2.2
    if positive then 0 < a else a < 0 := by
  have hc : orientedFlippedFaces.all faceRegularity = true := by decide +kernel
  exact rectangular_face_orientation_of_check w hw f positive ((List.all_eq_true.mp hc) _ hm)

def multiplyComplex {R : Type*} [Ring R] (w : R) (a b : R × R) : R × R :=
  (a.1*b.1-w*a.2*b.2,a.1*b.2+a.2*b.1)

def cornerFactor {R : Type*} [Field R] (w : R) (i : Vertex) (f : Triangle × Bool) : R × R :=
  let ((a,b,c),pos) := f
  let p := rectangularPoint w
  let pair := if i = a then some (b,c) else if i = b then some (c,a)
    else if i = c then some (a,b) else none
  match pair with
  | none => (1,0)
  | some (j,k) =>
    let u := p j-p i
    let v := p k-p i
    (weightedDot w u v, if pos then Type5.cross u v else -Type5.cross u v)

/-- The factors are the dot and signed cross products at the successive corners
incident to the vertex, with the imaginary coordinate scaled by the rectangle height. -/
def rectangularCornerProduct {R : Type*} [Field R] (w : R) (i : Vertex) : R × R :=
  orientedFaces.foldl (fun c f => multiplyComplex w c (cornerFactor w i f)) (1,0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem rectangular_corner_product_real (w : ℝ) (i : Vertex) :
    (rectangularCornerProduct w i).2 = 0 := by
  fin_cases i <;>
    norm_num [rectangularCornerProduct,orientedFaces,faces,cornerFactor,multiplyComplex,
      rectangularPoint,weightedDot,Type5.cross,List.foldl_cons] <;> ring

theorem rectangular_corner_product_square_positive (i : Vertex) :
    0 < (rectangularCornerProduct (1 : ℝ) i).1 := by
  fin_cases i <;>
    norm_num [rectangularCornerProduct,orientedFaces,faces,cornerFactor,multiplyComplex,
      rectangularPoint,weightedDot,Type5.cross,List.foldl_cons]

private theorem cross_eq_area (p : Vertex → ℝ × ℝ) (a b c : Vertex) :
    Type5.cross (p b-p a) (p c-p a) = area p a b c := by
  simp only [area,Type5.cross,Prod.fst_sub,Prod.snd_sub]
  ring

private theorem area_cycle (p : Vertex → ℝ × ℝ) (a b c : Vertex) :
    area p b c a = area p a b c := by
  unfold area
  ring

private theorem face_area_ne (w : ℝ) (hw : 1 ≤ w) (f : Triangle) (s : Bool)
    (hf : (f,s) ∈ orientedFaces) :
    area (rectangularPoint w) f.1 f.2.1 f.2.2 ≠ 0 := by
  have hh := rectangular_face_orientation w hw f s hf
  cases s
  · exact hh.ne
  · exact hh.ne'

private def cornerSquare (w : ℝ) (a : ℝ × ℝ) : ℝ := a.1^2+w*a.2^2

private theorem cornerSquare_mul (w : ℝ) (a b : ℝ × ℝ) :
    cornerSquare w (multiplyComplex w a b) = cornerSquare w a*cornerSquare w b := by
  simp only [cornerSquare,multiplyComplex]
  ring

private theorem cornerSquare_factor (w : ℝ) (hw : 1 ≤ w) (i : Vertex) (f : Triangle × Bool)
    (hf : f ∈ orientedFaces) : 0 < cornerSquare w (cornerFactor w i f) := by
  rcases f with ⟨⟨a,b,c⟩,s⟩
  have hA := face_area_ne w hw (a,b,c) s hf
  have hB : area (rectangularPoint w) b c a ≠ 0 := by rw [area_cycle]; exact hA
  have hC : area (rectangularPoint w) c a b ≠ 0 := by
    rw [area_cycle (rectangularPoint w) b c a,area_cycle (rectangularPoint w) a b c]
    exact hA
  have hw' : 0 < w := by linarith
  have hb : (cornerFactor w i ((a,b,c),s)).2 = 0 →
      cornerFactor w i ((a,b,c),s) = (1,0) := by
    intro hz
    by_cases ha : i = a
    · cases s <;> simp [cornerFactor,ha,cross_eq_area,hA] at hz
    by_cases hb : i = b
    · subst i
      cases s <;> simp [cornerFactor,ha,cross_eq_area,hB] at hz
    by_cases hc : i = c
    · subst i
      cases s <;> simp [cornerFactor,ha,hb,cross_eq_area,hC] at hz
    · simp [cornerFactor,ha,hb,hc]
  by_cases h : (cornerFactor w i ((a,b,c),s)).2 = 0
  · simp [hb h,cornerSquare]
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hw' (sq_pos_of_ne_zero h))

private theorem fold_cornerSquare_pos (w : ℝ) (i : Vertex) (l : List (Triangle × Bool))
    (h : ∀ f ∈ l, 0 < cornerSquare w (cornerFactor w i f)) (a : ℝ × ℝ)
    (ha : 0 < cornerSquare w a) :
    0 < cornerSquare w (l.foldl (fun c f => multiplyComplex w c (cornerFactor w i f)) a) := by
  induction l generalizing a with
  | nil => exact ha
  | cons f l ih =>
    apply ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    rw [cornerSquare_mul]
    exact mul_pos ha (h f List.mem_cons_self)

private theorem rectangular_product_continuous (i : Vertex) :
    Continuous (fun w : ℝ => (rectangularCornerProduct w i).1) := by
  have hp (v : Vertex) : Continuous (fun w : ℝ => rectangularPoint w v) := by
    fin_cases v <;> norm_num [rectangularPoint] <;> first | fun_prop | constructor <;> fun_prop
  have hf (f : Triangle × Bool) : Continuous (fun w : ℝ => cornerFactor w i f) := by
    rcases f with ⟨⟨a,b,c⟩,s⟩
    by_cases ia : i=a
    · subst i
      cases s <;> simp [cornerFactor,weightedDot,Type5.cross] <;>
        first | fun_prop | constructor <;> fun_prop
    by_cases ib : i=b
    · subst i
      cases s <;> simp [cornerFactor,ia,weightedDot,Type5.cross] <;>
        first | fun_prop | constructor <;> fun_prop
    by_cases ic : i=c
    · subst i
      cases s <;> simp [cornerFactor,ia,ib,weightedDot,Type5.cross] <;>
        first | fun_prop | constructor <;> fun_prop
    cases s <;>
      simp [cornerFactor,ia,ib,ic,weightedDot,Type5.cross] <;> first | fun_prop | constructor <;> fun_prop
  have hfold (l : List (Triangle × Bool)) (a : ℝ → ℝ × ℝ) (ha : Continuous a) :
      Continuous (fun w : ℝ => l.foldl (fun c f => multiplyComplex w c (cornerFactor w i f)) (a w)) := by
    induction l generalizing a with
    | nil => exact ha
    | cons f l ih =>
      exact ih (fun w => multiplyComplex w (a w) (cornerFactor w i f))
        (by unfold multiplyComplex; fun_prop)
  exact (hfold orientedFaces (fun _ => (1,0)) continuous_const).fst

theorem rectangular_corner_product_positive (w : ℝ) (hw : 1 ≤ w) (i : Vertex) :
    0 < (rectangularCornerProduct w i).1 := by
  let f : ℝ → ℝ := fun s => (rectangularCornerProduct s i).1
  have hne (s : ℝ) (hs : 1 ≤ s) : f s ≠ 0 := by
    have hh := fold_cornerSquare_pos s i orientedFaces (fun g hg => cornerSquare_factor s hs i g hg)
      (1,0) (by norm_num [cornerSquare])
    change 0 < cornerSquare s (rectangularCornerProduct s i) at hh
    intro h
    simp [cornerSquare,rectangular_corner_product_real,show (rectangularCornerProduct s i).1 = 0 from h] at hh
  by_contra! hn
  have h0 : 0 ∈ Set.Icc (f w) (f 1) :=
    ⟨hn,(rectangular_corner_product_square_positive i).le⟩
  obtain ⟨s,hs,he⟩ := isPreconnected_Ici.intermediate_value (s := Set.Ici (1 : ℝ)) hw (by simp)
    (rectangular_product_continuous i).continuousOn h0
  exact hne s hs he

end OrigamiTorus.Type7
