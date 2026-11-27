module

public import OrigamiTorus.Type6Data
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Coordinate elimination for the Type 5 radical reconstruction. -/

@[expose] public section

namespace OrigamiTorus.Type5

abbrev Plane (R : Type*) := R × R
abbrev Space (R : Type*) := R × R × R

def dot {R : Type*} [Ring R] (u v : Plane R) : R := u.1*v.1 + u.2*v.2

def cross {R : Type*} [Ring R] (u v : Plane R) : R := u.1*v.2 - u.2*v.1

def linearSolve {R : Type*} [Field R] (u v : Plane R) (a b : R) : Plane R :=
  ((a*v.2 - u.2*b) / cross u v, (u.1*b - a*v.1) / cross u v)

theorem linearSolve_spec {u v : Plane ℝ} (h : cross u v ≠ 0) (a b : ℝ) :
    dot u (linearSolve u v a b) = a ∧ dot v (linearSolve u v a b) = b := by
  unfold cross at h
  simp only [linearSolve, dot, cross]
  constructor
  · calc
      _ = (a*(u.1*v.2-u.2*v.1))/(u.1*v.2-u.2*v.1) := by
        simp only [mul_div_assoc, ← add_div]
        congr 1
        ring
      _ = a := mul_div_cancel_right₀ _ h
  · calc
      _ = (b*(u.1*v.2-u.2*v.1))/(u.1*v.2-u.2*v.1) := by
        simp only [mul_div_assoc, ← add_div]
        congr 1
        ring
      _ = b := mul_div_cancel_right₀ _ h

def horizontal {R : Type*} (p : Space R) : Plane R := (p.1,p.2.1)
def atHeight {R : Type*} (p : Plane R) (z : R) : Space R := (p.1,p.2,z)

def squared2 {R : Type*} [Ring R] (p : Plane R) : R := dot p p
def squared3 {R : Type*} [Ring R] (p : Space R) : R := squared2 (horizontal p) + p.2.2^2
def dot3 {R : Type*} [Ring R] (u v : Space R) : R := dot (horizontal u) (horizontal v) + u.2.2*v.2.2

/-- Remove the common origin-anchor equation from an edge length equation. -/
theorem edgeEquation_iff (u s : Plane ℝ) (v r : Space ℝ) (h0 : squared3 v = squared2 u) :
    squared3 (v-r) = squared2 (u-s) ↔
      dot3 r v - dot s u = (squared3 r - squared2 s)/2 := by
  simp only [squared3, squared2, dot3, horizontal, dot, Prod.fst_sub, Prod.snd_sub] at h0 ⊢
  constructor <;> intro h <;> nlinarith only [h, h0]

def anchorRhs {R : Type*} [Field R] (r s u : Plane R) : R :=
  dot s u + (squared2 r - squared2 s)/2

/-- Planar part determined by the two subtracted anchor equations. -/
def projection {R : Type*} [Field R] (r₂ r₅ s₂ s₅ u : Plane R) : Plane R :=
  linearSolve r₂ r₅ (anchorRhs r₂ s₂ u) (anchorRhs r₅ s₅ u)

def rootRadicand {R : Type*} [Field R] (r₂ r₅ s₂ s₅ u : Plane R) : R :=
  squared2 u - squared2 (projection r₂ r₅ s₂ s₅ u)

noncomputable def signedRoot (positiveBranch : Bool) (d : ℝ) : ℝ :=
  if positiveBranch then Real.sqrt d else -Real.sqrt d

theorem signedRoot_sq (positiveBranch : Bool) {d : ℝ} (hd : 0 ≤ d) :
    signedRoot positiveBranch d ^ 2 = d := by
  cases positiveBranch <;> simp [signedRoot, Real.sq_sqrt hd]

noncomputable def makeRoot (r₂ r₅ s₂ s₅ u : Plane ℝ) (positiveBranch : Bool) : Space ℝ :=
  atHeight (projection r₂ r₅ s₂ s₅ u)
    (signedRoot positiveBranch (rootRadicand r₂ r₅ s₂ s₅ u))

/-- The radical root satisfies all three origin and anchor equations. -/
theorem makeRoot_edges (r₂ r₅ s₂ s₅ u : Plane ℝ) (positiveBranch : Bool)
    (hanchor : cross r₂ r₅ ≠ 0) (hrad : 0 ≤ rootRadicand r₂ r₅ s₂ s₅ u) :
    let r := makeRoot r₂ r₅ s₂ s₅ u positiveBranch
    squared3 r = squared2 u ∧
    squared3 (r - atHeight r₂ 0) = squared2 (u-s₂) ∧
    squared3 (r - atHeight r₅ 0) = squared2 (u-s₅) := by
  let v := projection r₂ r₅ s₂ s₅ u
  let z := signedRoot positiveBranch (rootRadicand r₂ r₅ s₂ s₅ u)
  change squared3 (atHeight v z) = squared2 u ∧
    squared3 (atHeight v z - atHeight r₂ 0) = squared2 (u-s₂) ∧
    squared3 (atHeight v z - atHeight r₅ 0) = squared2 (u-s₅)
  have hz := signedRoot_sq positiveBranch hrad
  have h0 : squared3 (atHeight v z) = squared2 u := by
    change squared2 v + z^2 = squared2 u
    rw [show z^2 = squared2 u - squared2 v from hz]
    ring
  obtain ⟨ha,hb⟩ := linearSolve_spec hanchor (anchorRhs r₂ s₂ u) (anchorRhs r₅ s₅ u)
  refine ⟨h0, (edgeEquation_iff _ _ _ _ h0).mpr ?_, (edgeEquation_iff _ _ _ _ h0).mpr ?_⟩
  · change dot r₂ v + 0*z - dot s₂ u = (squared2 r₂ + (0 : ℝ)^2 - squared2 s₂)/2
    have ha' : dot r₂ v = dot s₂ u + (squared2 r₂ - squared2 s₂)/2 := ha
    linarith only [ha']
  · change dot r₅ v + 0*z - dot s₅ u = (squared2 r₅ + (0 : ℝ)^2 - squared2 s₅)/2
    have hb' : dot r₅ v = dot s₅ u + (squared2 r₅ - squared2 s₅)/2 := hb
    linarith only [hb']

def discriminant {R : Type*} [Ring R] (a b c : R) : R := b^2 - 4*a*c

noncomputable def quadraticRoot (a b c : ℝ) (positiveBranch : Bool) : ℝ :=
  (-b + signedRoot positiveBranch (discriminant a b c))/(2*a)

theorem quadraticRoot_spec (a b c : ℝ) (positiveBranch : Bool) (ha : a ≠ 0)
    (hd : 0 ≤ discriminant a b c) :
    let t := quadraticRoot a b c positiveBranch
    a*t^2 + b*t + c = 0 := by
  have hs := signedRoot_sq positiveBranch hd
  simp only [quadraticRoot]
  field_simp [ha]
  simp only [discriminant] at hs ⊢
  linear_combination hs

/-- A nonzero polynomial of degree at most two cannot have three distinct real roots. -/
theorem three_roots_force_zero {a b c x y z : ℝ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : a*x^2 + b*x + c = 0) (hy : a*y^2 + b*y + c = 0)
    (hz : a*z^2 + b*z + c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have h₁ : (x-y) * (a*(x+y)+b) = 0 := by linear_combination hx-hy
  have h₂ : (x-z) * (a*(x+z)+b) = 0 := by linear_combination hx-hz
  have h₁' := (mul_eq_zero.mp h₁).resolve_left (sub_ne_zero.mpr hxy)
  have h₂' := (mul_eq_zero.mp h₂).resolve_left (sub_ne_zero.mpr hxz)
  have h₃ : a*(y-z) = 0 := by linear_combination h₁'-h₂'
  have ha := (mul_eq_zero.mp h₃).resolve_right (sub_ne_zero.mpr hyz)
  subst a
  simp_all

/-- Type 5 in Lutz numbering. Vertices 1, 2 and 5 are the anchors. -/
def faces : List Triangle :=
  [(0,1,2), (0,3,1), (0,2,4), (0,5,3), (0,4,5), (1,5,2), (1,3,6), (1,6,4),
    (1,4,7), (1,7,5), (2,6,3), (2,3,7), (2,7,4), (2,5,6), (3,5,7), (4,6,5)]

def anchors : List Vertex := [1,2,5]
def roots : List Vertex := [3,4]
def leaves : List Vertex := [0,6,7]

def edgeList : List Edge := (faces.flatMap faceEdges).eraseDups

/-- The Type 5 graph is the join of the anchor triangle with the complete bipartite
graph on the two roots and three leaves. -/
theorem edges_from_anchor_root_leaf (u v : Vertex) :
    (edgeList.contains (orderedEdge u v) = true) ↔
      u ≠ v ∧ (u ∈ anchors ∨ v ∈ anchors ∨
        (u ∈ roots ∧ v ∈ leaves) ∨ (v ∈ roots ∧ u ∈ leaves)) := by
  fin_cases u <;> fin_cases v <;> decide +kernel

/-- The oriented link cycles of the eight vertices in the square construction. -/
def orientedLinkCycle : Vertex → List Vertex :=
  ![[1,2,4,5,3], [0,3,6,4,7,5,2], [0,1,5,6,3,7,4], [0,5,7,2,6,1],
    [0,2,7,1,6,5], [0,4,6,2,1,7,3], [1,3,2,5,4], [1,4,2,3,5]]

def linkFromFaces (v : Vertex) : List Edge :=
  faces.filterMap fun (a,b,c) =>
    if v = a then some (b,c) else if v = b then some (c,a)
    else if v = c then some (a,b) else none

def directedCycleEdges (ns : List Vertex) : List Edge :=
  ns.zip (ns.drop 1 ++ ns.take 1)

/-- Each face star has the listed simple cyclic link, with the orientations induced
by the faces. -/
theorem linkCycles_checked (v : Vertex) :
    let ns := orientedLinkCycle v
    let cyclic := directedCycleEdges ns
    let found := linkFromFaces v
    ns.Nodup ∧ 3 ≤ ns.length ∧ cyclic.all found.contains = true ∧ found.all cyclic.contains = true := by
  fin_cases v <;> decide +kernel


def smul2 {R : Type*} [Ring R] (a : R) (v : Plane R) : Plane R := (a*v.1,a*v.2)
def smul3 {R : Type*} [Ring R] (a : R) (v : Space R) : Space R :=
  atHeight (smul2 a (horizontal v)) (a*v.2.2)

/-- The horizontal part of a leaf is affine in its intrinsic position. The last
two linear equations are (z_i z = a_imathbin{\cdot}u+b_i) for the roots. -/
structure LeafData (R : Type*) where
  base : Plane R
  colX : Plane R
  colY : Plane R
  a₃ : Plane R
  a₄ : Plane R
  b₃ : R
  b₄ : R
  z₃ : R
  z₄ : R

def LeafData.planarLin {R : Type*} [Ring R] (p : LeafData R) (u : Plane R) : Plane R :=
  smul2 u.1 p.colX + smul2 u.2 p.colY

def LeafData.lineNormal {R : Type*} [Ring R] (p : LeafData R) : Plane R :=
  smul2 p.z₄ p.a₃ - smul2 p.z₃ p.a₄

def LeafData.lineOffset {R : Type*} [Ring R] (p : LeafData R) : R :=
  p.z₄*p.b₃ - p.z₃*p.b₄

def LeafData.intrinsicBase {R : Type*} [Field R] (p : LeafData R) : Plane R :=
  smul2 (-p.lineOffset/squared2 p.lineNormal) p.lineNormal

def LeafData.intrinsicDirection {R : Type*} [Field R] (p : LeafData R) : Plane R :=
  (-p.lineNormal.2,p.lineNormal.1)

def LeafData.extrinsicBase {R : Type*} [Field R] (p : LeafData R) : Space R :=
  atHeight (p.planarLin p.intrinsicBase + p.base)
    ((dot p.a₃ p.intrinsicBase + p.b₃)/p.z₃)

def LeafData.extrinsicDirection {R : Type*} [Field R] (p : LeafData R) : Space R :=
  atHeight (p.planarLin p.intrinsicDirection) (dot p.a₃ p.intrinsicDirection/p.z₃)

def LeafData.quadratic {R : Type*} [Field R] (p : LeafData R) : R × R × R :=
  let u₀ := p.intrinsicBase
  let du := p.intrinsicDirection
  let v₀ := p.extrinsicBase
  let dv := p.extrinsicDirection
  (squared3 dv - squared2 du, 2*(dot3 v₀ dv - dot u₀ du), squared3 v₀ - squared2 u₀)

def LeafData.intrinsicAt {R : Type*} [Field R] (p : LeafData R) (t : R) : Plane R :=
  p.intrinsicBase + smul2 t p.intrinsicDirection

def LeafData.extrinsicAt {R : Type*} [Field R] (p : LeafData R) (t : R) : Space R :=
  p.extrinsicBase + smul3 t p.extrinsicDirection

theorem LeafData.quadratic_eq (p : LeafData ℝ) (t : ℝ) :
    squared3 (p.extrinsicAt t) - squared2 (p.intrinsicAt t) =
      p.quadratic.1*t^2 + p.quadratic.2.1*t + p.quadratic.2.2 := by
  simp only [LeafData.intrinsicAt, LeafData.extrinsicAt, LeafData.quadratic, squared3, squared2,
    dot, dot3, horizontal, smul3, smul2, atHeight, Prod.fst_add, Prod.snd_add]
  ring

theorem LeafData.onLine {p : LeafData ℝ} (hn : squared2 p.lineNormal ≠ 0) (t : ℝ) :
    dot p.lineNormal (p.intrinsicAt t) + p.lineOffset = 0 := by
  let n := p.lineNormal
  let m := p.lineOffset
  have hs : dot n (smul2 (-m / squared2 n) n) = (-m / squared2 n) * squared2 n := by
    simp [dot, smul2, squared2]
    ring
  have hd : dot n (smul2 t (-n.2,n.1)) = 0 := by
    simp [dot,smul2]
    ring
  calc
    _ = dot n (smul2 (-m / squared2 n) n) + dot n (smul2 t (-n.2,n.1)) + m := by
      simp [LeafData.intrinsicAt, LeafData.intrinsicBase, LeafData.intrinsicDirection, n, m, dot]
      ring
    _ = 0 := by rw [hs, hd, div_mul_cancel₀ _ hn]; ring

theorem LeafData.linear_equations {p : LeafData ℝ} (hz : p.z₃ ≠ 0)
    (hn : squared2 p.lineNormal ≠ 0) (t : ℝ) :
    let u := p.intrinsicAt t
    let v := p.extrinsicAt t
    horizontal v = p.planarLin u + p.base ∧
    p.z₃*v.2.2 = dot p.a₃ u + p.b₃ ∧
    p.z₄*v.2.2 = dot p.a₄ u + p.b₄ := by
  let u := p.intrinsicAt t
  let v := p.extrinsicAt t
  change horizontal v = p.planarLin u + p.base ∧ p.z₃*v.2.2 = dot p.a₃ u + p.b₃ ∧
    p.z₄*v.2.2 = dot p.a₄ u + p.b₄
  have h3 : p.z₃*v.2.2 = dot p.a₃ u + p.b₃ := by
    simp [u, v, LeafData.extrinsicAt, LeafData.extrinsicBase, LeafData.extrinsicDirection,
      LeafData.intrinsicAt, smul3, smul2, atHeight, dot]
    field_simp [hz]
    ring
  have hline := p.onLine hn t
  have heq : p.z₄*(dot p.a₃ u+p.b₃) - p.z₃*(dot p.a₄ u+p.b₄) = 0 := by
    simp [u, LeafData.lineNormal, LeafData.lineOffset, dot, smul2] at hline ⊢
    linear_combination hline
  refine ⟨?_,h3,?_⟩
  · apply Prod.ext <;>
      simp [u, v, LeafData.extrinsicAt, LeafData.extrinsicBase, LeafData.extrinsicDirection,
        LeafData.planarLin, LeafData.intrinsicAt, horizontal, smul2, smul3, atHeight] <;>
      ring
  · apply (mul_left_cancel₀ hz)
    linear_combination p.z₄*h3 + heq

/-- Each radical branch solves the leaf norm equation and all its linear equations. -/
theorem LeafData.branch_sound (p : LeafData ℝ) (positiveBranch : Bool) (hz : p.z₃ ≠ 0)
    (hn : squared2 p.lineNormal ≠ 0) (ha : p.quadratic.1 ≠ 0)
    (hd : 0 ≤ discriminant p.quadratic.1 p.quadratic.2.1 p.quadratic.2.2) :
    let t := quadraticRoot p.quadratic.1 p.quadratic.2.1 p.quadratic.2.2 positiveBranch
    let u := p.intrinsicAt t
    let v := p.extrinsicAt t
    squared3 v = squared2 u ∧ horizontal v = p.planarLin u + p.base ∧
      p.z₃*v.2.2 = dot p.a₃ u + p.b₃ ∧ p.z₄*v.2.2 = dot p.a₄ u + p.b₄ := by
  let t := quadraticRoot p.quadratic.1 p.quadratic.2.1 p.quadratic.2.2 positiveBranch
  refine ⟨sub_eq_zero.mp ?_,p.linear_equations hz hn t⟩
  rw [LeafData.quadratic_eq]
  exact quadraticRoot_spec _ _ _ positiveBranch ha hd

/-- A genuine eliminated affine equation is parametrized by its perpendicular direction.
The root with nonzero height then determines the extrinsic leaf uniquely. -/
theorem LeafData.parameterization (p : LeafData ℝ) (hz : p.z₃ ≠ 0)
    (hn : squared2 p.lineNormal ≠ 0) (u : Plane ℝ) (v : Space ℝ)
    (hxy : horizontal v = p.planarLin u + p.base)
    (h₃ : p.z₃*v.2.2 = dot p.a₃ u + p.b₃)
    (h₄ : p.z₄*v.2.2 = dot p.a₄ u + p.b₄) :
    ∃ t : ℝ, u = p.intrinsicAt t ∧ v = p.extrinsicAt t := by
  let n := p.lineNormal
  let m := p.lineOffset
  have hl : dot n u + m = 0 := by
    simp only [n,m,LeafData.lineNormal,LeafData.lineOffset,dot,smul2,Prod.fst_sub,Prod.snd_sub]
    simp only [dot] at h₃ h₄
    linear_combination -p.z₄*h₃+p.z₃*h₄
  let t := cross n u / squared2 n
  have hi : u = p.intrinsicAt t := by
    have hn' : squared2 n ≠ 0 := hn
    apply Prod.ext
    · change u.1 = (-m/squared2 n)*n.1 + (cross n u/squared2 n)*(-n.2)
      field_simp [hn']
      simp only [squared2,dot,cross] at hl ⊢
      linear_combination n.1*hl
    · change u.2 = (-m/squared2 n)*n.2 + (cross n u/squared2 n)*n.1
      field_simp [hn']
      simp only [squared2,dot,cross] at hl ⊢
      linear_combination n.2*hl
  obtain ⟨hp,hheight,_⟩ := p.linear_equations hz hn t
  have hhor := hxy.trans ((congrArg (fun u => p.planarLin u + p.base) hi).trans hp.symm)
  have hvert : v.2.2 = (p.extrinsicAt t).2.2 := by
    apply mul_left_cancel₀ hz
    exact h₃.trans ((congrArg (fun u => dot p.a₃ u + p.b₃) hi).trans hheight.symm)
  have hx : v.1 = (p.extrinsicAt t).1 := congrArg (fun q : Plane ℝ => q.1) hhor
  have hy : v.2.1 = (p.extrinsicAt t).2.1 := congrArg (fun q : Plane ℝ => q.2) hhor
  exact ⟨t,hi,Prod.ext hx (Prod.ext hy hvert)⟩

/-- The two radical candidates for a quadratic, or the single candidate for a linear equation. -/
noncomputable def polynomialCandidates (a b c : ℝ) : List ℝ := by
  classical
  exact if a ≠ 0 then [quadraticRoot a b c false,quadraticRoot a b c true]
    else if b ≠ 0 then [-c/b] else []

theorem polynomialCandidates_length (a b c : ℝ) : (polynomialCandidates a b c).length ≤ 2 := by
  classical
  unfold polynomialCandidates
  split
  · simp
  · split <;> simp

theorem polynomialCandidates_complete (a b c t : ℝ) (h : a*t^2+b*t+c = 0)
    (hn : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) : t ∈ polynomialCandidates a b c := by
  classical
  by_cases ha : a ≠ 0
  · have hh : (2*a*t+b)^2 = discriminant a b c := by
      unfold discriminant
      linear_combination 4*a*h
    have hd : 0 ≤ discriminant a b c := hh ▸ sq_nonneg _
    have hr := Real.sq_sqrt hd
    have hv : (2*a*t+b - Real.sqrt (discriminant a b c)) *
        (2*a*t+b + Real.sqrt (discriminant a b c)) = 0 := by
      linear_combination hh-hr
    unfold polynomialCandidates
    split <;> try contradiction
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    rcases mul_eq_zero.mp hv with hp | hm
    · right
      simp [quadraticRoot,signedRoot]
      apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).mpr
      linear_combination hp
    · left
      simp [quadraticRoot,signedRoot]
      apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).mpr
      linear_combination hm
  · have ha' : a = 0 := not_ne_iff.mp ha
    by_cases hb : b ≠ 0
    · unfold polynomialCandidates
      split <;> try contradiction
      simp only [List.mem_singleton]
      apply (eq_div_iff hb).mpr
      rw [ha'] at h
      linear_combination h
    · have hb' : b = 0 := not_ne_iff.mp hb
      simp [ha',hb'] at h
      exact (((hn.resolve_left ha).resolve_left hb) h).elim

noncomputable def LeafData.candidates (p : LeafData ℝ) : List (Plane ℝ × Space ℝ) :=
  let q := p.quadratic
  (polynomialCandidates q.1 q.2.1 q.2.2).map (fun t => (p.intrinsicAt t,p.extrinsicAt t))

theorem LeafData.candidates_length (p : LeafData ℝ) : p.candidates.length ≤ 2 := by
  simpa [LeafData.candidates] using polynomialCandidates_length p.quadratic.1 p.quadratic.2.1 p.quadratic.2.2

theorem LeafData.candidates_complete (p : LeafData ℝ) (hz : p.z₃ ≠ 0)
    (hn : squared2 p.lineNormal ≠ 0)
    (hq : p.quadratic.1 ≠ 0 ∨ p.quadratic.2.1 ≠ 0 ∨ p.quadratic.2.2 ≠ 0)
    (u : Plane ℝ) (v : Space ℝ) (h0 : squared3 v = squared2 u)
    (hxy : horizontal v = p.planarLin u + p.base)
    (h₃ : p.z₃*v.2.2 = dot p.a₃ u + p.b₃)
    (h₄ : p.z₄*v.2.2 = dot p.a₄ u + p.b₄) : (u,v) ∈ p.candidates := by
  obtain ⟨t,rfl,rfl⟩ := p.parameterization hz hn u v hxy h₃ h₄
  have he := sub_eq_zero.mpr h0
  rw [LeafData.quadratic_eq] at he
  exact List.mem_map.mpr ⟨t,polynomialCandidates_complete _ _ _ _ he hq,rfl⟩

/-- The five successive lists of at most two choices give at most 32 candidates. -/
theorem branch_count {α β γ : Type} (roots₁ : List α) (roots₂ : α → List β)
    (leaves₁ leaves₂ leaves₃ : α → β → List γ)
    (hr₁ : roots₁.length ≤ 2) (hr₂ : ∀ a, (roots₂ a).length ≤ 2)
    (hl₁ : ∀ a b, (leaves₁ a b).length ≤ 2)
    (hl₂ : ∀ a b, (leaves₂ a b).length ≤ 2)
    (hl₃ : ∀ a b, (leaves₃ a b).length ≤ 2) :
    (roots₁.flatMap fun a => (roots₂ a).flatMap fun b =>
      (leaves₁ a b).flatMap fun u => (leaves₂ a b).flatMap fun v =>
        (leaves₃ a b).map fun w => (a,b,u,v,w)).length ≤ 32 := by
  have bound {ι η : Type} (l : List ι) (f : ι → List η) (n : Nat)
      (h : ∀ i, (f i).length ≤ n) : (l.flatMap f).length ≤ l.length*n := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,one_mul]
      have := h a
      omega
  calc
    _ ≤ roots₁.length*16 := by
      apply bound
      intro a
      calc
        _ ≤ (roots₂ a).length*8 := by
          apply bound
          intro b
          calc
            _ ≤ (leaves₁ a b).length*4 := by
              apply bound
              intro u
              calc
                _ ≤ (leaves₂ a b).length*2 := by
                  apply bound
                  intro v
                  simpa using hl₃ a b
                _ ≤ 4 := by have := hl₂ a b; omega
            _ ≤ 8 := by have := hl₁ a b; omega
        _ ≤ 16 := by have := hr₂ a; omega
    _ ≤ 32 := by omega

end OrigamiTorus.Type5
