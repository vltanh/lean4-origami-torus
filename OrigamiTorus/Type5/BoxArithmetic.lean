module

public import OrigamiTorus.Type5.Reduction
public import OrigamiTorus.Certificates.RadicalIntervals
import Mathlib.Tactic

/-! Compositional interval evaluation of the Type 5 radical formulas. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type5.BoxArithmetic

open Inclusion IntervalDyadicReal

/-- A computed dyadic enclosure with its membership proof. -/
structure Bound (x : ℝ) where
  range : Interval Dyadic
  mem : x ∈ range

def precision : ℕ := 120

def rational (q : ℚ) : Bound (q : ℝ) := ⟨rat q precision,ratCast_mem q precision⟩

def integer (i : ℤ) : Bound (i : ℝ) := ⟨Interval.singleton (i : Dyadic),intCast_mem i⟩

def zero : Bound (0 : ℝ) := ⟨(integer 0).range,by simpa using (integer 0).mem⟩
def one : Bound (1 : ℝ) := ⟨(integer 1).range,by simpa using (integer 1).mem⟩
def two : Bound (2 : ℝ) := integer 2
def four : Bound (4 : ℝ) := integer 4

def plus {x y : ℝ} (a : Bound x) (b : Bound y) : Bound (x+y) := ⟨a.range.add b.range,add_mem a.mem b.mem⟩
def minus {x y : ℝ} (a : Bound x) (b : Bound y) : Bound (x-y) := ⟨a.range.sub b.range,sub_mem a.mem b.mem⟩
def neg {x : ℝ} (a : Bound x) : Bound (-x) := ⟨a.range.neg,neg_mem a.mem⟩
def times {x y : ℝ} (a : Bound x) (b : Bound y) : Bound (x*y) := ⟨a.range.mul b.range,mul_mem a.mem b.mem⟩
def divide {x y : ℝ} (a : Bound x) (b : Bound y) : Bound (x/y) :=
  ⟨a.range.mul (inverse b.range precision),div_mem a.mem b.mem precision⟩
def sq {x : ℝ} (a : Bound x) : Bound (x^2) := ⟨a.range.pow 2,pow_mem 2 a.mem⟩
def sqrt {x : ℝ} (a : Bound x) : Bound (Real.sqrt x) :=
  ⟨squareRoot a.range precision,squareRoot_mem a.mem precision⟩

def signedSqrt {x : ℝ} (positive : Bool) (a : Bound x) : Bound (signedRoot positive x) :=
  let b := sqrt a
  ⟨if positive then b.range else b.range.neg,by
    cases positive
    · exact neg_mem b.mem
    · exact b.mem⟩

abbrev PlaneBounds (p : Plane ℝ) := Bound p.1 × Bound p.2
abbrev SpaceBounds (p : Space ℝ) := Bound p.1 × Bound p.2.1 × Bound p.2.2

def planeZero : PlaneBounds ((0,0) : Plane ℝ) := (zero,zero)
def planeX : PlaneBounds ((1,0) : Plane ℝ) := (one,zero)
def planeY : PlaneBounds ((0,1) : Plane ℝ) := (zero,one)

def planePlus {u v : Plane ℝ} (a : PlaneBounds u) (b : PlaneBounds v) : PlaneBounds (u+v) :=
  (plus a.1 b.1,plus a.2 b.2)
def planeMinus {u v : Plane ℝ} (a : PlaneBounds u) (b : PlaneBounds v) : PlaneBounds (u-v) :=
  (minus a.1 b.1,minus a.2 b.2)
def planeScale {x : ℝ} {u : Plane ℝ} (a : Bound x) (b : PlaneBounds u) : PlaneBounds (smul2 x u) :=
  (times a b.1,times a b.2)
def spacePlus {u v : Space ℝ} (a : SpaceBounds u) (b : SpaceBounds v) : SpaceBounds (u+v) :=
  (plus a.1 b.1,plus a.2.1 b.2.1,plus a.2.2 b.2.2)
def spaceScale {x : ℝ} {u : Space ℝ} (a : Bound x) (b : SpaceBounds u) : SpaceBounds (smul3 x u) :=
  (times a b.1,times a b.2.1,times a b.2.2)

def height {p : Plane ℝ} {z : ℝ} (a : PlaneBounds p) (b : Bound z) : SpaceBounds (atHeight p z) :=
  (a.1,a.2,b)
def plane {p : Space ℝ} (a : SpaceBounds p) : PlaneBounds (horizontal p) := (a.1,a.2.1)
def dotBounds {u v : Plane ℝ} (a : PlaneBounds u) (b : PlaneBounds v) : Bound (dot u v) :=
  plus (times a.1 b.1) (times a.2 b.2)
def crossBounds {u v : Plane ℝ} (a : PlaneBounds u) (b : PlaneBounds v) : Bound (cross u v) :=
  minus (times a.1 b.2) (times a.2 b.1)
def squaredPlane {u : Plane ℝ} (a : PlaneBounds u) : Bound (squared2 u) := dotBounds a a
def squaredSpace {u : Space ℝ} (a : SpaceBounds u) : Bound (squared3 u) := plus (squaredPlane (plane a)) (sq a.2.2)
def dotSpace {u v : Space ℝ} (a : SpaceBounds u) (b : SpaceBounds v) : Bound (dot3 u v) :=
  plus (dotBounds (plane a) (plane b)) (times a.2.2 b.2.2)

def solve {u v : Plane ℝ} {a b : ℝ} (U : PlaneBounds u) (V : PlaneBounds v) (A : Bound a) (B : Bound b) :
    PlaneBounds (linearSolve u v a b) :=
  let det := crossBounds U V
  (divide (minus (times A V.2) (times U.2 B)) det,
   divide (minus (times U.1 B) (times A V.1)) det)

def rhs {r s u : Plane ℝ} (R : PlaneBounds r) (S : PlaneBounds s) (U : PlaneBounds u) : Bound (anchorRhs r s u) :=
  plus (dotBounds S U) (divide (minus (squaredPlane R) (squaredPlane S)) two)

def project {a b s₂ s₅ u : Plane ℝ} (A : PlaneBounds a) (B : PlaneBounds b)
    (S₂ : PlaneBounds s₂) (S₅ : PlaneBounds s₅) (U : PlaneBounds u) : PlaneBounds (projection a b s₂ s₅ u) :=
  solve A B (rhs A S₂ U) (rhs B S₅ U)

def root {a b s₂ s₅ u : Plane ℝ} (A : PlaneBounds a) (B : PlaneBounds b)
    (S₂ : PlaneBounds s₂) (S₅ : PlaneBounds s₅) (U : PlaneBounds u) (positive : Bool) :
    SpaceBounds (makeRoot a b s₂ s₅ u positive) :=
  let P := project A B S₂ S₅ U
  height P (signedSqrt positive (minus (squaredPlane U) (squaredPlane P)))

structure LeafBounds (p : LeafData ℝ) where
  base : PlaneBounds p.base
  colX : PlaneBounds p.colX
  colY : PlaneBounds p.colY
  a₃ : PlaneBounds p.a₃
  a₄ : PlaneBounds p.a₄
  b₃ : Bound p.b₃
  b₄ : Bound p.b₄
  z₃ : Bound p.z₃
  z₄ : Bound p.z₄

def coefficient {r : Space ℝ} {s X Y : Plane ℝ} (R : SpaceBounds r) (S : PlaneBounds s)
    (Bx : PlaneBounds X) (By : PlaneBounds Y) : PlaneBounds (leafRootCoefficient r s X Y) :=
  (minus S.1 (dotBounds (plane R) Bx),minus S.2 (dotBounds (plane R) By))

def constant {r : Space ℝ} {s b : Plane ℝ} (R : SpaceBounds r) (S : PlaneBounds s) (B : PlaneBounds b) :
    Bound (leafRootConstant r s b) :=
  minus (divide (minus (squaredSpace R) (squaredPlane S)) two) (dotBounds (plane R) B)

def leaf {a b s₂ s₅ s₃ s₄ : Plane ℝ} {r₃ r₄ : Space ℝ} (A : PlaneBounds a) (B : PlaneBounds b)
    (R₃ : SpaceBounds r₃) (R₄ : SpaceBounds r₄) (S₂ : PlaneBounds s₂) (S₅ : PlaneBounds s₅)
    (S₃ : PlaneBounds s₃) (S₄ : PlaneBounds s₄) : LeafBounds (normalizedLeafData a b r₃ r₄ s₂ s₅ s₃ s₄) :=
  let f {u : Plane ℝ} (U : PlaneBounds u) := project A B S₂ S₅ U
  let c := f planeZero
  let X := planeMinus (f planeX) c
  let Y := planeMinus (f planeY) c
  ⟨c,X,Y,coefficient R₃ S₃ X Y,coefficient R₄ S₄ X Y,constant R₃ S₃ c,constant R₄ S₄ c,R₃.2.2,R₄.2.2⟩

namespace LeafBounds

variable {p : LeafData ℝ}

def linear (D : LeafBounds p) {u : Plane ℝ} (U : PlaneBounds u) : PlaneBounds (p.planarLin u) :=
  planePlus (planeScale U.1 D.colX) (planeScale U.2 D.colY)
def normal (D : LeafBounds p) : PlaneBounds p.lineNormal :=
  planeMinus (planeScale D.z₄ D.a₃) (planeScale D.z₃ D.a₄)
def intercept (D : LeafBounds p) : Bound p.lineOffset := minus (times D.z₄ D.b₃) (times D.z₃ D.b₄)
def uBase (D : LeafBounds p) : PlaneBounds p.intrinsicBase :=
  planeScale (divide (neg D.intercept) (squaredPlane D.normal)) D.normal
def uDirection (D : LeafBounds p) : PlaneBounds p.intrinsicDirection := (neg D.normal.2,D.normal.1)
def vBase (D : LeafBounds p) : SpaceBounds p.extrinsicBase :=
  height (planePlus (D.linear D.uBase) D.base) (divide (plus (dotBounds D.a₃ D.uBase) D.b₃) D.z₃)
def vDirection (D : LeafBounds p) : SpaceBounds p.extrinsicDirection :=
  height (D.linear D.uDirection) (divide (dotBounds D.a₃ D.uDirection) D.z₃)
def quadratic (D : LeafBounds p) : Bound p.quadratic.1 × Bound p.quadratic.2.1 × Bound p.quadratic.2.2 :=
  (minus (squaredSpace D.vDirection) (squaredPlane D.uDirection),
   times two (minus (dotSpace D.vBase D.vDirection) (dotBounds D.uBase D.uDirection)),
   minus (squaredSpace D.vBase) (squaredPlane D.uBase))
def discriminant (D : LeafBounds p) : Bound (Type5.discriminant p.quadratic.1 p.quadratic.2.1 p.quadratic.2.2) :=
  minus (sq D.quadratic.2.1) (times (times four D.quadratic.1) D.quadratic.2.2)
def parameter (D : LeafBounds p) (positive : Bool) :
    Bound (quadraticRoot p.quadratic.1 p.quadratic.2.1 p.quadratic.2.2 positive) :=
  divide (plus (neg D.quadratic.2.1) (signedSqrt positive D.discriminant)) (times two D.quadratic.1)
def intrinsicAt (D : LeafBounds p) {t : ℝ} (T : Bound t) : PlaneBounds (p.intrinsicAt t) :=
  planePlus D.uBase (planeScale T D.uDirection)
def extrinsicAt (D : LeafBounds p) {t : ℝ} (T : Bound t) : SpaceBounds (p.extrinsicAt t) :=
  spacePlus D.vBase (spaceScale T D.vDirection)

end LeafBounds

def positive (I : Interval Dyadic) : Bool := I.lb.any fun l => 0 < l

theorem positive_of_check {x : ℝ} (b : Bound x) (h : positive b.range = true) : 0 < x := by
  obtain ⟨I,hx⟩ := b
  rw [mem_iff_mem_map,Interval.mem_map_iff] at hx
  rcases I with ⟨_ | a,r⟩
  · simp [positive] at h
  · have ha : 0 < a := by simpa [positive] using h
    have hreal : 0 < Dyadic.toReal a := by simpa [Dyadic.toReal] using Dyadic.toReal_lt_toReal.mpr ha
    exact hreal.trans_le (hx.1 a rfl)

end OrigamiTorus.Type5.BoxArithmetic
