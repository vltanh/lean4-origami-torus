module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions.SumProd
import Mathlib.Tactic

/-!
# Type 5 origami tori

The Type 5 face complex admits piecewise-isometric embeddings for the
unit square and for every modulus in the specified closed nonrectangular box.
-/

@[expose] public section

namespace OrigamiTorus

abbrev Vertex := Fin 8
abbrev Triangle := Vertex × Vertex × Vertex

def triangleVertices (f : Triangle) : List Vertex := [f.1, f.2.1, f.2.2]

abbrev Point3 := ℝ × ℝ × ℝ

def triangleVertexSet (f : Triangle) : Finset Vertex := (triangleVertices f).toFinset

def faceWeights (s : Finset Vertex) : Set (Vertex → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ ∀ i ∉ s, w i = 0}

def triangleWeightSpace (fs : List Triangle) : Set (Vertex → ℝ) :=
  {w | ∃ f ∈ fs, w ∈ faceWeights (triangleVertexSet f)}

noncomputable def evaluateWeights (q : Vertex → Point3) (w : Vertex → ℝ) : Point3 :=
  ∑ i, w i • q i

noncomputable def evaluateTriangles (fs : List Triangle) (q : Vertex → Point3)
    (w : triangleWeightSpace fs) : Point3 := evaluateWeights q w.val

def complexLattice (u v : ℂ) : Set ℂ :=
  {p | ∃ m n : ℤ, (m : ℂ)*u+(n : ℂ)*v=p}

def complexPeriodSubgroup (u v : ℂ) : AddSubgroup ℂ where
  carrier := complexLattice u v
  zero_mem' := ⟨0,0,by simp⟩
  add_mem' := by
    rintro _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
    exact ⟨a+c,b+d,by push_cast; ring⟩
  neg_mem' := by
    rintro _ ⟨a,b,rfl⟩
    exact ⟨-a,-b,by push_cast; ring⟩

abbrev ComplexTorus (u v : ℂ) := ℂ ⧸ complexPeriodSubgroup u v

def complexTorusProjection (u v : ℂ) (p : ℂ) : ComplexTorus u v := p

namespace Type5

abbrev Plane (R : Type*) := R × R
abbrev Space (R : Type*) := R × R × R

def dot {R : Type*} [Ring R] (u v : Plane R) : R := u.1*v.1 + u.2*v.2
def horizontal {R : Type*} (p : Space R) : Plane R := (p.1,p.2.1)
def squared2 {R : Type*} [Ring R] (p : Plane R) : R := dot p p
def squared3 {R : Type*} [Ring R] (p : Space R) : R := squared2 (horizontal p) + p.2.2^2

end Type5

end OrigamiTorus

namespace OrigamiTorusType5Challenge

open OrigamiTorus

/-- The unit square lattice torus has a piecewise-isometric Type 5 embedding. -/
theorem type5_square :
    let a : ℂ := 1
    let b : ℂ := Complex.I
    let fs : List Triangle :=
      [(0,1,2), (0,3,1), (0,2,4), (0,5,3), (0,4,5), (1,5,2), (1,3,6), (1,6,4),
        (1,4,7), (1,7,5), (2,6,3), (2,3,7), (2,7,4), (2,5,6), (3,5,7), (4,6,5)]
    ∃ (H : triangleWeightSpace fs ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles fs Q u) ∧
      (∀ f ∈ fs, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ fs, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  sorry

/-- The same Type 5 face complex realizes every lattice torus in the specified
closed nonrectangular modulus box. -/
theorem type5_nonrectangular_box (x y : ℝ)
    (hx : x ∈ Set.Icc (174241221608834/10^15) (174241221628834/10^15))
    (hy : y ∈ Set.Icc (1084897889745590/10^15) (1084897889765590/10^15)) :
    let a : ℂ := 1
    let b : ℂ := x+y*Complex.I
    let fs : List Triangle :=
      [(0,1,2), (0,3,1), (0,2,4), (0,5,3), (0,4,5), (1,5,2), (1,3,6), (1,6,4),
        (1,4,7), (1,7,5), (2,6,3), (2,3,7), (2,7,4), (2,5,6), (3,5,7), (4,6,5)]
    ∃ (H : triangleWeightSpace fs ≃ₜ ComplexTorus a b)
      (F : ComplexTorus a b → Point3) (Q : Vertex → Point3) (P : Triangle → Vertex → ℂ),
      Topology.IsClosedEmbedding F ∧
      (∀ u, F (H u) = evaluateTriangles fs Q u) ∧
      (∀ f ∈ fs, ∀ u, u.val ∈ faceWeights (triangleVertexSet f) →
        H u = complexTorusProjection a b (∑ i, u.val i • P f i)) ∧
      ∀ f ∈ fs, ∀ u v,
        u.val ∈ faceWeights (triangleVertexSet f) →
        v.val ∈ faceWeights (triangleVertexSet f) →
        Type5.squared3 (F (H u) - F (H v)) =
          dist (∑ i, u.val i • P f i) (∑ i, v.val i • P f i)^2 := by
  sorry

end OrigamiTorusType5Challenge
