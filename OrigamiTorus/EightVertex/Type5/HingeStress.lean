module

public import OrigamiTorus.EightVertex.Type5.Square
import Mathlib.Tactic

/-! Period equilibrium for the missing root edge when it is lifted through one leaf. -/

public section

namespace OrigamiTorus.Type5.HingeStress

/-- Add the coherent shift on the root segment through leaf `j` to the core marking. -/
def augmentedShift (j v k : Vertex) : ℤ × ℤ :=
  if v = 3 ∧ k = 4 then squareShift 3 j + squareShift j 4
  else if v = 4 ∧ k = 3 then squareShift 4 j + squareShift j 3
  else squareShift v k

/-- The difference of the two intrinsic root equilibrium rows, evaluated on affine weights. -/
def rootDifference (j : Vertex) (a : Vertex → ℝ) : ℝ × ℝ :=
  let term (k : Vertex) :=
    let d := augmentedShift j 4 k - augmentedShift j 3 k
    (a k * (d.1 : ℝ), a k * (d.2 : ℝ))
  term 1 + term 2 + term 3 + term 4 + term 5

private theorem rows (a : Vertex → ℝ) :
    rootDifference 0 a =
        (-(a 2+a 3+a 4+a 5), a 3+a 4+a 5) ∧
    rootDifference 6 a = (-(a 2+a 5), a 5) ∧
    rootDifference 7 a = (-(a 2+a 3+a 4+a 5), a 5) := by
  norm_num [rootDifference, augmentedShift, squareShift, positiveShift, Prod.ext_iff]
  ring_nf
  simp

/-- At a stationary coherent root chord, affine dependence can involve only the two
roots and their common anchor in the leaf link. The other two anchor weights vanish. -/
theorem outside_hinge_weights_zero (a : Vertex → ℝ)
    (hs : a 1 + a 2 + a 3 + a 4 + a 5 = 0) :
    (rootDifference 0 a = 0 → a 1 = 0 ∧ a 2 = 0) ∧
    (rootDifference 6 a = 0 → a 2 = 0 ∧ a 5 = 0) ∧
    (rootDifference 7 a = 0 → a 1 = 0 ∧ a 5 = 0) := by
  obtain ⟨h₀,h₆,h₇⟩ := rows a
  rw [h₀,h₆,h₇]
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    dsimp at hx hy
    constructor <;> linarith
  constructor <;> intro h
  all_goals
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    dsimp at hx hy
    constructor <;> linarith

end OrigamiTorus.Type5.HingeStress
