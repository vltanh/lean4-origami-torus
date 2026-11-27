module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Affine determinant identities behind the Type 2 sign restrictions. -/

@[expose] public section

namespace OrigamiTorus

abbrev Point3 := ℝ × ℝ × ℝ

def determinant3 (a b c : Point3) : ℝ :=
  a.1 * (b.2.1*c.2.2 - b.2.2*c.2.1) -
  a.2.1 * (b.1*c.2.2 - b.2.2*c.1) +
  a.2.2 * (b.1*c.2.1 - b.2.1*c.1)

/-- Affine determinant with the four rows `(1, point)`. -/
def affineBracket (a b c d : Point3) : ℝ :=
  determinant3 (b-a) (c-a) (d-a)

private theorem determinant3_plucker (u a b c d : Point3) :
    determinant3 u a b * determinant3 u c d -
      determinant3 u a c * determinant3 u b d +
      determinant3 u a d * determinant3 u b c = 0 := by
  simp only [determinant3]
  ring

/-- The three-term affine Grassmann–Plücker identity. -/
theorem affineBracket_plucker (s t a b c d : Point3) :
    affineBracket s t a b * affineBracket s t c d -
      affineBracket s t a c * affineBracket s t b d +
      affineBracket s t a d * affineBracket s t b c = 0 :=
  determinant3_plucker (t-s) (a-s) (b-s) (c-s) (d-s)

theorem affineBracket_circuitSum (a b c d e : Point3) :
    affineBracket b c d e - affineBracket a c d e + affineBracket a b d e -
      affineBracket a b c e + affineBracket a b c d = 0 := by
  simp only [affineBracket, determinant3, Prod.fst_sub, Prod.snd_sub]
  ring

set_option maxHeartbeats 2000000 in
private theorem smul_point (k : ℝ) (p : Point3) :
    k • p = (k*p.1, k*p.2.1, k*p.2.2) := rfl

/-- The alternating four-point minors give an affine dependence of five points. -/
theorem affineBracket_circuitVector (a b c d e : Point3) :
    affineBracket b c d e • a - affineBracket a c d e • b + affineBracket a b d e • c -
      affineBracket a b c e • d + affineBracket a b c d • e = 0 := by
  ext <;>
    simp only [affineBracket, determinant3, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
      Prod.snd_sub, smul_point, Prod.fst_zero, Prod.snd_zero] <;>
    ring

end OrigamiTorus
