module

public import OrigamiTorus.Type4.LiftWideData

/-! The finite edge–face tests shared by the Type 7 height certificates. -/

@[expose] public section

namespace OrigamiTorus.Type7

open Type4.StripLift (volumeCoeffs)
open StripPolynomial (Coefficients)

def separationCheck (P : Vertex → Coefficients × Coefficients) (Z : Vertex → Coefficients)
    (sign : Coefficients → ℤ) (q : Edge × Triangle) : Bool :=
  let ((a,b),c,d,e) := q
  let v i j k m := sign (volumeCoeffs P Z i j k m)
  let v₀ := v b c d e
  let v₁ := v a c d e
  let v₂ := v a b d e
  let v₃ := v a b c e
  let v₄ := v a b c d
  decide (0 < v₀*v₁ ∨ 0 < v₂*v₃ ∨ 0 < v₃*v₄ ∨ v₂*v₄ < 0)

def stripPairChunk (i : Fin 29) : List (Edge × Triangle) := ((disjointPairs faces).drop (5*i.val)).take 5

end OrigamiTorus.Type7
