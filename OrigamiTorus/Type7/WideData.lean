module

public import OrigamiTorus.Type7.LiftData

/-! Height polynomials for the six wider Type 7 cells. -/

@[expose] public section

namespace OrigamiTorus.Type7

open Type4.StripLift
open StripPolynomial (Coefficients C T H)

def extrapolateHeight : Coefficients → Coefficients
  | [] => []
  | a::tail => StripPolynomial.add [a]
      (StripPolynomial.mul (StripPolynomial.add (C 1) T) (extrapolateHeight tail))

def widerHeight (i : Fin 5) (v : Vertex) : Coefficients :=
  if i = 1 then extrapolateHeight (wideZ 0 v)
  else if i = 2 ∧ v = 3 then
    StripPolynomial.add (wideZ i v) (StripPolynomial.mul (C (1/100)) (StripPolynomial.add (C 1) H))
  else wideZ i v

def widerPairCheck (i : Fin 5) := separationCheck (wideP i) (widerHeight i) signClosed

end OrigamiTorus.Type7
