module

public import OrigamiTorus.EightVertex.Type6.Lift
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-! A generic choice of heights exists when no planar quadruple is collinear. -/

public section

open Filter Polynomial

namespace OrigamiTorus

private noncomputable def heightPolynomial (p : Vertex → ℝ × ℝ) (a b c d : Vertex) : ℝ[X] :=
  monomial a.val (-area p b c d) + monomial b.val (area p a c d) +
    monomial c.val (-area p a b d) + monomial d.val (area p a b c)

private theorem heightPolynomial_eval (p : Vertex → ℝ × ℝ) (a b c d : Vertex) (t : ℝ) :
    (heightPolynomial p a b c d).eval t = volume p (fun v => t^v.val) a b c d := by
  simp [heightPolynomial, volume]
  ring

private theorem heightPolynomial_ne_zero (p : Vertex → ℝ × ℝ) {a b c d : Vertex}
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hn : area p b c d ≠ 0 ∨ area p a c d ≠ 0 ∨ area p a b d ≠ 0 ∨ area p a b c ≠ 0) :
    heightPolynomial p a b c d ≠ 0 := by
  have ab : a.val ≠ b.val := ne_of_lt hab
  have ac : a.val ≠ c.val := ne_of_lt (hab.trans hbc)
  have ad : a.val ≠ d.val := ne_of_lt (hab.trans (hbc.trans hcd))
  have bc : b.val ≠ c.val := ne_of_lt hbc
  have bd : b.val ≠ d.val := ne_of_lt (hbc.trans hcd)
  have cd : c.val ≠ d.val := ne_of_lt hcd
  intro he
  rcases hn with hn | hn | hn | hn
  · have hh := congrArg (fun f : ℝ[X] => f.coeff a.val) he
    exact hn (by simpa [heightPolynomial, coeff_monomial, ab, ac, ad, Ne.symm ab, Ne.symm ac, Ne.symm ad] using hh)
  · have hh := congrArg (fun f : ℝ[X] => f.coeff b.val) he
    exact hn (by simpa [heightPolynomial, coeff_monomial, ab, bc, bd, Ne.symm ab, Ne.symm bc, Ne.symm bd] using hh)
  · have hh := congrArg (fun f : ℝ[X] => f.coeff c.val) he
    exact hn (by simpa [heightPolynomial, coeff_monomial, ac, bc, cd, Ne.symm ac, Ne.symm bc, Ne.symm cd] using hh)
  · have hh := congrArg (fun f : ℝ[X] => f.coeff d.val) he
    exact hn (by simpa [heightPolynomial, coeff_monomial, ad, bd, cd, Ne.symm ad, Ne.symm bd, Ne.symm cd] using hh)

theorem exists_generic_lift_of_noncollinear (p : Vertex → ℝ × ℝ)
    (hn : ∀ a b c d : Vertex, a < b → b < c → c < d →
      area p b c d ≠ 0 ∨ area p a c d ≠ 0 ∨ area p a b d ≠ 0 ∨ area p a b c ≠ 0) :
    ∃ z : Vertex → ℝ, GenericLift p z := by
  have he : ∀ᶠ t : ℝ in cofinite, GenericLift p (fun v => t^v.val) := by
    unfold GenericLift
    simp only [eventually_all]
    intro a b c d hab hbc hcd
    have hh := eventually_eval_ne_zero_cofinite (heightPolynomial_ne_zero p hab hbc hcd
      (hn a b c d hab hbc hcd))
    simpa only [heightPolynomial_eval] using hh
  obtain ⟨t, ht⟩ := he.exists
  exact ⟨_,ht⟩

end OrigamiTorus
