module

public import OrigamiTorus.Type6.Data
import OrigamiTorus.Type6.Signs
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-! The strict certificate persists under perturbation to a lift in general position. -/

@[expose] public section

open Filter Set
open scoped Topology

namespace OrigamiTorus

private theorem volume_add_mul (p : Vertex → ℝ × ℝ) (z z' : Vertex → ℝ) (u : ℝ)
    (a b c d : Vertex) :
    volume p (fun v => z v + u * z' v) a b c d = volume p z a b c d + u * volume p z' a b c d := by
  unfold volume
  ring

private theorem eventually_affine_ne_zero (a b : ℝ) (hb : b ≠ 0) :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), a + u * b ≠ 0 := by
  by_cases ha : a = 0
  · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with u hu
    simpa [ha] using mul_ne_zero (ne_of_gt hu) hb
  · have hcont : ContinuousAt (fun u : ℝ => a + u * b) 0 := by fun_prop
    have hn : (fun u : ℝ => a + u * b) 0 ≠ 0 := by simpa
    exact (hcont.eventually_ne hn).filter_mono nhdsWithin_le_nhds

private theorem eventually_isSeparated (p : Vertex → ℝ × ℝ) (z z' : Vertex → ℝ)
    (pair : Edge × Triangle) (hp : isSeparated p z pair) :
    ∀ᶠ u in 𝓝[>] (0 : ℝ), isSeparated p (fun v => z v + u * z' v) pair := by
  obtain ⟨⟨a,b⟩,c,d,e⟩ := pair
  simp only [isSeparated, separates] at hp ⊢
  simp only [volume_add_mul]
  refine (show ∀ᶠ u in 𝓝 (0 : ℝ), _ from ?_).filter_mono nhdsWithin_le_nhds
  rcases hp with hp | hp | hp | hp
  · apply Eventually.mono _ (fun _ h => Or.inl h)
    apply ContinuousAt.eventually_lt (by fun_prop) (by fun_prop)
    simpa using hp
  · apply Eventually.mono _ (fun _ h => Or.inr (Or.inl h))
    apply ContinuousAt.eventually_lt (by fun_prop) (by fun_prop)
    simpa using hp
  · apply Eventually.mono _ (fun _ h => Or.inr (Or.inr (Or.inl h)))
    apply ContinuousAt.eventually_lt (by fun_prop) (by fun_prop)
    simpa using hp
  · apply Eventually.mono _ (fun _ h => Or.inr (Or.inr (Or.inr h)))
    apply ContinuousAt.eventually_lt (by fun_prop) (by fun_prop)
    simpa using hp

/-- A generic direction permits an arbitrarily small height perturbation preserving
all the strict witnesses on the given finite list. -/
theorem exists_generic_separating_lift (p : Vertex → ℝ × ℝ) (z z' : Vertex → ℝ)
    (pairs : List (Edge × Triangle)) (direction : GenericLift p z')
    (hsep : ∀ pair ∈ pairs, isSeparated p z pair) :
    ∃ z : Vertex → ℝ, GenericLift p z ∧ ∀ pair ∈ pairs, isSeparated p z pair := by
  let perturb (u : ℝ) (v : Vertex) := z v + u * z' v
  change ∃ z, GenericLift p z ∧ ∀ pair ∈ pairs, isSeparated p z pair
  have hg : ∀ᶠ u in 𝓝[>] (0 : ℝ), GenericLift p (perturb u) := by
    unfold GenericLift
    simp only [Filter.eventually_all]
    intro a b c d
    by_cases hc : a < b ∧ b < c ∧ c < d
    · simp only [hc.1, hc.2.1, hc.2.2, true_implies]
      simp only [perturb, volume_add_mul]
      exact eventually_affine_ne_zero _ _ (direction a b c d hc.1 hc.2.1 hc.2.2)
    · exact fun hab hbc hcd => (hc ⟨hab,hbc,hcd⟩).elim
  have hs : ∀ᶠ u in 𝓝[>] (0 : ℝ), ∀ pair ∈ pairs, isSeparated p (perturb u) pair := by
    rw [Filter.eventually_all]
    intro pair
    by_cases hp : pair ∈ pairs
    · simpa only [hp, true_implies] using
        eventually_isSeparated p z z' pair (hsep pair hp)
    · exact Filter.Eventually.of_forall (fun _ h => (hp h).elim)
  obtain ⟨u, hu⟩ := (hg.and hs).exists
  exact ⟨perturb u, hu⟩

theorem type6_genericSeparatingLift (second : Bool) (x w : ℝ) (hd : chartDomain second x w) :
    let p := stripPoint second x w
    ∃ z : Vertex → ℝ, GenericLift p z ∧ ∀ pair ∈ type6DisjointPairs, isSeparated p z pair :=
  exists_generic_separating_lift (stripPoint second x w) (lift second)
    (generalPositionDirection second) type6DisjointPairs
    (type6_nonzeroDirection second x w hd) (type6_strictSeparation second x w hd)

/-- Bit mask of the three vertex labels of a face. -/
def faceCode (f : Triangle) : Nat := 2 ^ f.1.val + 2 ^ f.2.1.val + 2 ^ f.2.2.val

/-- The Type 3 flip has the face list of Lutz Type 6 under the explicit relabeling. -/
theorem type6_flipRelabels :
    Function.Injective flipRelabeling ∧
    let relabeled := type6FlippedFaces.map fun (a,b,c) =>
      faceCode (flipRelabeling a, flipRelabeling b, flipRelabeling c)
    let canonical := type6Faces.map faceCode
    relabeled.all canonical.contains = true ∧ canonical.all relabeled.contains = true := by
  decide +kernel

end OrigamiTorus
