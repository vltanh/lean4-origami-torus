module

public import OrigamiTorus.LatticeReduction
public import OrigamiTorus.PeriodicArea
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic

/-! Quotient homeomorphisms induced by similarities of plane lattices. -/

open scoped ComplexConjugate

namespace OrigamiTorus

@[expose] public section

/-- The additive group of integral combinations of two periods. -/
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

def complexSimilarity (D : ℂ) (reflect : Bool) (p : ℂ) : ℂ :=
  D*(if reflect then conj p else p)

def complexSimilarityLinear (D : ℂ) (reflect : Bool) : ℂ →ₗ[ℝ] ℂ where
  toFun := complexSimilarity D reflect
  map_add' a b := by cases reflect <;> simp [complexSimilarity,mul_add]
  map_smul' r a := by
    cases reflect <;> simp [complexSimilarity,Complex.real_smul,mul_left_comm]

private theorem complexSimilarity_sub (D : ℂ) (reflect : Bool) (p q : ℂ) :
    complexSimilarity D reflect (p-q) = complexSimilarity D reflect p - complexSimilarity D reflect q := by
  cases reflect <;> simp [complexSimilarity, map_sub, mul_sub]

private noncomputable def similarityHomeomorph (D : ℂ) (reflect : Bool) (hD : D ≠ 0) : ℂ ≃ₜ ℂ :=
  (if reflect then Complex.conjCLE.toHomeomorph else Homeomorph.refl ℂ).trans (Homeomorph.mulLeft₀ D hD)

private theorem similarityHomeomorph_apply (D : ℂ) (reflect : Bool) (hD : D ≠ 0) (p : ℂ) :
    similarityHomeomorph D reflect hD p = complexSimilarity D reflect p := by
  cases reflect <;> simp [similarityHomeomorph,complexSimilarity]

private def basisPoint (x y : ℝ) (p : ℝ × ℝ) : ℂ := (p.1 : ℂ)+(p.2 : ℂ)*(x+y*Complex.I)

private theorem basisPoint_sub (x y : ℝ) (p q : ℝ × ℝ) :
    basisPoint x y (p-q) = basisPoint x y p - basisPoint x y q := by
  simp only [basisPoint,Prod.fst_sub,Prod.snd_sub,Complex.ofReal_sub]
  ring

private theorem basisPoint_realPeriod (x y : ℝ) (d : Period) :
    basisPoint x y (realPeriod d) = (d.1 : ℂ)*1+(d.2 : ℂ)*(x+y*Complex.I) := by
  simp [basisPoint,realPeriod]

private noncomputable def basisHomeomorph (x y : ℝ) (hy : y ≠ 0) : (ℝ × ℝ) ≃ₜ ℂ :=
  (periodCoordinatesHomeomorph x y hy).symm.trans Complex.equivRealProdCLM.symm.toHomeomorph

private theorem basisHomeomorph_apply (x y : ℝ) (hy : y ≠ 0) (p : ℝ × ℝ) :
    basisHomeomorph x y hy p = basisPoint x y p := by
  change Complex.equivRealProdCLM.symm (p.1+x*p.2,y*p.2) = _
  rw [Complex.equivRealProdCLM_symm_apply]
  push_cast
  unfold basisPoint
  ring

private theorem basisHomeomorph_periodCoordinates (x y : ℝ) (hy : y ≠ 0) (p : ℝ × ℝ) :
    basisHomeomorph x y hy (periodCoordinates x y p) = Complex.equivRealProdCLM.symm p := by
  change Complex.equivRealProdCLM.symm
    ((periodCoordinatesHomeomorph x y hy).symm ((periodCoordinatesHomeomorph x y hy) p)) = _
  rw [Homeomorph.symm_apply_apply]

end

private theorem homeomorph_of_equal_fibers {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : X → Y) (g : X → Z)
    (hf : Function.Surjective f) (hfo : IsOpenMap f) (hfc : Continuous f)
    (hg : Function.Surjective g) (hgo : IsOpenMap g) (hgc : Continuous g)
    (he : ∀ p q, f p=f q ↔ g p=g q) : ∃ e : Y ≃ₜ Z, ∀ p, e (f p) = g p := by
  let h (y : Y) := g (hf y).choose
  have hfactor (p : X) : h (f p) = g p := (he _ _).mp (hf (f p)).choose_spec
  have hc : Continuous h := (hfo.isQuotientMap hfc hf).continuous_iff.mpr (by
    have heq : h ∘ f = g := funext hfactor
    rwa [heq])
  have ho : IsOpenMap h := by
    intro U hU
    have himage : h '' U = g '' (f ⁻¹' U) := by
      ext z
      constructor
      · rintro ⟨y,hy,rfl⟩
        obtain ⟨p,rfl⟩ := hf y
        exact ⟨p,hy,(hfactor p).symm⟩
      · rintro ⟨p,hp,rfl⟩
        exact ⟨f p,hp,hfactor p⟩
    rw [himage]
    exact hgo _ (hU.preimage hfc)
  have hi : Function.Injective h := by
    intro a b e
    obtain ⟨p,rfl⟩ := hf a
    obtain ⟨q,rfl⟩ := hf b
    rw [hfactor,hfactor] at e
    exact (he _ _).mpr e
  have hs : Function.Surjective h := by
    intro z
    obtain ⟨p,rfl⟩ := hg z
    exact ⟨f p,hfactor p⟩
  exact ⟨(Equiv.ofBijective h ⟨hi,hs⟩).toHomeomorphOfContinuousOpen hc ho,hfactor⟩

/-- A similarity carrying the normalized lattice onto the target lattice
induces the corresponding homeomorphism on the plane quotients. -/
public theorem complexTorus_rebase (u v : ℂ) (x y : ℝ) (hy : y ≠ 0)
    (D : ℂ) (reflect : Bool) (hD : D ≠ 0)
    (hL : complexSimilarity D reflect '' complexLattice 1 (x+y*Complex.I) = complexLattice u v) :
    ∃ J : MarkedTorus ≃ₜ ComplexTorus u v, ∀ p : ℝ × ℝ,
      J (projectPeriods (periodCoordinates x y p)) =
        complexTorusProjection u v (complexSimilarity D reflect (Complex.equivRealProdCLM.symm p)) := by
  let B := basisHomeomorph x y hy
  let S := similarityHomeomorph D reflect hD
  let π := complexTorusProjection u v
  let G := π ∘ S ∘ B
  have hπ : Topology.IsQuotientMap π := QuotientAddGroup.isQuotientMap_mk _
  have hπo : IsOpenMap π := QuotientAddGroup.isOpenMap_coe
  have hp₁ : Function.Surjective (fun p : ℝ => (p : AddCircle (1 : ℝ))) := QuotientAddGroup.mk_surjective
  have hp₂ : Continuous (fun p : ℝ => (p : AddCircle (1 : ℝ))) := AddCircle.continuous_mk' 1
  have hp₃ : IsOpenMap (fun p : ℝ => (p : AddCircle (1 : ℝ))) := QuotientAddGroup.isOpenMap_coe
  have hrel (p q : ℝ × ℝ) : projectPeriods p = projectPeriods q ↔ G p = G q := by
    have hb (t : ℝ × ℝ) : B t = basisPoint x y t := basisHomeomorph_apply x y hy t
    have hs (z : ℂ) : S z = complexSimilarity D reflect z := similarityHomeomorph_apply D reflect hD z
    have hdiff : S (B p) - S (B q) = S (B (p-q)) := by
      rw [hs,hs,hs,hb,hb,hb,basisPoint_sub,complexSimilarity_sub]
    have hmem : S (B (p-q)) ∈ complexPeriodSubgroup u v ↔
        B (p-q) ∈ complexLattice 1 (x+y*Complex.I) := by
      change S (B (p-q)) ∈ complexLattice u v ↔ _
      rw [← hL]
      constructor
      · rintro ⟨a,ha,he⟩
        have he' : complexSimilarity D reflect a = S (B (p-q)) := he
        have h := S.injective ((hs a).trans he')
        exact h ▸ ha
      · intro h
        exact ⟨_,h,(hs (B (p-q))).symm⟩
    have hcoord : B (p-q) ∈ complexLattice 1 (x+y*Complex.I) ↔
        ∃ d : Period, q + realPeriod d = p := by
      constructor
      · rintro ⟨a,b,h⟩
        have hB : B (realPeriod (a,b)) = B (p-q) := by
          rw [hb,basisPoint_realPeriod]
          exact h
        exact ⟨(a,b),by rw [B.injective hB]; abel⟩
      · rintro ⟨⟨a,b⟩,h⟩
        have h' : p-q = realPeriod (a,b) := by rw [← h]; abel
        rw [h',hb,basisPoint_realPeriod]
        exact ⟨a,b,rfl⟩
    have hg : G p = G q ↔ ∃ d : Period, q+realPeriod d=p := by
      change (↑(S (B p)) : ComplexTorus u v) = ↑(S (B q)) ↔ _
      rw [QuotientAddGroup.eq_iff_sub_mem,hdiff,hmem,hcoord]
    rw [hg,eq_comm,projectPeriods_eq_iff]
  obtain ⟨J,hJ⟩ := homeomorph_of_equal_fibers projectPeriods G (hp₁.prodMap hp₁)
    (hp₃.prodMap hp₃) ((hp₂.comp continuous_fst).prodMk (hp₂.comp continuous_snd))
    (hπ.surjective.comp (S.surjective.comp B.surjective))
    (hπo.comp (S.isOpenMap.comp B.isOpenMap))
    (hπ.continuous.comp (S.continuous.comp B.continuous)) hrel
  refine ⟨J,fun p => ?_⟩
  rw [hJ]
  change π (S (B (periodCoordinates x y p))) = _
  rw [basisHomeomorph_periodCoordinates x y hy,similarityHomeomorph_apply]

end OrigamiTorus
