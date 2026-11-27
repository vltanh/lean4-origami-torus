module

public import OrigamiTorus.Type7.Holonomy
import Mathlib.Tactic

/-! Positive oriented area rules out rotational gluing for the flat Type 7 development. -/

@[expose] public section

namespace OrigamiTorus.Type7

variable (flipped : Bool)

abbrev FaceSide := Fin 16 × Fin 3

def sideLabels (d : FaceSide) : Edge :=
  let (a,b,c) := markedFace flipped d.1
  ![(a,b),(b,c),(c,a)] d.2

def reverseFaceSide (d : FaceSide) : FaceSide :=
  let (a,b) := sideLabels flipped d
  let j := leftFace flipped b a
  (j,((List.finRange 3).find? fun k => sideLabels flipped (j,k) == (b,a)).getD 0)

theorem sideLabels_mem (d : FaceSide) : sideLabels flipped d ∈ directedSides (markedFace flipped d.1) := by
  revert d
  cases flipped <;> decide +kernel

theorem sideLabels_reverse (d : FaceSide) :
    sideLabels flipped (reverseFaceSide flipped d) = (sideLabels flipped d).swap := by
  revert d
  cases flipped <;> decide +kernel

theorem reverseFaceSide_involutive : Function.Involutive (reverseFaceSide flipped) := by
  unfold Function.Involutive
  cases flipped <;> decide +kernel

/-- If all edge transitions fixed a common point, the positively oriented
double areas would cancel edge by edge. -/
theorem no_common_transition_center (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (C : ℂ)
    (hfix : ∀ a b, HasSide flipped a b → edgeTransition flipped q he a b C = C) : False := by
  let P (j : Fin 16) := (markedDevelopment flipped q he j).point
  let areaSide (d : FaceSide) :=
    complexCross (P d.1 (sideLabels flipped d).1-C) (P d.1 (sideLabels flipped d).2-C)
  have hneg (d : FaceSide) : areaSide (reverseFaceSide flipped d) = -areaSide d := by
    rcases h : sideLabels flipped d with ⟨a,b⟩
    have hs := sideLabels_mem flipped d
    rw [h] at hs
    have hf := leftFace_of_side flipped d.1 a b hs
    have hrev := sideLabels_reverse flipped d
    rw [h] at hrev
    have hr : (reverseFaceSide flipped d).1 = leftFace flipped b a := by
      unfold reverseFaceSide
      rw [h]
    have hside := hasSide_of_side flipped d.1 a b hs
    have hA := edgeTransition_apply_a flipped q he a b hside
    have hB := edgeTransition_apply_b flipped q he a b hside
    rw [hf] at hA hB
    change edgeTransition flipped q he a b (P d.1 a) = P (leftFace flipped b a) a at hA
    change edgeTransition flipped q he a b (P d.1 b) = P (leftFace flipped b a) b at hB
    dsimp only [areaSide]
    rw [h,hrev,hr]
    change complexCross (P (leftFace flipped b a) b-C) (P (leftFace flipped b a) a-C) =
      -complexCross (P d.1 a-C) (P d.1 b-C)
    rw [← hA,← hB,ComplexMotion.cross_eq_of_fixed_of_unit _ (hfix a b hside) (edgeTransition_unit flipped q he a b)]
    exact complexCross_swap _ _
  have hsum : ∑ d, areaSide d = 0 := by
    let R : FaceSide ≃ FaceSide :=
      ⟨reverseFaceSide flipped,reverseFaceSide flipped,reverseFaceSide_involutive flipped,reverseFaceSide_involutive flipped⟩
    have heq := R.sum_comp areaSide
    change (∑ d, areaSide (reverseFaceSide flipped d)) = ∑ d, areaSide d at heq
    simp only [hneg,Finset.sum_neg_distrib] at heq
    linarith only [heq]
  let areaFace (i : Fin 16) :=
    let (a,b,c) := markedFace flipped i
    complexCross (P i b-P i a) (P i c-P i a)
  have hparts (i : Fin 16) : ∑ d : Fin 3, areaSide (i,d) = areaFace i := by
    rw [Fin.sum_univ_three]
    rcases hf : markedFace flipped i with ⟨a,b,c⟩
    simp only [areaSide,areaFace,sideLabels,hf]
    change complexCross (P i a-C) (P i b-C) + complexCross (P i b-C) (P i c-C) +
      complexCross (P i c-C) (P i a-C) = complexCross (P i b-P i a) (P i c-P i a)
    simp only [complexCross_apply,Complex.sub_re,Complex.sub_im]
    ring
  have hsumpos : 0 < ∑ i, areaFace i := Finset.sum_pos
    (fun j _ => (markedDevelopment flipped q he j).orientation) Finset.univ_nonempty
  rw [Fintype.sum_prod_type] at hsum
  simp only [hparts] at hsum
  exact hsumpos.ne' hsum

/-- Both generators are translations. A nonidentity multiplier would give a
common fixed point by commutation, contradicting the area calculation. -/
theorem generator_multipliers_one (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q))
    (hflat : ∀ v, coneAngles (faceChoice flipped) (Type2.euclideanPoint ∘ q) v = 2*Real.pi) :
    (edgeTransition flipped q he 1 2).multiplier = 1 ∧ (edgeTransition flipped q he 4 7).multiplier = 1 := by
  have hrel := markedTransitionRelations flipped q he hflat
  constructor
  · by_contra hm
    obtain ⟨C,hu,huniq⟩ := ComplexMotion.existsUnique_fixed_of_multiplier_ne_one (edgeTransition flipped q he 1 2) hm
    have hv := ComplexMotion.fixes_of_commute_of_unique_fixed hrel.commute hu huniq
    exact no_common_transition_center flipped q he C (all_transitions_fix_of_generators_fix flipped q he hrel hu hv)
  · by_contra hm
    obtain ⟨C,hv,huniq⟩ := ComplexMotion.existsUnique_fixed_of_multiplier_ne_one (edgeTransition flipped q he 4 7) hm
    have hu := ComplexMotion.fixes_of_commute_of_unique_fixed hrel.commute.symm hv huniq
    exact no_common_transition_center flipped q he C (all_transitions_fix_of_generators_fix flipped q he hrel hu hv)

theorem edgeTransition_multiplier_one (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q))
    (hflat : ∀ v, coneAngles (faceChoice flipped) (Type2.euclideanPoint ∘ q) v = 2*Real.pi)
    (a b : Vertex) (hs : HasSide flipped a b) : (edgeTransition flipped q he a b).multiplier = 1 := by
  have hrel := markedTransitionRelations flipped q he hflat
  obtain ⟨hu,hv⟩ := generator_multipliers_one flipped q he hflat
  have hinv (g : ComplexMotion) (hg : g.multiplier = 1) : (g⁻¹).multiplier = 1 := by
    have h := ComplexMotion.multiplier_mul g g⁻¹
    simpa only [mul_inv_cancel,ComplexMotion.multiplier_one,hg,one_mul] using h.symm
  have hforward (a b : Vertex) (hab : a < b) (hs : HasSide flipped a b) :
      (edgeTransition flipped q he a b).multiplier = 1 := by
    rcases edge_cases flipped a b hab hs with ht | hr
    · rw [edgeTransition_of_onTree flipped q he a b hs ht,ComplexMotion.multiplier_one]
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with hr|hr|hr|hr|hr|hr|hr|hr|hr <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj hr <;>
        first
        | exact hu
        | exact hv
        | rw [hrel.edge01,ComplexMotion.multiplier_mul,hu,hv,one_mul]
        | rw [hrel.edge02]; exact hinv _ hu
        | rw [hrel.edge03,ComplexMotion.multiplier_one]
        | rw [hrel.edge05,ComplexMotion.multiplier_one]
        | rw [hrel.edge06,ComplexMotion.multiplier_one]
        | rw [hrel.edge07]; exact hinv _ hv
        | rw [hrel.edge14]; exact hv
  rcases lt_or_gt_of_ne (labels_of_hasSide flipped a b hs).1 with hlt | hlt
  · exact hforward a b hlt hs
  · have hr := hasSide_rev flipped a b hs
    rw [edgeTransition_rev flipped q he b a hr]
    exact hinv _ (hforward b a hlt hr)

end OrigamiTorus.Type7
