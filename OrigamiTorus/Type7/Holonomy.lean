module

public import OrigamiTorus.Type7.VertexHolonomy
import Mathlib.Tactic

/-! Reducing the edge identifications to the two marked generators. -/

@[expose] public section

namespace OrigamiTorus.Type7

variable (flipped : Bool)

/-- Membership in the dual tree, independent of traversal direction. -/
def OnDevelopmentTree (a b : Vertex) : Prop :=
  ∃ j : Fin 15, (developmentTree flipped j).2 = (a,b) ∨ (developmentTree flipped j).2 = (b,a)

instance (a b : Vertex) : Decidable (OnDevelopmentTree flipped a b) := inferInstanceAs
  (Decidable (∃ j : Fin 15, (developmentTree flipped j).2 = (a,b) ∨ (developmentTree flipped j).2 = (b,a)))

theorem edgeTransition_of_onTree (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (a b : Vertex)
    (hs : HasSide flipped a b) (h : OnDevelopmentTree flipped a b) : edgeTransition flipped q he a b = 1 := by
  obtain ⟨j,hj⟩ := h
  have ht := edgeTransition_tree flipped q he j
  rcases ht' : developmentTree flipped j with ⟨⟨f,g⟩,c,d⟩
  rw [ht'] at ht hj
  change edgeTransition flipped q he c d = 1 at ht
  change (c,d) = (a,b) ∨ (c,d) = (b,a) at hj
  rcases hj with hj | hj
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hj
    exact ht
  · have hr := edgeTransition_rev flipped q he b a (hasSide_rev flipped a b hs)
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hj
    rw [hr,ht,inv_one]

/-- The transitions off the dual tree, in the directions of increasing labels. -/
structure MarkedTransitionRelations (G : Vertex → Vertex → ComplexMotion) : Prop where
  edge01 : G 0 1 = G 4 7 * G 1 2
  edge02 : G 0 2 = (G 1 2)⁻¹
  edge03 : G 0 3 = 1
  edge05 : G 0 5 = 1
  edge06 : G 0 6 = 1
  edge07 : G 0 7 = (G 4 7)⁻¹
  edge14 : G 1 4 = G 4 7
  commute : Commute (G 1 2) (G 4 7)

/-- Removing the tree sides leaves the same vertex words for both diagonals. -/
def nonTreeNeighbors (v : Vertex) : List Vertex :=
  ![[2,3,1,6,5,7], [4,2,0], [0,1], [0], [7,1], [0], [0], [0,4]] v

private theorem vertexTransition_of_nonTree (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q)) (v : Vertex) :
    vertexTransition flipped q he v = ((nonTreeNeighbors v).map (edgeTransition flipped q he v)).prod := by
  have labels : List.ofFn (linkLabel flipped v) = chartLink flipped v := by
    revert v
    cases flipped <;> decide +kernel
  have hall : ∀ s : Bool, ∀ v b : Vertex, b ∈ chartLink s v → HasSide s v b := by decide +kernel
  have htable : (chartLink flipped v).filter (fun b => !decide (OnDevelopmentTree flipped v b)) =
      nonTreeNeighbors v := by
    revert v
    cases flipped <;> decide +kernel
  let G := edgeTransition flipped q he v
  have hfilter (l : List Vertex) (hl : ∀ b ∈ l, HasSide flipped v b) :
      (l.map G).prod = ((l.filter fun b => !decide (OnDevelopmentTree flipped v b)).map G).prod := by
    induction l with
    | nil => rfl
    | cons b l ih =>
      have ht := ih (fun c hc => hl c (List.mem_cons_of_mem _ hc))
      by_cases hb : OnDevelopmentTree flipped v b
      · have hG : G b = 1 := edgeTransition_of_onTree flipped q he v b (hl b List.mem_cons_self) hb
        simp [List.filter_cons,hb,hG,ht]
      · simp [List.filter_cons,hb,ht]
  change (List.ofFn (G ∘ linkLabel flipped v)).prod = _
  rw [← List.map_ofFn,labels,hfilter (chartLink flipped v) (hall flipped v),htable]

theorem markedTransitionRelations (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q))
    (hflat : ∀ v, coneAngles (faceChoice flipped) (Type2.euclideanPoint ∘ q) v = 2*Real.pi) :
    MarkedTransitionRelations (edgeTransition flipped q he) := by
  let G := edgeTransition flipped q he
  have hrev (a b : Vertex) (hs : ∀ s : Bool, HasSide s a b) :
      G b a = (G a b)⁻¹ := edgeTransition_rev flipped q he a b (hs flipped)
  have hword (v : Vertex) : ((nonTreeNeighbors v).map (G v)).prod = 1 :=
    (vertexTransition_of_nonTree flipped q he v).symm.trans (vertexTransition_eq_one flipped q he hflat v)
  have h0 := hword 0
  have h1 := hword 1
  have h2 := hword 2
  have h3 := hword 3
  have h4 := hword 4
  have h5 := hword 5
  have h6 := hword 6
  have h7 := hword 7
  change G 0 2*(G 0 3*(G 0 1*(G 0 6*(G 0 5*(G 0 7*1))))) = 1 at h0
  change G 1 4*(G 1 2*(G 1 0*1)) = 1 at h1
  change G 2 0*(G 2 1*1) = 1 at h2
  change G 3 0*1 = 1 at h3
  change G 4 7*(G 4 1*1) = 1 at h4
  change G 5 0*1 = 1 at h5
  change G 6 0*1 = 1 at h6
  change G 7 0*(G 7 4*1) = 1 at h7
  simp only [hrev 0 1 (by decide +kernel),hrev 0 2 (by decide +kernel),hrev 1 2 (by decide +kernel),
    hrev 0 3 (by decide +kernel),hrev 1 4 (by decide +kernel),hrev 0 5 (by decide +kernel),
    hrev 0 6 (by decide +kernel),hrev 0 7 (by decide +kernel),hrev 4 7 (by decide +kernel),mul_one]
    at h0 h1 h2 h3 h4 h5 h6 h7
  have hc : G 0 3 = 1 := inv_eq_one.mp h3
  have hd : G 0 5 = 1 := inv_eq_one.mp h5
  have he' : G 0 6 = 1 := inv_eq_one.mp h6
  have hg : G 1 4 = G 4 7 := (mul_inv_eq_one.mp h4).symm
  have hb : G 0 2 = (G 1 2)⁻¹ := by
    have hh := mul_eq_one_iff_eq_inv.mp h2
    simpa using congrArg (fun x : ComplexMotion => x⁻¹) hh
  have hf : G 0 7 = (G 4 7)⁻¹ := by
    have hh := mul_eq_one_iff_eq_inv.mp h7
    simpa using congrArg (fun x : ComplexMotion => x⁻¹) hh
  have ha : G 0 1 = G 4 7 * G 1 2 := by
    rw [← mul_assoc,hg] at h1
    exact (mul_inv_eq_one.mp h1).symm
  rw [ha,hb,hc,hd,he',hf,one_mul,one_mul,one_mul] at h0
  have huv : Commute (G 1 2) (G 4 7) := by
    show G 1 2 * G 4 7 = G 4 7 * G 1 2
    calc
      _ = G 1 2 * ((G 1 2)⁻¹ * ((G 4 7 * G 1 2) * (G 4 7)⁻¹)) * G 4 7 := by rw [h0,mul_one]
      _ = _ := by group
  exact ⟨ha,hb,hc,hd,he',hf,hg,huv⟩

/-- Every increasing directed side is in the dual tree or in the complement listed above. -/
theorem edge_cases (a b : Vertex) (hab : a < b) (hs : HasSide flipped a b) :
    OnDevelopmentTree flipped a b ∨ (a,b) ∈ ([(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,4),(1,2),(4,7)] : List Edge) := by
  revert a b
  cases flipped <;> decide +kernel

theorem all_transitions_fix_of_generators_fix (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q))
    (hrel : MarkedTransitionRelations (edgeTransition flipped q he)) {C : ℂ}
    (hu : edgeTransition flipped q he 1 2 C = C) (hv : edgeTransition flipped q he 4 7 C = C) :
    ∀ a b, HasSide flipped a b → edgeTransition flipped q he a b C = C := by
  have hinv {g : ComplexMotion} (h : g C = C) : g⁻¹ C = C := by
    rw [AffineEquiv.inv_def]
    exact (AffineEquiv.symm_apply_eq _).mpr h.symm
  have hforward (a b : Vertex) (hab : a < b) (hs : HasSide flipped a b) : edgeTransition flipped q he a b C = C := by
    rcases edge_cases flipped a b hab hs with ht | hr
    · rw [edgeTransition_of_onTree flipped q he a b hs ht]
      rfl
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with hr|hr|hr|hr|hr|hr|hr|hr|hr <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj hr <;>
        first
        | exact hu
        | exact hv
        | rw [hrel.edge01]; change edgeTransition flipped q he 4 7 (edgeTransition flipped q he 1 2 C) = _; rw [hu,hv]
        | rw [hrel.edge02]; exact hinv hu
        | rw [hrel.edge03]; rfl
        | rw [hrel.edge05]; rfl
        | rw [hrel.edge06]; rfl
        | rw [hrel.edge07]; exact hinv hv
        | rw [hrel.edge14]; exact hv
  intro a b hs
  rcases lt_or_gt_of_ne (labels_of_hasSide flipped a b hs).1 with hlt | hlt
  · exact hforward a b hlt hs
  · have hr := hasSide_rev flipped a b hs
    rw [edgeTransition_rev flipped q he b a hr]
    exact hinv (hforward b a hlt hr)

end OrigamiTorus.Type7
