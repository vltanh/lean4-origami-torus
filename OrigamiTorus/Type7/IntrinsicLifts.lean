module

public import OrigamiTorus.Type7.Translations
import Mathlib.Tactic

/-! The translational face gluing gives the periodic Type 7 lift table. -/

@[expose] public section

namespace OrigamiTorus.Type7

variable (flipped : Bool)

/-- Interpret an integer pair in the developed period basis. -/
def complexPeriod (U V : ℂ) (d : Period) : ℂ := (d.1 : ℂ)*U+(d.2 : ℂ)*V

@[simp] theorem complexPeriod_zero (U V : ℂ) : complexPeriod U V 0 = 0 := by
  simp [complexPeriod]

theorem complexPeriod_sub (U V : ℂ) (d e : Period) :
    complexPeriod U V (d-e) = complexPeriod U V d-complexPeriod U V e := by
  simp only [complexPeriod,Prod.fst_sub,Prod.snd_sub,Int.cast_sub]
  ring

theorem complexPeriod_neg (U V : ℂ) (d : Period) : complexPeriod U V (-d) = -complexPeriod U V d := by
  simp only [complexPeriod,Prod.fst_neg,Prod.snd_neg,Int.cast_neg]
  ring

/-- The integer change of copies of the initial vertex of a directed side. -/
def transitionShift (a b : Vertex) : Period :=
  facePeriod (chartLifts flipped (leftFace flipped b a)) a - facePeriod (chartLifts flipped (leftFace flipped a b)) a

theorem transitionShift_rev (a b : Vertex) (hs : HasSide flipped a b) :
    transitionShift flipped b a = - transitionShift flipped a b := by
  revert a b
  cases flipped <;> decide +kernel

private theorem transitionShift_tree (a b : Vertex) (hs : HasSide flipped a b) (h : OnDevelopmentTree flipped a b) :
    transitionShift flipped a b = 0 := by
  revert a b
  cases flipped <;> decide +kernel

private theorem transitionShift_table :
    transitionShift flipped 0 1 = (0,1) ∧ transitionShift flipped 0 2 = (1,-1) ∧
    transitionShift flipped 0 3 = 0 ∧ transitionShift flipped 0 5 = 0 ∧ transitionShift flipped 0 6 = 0 ∧
    transitionShift flipped 0 7 = (-1,0) ∧ transitionShift flipped 1 4 = (1,0) ∧
    transitionShift flipped 1 2 = (-1,1) ∧ transitionShift flipped 4 7 = (1,0) := by
  cases flipped <;> decide +kernel

/-- Each actual gluing translation is the entry from the integer shift table
in the basis encoded by the two generators. -/
theorem edgeTransition_offset (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q))
    (hflat : ∀ v, coneAngles (faceChoice flipped) (Type2.euclideanPoint ∘ q) v = 2*Real.pi)
    (a b : Vertex) (hs : HasSide flipped a b) :
    let U := edgeTransition flipped q he 4 7 0
    let V := edgeTransition flipped q he 1 2 0+U
    edgeTransition flipped q he a b 0 = complexPeriod U V (transitionShift flipped a b) := by
  let U := edgeTransition flipped q he 4 7 0
  let V := edgeTransition flipped q he 1 2 0+U
  have hr := markedTransitionRelations flipped q he hflat
  obtain ⟨hu,hv⟩ := generator_multipliers_one flipped q he hflat
  obtain ⟨h01,h02,h03,h05,h06,h07,h14,h12,h47⟩ := transitionShift_table flipped
  have hf (a b : Vertex) (hab : a < b) (hs : HasSide flipped a b) :
      edgeTransition flipped q he a b 0 = complexPeriod U V (transitionShift flipped a b) := by
    rcases edge_cases flipped a b hab hs with ht | hrest
    · rw [edgeTransition_of_onTree flipped q he a b hs ht,transitionShift_tree flipped a b hs ht,complexPeriod_zero]
      rfl
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hrest
      rcases hrest with h|h|h|h|h|h|h|h|h
      all_goals obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
      · rw [hr.edge01,h01]
        change edgeTransition flipped q he 4 7 (edgeTransition flipped q he 1 2 0) = _
        rw [ComplexMotion.apply_eq _ (edgeTransition flipped q he 1 2 0),hv,one_mul]
        simp [complexPeriod,U,V]
      · rw [hr.edge02,ComplexMotion.inverse_offset _ hu,h02]
        simp [complexPeriod,U,V]
      · rw [hr.edge03,h03,complexPeriod_zero]; rfl
      · rw [hr.edge05,h05,complexPeriod_zero]; rfl
      · rw [hr.edge06,h06,complexPeriod_zero]; rfl
      · rw [hr.edge07,ComplexMotion.inverse_offset _ hv,h07]
        simp [complexPeriod,U]
      · rw [hr.edge14,h14]
        simp [complexPeriod,U]
      · rw [h12]
        simp [complexPeriod,V]
      · rw [h47]
        simp [complexPeriod,U]
  change edgeTransition flipped q he a b 0 = complexPeriod U V (transitionShift flipped a b)
  rcases lt_or_gt_of_ne (labels_of_hasSide flipped a b hs).1 with hab | hab
  · exact hf a b hab hs
  · have hrev := hasSide_rev flipped a b hs
    rw [edgeTransition_rev flipped q he b a hrev,
      ComplexMotion.inverse_offset _ (edgeTransition_multiplier_one flipped q he hflat b a hrev),
      hf b a hab hrev,transitionShift_rev flipped b a hrev,complexPeriod_neg]

/-- A chosen copy of each label whose two assigned period shifts vanish. -/
def representativeFace : Vertex → Fin 16 :=
  ![3,4,1,0,7,if flipped then 1 else 0,0,14]

private theorem representative_mem (a : Vertex) :
    a ∈ triangleVertexSet (markedFace flipped (representativeFace flipped a)) ∧
      facePeriod (chartLifts flipped (representativeFace flipped a)) a = 0 := by
  revert a
  cases flipped <;> decide +kernel

private theorem face_in_link (a : Vertex) (j : Fin 16) (hj : a ∈ triangleVertexSet (markedFace flipped j)) :
    ∃ i : Fin (linkSize flipped a), leftFace flipped a (linkLabel flipped a i) = j := by
  revert a j
  cases flipped <;> decide +kernel

/-- The copies of every spatial vertex in the full development differ by the
integer periods of the marked lift table. -/
theorem markedDevelopment_periodic (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles (faceChoice flipped) q))
    (hflat : ∀ v, coneAngles (faceChoice flipped) (Type2.euclideanPoint ∘ q) v = 2*Real.pi) :
    let P (j : Fin 16) := (markedDevelopment flipped q he j).point
    let (U,V) := chartMarkingDisplacements flipped (spatialEdgeSq q)
    ∀ j a, a ∈ triangleVertexSet (markedFace flipped j) →
      P j a = P (representativeFace flipped a) a + complexPeriod U V (facePeriod (chartLifts flipped j) a) := by
  let P (j : Fin 16) := (markedDevelopment flipped q he j).point
  let U := edgeTransition flipped q he 4 7 0
  let V := edgeTransition flipped q he 1 2 0+U
  let R (j : Fin 16) (a : Vertex) := P j a-complexPeriod U V (facePeriod (chartLifts flipped j) a)
  have hstep (a : Vertex) (i : Fin (linkSize flipped a)) :
      R (leftFace flipped a (linkLabel flipped a i)) a =
        R (leftFace flipped a (linkLabel flipped a ((finRotate _).symm i))) a := by
    let b := linkLabel flipped a i
    let l := leftFace flipped a b
    let r := leftFace flipped b a
    have hs : HasSide flipped a b := (link_incidence flipped a i).1
    have hf : r = leftFace flipped a (linkLabel flipped a ((finRotate _).symm i)) :=
      (link_incidence flipped a i).2.1
    have h := edgeTransition_apply_a flipped q he a b hs
    change edgeTransition flipped q he a b (P l a) = P r a at h
    rw [ComplexMotion.apply_eq _ (P l a),edgeTransition_multiplier_one flipped q he hflat a b hs,one_mul] at h
    have ho : edgeTransition flipped q he a b 0 = complexPeriod U V (transitionShift flipped a b) :=
      edgeTransition_offset flipped q he hflat a b hs
    rw [ho] at h
    have he' : transitionShift flipped a b = facePeriod (chartLifts flipped r) a -
      facePeriod (chartLifts flipped l) a := rfl
    rw [he',complexPeriod_sub] at h
    have hR : R l a = R r a := by
      dsimp only [R]
      linear_combination h
    rw [hf] at hR
    exact hR
  have hl (a : Vertex) (i : Fin (linkSize flipped a)) :
      R (leftFace flipped a (linkLabel flipped a i)) a =
        R (leftFace flipped a (linkLabel flipped a ⟨0, Nat.succ_pos _⟩)) a :=
    eq_initial_of_eq_predecessor (fun j => R (leftFace flipped a (linkLabel flipped a j)) a) (hstep a) i
  have hmatch (j : Fin 16) (a : Vertex) (ha : a ∈ triangleVertexSet (markedFace flipped j)) :
      P j a = P (representativeFace flipped a) a + complexPeriod U V (facePeriod (chartLifts flipped j) a) := by
    obtain ⟨i,hi⟩ := face_in_link flipped a j ha
    obtain ⟨r,hr⟩ := face_in_link flipped a (representativeFace flipped a) (representative_mem flipped a).1
    have heq := (hl a i).trans (hl a r).symm
    rw [hi,hr] at heq
    dsimp only [R] at heq
    rw [(representative_mem flipped a).2,complexPeriod_zero,sub_zero] at heq
    exact sub_eq_iff_eq_add.mp heq
  have hmark : chartMarkingDisplacements flipped (spatialEdgeSq q) = (U,V) := by
    rw [markedDevelopment_displacements flipped]
    change (P 2 4-P 7 4,P 3 0-P 6 0) = (U,V)
    rw [hmatch 2 4 (by cases flipped <;> decide +kernel),hmatch 7 4 (by cases flipped <;> decide +kernel),
      hmatch 3 0 (by cases flipped <;> decide +kernel),hmatch 6 0 (by cases flipped <;> decide +kernel)]
    have hk : facePeriod (chartLifts flipped 2) 4 = (1,0) ∧
        facePeriod (chartLifts flipped 7) 4 = 0 ∧ facePeriod (chartLifts flipped 3) 0 = 0 ∧
        facePeriod (chartLifts flipped 6) 0 = (0,-1) := by cases flipped <;> decide +kernel
    rw [hk.1,hk.2.1,hk.2.2.1,hk.2.2.2]
    change (P (representativeFace flipped 4) 4+complexPeriod U V (1,0)-
        (P (representativeFace flipped 4) 4+complexPeriod U V 0),
      P (representativeFace flipped 0) 0+complexPeriod U V 0-
        (P (representativeFace flipped 0) 0+complexPeriod U V (0,-1))) = _
    apply Prod.ext <;> simp [complexPeriod]
  rw [hmark]
  exact hmatch

end OrigamiTorus.Type7
