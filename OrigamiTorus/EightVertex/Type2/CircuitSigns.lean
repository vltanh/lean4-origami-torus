module

public import OrigamiTorus.EightVertex.Type2.BracketSigns
public import OrigamiTorus.Geometry.EmbeddedEdges
import Mathlib.Tactic

/-! The affine dependence and sign partitions of Type 2 circuits. -/

public section

open Set
open scoped BigOperators

namespace OrigamiTorus.Type2

@[expose] def natPlacement (r : Vertex → Point3) (i : ℕ) : Point3 := r (Fin.ofNat 8 i)

theorem vertex_label_val {i : ℕ} (hi : i < 8) : (Fin.ofNat 8 i).val = i :=
  Nat.mod_eq_of_lt hi

theorem natPlacement_val (r : Vertex → Point3) (v : Vertex) : natPlacement r v.val = r v := by
  simp only [natPlacement,Fin.ofNat_val_eq_self]

theorem natPlacement_ordered_minors (r : Vertex → Point3)
    (h : GenericLift (fun v => ((r v).1,(r v).2.1)) (fun v => (r v).2.2))
    (a b c d : ℕ) (ha : a < b) (hb : b < c) (hc : c < d) (hd : d < 8) :
    affineBracket (natPlacement r a) (natPlacement r b) (natPlacement r c) (natPlacement r d) ≠ 0 := by
  have hab : Fin.ofNat 8 a < Fin.ofNat 8 b := by
    change (Fin.ofNat 8 a).val < (Fin.ofNat 8 b).val
    rwa [vertex_label_val (ha.trans (hb.trans (hc.trans hd))),vertex_label_val (hb.trans (hc.trans hd))]
  have hbc : Fin.ofNat 8 b < Fin.ofNat 8 c := by
    change (Fin.ofNat 8 b).val < (Fin.ofNat 8 c).val
    rwa [vertex_label_val (hb.trans (hc.trans hd)),vertex_label_val (hc.trans hd)]
  have hcd : Fin.ofNat 8 c < Fin.ofNat 8 d := by
    change (Fin.ofNat 8 c).val < (Fin.ofNat 8 d).val
    rwa [vertex_label_val (hc.trans hd),vertex_label_val hd]
  simpa only [volume_eq_affineBracket,natPlacement] using
    h (Fin.ofNat 8 a) (Fin.ofNat 8 b) (Fin.ofNat 8 c) (Fin.ofNat 8 d) hab hbc hcd

theorem natPlacement_hull (r : Vertex → Point3) (s : Finset ℕ) :
    vertexHull (natPlacement r) s = vertexHull r (s.image (Fin.ofNat 8)) := by
  unfold vertexHull
  rw [Finset.coe_image,Set.image_image]
  rfl

@[expose] def faceLabels (f : Triangle) : List ℕ := (triangleVertices f).map Fin.val

theorem faceLabels_bounds {f : Triangle} {a : ℕ} (ha : a ∈ faceLabels f) : a < 8 := by
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
  exact v.isLt

theorem faceLabels_toFinset (f : Triangle) :
    (faceLabels f).toFinset.image (Fin.ofNat 8) = triangleVertexSet f := by
  ext v
  simp only [Finset.mem_image,triangleVertexSet,List.mem_toFinset]
  constructor
  · rintro ⟨i,hi,he⟩
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
    rw [Fin.ofNat_val_eq_self] at he
    exact he ▸ hw
  · intro hv
    exact ⟨v.val,List.mem_map.mpr ⟨v,hv,rfl⟩,Fin.ofNat_val_eq_self v⟩

theorem disjoint_fin_labels {s t : Finset ℕ} (hs : ∀ a ∈ s, a < 8) (ht : ∀ a ∈ t, a < 8)
    (hD : Disjoint s t) : Disjoint (s.image (Fin.ofNat 8)) (t.image (Fin.ofNat 8)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,he'⟩ := Finset.mem_image.mp hx'
  have heq := congrArg Fin.val (he.trans he'.symm)
  rw [vertex_label_val (hs a ha),vertex_label_val (ht b hb)] at heq
  exact Finset.disjoint_left.mp hD ha (heq.symm ▸ hb)

theorem natPlacement_edge_face_for {fs : List Triangle} (r : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles fs r))
    (a b : ℕ) (f : List ℕ) (ha : a < 8) (hb : b < 8) (heAB : Adjacent fs (Fin.ofNat 8 a) (Fin.ofNat 8 b))
    (hf : ∃ f' ∈ fs, f.toFinset = (faceLabels f').toFinset) (hdis : Disjoint ({a,b} : Finset ℕ) f.toFinset) :
    Disjoint (vertexHull (natPlacement r) {a,b}) (vertexHull (natPlacement r) f.toFinset) := by
  let A := Fin.ofNat 8 a
  let B := Fin.ofNat 8 b
  obtain ⟨f',hf',hEq⟩ := hf
  have hImage : f.toFinset.image (Fin.ofNat 8) = triangleVertexSet f' := by
    rw [hEq,faceLabels_toFinset]
  have hAB : ({a,b} : Finset ℕ).image (Fin.ofNat 8) = {A,B} := by simp [A,B]
  have hEdgeBounds (i : ℕ) (hi : i ∈ ({a,b} : Finset ℕ)) : i < 8 := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption
  have hFaceBounds (i : ℕ) (hi : i ∈ f.toFinset) : i < 8 := by
    rw [hEq] at hi
    exact faceLabels_bounds (List.mem_toFinset.mp hi)
  have htyped := disjoint_fin_labels hEdgeBounds hFaceBounds hdis
  rw [hAB,hImage] at htyped
  have hedge : ({A,B} : Finset Vertex) ∈ (triangleComplex fs).faces :=
    adjacent_pair_face heAB
  have hface : triangleVertexSet f' ∈ (triangleComplex fs).faces :=
    ⟨⟨f'.1,by simp [triangleVertexSet,triangleVertices]⟩,f',hf',le_rfl⟩
  rw [natPlacement_hull,natPlacement_hull,hAB,hImage]
  exact disjoint_vertexHull_of_injective_evaluateTriangles fs r he _ _ hedge hface htyped

theorem natPlacement_strict_support_for {fs : List Triangle} (r : Vertex → Point3)
    (h : ∀ v, HasStrictSupport fs r v) (v : ℕ) (s : List ℕ)
    (hs : ∀ w ∈ s, Adjacent fs (Fin.ofNat 8 v) (Fin.ofNat 8 w)) :
    natPlacement r v ∉ vertexHull (natPlacement r) s.toFinset := by
  rw [natPlacement_hull,natPlacement]
  apply strictSupport_not_mem_neighborHull fs r _ _ ?_ (h _)
  intro x hx
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hx
  exact hs w (List.mem_toFinset.mp hw)

private def label (Q : List ℕ) (hQ : Q.length = 5) (i : Fin 5) : ℕ :=
  Q[i.val]'(by simpa only [hQ] using i.isLt)

private def coefficient (p : ℕ → Point3) (Q : List ℕ) (i : Fin 5) : ℝ :=
  if i.val % 2 = 0 then bracketValue p (Q.eraseIdx i.val) else -bracketValue p (Q.eraseIdx i.val)

private def coefficientLiteral (Q : List ℕ) (i : Fin 5) : Sign :=
  if i.val % 2 == 0 then bracket (Q.eraseIdx i.val) else negate (bracket (Q.eraseIdx i.val))

private theorem coefficient_relation (p : ℕ → Point3) (Q : List ℕ) (hlen : Q.length = 5) :
    (∑ i, coefficient p Q i) = 0 ∧
      (∑ i, coefficient p Q i • p (label Q hlen i)) = 0 := by
  rcases Q with _ | ⟨a,_ | ⟨b,_ | ⟨c,_ | ⟨d,_ | ⟨e,_ | ⟨f,Q⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons,List.length_nil] at hlen <;> try omega
  constructor
  · simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change affineBracket (p b) (p c) (p d) (p e) +
      (-affineBracket (p a) (p c) (p d) (p e) +
      (affineBracket (p a) (p b) (p d) (p e) +
      (-affineBracket (p a) (p b) (p c) (p e) + affineBracket (p a) (p b) (p c) (p d)))) = 0
    linarith [affineBracket_circuitSum (p a) (p b) (p c) (p d) (p e)]
  · simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change affineBracket (p b) (p c) (p d) (p e) • p a +
      ((-affineBracket (p a) (p c) (p d) (p e)) • p b +
      (affineBracket (p a) (p b) (p d) (p e) • p c +
      ((-affineBracket (p a) (p b) (p c) (p e)) • p d + affineBracket (p a) (p b) (p c) (p d) • p e))) = 0
    simpa only [sub_eq_add_neg,neg_smul,add_assoc] using
      affineBracket_circuitVector (p a) (p b) (p c) (p d) (p e)

private theorem coefficientLiteral_truth (p : ℕ → Point3) (mark : ℕ → Bool)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0)
    (Q : List ℕ) (hL : Q.length = 5) (hn : Q.Nodup) (hV : ∀ x ∈ Q, x < 8)
    (i : Fin 5) :
    coefficient p Q i ≠ 0 ∧
      (determinantAssignment p mark (coefficientLiteral Q i).1 = (coefficientLiteral Q i).2 ↔
        0 < coefficient p Q i) := by
  have hsub := List.eraseIdx_sublist Q i.val
  have hlen : (Q.eraseIdx i.val).length = 4 := by
    have hi : i.val < Q.length := by simpa only [hL] using i.isLt
    rw [List.length_eraseIdx_of_lt hi,hL]
  have hn' := hsub.nodup hn
  have hv' : ∀ x ∈ Q.eraseIdx i.val, x < 8 := fun x hx => hV x (hsub.subset hx)
  have hb := bracketValue_ne_zero_of_ordered_minors p hp hlen hn' hv'
  by_cases he : i.val % 2 = 0
  · simp only [coefficient,coefficientLiteral,beq_iff_eq,he,ite_true]
    exact ⟨hb,determinantAssignment_bracket p mark hlen hn' hv' hb⟩
  · simp only [coefficient,coefficientLiteral,beq_iff_eq,he,ite_false]
    exact ⟨neg_ne_zero.mpr hb,
      (determinantAssignment_negate_bracket p mark hlen hn' hv' hb).trans neg_pos.symm⟩

private def partitionLiterals (Q : List ℕ) (side : ℕ → Bool) : SignClause :=
  List.zipWith (fun l v => if side v then l else negate l) (circuit Q) Q

private theorem coefficientLiteral_mem_partition (Q : List ℕ) (hL : Q.length = 5)
    (side : ℕ → Bool) (i : Fin 5) :
    (if side (label Q hL i) then coefficientLiteral Q i else negate (coefficientLiteral Q i)) ∈
      partitionLiterals Q side := by
  have hcl : (circuit Q).length = 5 := by simp [circuit]
  have hi : i.val < (partitionLiterals Q side).length := by simp [partitionLiterals,hcl,hL]
  have hh : (partitionLiterals Q side)[i.val]'hi =
      (if side (label Q hL i) then coefficientLiteral Q i else negate (coefficientLiteral Q i)) := by
    simp only [partitionLiterals,List.getElem_zipWith,circuit,List.getElem_map,List.getElem_range,
      label,coefficientLiteral]
    rfl
  rw [← hh]
  exact List.getElem_mem hi

private theorem forbidden_partition_sound (p : ℕ → Point3) (mark : ℕ → Bool)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0)
    (Q : List ℕ) (hL : Q.length = 5) (hn : Q.Nodup) (hV : ∀ x ∈ Q, x < 8) (side : ℕ → Bool)
    (hd : Disjoint (vertexHull p (Q.filter side).toFinset)
      (vertexHull p (Q.filter fun v => !side v).toFinset)) :
    ∀ C ∈ forbid (partitionLiterals Q side), ∃ l ∈ C, determinantAssignment p mark l.1 = l.2 := by
  classical
  let A := determinantAssignment p mark
  let vals := coefficient p Q
  let labels := label Q hL
  let ls := partitionLiterals Q side
  intro C hC
  by_contra! hc
  change ∀ l ∈ C, ¬ A l.1 = l.2 at hc
  have ho : ∃ orient : Bool, ∀ l ∈ ls, (A l.1 = l.2) ↔ orient = true := by
    change C ∈ [ls,ls.map negate] at hC
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hC
    rcases hC with hC | hC
    · exact ⟨false,fun l hl => by simp [hc l (hC.symm ▸ hl)]⟩
    · refine ⟨true,fun l hl => ?_⟩
      have hA : A l.1 = l.2 := not_not.mp (fun hf => hc (negate l)
        (hC.symm ▸ (List.mem_map_of_mem hl : negate l ∈ ls.map negate)) ((literal_negate_iff A l).mpr hf))
      simp [hA]
  obtain ⟨orient,ho⟩ := ho
  have hSem (i : Fin 5) := coefficientLiteral_truth p mark hp Q hL hn hV i
  have hAlign (i : Fin 5) : 0 < vals i ↔ side (labels i) = orient := by
    have hsign : A (coefficientLiteral Q i).1 = (coefficientLiteral Q i).2 ↔ 0 < vals i := (hSem i).2
    have ht := ho _ (coefficientLiteral_mem_partition Q hL side i)
    change (A (if side (labels i) then coefficientLiteral Q i else negate (coefficientLiteral Q i)).1 =
      (if side (labels i) then coefficientLiteral Q i else negate (coefficientLiteral Q i)).2) ↔ orient = true at ht
    cases orient <;> cases hs : side (labels i) <;>
      simp only [hs,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false,literal_negate_iff,hsign,
        iff_false,iff_true,not_not] at ht ⊢ <;> tauto
  have hnz : vals ≠ 0 := fun he => (hSem 0).1 (congrFun he 0)
  have hrel := coefficient_relation p Q hL
  obtain ⟨x,hx,hy⟩ := vertexHull_inter_of_signed_relation (p ∘ labels) vals hnz hrel.1 hrel.2
  have hmono {S : Finset (Fin 5)} {T : Finset ℕ} (hST : ∀ i ∈ S, labels i ∈ T) :
      vertexHull (p ∘ labels) S ⊆ vertexHull p T := by
    apply convexHull_mono
    rintro _ ⟨i,hi,rfl⟩
    exact ⟨labels i,hST i hi,rfl⟩
  have hmem (i : Fin 5) : labels i ∈ Q := List.getElem_mem _
  have hpos : x ∈ vertexHull p (Q.filter fun v => side v == orient).toFinset := by
    apply hmono ?_ hx
    intro i hi
    have h := (hAlign i).mp (Finset.mem_filter.mp hi).2
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hmem i,by simp [h]⟩)
  have hneg : x ∈ vertexHull p (Q.filter fun v => side v == !orient).toFinset := by
    apply hmono ?_ hy
    intro i hi
    have hn' : side (labels i) ≠ orient := fun he =>
      (Finset.mem_filter.mp hi).2.not_gt ((hAlign i).mpr he)
    have hne : side (labels i) = !orient := by
      cases hEq : side (labels i) <;> cases orient <;> simp_all only [Bool.not_true,Bool.not_false,
        Bool.true_eq_false,Bool.false_eq_true]
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hmem i,by simp [hne]⟩)
  cases orient
  · exact Set.disjoint_left.mp hd.symm (by simpa using hpos) (by simpa using hneg)
  · exact Set.disjoint_left.mp hd (by simpa using hpos) (by simpa using hneg)

private theorem partitionLiterals_true (Q : List ℕ) (hL : Q.length = 5) :
    partitionLiterals Q (fun _ => true) = circuit Q := by
  have hlen : (circuit Q).length = Q.length := by simp [circuit,hL]
  have hzip (L : SignClause) (R : List ℕ) (he : L.length = R.length) :
      List.zipWith (fun (l : Sign) (_ : ℕ) => l) L R = L := by
    induction L generalizing R with
    | nil => simp
    | cons l L ih =>
      cases R with
      | nil => simp at he
      | cons a R => simp [List.zipWith,ih R (by simpa using he)]
  exact hzip _ _ hlen

@[expose] def circuitFor (fs : List (List Nat)) (edge : Nat → Nat → Bool) (q : List Nat) : List SignClause :=
    let signs := circuit q
    let forbidPartition (side : List Nat) :=
      forbid (List.zipWith (fun l v => if side.contains v then l else negate l) signs q)
    forbid signs ++
      ((choose 2 q).filter fun e =>
        match e with
        | [a,b] => edge a b && fs.contains (q.filter fun v => !e.contains v)
        | _ => false).flatMap forbidPartition ++
      (q.filter fun v => (q.filter (· != v)).all (edge v)).flatMap
        (fun v => forbidPartition [v])

theorem circuitFor_sound (fs : List (List Nat)) (edge : ℕ → ℕ → Bool)
    (p : ℕ → Point3) (mark : ℕ → Bool)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0)
    (hEF : ∀ a b f, a < 8 → b < 8 → edge a b = true → f ∈ fs → Disjoint ({a,b} : Finset ℕ) f.toFinset →
      Disjoint (vertexHull p {a,b}) (vertexHull p f.toFinset))
    (hSup : ∀ v (s : List ℕ), v < 8 → (∀ w ∈ s, w < 8 ∧ edge v w = true) → p v ∉ vertexHull p s.toFinset)
    (Q : List ℕ) (hL : Q.length = 5) (hn : Q.Nodup) (hV : ∀ x ∈ Q, x < 8) :
    ∀ C ∈ circuitFor fs edge Q, ∃ l ∈ C, determinantAssignment p mark l.1 = l.2 := by
  intro C hC
  simp only [circuitFor,List.append_assoc,List.mem_append,List.mem_flatMap,List.mem_filter] at hC
  rcases hC with hC | ⟨E,⟨hE,hEF'⟩,hC⟩ | ⟨v,⟨hv,hs⟩,hC⟩
  · have hD : Disjoint (vertexHull p (Q.filter fun _ => true).toFinset)
        (vertexHull p (Q.filter fun _ => !true).toFinset) := by simp [vertexHull]
    have hpart := forbidden_partition_sound p mark hp Q hL hn hV (fun _ => true) hD C
    rw [partitionLiterals_true Q hL] at hpart
    exact hpart hC
  · have hE' := (mem_choose_iff _ _ _).mp hE
    have hElen := hE'.2
    rcases E with _ | ⟨a,_ | ⟨b,_ | ⟨c,E⟩⟩⟩ <;>
      simp only [List.length_nil,List.length_cons] at hElen <;> try omega
    let f := Q.filter (fun v => !([a,b] : List ℕ).contains v)
    change (edge a b && fs.contains f) = true at hEF'
    simp only [Bool.and_eq_true,List.contains_iff_mem] at hEF'
    have hD : Disjoint ({a,b} : Finset ℕ) f.toFinset := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have hHi : i ∈ ([a,b] : List ℕ) := by simpa using hi
      have hHj := (List.mem_filter.mp (List.mem_toFinset.mp hj)).2
      simp [hHi] at hHj
    have hLeft : (Q.filter (fun v => ([a,b] : List ℕ).contains v)).toFinset = {a,b} := by
      ext i
      simp only [List.mem_toFinset,List.mem_filter,List.contains_iff_mem]
      constructor
      · intro hi
        simpa using hi.2
      · intro hi
        have hMem : i ∈ ([a,b] : List ℕ) := by simpa using hi
        exact ⟨hE'.1.subset hMem,hMem⟩
    apply forbidden_partition_sound p mark hp Q hL hn hV (fun v => ([a,b] : List ℕ).contains v) _ C hC
    rw [hLeft]
    exact hEF a b f (hV a (hE'.1.subset (by simp))) (hV b (hE'.1.subset (by simp))) hEF'.1 hEF'.2 hD
  · let f := Q.filter (· != v)
    have hSup' : p v ∉ vertexHull p f.toFinset := hSup v f (hV v hv)
      (fun w hw => ⟨hV w (List.mem_filter.mp hw).1,List.all_eq_true.mp hs w hw⟩)
    have hLeft : (Q.filter (fun w => ([v] : List ℕ).contains w)).toFinset = {v} := by
      ext i
      simp only [List.mem_toFinset,List.mem_filter,List.contains_iff_mem,List.mem_singleton,Finset.mem_singleton]
      constructor
      · exact And.right
      · rintro rfl
        exact ⟨hv,rfl⟩
    have hRight : Q.filter (fun w => !([v] : List ℕ).contains w) = f := by
      congr 1
      funext w
      by_cases h : w = v <;> simp [bne,h]
    apply forbidden_partition_sound p mark hp Q hL hn hV (fun w => ([v] : List ℕ).contains w) _ C hC
    rw [hLeft,hRight]
    apply disjoint_left.mpr
    intro x hx hy
    have hx' : x = p v := by simpa [vertexHull] using hx
    exact hSup' (hx' ▸ hy)

/-- The circuit clauses hold for every general-position placement that
separates disjoint edges and faces and has a strict support at every vertex. -/
theorem determinantAssignment_satisfies_circuitClauses (p : ℕ → Point3) (mark : ℕ → Bool)
    (hp : ∀ a b c d : ℕ, a < b → b < c → c < d → d < 8 →
      affineBracket (p a) (p b) (p c) (p d) ≠ 0)
    (hEF : ∀ a b f, a < 8 → b < 8 → isEdge a b = true → f ∈ faces → Disjoint ({a,b} : Finset ℕ) f.toFinset →
      Disjoint (vertexHull p {a,b}) (vertexHull p f.toFinset))
    (hSup : ∀ v (s : List ℕ), v < 8 → (∀ w ∈ s, w < 8 ∧ isEdge v w = true) → p v ∉ vertexHull p s.toFinset) :
    ∀ C ∈ circuitClauses, ∃ l ∈ C, determinantAssignment p mark l.1 = l.2 := by
  intro C hC
  obtain ⟨Q,hQ,hC⟩ := List.mem_flatMap.mp hC
  have hQ' := (mem_choose_iff _ _ _).mp hQ
  exact circuitFor_sound faces isEdge p mark hp hEF hSup Q hQ'.2 (hQ'.1.nodup List.nodup_range)
    (fun x hx => List.mem_range.mp (hQ'.1.subset hx)) C hC

end OrigamiTorus.Type2
