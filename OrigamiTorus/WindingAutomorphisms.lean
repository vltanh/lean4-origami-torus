module

public import OrigamiTorus.WindingMarkings
import Mathlib.Tactic

/-! Complete search for symmetries of the three triangulations. The search
extends partial vertex permutations and prunes incompatible edges and faces. -/

@[expose] public section

namespace OrigamiTorus.Winding.Triangulation

def mapTriangle (p : Vertex → Vertex) (f : Triangle) : Triangle :=
  (p f.1,p f.2.1,p f.2.2)

def faceSets (k : Triangulation) : Finset (Finset Vertex) :=
  (k.faces.map triangleVertexSet).toFinset

def IsAutomorphism (k : Triangulation) (p : Equiv.Perm Vertex) : Prop :=
  (k.faces.map (triangleVertexSet ∘ mapTriangle p)).toFinset = k.faceSets

theorem labelSet_map (p : Equiv.Perm Vertex) (f : Triangle) :
    triangleVertexSet (mapTriangle p f) = (triangleVertexSet f).map p.toEmbedding := by
  rcases f with ⟨a,b,c⟩
  simp [mapTriangle,triangleVertexSet_eq]

theorem edge_in_face (k : Triangulation) (a b : Vertex) :
    orderedEdge a b ∈ k.edges ↔ a ≠ b ∧
      ∃ f ∈ k.faces, a ∈ triangleVertexSet f ∧ b ∈ triangleVertexSet f := by
  revert a b
  cases k <;> decide +kernel

theorem automorphism_preserves_edge {k : Triangulation} {p : Equiv.Perm Vertex}
    (hp : k.IsAutomorphism p) (a b : Vertex) :
    orderedEdge (p a) (p b) ∈ k.edges ↔ orderedEdge a b ∈ k.edges := by
  have himg : (k.faces.map (triangleVertexSet ∘ mapTriangle p)).toFinset = k.faceSets := hp
  rw [edge_in_face,edge_in_face]
  constructor
  · rintro ⟨hne,f,hf,ha,hb⟩
    have hm : triangleVertexSet f ∈ k.faceSets := List.mem_toFinset.mpr (List.mem_map.mpr ⟨f,hf,rfl⟩)
    rw [← himg] at hm
    obtain ⟨g,hg,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    change triangleVertexSet (mapTriangle p g) = triangleVertexSet f at he
    rw [← he,labelSet_map] at ha hb
    exact ⟨fun h => hne (congrArg p h),g,hg,by simpa using ha,by simpa using hb⟩
  · rintro ⟨hne,f,hf,ha,hb⟩
    have hm : triangleVertexSet (mapTriangle p f) ∈ k.faceSets := by
      rw [← himg]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨f,hf,rfl⟩)
    obtain ⟨g,hg,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    exact ⟨p.injective.ne hne,g,hg,by rw [he,labelSet_map]; simpa using ha,
      by rw [he,labelSet_map]; simpa using hb⟩

def readLabels (s : List Vertex) (a : Vertex) : Vertex := s[a.val]?.getD 0

def validPrefix (k : Triangulation) (s : List Vertex) : Bool :=
  let vs := (List.finRange 8).take s.length
  (vs.all fun a => vs.all fun b =>
    k.edges.contains (orderedEdge (readLabels s a) (readLabels s b)) == k.edges.contains (orderedEdge a b)) &&
  (k.faces.all fun f =>
    !(decide (f.1.val < s.length ∧ f.2.1.val < s.length ∧ f.2.2.val < s.length)) ||
      decide (triangleVertexSet (mapTriangle (readLabels s) f) ∈ k.faceSets))

def permutationPrefixes (k : Triangulation) : ℕ → List (List Vertex)
  | 0 => [[]]
  | n+1 => (permutationPrefixes k n).flatMap fun s =>
    (((List.finRange 8).filter fun a => !s.contains a).map (fun a => s++[a])).filter k.validPrefix

def automorphismLabels (k : Triangulation) : List (List Vertex) :=
  (k.permutationPrefixes 8).filter fun s =>
    decide ((k.faces.map (triangleVertexSet ∘ mapTriangle (readLabels s))).toFinset = k.faceSets)

private theorem read_ofFn_take (p : Vertex → Vertex) {n : ℕ} {a : Vertex} (ha : a.val < n) :
    readLabels ((List.ofFn p).take n) a = p a := by
  rw [readLabels,List.getElem?_take,ite_eq_left ha,List.getElem?_ofFn,dite_eq_left a.isLt]
  rfl

private theorem finRange_take_lt {a : Vertex} {n : ℕ} (h : a ∈ (List.finRange 8).take n) : a.val < n := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem h
  have hil : i < n := by simp only [List.length_take,List.length_finRange] at hi; omega
  simp only [List.getElem_take,List.getElem_finRange] at he
  have heval := congrArg Fin.val he
  exact (show i = a.val from heval) ▸ hil

private theorem validPrefix_of_automorphism {k : Triangulation} {p : Equiv.Perm Vertex}
    (hp : k.IsAutomorphism p) {n : ℕ} (hn : n ≤ 8) :
    k.validPrefix ((List.ofFn (p : Vertex → Vertex)).take n) = true := by
  have hl : ((List.ofFn (p : Vertex → Vertex)).take n).length = n := by
    simp [hn]
  simp only [validPrefix,hl,Bool.and_eq_true,List.all_eq_true]
  constructor
  · intro a ha b hb
    rw [read_ofFn_take p (finRange_take_lt ha),read_ofFn_take p (finRange_take_lt hb),beq_iff_eq]
    apply Bool.eq_iff_iff.mpr
    simp only [List.contains_iff_mem]
    exact automorphism_preserves_edge hp a b
  · intro f hf
    by_cases h : f.1.val < n ∧ f.2.1.val < n ∧ f.2.2.val < n
    · have he : mapTriangle (readLabels ((List.ofFn (p : Vertex → Vertex)).take n)) f =
          mapTriangle p f := by
        simp only [mapTriangle,read_ofFn_take p h.1,read_ofFn_take p h.2.1,read_ofFn_take p h.2.2]
      have himg : (k.faces.map (triangleVertexSet ∘ mapTriangle p)).toFinset = k.faceSets := hp
      have hm : triangleVertexSet (mapTriangle p f) ∈ k.faceSets := by
        rw [← himg]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨f,hf,rfl⟩)
      rw [he]
      simp [h,hm]
    · simp [h]

private theorem automorphism_mem_prefixes {k : Triangulation} {p : Equiv.Perm Vertex}
    (hp : k.IsAutomorphism p) (n : ℕ) (hn : n ≤ 8) :
    (List.ofFn (p : Vertex → Vertex)).take n ∈ k.permutationPrefixes n := by
  induction n with
  | zero => simp [permutationPrefixes]
  | succ n ih =>
    let l := List.ofFn (p : Vertex → Vertex)
    have hlt : n < l.length := by simp [l]; omega
    have hv : l[n] ∉ l.take n := by
      have hnd : l.Nodup := List.nodup_ofFn.mpr p.injective
      have hd : (l.take (n+1)).Nodup := hnd.take
      rw [← List.take_append_getElem hlt,List.nodup_append'] at hd
      exact fun hm => (List.disjoint_left.mp hd.2.2) hm (by simp)
    apply List.mem_flatMap.mpr
    refine ⟨l.take n,ih (by omega),List.mem_filter.mpr ⟨?_,validPrefix_of_automorphism hp hn⟩⟩
    refine List.mem_map.mpr ⟨l[n],List.mem_filter.mpr ⟨by simp,by simp [hv]⟩,?_⟩
    exact List.take_append_getElem hlt

theorem automorphism_in_labels {k : Triangulation} {p : Equiv.Perm Vertex}
    (hp : k.IsAutomorphism p) : List.ofFn (p : Vertex → Vertex) ∈ k.automorphismLabels := by
  have h := automorphism_mem_prefixes hp 8 (by decide)
  let l := List.ofFn (p : Vertex → Vertex)
  have hl : l.take 8 = l := List.take_of_length_le (by simp [l])
  have he : readLabels l = p := by
    funext a
    rw [← hl]
    exact read_ofFn_take p a.isLt
  apply List.mem_filter.mpr
  change l ∈ k.permutationPrefixes 8 ∧
    decide ((k.faces.map (triangleVertexSet ∘ mapTriangle (readLabels l))).toFinset = k.faceSets) = true
  rw [hl] at h
  refine ⟨h,?_⟩
  rw [he,decide_eq_true_eq]
  exact hp

private theorem prefix_length_nodup {k : Triangulation} {n : ℕ} {s : List Vertex}
    (h : s ∈ k.permutationPrefixes n) : s.length = n ∧ s.Nodup := by
  induction n generalizing s with
  | zero =>
    have hs : s = [] := by simpa [permutationPrefixes] using h
    simp [hs]
  | succ n ih =>
    obtain ⟨t,ht,hs⟩ := List.mem_flatMap.mp h
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_filter.mp hs).1
    obtain ⟨hl,hn⟩ := ih ht
    have hnot : a ∉ t := by simpa using (List.mem_filter.mp ha).2
    exact ⟨by simp [hl],by simp [List.nodup_append',hn,hnot]⟩

theorem automorphism_of_labels {k : Triangulation} {s : List Vertex}
    (hs : s ∈ k.automorphismLabels) :
    ∃ p : Equiv.Perm Vertex, k.IsAutomorphism p ∧ (p : Vertex → Vertex) = readLabels s := by
  obtain ⟨hm,hf⟩ := List.mem_filter.mp hs
  obtain ⟨hl,hn⟩ := prefix_length_nodup hm
  have hlt (a : Vertex) : a.val < s.length := hl.symm ▸ a.isLt
  have hread (a : Vertex) : readLabels s a = s[a.val]'(hlt a) := by
    have he : s[a.val]? = some (s[a.val]'(hlt a)) := List.getElem?_eq_some_iff.mpr ⟨hlt a,rfl⟩
    simp only [readLabels,he,Option.getD_some]
  have hi : Function.Injective (readLabels s) := by
    intro a b he
    apply Fin.ext
    rw [hread,hread] at he
    exact hn.getElem_inj_iff.mp he
  let p := Equiv.ofBijective (readLabels s) ⟨hi,Finite.injective_iff_surjective.mp hi⟩
  refine ⟨p,?_,rfl⟩
  change (k.faces.map (triangleVertexSet ∘ mapTriangle (readLabels s))).toFinset = k.faceSets
  exact of_decide_eq_true hf

def automorphismAction (k : Triangulation) (p : Vertex → Vertex) : PeriodMatrix :=
  (cyclePeriod k.dualCocycle (mapTriangle p k.basisCycles.1),
    cyclePeriod k.dualCocycle (mapTriangle p k.basisCycles.2))

def automorphismActions (k : Triangulation) : Finset PeriodMatrix :=
  (k.automorphismLabels.map (k.automorphismAction ∘ readLabels)).toFinset

theorem mem_automorphismActions (k : Triangulation) (A : PeriodMatrix) :
    A ∈ k.automorphismActions ↔
      ∃ p : Equiv.Perm Vertex, k.IsAutomorphism p ∧ k.automorphismAction p = A := by
  rw [automorphismActions,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨s,hs,hA⟩
    obtain ⟨p,hp,he⟩ := automorphism_of_labels hs
    exact ⟨p,hp,he.symm ▸ hA⟩
  · rintro ⟨p,hp,rfl⟩
    refine ⟨List.ofFn (p : Vertex → Vertex),automorphism_in_labels hp,?_⟩
    have he : readLabels (List.ofFn (p : Vertex → Vertex)) = p := by
      have hl : (List.ofFn (p : Vertex → Vertex)).take 8 = List.ofFn (p : Vertex → Vertex) :=
        List.take_of_length_le (by simp)
      funext a
      rw [← hl]
      exact read_ofFn_take p a.isLt
    change k.automorphismAction (readLabels (List.ofFn (p : Vertex → Vertex))) = k.automorphismAction p
    rw [he]

/-- The distinct actions, with matrices written in the two triangular cycles. -/
def actionTable : Triangulation → Finset PeriodMatrix
  | .type4 | .type7 => {((1,0),(0,1)),((0,1),(1,0)),((-1,0),(0,-1)),((0,-1),(-1,0))}
  | .type5 => {((1,0),(0,1)),((-1,1),(0,1)),((0,-1),(1,-1)),
      ((1,0),(1,-1)),((0,-1),(-1,0)),((-1,1),(-1,0))}

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
theorem automorphism_table (k : Triangulation) :
    k.automorphismActions = k.actionTable ∧ k.automorphismLabels.length =
      match k with
      | .type4 => 4
      | .type5 => 6
      | .type7 => 32 := by
  cases k <;> decide +kernel

end OrigamiTorus.Winding.Triangulation
