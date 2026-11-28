module

public import OrigamiTorus.EightVertex.Type5.Reconstruction
public import OrigamiTorus.Geometry.EmbeddedEdges
public import OrigamiTorus.Geometry.PlanarCompleteGraph
public import OrigamiTorus.Geometry.AngleDerivative
import Mathlib.Analysis.Convex.Between
import Mathlib.Data.List.Rotate
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

/-! The core and the excluded collinear and antipodal configurations of Type 5. -/

@[expose] public section

open InnerProductGeometry

namespace OrigamiTorus.Type5

open Type2 (Adjacent euclideanPoint linkDirection)

/-- The five core vertices, in anchor-then-root order. -/
def coreLabels : Fin 5 → Vertex := ![1,2,5,3,4]

theorem coreLabels_injective : Function.Injective coreLabels := by decide +kernel

theorem adjacency_test (a b : Vertex) :
    Adjacent faces a b ↔ edgeList.contains (orderedEdge a b) = true := by
  have h : ∀ a b : Vertex, edgeList.contains (orderedEdge a b) =
      ((a != b) && faces.any (fun f => (triangleVertices f).contains a &&
        (triangleVertices f).contains b)) := by decide +kernel
  rw [h,Bool.and_eq_true,List.any_eq_true]
  simp [Adjacent]

theorem adjacent_iff (a b : Vertex) :
    Adjacent faces a b ↔ a ≠ b ∧ (a ∈ anchors ∨ b ∈ anchors ∨
      (a ∈ roots ∧ b ∈ leaves) ∨ (b ∈ roots ∧ a ∈ leaves)) :=
  (adjacency_test a b).trans (edges_from_anchor_root_leaf a b)

theorem type5_covers (a : Vertex) : ∃ f ∈ faces, a ∈ triangleVertexSet f := by
  have h : ∀ a : Vertex, faces.any (fun f => (triangleVertices f).contains a) = true := by decide +kernel
  obtain ⟨f,hf,ha⟩ := List.any_eq_true.mp (h a)
  exact ⟨f,hf,by simpa using ha⟩

private theorem core_pair {i j : Fin 5} (h : i ≠ j)
    (hm : ¬ ({3,4} : Finset (Fin 5)) ⊆ {i,j}) :
    Adjacent faces (coreLabels i) (coreLabels j) := by
  rw [adjacency_test]
  revert i j
  decide +kernel

/-- The five core points cannot lie in a common affine plane in any
embedded Type 5 surface. -/
theorem core_not_in_plane_of_embedding (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (o : Point3)
    (P : Submodule ℝ Point3) (hP : Module.finrank ℝ P ≤ 2)
    (hcore : ∀ i : Fin 5, q (coreLabels i)-o ∈ P) : False :=
  almostClique_not_in_plane q he coreLabels coreLabels_injective
    (fun i => type5_covers (coreLabels i)) (fun _ _ => core_pair)
    ⟨by simp,(1,5,2),by decide +kernel,by decide +kernel⟩ o P hP hcore

/-- The core affine span of an embedded Type 5 surface is three-dimensional. -/
theorem core_not_coplanar (q : Vertex → Point3) (he : Function.Injective (evaluateTriangles faces q)) :
    ¬ Coplanar ℝ (Set.range (q ∘ coreLabels)) := by
  intro h
  exact core_not_in_plane_of_embedding q he (q (coreLabels 0)) _
    h.finrank_le_two (fun i => vsub_mem_vectorSpan ℝ ⟨i,rfl⟩ ⟨0,rfl⟩)

theorem mem_orientedLinkCycle (v w : Vertex) :
    w ∈ orientedLinkCycle v ↔ Adjacent faces v w := by
  rw [adjacency_test]
  revert v w
  decide +kernel

private def rotatedTail (v a : Vertex) : List Vertex :=
  ((orientedLinkCycle v).rotate ((orientedLinkCycle v).idxOf a)).tail

private def arc (v a b : Vertex) : List Vertex :=
  (rotatedTail v a).take ((rotatedTail v a).idxOf b)

private def arcRest (v a b : Vertex) : List Vertex :=
  (rotatedTail v a).drop ((rotatedTail v a).idxOf b + 1)

private def hasCrossEdges (v a b : Vertex) : Prop :=
  ∃ x y : Vertex, [x,y].Sublist (arc v a b) ∧
    edgeList.contains (orderedEdge a y) = true ∧ edgeList.contains (orderedEdge x b) = true

private instance (v a b : Vertex) : Decidable (hasCrossEdges v a b) := by
  unfold hasCrossEdges
  infer_instance

private theorem link_arcs (v a b : Vertex) (ha : a ∈ orientedLinkCycle v)
    (hb : b ∈ orientedLinkCycle v) (hne : a ≠ b) :
    (orientedLinkCycle v).rotate ((orientedLinkCycle v).idxOf a) =
      a :: (arc v a b ++ b :: arcRest v a b) := by
  revert a b
  fin_cases v <;> decide +kernel

private theorem missing_pair_arcs (v a b : Vertex) (ha : a ∈ orientedLinkCycle v)
    (hb : b ∈ orientedLinkCycle v) (hne : a ≠ b) (hab : ¬ Adjacent faces a b) :
    hasCrossEdges v a b ∨ hasCrossEdges v b a := by
  rw [adjacency_test] at hab
  revert a b
  fin_cases v <;> decide +kernel

private theorem angularCycleLength_rotate (a : List Vertex) (n : ℕ) (d : Vertex → EuclideanSpace ℝ (Fin 3)) :
    angularCycleLength ((a.rotate n).map d) = angularCycleLength (a.map d) := by
  rw [List.rotate_eq_drop_append_take_mod,List.map_append,angularCycleLength_append_comm,
    ← List.map_append,List.take_append_drop]

/-- In any embedded flat Type 5 star, the rays to two distinct neighbors cannot
be opposite. Each missing pair has a link arc whose diagonals would meet
radial edges on a minimizing semicircle. -/
theorem neighbors_not_opposite (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) {v a b : Vertex}
    (ha : a ∈ orientedLinkCycle v) (hb : b ∈ orientedLinkCycle v) (hne : a ≠ b)
    (hf : angularCycleLength ((orientedLinkCycle v).map (linkDirection q v)) = 2*Real.pi) :
    angle (linkDirection q v a) (linkDirection q v b) ≠ Real.pi := by
  let ns := orientedLinkCycle v
  let d := linkDirection q v
  intro hop
  have hn := no_edge_of_opposite_rays_of_embedding q he
    ((mem_orientedLinkCycle _ _).mp ha) ((mem_orientedLinkCycle _ _).mp hb) hop
  have exclude (a b : Vertex) (ha : a ∈ ns) (hb : b ∈ ns) (hne : a ≠ b)
      (hπ : angle (d a) (d b) = Real.pi) (hcross : hasCrossEdges v a b) : False := by
    obtain ⟨x,y,hxy,hay,hxb⟩ := hcross
    let xs := arc v a b
    let ys := arcRest v a b
    have hc : ns.rotate (ns.idxOf a) = a :: (xs ++ b :: ys) := link_arcs _ _ _ ha hb hne
    have hp : (a :: (xs ++ b :: ys)).Perm ns := hc ▸ List.rotate_perm _ _
    have hfour : [a,x,y,b].Sublist (a :: (xs ++ b :: ys)) :=
      (hxy.append (List.sublist_append_left [b] ys)).cons_cons a
    have hs : angularPathLength (d a) (xs.map d) (d b) +
        angularPathLength (d b) (ys.map d) (d a) = 2*Real.pi := by
      rw [← angularCycleLength_split_pair]
      simpa only [hc,List.map_cons,List.map_append] using
        (angularCycleLength_rotate ns (ns.idxOf a) d).trans hf
    have hge := angle_le_angularPathLength (d b) (d a) (ys.map d)
    rw [angle_comm (d b) (d a),hπ] at hge
    have hle := angle_le_angularPathLength (d a) (d b) (xs.map d)
    rw [hπ] at hle
    exact impossible_minimal_arc_of_embedding q he
      (hfour.nodup (hp.nodup_iff.mpr (linkCycles_checked v).1))
      (fun z hz => (mem_orientedLinkCycle _ _).mp (hp.mem_iff.mp (hfour.subset hz)))
      hxy ((adjacency_test _ _).mpr hay) ((adjacency_test _ _).mpr hxb) hπ (by linarith)
  rcases missing_pair_arcs v a b ha hb hne hn with h | h
  · exact exclude a b ha hb hne hop h
  · exact exclude b a hb ha hne.symm ((angle_comm _ _).trans hop) h

/-- In particular the two roots cannot be opposite at a flat leaf or anchor. -/
theorem roots_not_opposite_at_flat_star (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (v : Vertex)
    (hv : v ∈ leaves ∨ v ∈ anchors)
    (hf : angularCycleLength ((orientedLinkCycle v).map (linkDirection q v)) = 2*Real.pi) :
    angle (linkDirection q v 3) (linkDirection q v 4) ≠ Real.pi := by
  have hm : 3 ∈ orientedLinkCycle v ∧ 4 ∈ orientedLinkCycle v := by
    clear hf
    revert v
    decide +kernel
  exact neighbors_not_opposite q he hm.1 hm.2 (by decide) hf

/-- The intrinsic angle sum at a Type 5 vertex is one full turn. -/
def FlatAt (q : Vertex → Point3) (v : Vertex) : Prop :=
  angularCycleLength ((orientedLinkCycle v).map (linkDirection q v)) = 2*Real.pi

theorem flatAt_iff_coneAngles (q : Vertex → Point3) (v : Vertex) :
    FlatAt q v ↔ coneAngles faces (euclideanPoint ∘ q) v = 2*Real.pi := by
  let A (e : Edge) := angle (linkDirection q v e.1) (linkDirection q v e.2)
  have hper (v : Vertex) : (directedCycleEdges (orientedLinkCycle v)).Perm (linkFromFaces v) := by
    revert v
    decide +kernel
  have hf (fs : List Triangle) :
      ((fs.filterMap (cornerRays v)).map A).sum = coneAngles fs (euclideanPoint ∘ q) v := by
    induction fs with
    | nil => rfl
    | cons f fs ih =>
      unfold coneAngles at ih ⊢
      cases he : cornerRays v f with
      | none => simp [he,ih]
      | some e =>
        obtain ⟨a,b⟩ := e
        have hA : A (a,b) = angle ((euclideanPoint ∘ q) a-(euclideanPoint ∘ q) v)
            ((euclideanPoint ∘ q) b-(euclideanPoint ∘ q) v) := by
          simp [A,linkDirection,map_sub]
        simp [he,ih,hA]
  unfold FlatAt
  rw [angularCycleLength_eq_sum_zip]
  simp only [← List.map_drop,← List.map_take,← List.map_append,List.zip_map,List.map_map]
  change ((directedCycleEdges (orientedLinkCycle v)).map A).sum = 2*Real.pi ↔ _
  rw [((hper v).map A).sum_eq]
  exact Iff.of_eq (congrArg (fun u : ℝ => u = 2*Real.pi) (hf faces))

/-- The five neighbors of a Type 5 leaf in cyclic order. -/
def leafNeighbor (v : Vertex) (i : Fin 5) : Vertex :=
  ((orientedLinkCycle v)[i.val]?).getD 0

theorem leafNeighbor_mem_core (v : Vertex) (hv : v ∈ leaves) (i : Fin 5) :
    leafNeighbor v i ∈ Set.range coreLabels := by
  have h : ∀ i, ∃ j : Fin 5, leafNeighbor v i = coreLabels j := by
    revert hv
    fin_cases v <;> decide +kernel
  obtain ⟨j,hj⟩ := h i
  exact ⟨j,hj.symm⟩

theorem core_mem_leafNeighbor (v : Vertex) (hv : v ∈ leaves) (i : Fin 5) :
    coreLabels i ∈ Set.range (leafNeighbor v) := by
  have h : ∀ i, ∃ j : Fin 5, leafNeighbor v j = coreLabels i := by
    revert hv
    fin_cases v <;> decide +kernel
  exact h i

theorem leafNeighbor_injective (v : Vertex) (hv : v ∈ leaves) :
    Function.Injective (leafNeighbor v) := by
  revert hv
  fin_cases v <;> decide +kernel

theorem leaf_center_adjacent (v : Vertex) (hv : v ∈ leaves) (i : Fin 5) :
    Adjacent faces v (leafNeighbor v i) := by
  rw [adjacency_test]
  revert hv i
  fin_cases v <;> decide +kernel

theorem leaf_consecutive_adjacent (v : Vertex) (hv : v ∈ leaves) (i : Fin 5) :
    Adjacent faces (leafNeighbor v i) (leafNeighbor v (finRotate 5 i)) := by
  rw [adjacency_test]
  revert hv i
  fin_cases v <;> decide +kernel

private theorem leaf_skip_nonedge (v : Vertex) (hv : v ∈ leaves) (i : Fin 5)
    (hn : ¬ Adjacent faces (leafNeighbor v i) (leafNeighbor v (finRotate 5 (finRotate 5 i)))) :
    let a := leafNeighbor v i
    let b := leafNeighbor v (finRotate 5 i)
    let c := leafNeighbor v (finRotate 5 (finRotate 5 i))
    (a,c) ∈ ([(3,4),(4,3)] : List Edge) ∧ b ∈ anchors := by
  rw [adjacency_test] at hn
  revert hv i
  fin_cases v <;> decide +kernel

/-- No two consecutive edges of a flat leaf's link lie on one line. -/
theorem leaf_link_triple_not_collinear (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q))
    (hflat : ∀ u ∈ anchors, FlatAt q u) (v : Vertex) (hv : v ∈ leaves) (i : Fin 5) :
    let n := leafNeighbor v
    ¬ Collinear ℝ ({q (n i),q (n (finRotate 5 i)),q (n (finRotate 5 (finRotate 5 i)))} : Set Point3) := by
  let n := leafNeighbor v
  let a := n i
  let b := n (finRotate 5 i)
  let c := n (finRotate 5 (finRotate 5 i))
  change ¬ Collinear ℝ ({q a,q b,q c} : Set Point3)
  intro hc
  have hab : Adjacent faces a b := leaf_consecutive_adjacent v hv i
  have hbc : Adjacent faces b c := leaf_consecutive_adjacent v hv (finRotate 5 i)
  have hskip : ∀ j : Fin 5, j ≠ finRotate 5 (finRotate 5 j) := by decide +kernel
  have hac : a ≠ c := (leafNeighbor_injective v hv).ne (hskip i)
  have hmid : Wbtw ℝ (q a) (q b) (q c) := by
    rcases hc.wbtw_or_wbtw_or_wbtw with h | h | h
    · exact h
    · exact False.elim (not_mem_edge_of_embedding q he (type5_covers c)
        hab hac.symm hbc.1.symm h.symm.mem_segment)
    · exact False.elim (not_mem_edge_of_embedding q he (type5_covers a)
        hbc hab.1 hac h.symm.mem_segment)
  have hnac : ¬ Adjacent faces a c := fun hadj =>
    not_mem_edge_of_embedding q he (type5_covers b) hadj hab.1.symm hbc.1 hmid.mem_segment
  have hqi := vertex_injective_of_injective_evaluateTriangles faces q type5_covers he
  have hqj := Type2.euclideanPoint_injective.comp hqi
  have heuc : Sbtw ℝ (euclideanPoint (q a)) (euclideanPoint (q b)) (euclideanPoint (q c)) :=
    ⟨hmid.map euclideanPoint.toAffineMap,hqj.ne hab.1.symm,hqj.ne hbc.1⟩
  have hπ : angle (linkDirection q b a) (linkDirection q b c) = Real.pi := by
    simpa [EuclideanGeometry.angle,linkDirection,map_sub] using heuc.angle₁₂₃_eq_pi
  obtain ⟨hr,hb⟩ := leaf_skip_nonedge v hv i hnac
  have hno := roots_not_opposite_at_flat_star q he b (Or.inr hb) (hflat b hb)
  change (a,c) ∈ ([(3,4),(4,3)] : List Edge) at hr
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hr
  obtain ⟨ha,hc⟩ | ⟨ha,hc⟩ := hr
  · rw [ha,hc] at hπ
    exact hno hπ
  · rw [ha,hc] at hπ
    exact hno ((angle_comm _ _).trans hπ)

end OrigamiTorus.Type5
