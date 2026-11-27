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

private theorem mem_orientedLinkCycle (v w : Vertex) :
    w ∈ orientedLinkCycle v ↔ Adjacent faces v w := by
  rw [adjacency_test]
  revert v w
  decide +kernel

private structure RootArc where
  a : Vertex
  b : Vertex
  x : Vertex
  y : Vertex
  rest : List Vertex
  other : Vertex

private def rootArc (v : Vertex) : RootArc :=
  ![⟨3,4,1,2,[],5⟩,⟨4,3,7,5,[2,0],6⟩,⟨4,3,0,1,[5,6],7⟩,⟨3,4,1,2,[],5⟩,
    ⟨3,4,1,2,[],5⟩,⟨4,3,6,2,[1,7],0⟩,⟨3,4,2,5,[],1⟩,⟨3,4,5,1,[],2⟩] v

private def rootArcCycle (d : RootArc) : List Vertex :=
  d.a :: ((d.x :: d.y :: d.rest) ++ d.b :: [d.other])

private theorem rootArc_checked (v : Vertex) (hv : v ∈ leaves ∨ v ∈ anchors) :
    let d := rootArc v
    (d.a,d.b) ∈ ([(3,4),(4,3)] : List Edge) ∧
    (orientedLinkCycle v).rotate ((orientedLinkCycle v).idxOf d.a) = rootArcCycle d ∧
    Adjacent faces d.a d.y ∧ Adjacent faces d.x d.b := by
  dsimp only
  rw [adjacency_test,adjacency_test]
  revert hv
  fin_cases v <;> decide +kernel

private theorem angularCycleLength_rotate (a : List Vertex) (n : ℕ) (d : Vertex → EuclideanSpace ℝ (Fin 3)) :
    angularCycleLength ((a.rotate n).map d) = angularCycleLength (a.map d) := by
  rw [List.rotate_eq_drop_append_take_mod,List.map_append,angularCycleLength_append_comm,
    ← List.map_append,List.take_append_drop]

/-- The neighbors at vertices 3 and 4 cannot be opposite at a flat leaf or
anchor star. Two interior rays on one minimizing semicircle would force
the intersection of disjoint edges. -/
theorem roots_not_opposite_at_flat_star (q : Vertex → Point3)
    (he : Function.Injective (evaluateTriangles faces q)) (v : Vertex)
    (hv : v ∈ leaves ∨ v ∈ anchors)
    (hf : angularCycleLength ((orientedLinkCycle v).map (linkDirection q v)) = 2*Real.pi) :
    angle (linkDirection q v 3) (linkDirection q v 4) ≠ Real.pi := by
  let r := rootArc v
  obtain ⟨horder,hcycle,hay,hxb⟩ := rootArc_checked v hv
  change (r.a,r.b) ∈ ([(3,4),(4,3)] : List Edge) at horder
  change (orientedLinkCycle v).rotate ((orientedLinkCycle v).idxOf r.a) = (rootArcCycle r) at hcycle
  let d := linkDirection q v
  intro hop
  have hπ : angle (d r.a) (d r.b) = Real.pi := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at horder
    obtain ⟨ha,hb⟩ | ⟨ha,hb⟩ := horder <;> simp [ha,hb,angle_comm (d 4) (d 3),hop,d]
  have hrot : angularCycleLength ((rootArcCycle r).map d) = 2*Real.pi := by
    rw [← hcycle, angularCycleLength_rotate]
    exact hf
  have hsum : angularPathLength (d r.a) ((r.x :: r.y :: r.rest).map d) (d r.b) +
      angularPathLength (d r.b) ([r.other].map d) (d r.a) = 2*Real.pi := by
    rw [← angularCycleLength_split_pair]
    simpa only [rootArcCycle,List.map_cons,List.map_append] using hrot
  have hge := angle_le_angularPathLength (d r.b) (d r.a) ([r.other].map d)
  rw [angle_comm (d r.b) (d r.a),hπ] at hge
  have hle := angle_le_angularPathLength (d r.a) (d r.b) ((r.x :: r.y :: r.rest).map d)
  rw [hπ] at hle
  have hmin : angularPathLength (d r.a) ((r.x :: r.y :: r.rest).map d) (d r.b) = Real.pi := by
    linarith
  have hperm : (rootArcCycle r).Perm (orientedLinkCycle v) := hcycle ▸ List.rotate_perm _ _
  have hfour : [r.a,r.x,r.y,r.b].Sublist (rootArcCycle r) := by
    change [r.a,r.x,r.y,r.b].Sublist (r.a :: r.x :: r.y :: (r.rest ++ [r.b,r.other]))
    apply List.Sublist.cons_cons
    apply List.Sublist.cons_cons
    apply List.Sublist.cons_cons
    exact (List.sublist_append_left [r.b] [r.other]).trans (List.sublist_append_right _ _)
  have hn := hfour.nodup (hperm.nodup_iff.mpr (linkCycles_checked v).1)
  have hm (k : Vertex) (hk : k ∈ [r.a,r.x,r.y,r.b]) : Adjacent faces v k :=
    (mem_orientedLinkCycle v k).mp (hperm.mem_iff.mp (hfour.subset hk))
  exact impossible_minimal_arc_of_embedding q he hn hm
    (List.sublist_append_left [r.x,r.y] r.rest) hay hxb hπ hmin

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
