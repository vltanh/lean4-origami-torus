module

public import OrigamiTorus.Geometry.TriangleIntersections
public import OrigamiTorus.Geometry.PlanarFan
public import OrigamiTorus.Geometry.PlanarArea
public import OrigamiTorus.Type6.Periods
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Tactic

/-! Gluing the lifted Type 6 triangles in the quotient by the specified periods. -/

namespace OrigamiTorus

open Filter
open scoped Topology

@[expose] public section

/-- The flat torus in coordinates along its two lattice generators. -/
abbrev MarkedTorus := AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

/-- The two integer periods attached to each labeled vertex of a lifted face. -/
def facePeriod (f : LiftedFace) (i : Vertex) : Period :=
  if i = f.1.1 then f.1.2 else if i = f.2.1.1 then f.2.1.2 else
    if i = f.2.2.1 then f.2.2.2 else (0,0)

/-- Cyclic orders induced by the oriented Type 6 faces. -/
def type6_linkCycle : Vertex → List Vertex :=
  ![[1,5,2,4,3], [0,3,6,7,4,5], [0,5,7,6,4], [0,4,7,5,6,1],
    [0,2,6,5,1,7,3], [0,1,4,6,3,7,2], [1,3,5,4,2,7], [1,6,2,5,3,4]]

def directedLinkFromFaces (fs : List Triangle) (v : Vertex) : List Edge :=
  fs.filterMap fun (a,b,c) =>
    if v = a then some (b,c) else if v = b then some (c,a) else
      if v = c then some (a,b) else none

/-- Each vertex belongs to a single simple cycle of consistently oriented faces. -/
theorem type6_linkCycle_checked (v : Vertex) :
    let ns := type6_linkCycle v
    let cycle := ns.zip (ns.drop 1 ++ ns.take 1)
    let found := directedLinkFromFaces type6FlippedFaces v
    ns.Nodup ∧ 3 ≤ ns.length ∧ cycle.all found.contains = true ∧ found.all cycle.contains = true := by
  fin_cases v <;> decide +kernel

/-- A table period read in the direction of travel along an edge. -/
def type6_edgeShift (a b : Vertex) : Option Period :=
  (List.finRange 24).findSome? fun e =>
    let ((u,v),d) := edgePeriod e
    if (a,b) = (u,v) then some d else if (b,a) = (u,v) then some (-d) else none

def type6_walkShift (path : List Vertex) : Option Period :=
  (path.zip (path.drop 1)).foldlM
    (fun acc (a,b) => (acc + ·) <$> type6_edgeShift a b) 0

/-- Two edge loops based at vertex 1 give both marked periods. -/
theorem type6_walkShifts_generate :
    type6_walkShift [1,0,4,1] = some (0,-1) ∧
    type6_walkShift [1,5,7,1] = some (-1,0) := by
  decide +kernel

def realPeriod (p : Period) : ℝ × ℝ := (p.1,p.2)

/-- Scaled planar coordinates expressed along the basis `(1,0),(x,w)`. -/
noncomputable def periodCoordinates (x w : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 - x*(p.2/w), p.2/w)

/-- Projection from lattice coordinates to the marked quotient. -/
def projectPeriods (v : ℝ × ℝ) : MarkedTorus := (v.1,v.2)

private noncomputable def periodCoordinatesLinear (x w : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := periodCoordinates x w
  map_add' a b := by
    apply Prod.ext
    · simp [periodCoordinates,add_div]
      ring
    · simp [periodCoordinates,add_div]
  map_smul' r a := by
    have h (p : ℝ × ℝ) : r • p = (r*p.1,r*p.2) := rfl
    apply Prod.ext <;> simp [periodCoordinates,h] <;> ring

/-- The invertible change from planar to lattice-basis coordinates. -/
noncomputable def periodCoordinatesHomeomorph (x w : ℝ) (hw : w ≠ 0) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := periodCoordinates x w
  invFun := fun p => (p.1+x*p.2,w*p.2)
  left_inv := by
    intro p
    apply Prod.ext
    · simp only [periodCoordinates]
      field_simp [hw]
      ring
    · simp only [periodCoordinates]
      field_simp [hw]
  right_inv := by
    intro p
    apply Prod.ext
    · simp only [periodCoordinates]
      field_simp [hw]
      ring
    · simp only [periodCoordinates]
      field_simp [hw]
  continuous_toFun := by unfold periodCoordinates; fun_prop
  continuous_invFun := by fun_prop

/-- The quotient projection is open in the scaled plane itself. -/
theorem isOpenMap_project_periodCoordinates (x w : ℝ) (hw : w ≠ 0) :
    IsOpenMap (projectPeriods ∘ periodCoordinates x w) := by
  have h : IsOpenMap (fun t : ℝ => (t : AddCircle (1 : ℝ))) := QuotientAddGroup.isOpenMap_coe
  exact (h.prodMap h).comp (periodCoordinatesHomeomorph x w hw).isOpenMap

theorem periodCoordinates_translate (x w : ℝ) (hw : w ≠ 0) (d : Period) (p : ℝ × ℝ) :
    periodCoordinates x w (translatePoint x w d p) = periodCoordinates x w p + realPeriod d := by
  apply Prod.ext
  · simp only [periodCoordinates,translatePoint,realPeriod,Prod.fst_add]
    field_simp [hw]
    ring
  · simp only [periodCoordinates,translatePoint,realPeriod,Prod.snd_add]
    field_simp [hw]

private theorem projectPeriods_add_period (p : ℝ × ℝ) (d : Period) :
    projectPeriods (p + realPeriod d) = projectPeriods p := by
  have hzero (j : ℤ) : ((j : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).mpr ⟨j, by simp [zsmul_eq_mul]⟩
  apply Prod.ext
  · change (↑(p.1 + (d.1 : ℝ)) : AddCircle (1 : ℝ)) = ↑p.1
    rw [AddCircle.coe_add, hzero, add_zero]
  · change (↑(p.2 + (d.2 : ℝ)) : AddCircle (1 : ℝ)) = ↑p.2
    rw [AddCircle.coe_add, hzero, add_zero]

/-- Projecting the scaled physical plane identifies points exactly when they
are separated by an integer combination of its two periods. -/
theorem periodCoordinates_project_eq_iff (x w : ℝ) (hw : w ≠ 0) (p q : ℝ × ℝ) :
    projectPeriods (periodCoordinates x w p) = projectPeriods (periodCoordinates x w q) ↔
      ∃ d : Period, translatePoint x w d p = q := by
  constructor
  · intro h
    let P := periodCoordinates x w p
    let Q := periodCoordinates x w q
    have h₁ : (↑(Q.1-P.1) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, sub_eq_zero]
      exact (congrArg Prod.fst h).symm
    have h₂ : (↑(Q.2-P.2) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_sub, sub_eq_zero]
      exact (congrArg Prod.snd h).symm
    obtain ⟨m,hm⟩ := (AddCircle.coe_eq_zero_iff 1).mp h₁
    obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff 1).mp h₂
    simp only [zsmul_eq_mul, mul_one] at hm hn
    have hcoord : periodCoordinates x w (translatePoint x w (m,n) p) = Q := by
      rw [periodCoordinates_translate x w hw]
      exact Prod.ext (by simp only [realPeriod,Prod.fst_add]; linarith)
        (by simp only [realPeriod,Prod.snd_add]; linarith)
    have hinj : Function.Injective (periodCoordinates x w) := by
      intro a b e
      change (a.1-x*(a.2/w),a.2/w) = (b.1-x*(b.2/w),b.2/w) at e
      obtain ⟨hs,hd⟩ := Prod.mk.inj e
      have hv : a.2 = b.2 := (div_left_inj₀ hw).mp hd
      exact Prod.ext (by rw [hv] at hs; linarith) hv
    exact ⟨(m,n), hinj hcoord⟩
  · rintro ⟨d,rfl⟩
    rw [periodCoordinates_translate x w hw, projectPeriods_add_period]

/-- The period function recovers the three stored corner shifts on every face. -/
theorem type6_facePeriod_correct :
    ∀ f : Fin 16, let t := liftedFaces f
      facePeriod t t.1.1 = t.1.2 ∧
        facePeriod t t.2.1.1 = t.2.1.2 ∧
        facePeriod t t.2.2.1 = t.2.2.2 := by
  decide +kernel

noncomputable def latticeCorner (x w : ℝ) (q : Vertex → ℝ × ℝ) (c : Corner) : ℝ × ℝ :=
  periodCoordinates x w (translatePoint x w c.2 (q c.1))

/-- The closed lifted triangle, in lattice coordinates. -/
noncomputable def latticeTriangle (x w : ℝ) (q : Vertex → ℝ × ℝ) (f : LiftedFace) :
    Set (ℝ × ℝ) :=
  planarTriangle (latticeCorner x w q f.1) (latticeCorner x w q f.2.1)
    (latticeCorner x w q f.2.2)

/-- The lifted triangle double area after passing to unit lattice coordinates. -/
noncomputable def latticeFaceArea (x w : ℝ) (q : Vertex → ℝ × ℝ) (f : LiftedFace) : ℝ :=
  let p := latticeCorner x w q
  let a := p f.1
  let b := p f.2.1
  let c := p f.2.2
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)

theorem latticeFaceArea_eq (x w : ℝ) (hw : w ≠ 0) (q : Vertex → ℝ × ℝ) (f : LiftedFace) :
    latticeFaceArea x w q f = periodicFaceArea x w q f / w := by
  simp only [latticeFaceArea,latticeCorner,periodicFaceArea,periodCoordinates]
  field_simp [hw]
  ring

/-- The sixteen oriented double areas add to twice the unit fundamental area. -/
theorem type6_latticeTotalArea (x w : ℝ) (hw : w ≠ 0) (q : Vertex → ℝ × ℝ) :
    ∑ f : Fin 16, latticeFaceArea x w q (liftedFaces f) = 2 := by
  simp_rw [latticeFaceArea_eq x w hw]
  rw [← Finset.sum_div, type6_periodicTotalArea]
  exact mul_div_cancel_right₀ 2 hw

/-- An outgoing edge represented in the lift with initial vertex at the origin. -/
def liftedEdgeDirection (shift : Vertex → Vertex → Period) (x w : ℝ)
    (q : Vertex → ℝ × ℝ) (v a : Vertex) : ℝ × ℝ :=
  translatePoint x w (shift v a) (q a) - q v

def rotateCorners (k : Fin 3) (f : LiftedFace) : LiftedFace :=
  if k = 0 then f else if k = 1 then (f.2.1,f.2.2,f.1) else (f.2.2,f.1,f.2.1)

theorem type6_link_corner_data (v : Vertex) (i : Fin (type6_linkCycle v).length) :
    ∃ (j : Fin 16) (k : Fin 3),
      let f := rotateCorners k (liftedFaces j)
      f.1.1 = v ∧ f.2.1.1 = (type6_linkCycle v).get i ∧
      f.2.2.1 = (type6_linkCycle v).get (finRotate _ i) ∧
      (type6_edgeShift f.1.1 f.2.1.1).getD 0 = (liftedSide f.1 f.2.1).2.2 ∧
      (type6_edgeShift f.1.1 f.2.2.1).getD 0 = (liftedSide f.1 f.2.2).2.2 := by
  fin_cases v <;> revert i <;> decide +kernel

theorem facePeriod_correct (f : LiftedFace)
    (hd : f.1.1 ≠ f.2.1.1 ∧ f.1.1 ≠ f.2.2.1 ∧ f.2.1.1 ≠ f.2.2.1) :
    facePeriod f f.1.1 = f.1.2 ∧ facePeriod f f.2.1.1 = f.2.1.2 ∧
      facePeriod f f.2.2.1 = f.2.2.2 := by
  simp [facePeriod, hd.1.symm, hd.2.1.symm, hd.2.2.symm]

private theorem rotated_face_data (g : LiftedFace) (k : Fin 3)
    (hd : g.1.1 ≠ g.2.1.1 ∧ g.1.1 ≠ g.2.2.1 ∧ g.2.1.1 ≠ g.2.2.1) :
    let f := rotateCorners k g
    triangleVertexSet (liftedVertices f) = triangleVertexSet (liftedVertices g) ∧
      facePeriod g f.1.1 = f.1.2 ∧ facePeriod g f.2.1.1 = f.2.1.2 ∧
      facePeriod g f.2.2.1 = f.2.2.2 := by
  obtain ⟨ha,hb,hc⟩ := facePeriod_correct g hd
  fin_cases k <;> refine ⟨?_, ?_⟩ <;>
    first | exact ⟨ha,hb,hc⟩ | exact ⟨hb,hc,ha⟩ | exact ⟨hc,ha,hb⟩ |
      (ext i; simp [rotateCorners, liftedVertices, triangleVertexSet, triangleVertices,
        or_left_comm, or_comm])

private theorem rotated_labels_distinct (g : LiftedFace) (k : Fin 3)
    (hd : g.1.1 ≠ g.2.1.1 ∧ g.1.1 ≠ g.2.2.1 ∧ g.2.1.1 ≠ g.2.2.1) :
    let f := rotateCorners k g
    f.1.1 ≠ f.2.1.1 ∧ f.1.1 ≠ f.2.2.1 ∧ f.2.1.1 ≠ f.2.2.1 := by
  fin_cases k
  · exact hd
  · exact ⟨hd.2.2, hd.1.symm, hd.2.1.symm⟩
  · exact ⟨hd.2.1.symm, hd.2.2.symm, hd.1⟩

private theorem type6_reverse_edge_lift :
    ∀ (j : Fin 16) (k : Fin 3), ∃ (l : Fin 16) (r : Fin 3),
      let f := rotateCorners k (liftedFaces j)
      let g := rotateCorners r (liftedFaces l)
      g.1.1 = f.2.1.1 ∧ g.2.1.1 = f.1.1 ∧
        g.2.1.2 - g.1.2 = f.1.2 - f.2.1.2 := by
  decide +kernel

private theorem periodicFaceArea_rotate (x w : ℝ) (q : Vertex → ℝ × ℝ) (f : LiftedFace)
    (k : Fin 3) : periodicFaceArea x w q (rotateCorners k f) = periodicFaceArea x w q f := by
  fin_cases k <;> norm_num [rotateCorners,periodicFaceArea] <;> ring

private theorem edgeDirection_eq_sub (shift : Vertex → Vertex → Period)
    (x w : ℝ) (q : Vertex → ℝ × ℝ) (a b : Corner)
    (hab : shift a.1 b.1 = (liftedSide a b).2.2) :
    liftedEdgeDirection shift x w q a.1 b.1 =
      translatePoint x w b.2 (q b.1) - translatePoint x w a.2 (q a.1) := by
  apply Prod.ext <;>
    simp only [liftedEdgeDirection,hab,liftedSide,translatePoint,
      Prod.fst_sub,Prod.snd_sub,Int.cast_sub] <;> ring

private theorem edgeDirection_cross_eq (shift : Vertex → Vertex → Period)
    (x w : ℝ) (q : Vertex → ℝ × ℝ) (a b c : Corner)
    (hab : shift a.1 b.1 = (liftedSide a b).2.2)
    (hac : shift a.1 c.1 = (liftedSide a c).2.2) :
    Type5.cross (liftedEdgeDirection shift x w q a.1 b.1) (liftedEdgeDirection shift x w q a.1 c.1) =
      periodicFaceArea x w q (a,b,c) := by
  rw [edgeDirection_eq_sub shift x w q _ _ hab, edgeDirection_eq_sub shift x w q _ _ hac]
  rfl

/-- Affine evaluation on one lifted face in lattice coordinates. -/
noncomputable def facePeriodPoint (x w : ℝ) (q : Vertex → ℝ × ℝ)
    (f : LiftedFace) (u : Vertex → ℝ) : ℝ × ℝ :=
  ∑ i, u i • (periodCoordinates x w (q i) + realPeriod (facePeriod f i))

/-- The lattice-coordinate formula is affine evaluation in the lifted plane
followed by conversion to the lattice basis. -/
theorem facePeriodPoint_eq_coordinates (x w : ℝ) (hw : w ≠ 0) (q : Vertex → ℝ × ℝ)
    (f : LiftedFace) (u : Vertex → ℝ) :
    facePeriodPoint x w q f u = periodCoordinates x w
      (∑ i, u i • translatePoint x w (facePeriod f i) (q i)) := by
  unfold facePeriodPoint
  simp_rw [← periodCoordinates_translate x w hw]
  change (∑ i, u i • periodCoordinatesLinear x w (translatePoint x w (facePeriod f i) (q i))) =
    periodCoordinatesLinear x w (∑ i, u i • translatePoint x w (facePeriod f i) (q i))
  simp only [map_sum,map_smul]

end

@[expose] public section

/-- Two face lifts differ by a common integral translation on their shared labels. -/
def SharedFacePeriods {ι : Type*} (lift : ι → LiftedFace) : Prop :=
  ∀ (f g : ι) (a b : Vertex),
    a ∈ triangleVertexSet (liftedVertices (lift f)) →
    a ∈ triangleVertexSet (liftedVertices (lift g)) →
    b ∈ triangleVertexSet (liftedVertices (lift f)) →
    b ∈ triangleVertexSet (liftedVertices (lift g)) →
    facePeriod (lift f) a - facePeriod (lift g) a = facePeriod (lift f) b - facePeriod (lift g) b

/-- Combinatorial data for gluing compatible triangular lifts, with their
oppositely oriented edges and cyclic vertex fans. -/
structure PeriodicFaceSystem {ι : Type*} (fs : List Triangle) (lift : ι → LiftedFace) where
  mem : ∀ j, liftedVertices (lift j) ∈ fs
  cover : ∀ u : triangleWeightSpace fs, ∃ j, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift j)))
  shared : SharedFacePeriods lift
  distinct : ∀ j, let f := lift j
    f.1.1 ≠ f.2.1.1 ∧ f.1.1 ≠ f.2.2.1 ∧ f.2.1.1 ≠ f.2.2.1
  reverseEdge : ∀ (j : ι) (k : Fin 3), ∃ (l : ι) (r : Fin 3),
    let f := rotateCorners k (lift j)
    let g := rotateCorners r (lift l)
    g.1.1 = f.2.1.1 ∧ g.2.1.1 = f.1.1 ∧ g.2.1.2 - g.1.2 = f.1.2 - f.2.1.2
  link : Vertex → List Vertex
  link_nonempty : ∀ v, 0 < (link v).length
  edgeShift : Vertex → Vertex → Period
  link_corner : ∀ (v : Vertex) (i : Fin (link v).length), ∃ (j : ι) (k : Fin 3),
    let f := rotateCorners k (lift j)
    f.1.1 = v ∧ f.2.1.1 = (link v).get i ∧ f.2.2.1 = (link v).get (finRotate _ i) ∧
      edgeShift f.1.1 f.2.1.1 = (liftedSide f.1 f.2.1).2.2 ∧
      edgeShift f.1.1 f.2.2.1 = (liftedSide f.1 f.2.2).2.2


end

private theorem type6_shared_periods : SharedFacePeriods liftedFaces := by
  unfold SharedFacePeriods
  decide +kernel

private theorem periodPoint_agree {ι : Type*} (lift : ι → LiftedFace) (hshare : SharedFacePeriods lift)
    (x w : ℝ) (q : Vertex → ℝ × ℝ) (f g : ι) (u : Vertex → ℝ)
    (hf : u ∈ faceWeights (triangleVertexSet (liftedVertices (lift f))))
    (hg : u ∈ faceWeights (triangleVertexSet (liftedVertices (lift g)))) :
    projectPeriods (facePeriodPoint x w q (lift f) u) =
      projectPeriods (facePeriodPoint x w q (lift g) u) := by
  have hu : ∃ a, u a ≠ 0 := by
    by_contra! h
    have H := hf.2.1
    simp [h] at H
  obtain ⟨a,ha⟩ := hu
  let d := facePeriod (lift f) a - facePeriod (lift g) a
  have on_face {j : ι} {i : Vertex} (h : u ∈ faceWeights
      (triangleVertexSet (liftedVertices (lift j)))) (hi : u i ≠ 0) :
      i ∈ triangleVertexSet (liftedVertices (lift j)) := by
    by_contra hn
    exact hi (h.2.2 i hn)
  have point (i : Vertex) (hi : u i ≠ 0) :
      periodCoordinates x w (q i) + realPeriod (facePeriod (lift f) i) =
      (periodCoordinates x w (q i) + realPeriod (facePeriod (lift g) i)) + realPeriod d := by
    have he : facePeriod (lift f) i - facePeriod (lift g) i = d :=
      hshare f g i a (on_face hf hi) (on_face hg hi) (on_face hf ha) (on_face hg ha)
    have h₁ := congrArg (fun p : Period => (p.1 : ℝ)) he
    have h₂ := congrArg (fun p : Period => (p.2 : ℝ)) he
    simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub] at h₁ h₂
    exact Prod.ext (by simp only [Prod.fst_add, realPeriod]; linarith)
      (by simp only [Prod.snd_add, realPeriod]; linarith)
  have hsum : facePeriodPoint x w q (lift f) u = facePeriodPoint x w q (lift g) u + realPeriod d := by
    unfold facePeriodPoint
    rw [← one_smul ℝ (realPeriod d), ← hf.2.1, Finset.sum_smul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : u i = 0
    · simp [hi]
    · rw [← smul_add, point i hi]
  rw [hsum, projectPeriods_add_period]

/-- Develop the face containing the point and project it to the marked quotient. -/
public noncomputable def periodicDevelopment {ι : Type*} {fs : List Triangle} (lift : ι → LiftedFace)
    (hcover : ∀ u : triangleWeightSpace fs, ∃ f : ι,
      u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift f))))
    (x w : ℝ) (q : Vertex → ℝ × ℝ) (u : triangleWeightSpace fs) : MarkedTorus :=
  projectPeriods (facePeriodPoint x w q (lift (hcover u).choose) u.val)

public theorem periodicDevelopment_on_face {ι : Type*} {fs : List Triangle} (lift : ι → LiftedFace)
    (hcover : ∀ u : triangleWeightSpace fs, ∃ f : ι,
      u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift f))))
    (hshare : SharedFacePeriods lift) (x w : ℝ) (q : Vertex → ℝ × ℝ)
    (f : ι) (u : triangleWeightSpace fs)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift f)))) :
    periodicDevelopment lift hcover x w q u = projectPeriods (facePeriodPoint x w q (lift f) u.val) := by
  unfold periodicDevelopment
  exact periodPoint_agree lift hshare x w q _ f u.val (hcover u).choose_spec hu

/-- Compatible affine lifts glue to a continuous map on the finite complex. -/
public theorem periodicDevelopment_continuous {ι : Type*} [Finite ι] {fs : List Triangle} (lift : ι → LiftedFace)
    (hcover : ∀ u : triangleWeightSpace fs, ∃ f : ι,
      u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift f))))
    (hshare : SharedFacePeriods lift) (x w : ℝ) (q : Vertex → ℝ × ℝ) :
    Continuous (periodicDevelopment lift hcover x w q) := by
  let s (f : ι) : Set (triangleWeightSpace fs) :=
    Subtype.val ⁻¹' faceWeights (triangleVertexSet (liftedVertices (lift f)))
  have hc : (⋃ f, s f) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro u
    obtain ⟨f,hf⟩ := hcover u
    exact Set.mem_iUnion.mpr ⟨f,hf⟩
  refine (locallyFinite_of_finite s).continuous hc (fun f => ?_) (fun f => ?_)
  · exact (isCompact_faceWeights _).isClosed.preimage continuous_subtype_val
  · have h₁ : Continuous (facePeriodPoint x w q (lift f)) := by
      unfold facePeriodPoint
      fun_prop
    have h₂ : Continuous (projectPeriods : ℝ × ℝ → MarkedTorus) :=
      ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst).prodMk
        ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)
    exact (h₂.comp (h₁.comp continuous_subtype_val)).continuousOn.congr
      (fun u hu => periodicDevelopment_on_face lift hcover hshare x w q f u hu)

public theorem weight_has_liftedFace (u : triangleWeightSpace type6FlippedFaces) :
    ∃ f : Fin 16, u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces f))) := by
  obtain ⟨t,ht,hu⟩ := u.property
  have H := type6_liftedSidesPair.1
  rw [← H, List.map_map] at ht
  obtain ⟨f,_,rfl⟩ := List.mem_map.mp ht
  exact ⟨f,hu⟩

/-- Affine development of the intrinsic faces into the marked lattice quotient. -/
public noncomputable def type6_intrinsicMap (x w : ℝ) (q : Vertex → ℝ × ℝ)
    : triangleWeightSpace type6FlippedFaces → MarkedTorus :=
  periodicDevelopment liftedFaces weight_has_liftedFace x w q

/-- On each face the quotient map agrees with the prescribed affine lift. -/
public theorem type6_intrinsicMap_on_face (x w : ℝ) (q : Vertex → ℝ × ℝ) (f : Fin 16)
    (u : triangleWeightSpace type6FlippedFaces)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (liftedFaces f)))) :
    type6_intrinsicMap x w q u = projectPeriods (facePeriodPoint x w q (liftedFaces f) u.val) :=
  periodicDevelopment_on_face liftedFaces weight_has_liftedFace type6_shared_periods x w q f u hu

/-- The prescribed affine lifts glue to a continuous map of the labeled complex. -/
public theorem type6_intrinsicMap_continuous (x w : ℝ) (q : Vertex → ℝ × ℝ) :
    Continuous (type6_intrinsicMap x w q) :=
  periodicDevelopment_continuous liftedFaces weight_has_liftedFace type6_shared_periods x w q

private def cornerWeights (a b c : Vertex) (s t : ℝ) : Vertex → ℝ :=
  Pi.single a (1-s-t) + Pi.single b s + Pi.single c t

private theorem cornerWeights_supported (a b c : Vertex) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ 1) :
    cornerWeights a b c s t ∈ faceWeights (triangleVertexSet (a,b,c)) := by
  refine ⟨fun i => ?_,?_,fun i hi => ?_⟩
  · simp only [cornerWeights,Pi.add_apply,Pi.single_apply]
    split_ifs <;> linarith
  · simp only [cornerWeights,Pi.add_apply,Pi.single_apply,Finset.sum_add_distrib,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    ring
  · simp only [triangleVertexSet_eq, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp [cornerWeights,hi.1,hi.2.1,hi.2.2]

private theorem sum_cornerWeights {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a b c : Vertex) (s t : ℝ) (p : Vertex → E) :
    (∑ i, cornerWeights a b c s t i • p i) = (1-s-t) • p a + s • p b + t • p c := by
  simp only [cornerWeights,Pi.add_apply,Pi.single_apply,add_smul,Finset.sum_add_distrib,
    ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

private theorem cornerWeights_total (a b c : Vertex) (u : Vertex → ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu : u ∈ faceWeights (triangleVertexSet (a,b,c))) :
    u a + u b + u c = 1 := by
  have hsum : (∑ i ∈ ({a,b,c} : Finset Vertex), u i) = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ _)]
    · exact hu.2.1
    · intro i _ hi
      exact hu.2.2 i (by rwa [triangleVertexSet_eq])
  rwa [Finset.sum_insert (show a ∉ ({b,c} : Finset Vertex) by simp [hab,hac]),
    Finset.sum_insert (show b ∉ ({c} : Finset Vertex) by simp [hbc]),
    Finset.sum_singleton, ← add_assoc] at hsum

private theorem cornerWeights_recover (a b c : Vertex) (u : Vertex → ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu : u ∈ faceWeights (triangleVertexSet (a,b,c))) :
    u = cornerWeights a b c (u b) (u c) := by
  have ha : 1-u b-u c = u a := by linarith [cornerWeights_total a b c u hab hac hbc hu]
  funext i
  by_cases ia : i = a
  · subst i
    simp [cornerWeights,hab,hac,ha]
  by_cases ib : i = b
  · subst i
    simp [cornerWeights,ia,hbc]
  by_cases ic : i = c
  · subst i
    simp [cornerWeights,ia,ib]
  have hz : u i = 0 := hu.2.2 i (by simp [triangleVertexSet_eq,ia,ib,ic])
  simp [cornerWeights,ia,ib,ic,hz]

private def facePoint (A B C : ℝ × ℝ) (s t : ℝ) : ℝ × ℝ :=
  A + s • (B-A) + t • (C-A)

private noncomputable def faceParam (A B C p : ℝ × ℝ) : ℝ × ℝ :=
  let d := Type5.cross (B-A) (C-A)
  (Type5.cross (p-A) (C-A) / d, Type5.cross (B-A) (p-A) / d)

private theorem continuous_faceParam (A B C : ℝ × ℝ) : Continuous (faceParam A B C) := by
  unfold faceParam Type5.cross
  fun_prop

private theorem continuous_cornerWeights (a b c : Vertex) :
    Continuous (fun p : ℝ × ℝ => cornerWeights a b c p.1 p.2) := by
  apply continuous_pi
  intro i
  simp only [cornerWeights,Pi.add_apply,Pi.single_apply]
  split_ifs <;> fun_prop

private theorem facePoint_faceParam (A B C p : ℝ × ℝ) (hd : Type5.cross (B-A) (C-A) ≠ 0) :
    facePoint A B C (faceParam A B C p).1 (faceParam A B C p).2 = p := by
  have h := coordinates_in_wedge (B-A) (C-A) (p-A) hd
  have he : p-A = (faceParam A B C p).1 • (B-A) + (faceParam A B C p).2 • (C-A) := h
  unfold facePoint
  rw [add_assoc, ← he]
  abel

private theorem faceParam_facePoint (A B C : ℝ × ℝ)
    (hd : Type5.cross (B-A) (C-A) ≠ 0) (s t : ℝ) :
    faceParam A B C (facePoint A B C s t) = (s,t) := by
  have scalar (a : ℝ) (q : ℝ × ℝ) : a • q = (a*q.1,a*q.2) := rfl
  apply Prod.ext
  · apply (div_eq_iff hd).mpr
    simp only [facePoint,Type5.cross,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,scalar]
    ring
  · apply (div_eq_iff hd).mpr
    simp only [facePoint,Type5.cross,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,scalar]
    ring

private def shiftedCorner (x w : ℝ) (q : Vertex → ℝ × ℝ) (d : Period) (c : Corner) :
    ℝ × ℝ :=
  translatePoint x w (c.2+d) (q c.1)

private theorem shiftedCorner_sub (x w : ℝ) (q : Vertex → ℝ × ℝ) (d : Period) (a b : Corner) :
    shiftedCorner x w q d b - shiftedCorner x w q d a =
      translatePoint x w b.2 (q b.1) - translatePoint x w a.2 (q a.1) := by
  apply Prod.ext <;> simp only [shiftedCorner,translatePoint,Prod.fst_sub,Prod.snd_sub,
    Prod.fst_add,Prod.snd_add,Int.cast_add] <;> ring

private theorem shiftedFace_det (x w : ℝ) (q : Vertex → ℝ × ℝ) (d : Period)
    (g : LiftedFace) (k : Fin 3) :
    let f := rotateCorners k g
    let A := shiftedCorner x w q d f.1
    let B := shiftedCorner x w q d f.2.1
    let C := shiftedCorner x w q d f.2.2
    Type5.cross (B-A) (C-A) = periodicFaceArea x w q g := by
  dsimp only
  rw [shiftedCorner_sub,shiftedCorner_sub,← periodicFaceArea_rotate x w q g k]
  rfl

namespace PeriodicFaceSystem

variable {ι : Type*} {fs : List Triangle} {lift : ι → LiftedFace} (S : PeriodicFaceSystem fs lift)

local notation "development" => periodicDevelopment lift S.cover

/-- The lifted faces based at any vertex cover a neighborhood
of that vertex, even when restricted to arbitrarily small barycentric weights. -/
private theorem vertexFan_mem_nhds (x w : ℝ) (q : Vertex → ℝ × ℝ)
    (hpos : ∀ j : ι, 0 < periodicFaceArea x w q (lift j)) (v : Vertex)
    {ε : ℝ} (hε : 0 < ε) :
    {p : ℝ × ℝ | ∃ (i : Fin (S.link v).length) (a b : ℝ),
      0 ≤ a ∧ 0 ≤ b ∧ a+b < ε ∧
      p = a • liftedEdgeDirection S.edgeShift x w q v ((S.link v).get i) +
        b • liftedEdgeDirection S.edgeShift x w q v ((S.link v).get (finRotate _ i))} ∈ 𝓝 0 := by
  let ns := S.link v
  let ray (i : Fin ns.length) := liftedEdgeDirection S.edgeShift x w q v (ns.get i)
  have hlen : 0 < ns.length := S.link_nonempty v
  let _ : Nonempty (Fin ns.length) := ⟨⟨0,hlen⟩⟩
  refine positiveFan_truncated_mem_nhds (finRotate ns.length) ray (fun i => ?_) hε
  obtain ⟨j,k,hv,ha,hb,h₁,h₂⟩ := S.link_corner v i
  let f := rotateCorners k (lift j)
  change 0 < Type5.cross (liftedEdgeDirection S.edgeShift x w q v (ns.get i))
    (liftedEdgeDirection S.edgeShift x w q v (ns.get (finRotate _ i)))
  rw [← hv, ← ha, ← hb, edgeDirection_cross_eq S.edgeShift x w q _ _ _ h₁ h₂]
  exact (periodicFaceArea_rotate x w q (lift j) k).symm ▸ hpos j

private theorem intrinsicMap_cornerWeights (x w : ℝ) (hw : w ≠ 0) (q : Vertex → ℝ × ℝ)
    (j : ι) (k : Fin 3) (d : Period) (s t : ℝ)
    (u : triangleWeightSpace fs)
    (hu : u.val = cornerWeights (rotateCorners k (lift j)).1.1
      (rotateCorners k (lift j)).2.1.1 (rotateCorners k (lift j)).2.2.1 s t)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ 1) :
    let f := rotateCorners k (lift j)
    let A := shiftedCorner x w q d f.1
    let B := shiftedCorner x w q d f.2.1
    let C := shiftedCorner x w q d f.2.2
    development x w q u = projectPeriods (periodCoordinates x w (facePoint A B C s t)) := by
  let f := rotateCorners k (lift j)
  obtain ⟨hset,ha,hb,hc⟩ := rotated_face_data (lift j) k (S.distinct j)
  have hus : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift j))) := by
    rw [hu, ← hset]
    exact cornerWeights_supported _ _ _ s t hs ht hst
  rw [periodicDevelopment_on_face lift S.cover S.shared x w q j u hus, facePeriodPoint_eq_coordinates x w hw,
    hu, sum_cornerWeights, ha,hb,hc]
  let A := translatePoint x w f.1.2 (q f.1.1)
  let B := translatePoint x w f.2.1.2 (q f.2.1.1)
  let C := translatePoint x w f.2.2.2 (q f.2.2.1)
  have he : (1-s-t) • A + s • B + t • C = facePoint A B C s t := by
    unfold facePoint
    module
  change projectPeriods (periodCoordinates x w ((1-s-t) • A + s • B + t • C)) = _
  rw [he]
  have hshift :
      facePoint (shiftedCorner x w q d f.1) (shiftedCorner x w q d f.2.1)
        (shiftedCorner x w q d f.2.2) s t = translatePoint x w d (facePoint A B C s t) := by
    unfold facePoint
    rw [shiftedCorner_sub,shiftedCorner_sub]
    apply Prod.ext <;> simp only [shiftedCorner,A,B,C,translatePoint,Prod.fst_add,Prod.snd_add,
      Int.cast_add] <;> ring
  rw [hshift,periodCoordinates_translate x w hw,projectPeriods_add_period]

private theorem eventually_inverse_face (x w : ℝ) (hw : w ≠ 0) (q : Vertex → ℝ × ℝ)
    (hpos : ∀ j : ι, 0 < periodicFaceArea x w q (lift j))
    (j : ι) (k : Fin 3) (d : Period) (s t : ℝ)
    (u : triangleWeightSpace fs)
    (hu : u.val = cornerWeights (rotateCorners k (lift j)).1.1
      (rotateCorners k (lift j)).2.1.1 (rotateCorners k (lift j)).2.2.1 s t)
    (hs : 0 < s) (hst : s+t < 1)
    {U : Set (triangleWeightSpace fs)} (hU : U ∈ 𝓝 u) :
    let f := rotateCorners k (lift j)
    let A := shiftedCorner x w q d f.1
    let B := shiftedCorner x w q d f.2.1
    let C := shiftedCorner x w q d f.2.2
    ∀ᶠ p in 𝓝 (facePoint A B C s t), 0 ≤ (faceParam A B C p).2 →
      projectPeriods (periodCoordinates x w p) ∈ development x w q '' U := by
  dsimp only
  let f := rotateCorners k (lift j)
  let A := shiftedCorner x w q d f.1
  let B := shiftedCorner x w q d f.2.1
  let C := shiftedCorner x w q d f.2.2
  let P := faceParam A B C
  let W := fun p => cornerWeights f.1.1 f.2.1.1 f.2.2.1 (P p).1 (P p).2
  let p₀ := facePoint A B C s t
  change ∀ᶠ p in 𝓝 p₀, 0 ≤ (P p).2 →
    projectPeriods (periodCoordinates x w p) ∈ development x w q '' U
  have hd : Type5.cross (B-A) (C-A) ≠ 0 := by
    rw [shiftedFace_det x w q d (lift j) k]
    exact (hpos j).ne'
  have hP : P p₀ = (s,t) := faceParam_facePoint A B C hd s t
  have hc : Continuous P := continuous_faceParam A B C
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hU
  have hW : Continuous W := (continuous_cornerWeights _ _ _).comp hc
  have hWu : W p₀ = u.val := by
    change cornerWeights f.1.1 f.2.1.1 f.2.2.1 (P p₀).1 (P p₀).2 = u.val
    rw [hP]
    exact hu.symm
  have hnear : W ⁻¹' Metric.ball u.val ε ∈ 𝓝 p₀ := by
    apply hW.continuousAt.preimage_mem_nhds
    rw [hWu]
    exact Metric.ball_mem_nhds u.val hε
  have hps : {p | 0 < (P p).1} ∈ 𝓝 p₀ :=
    (isOpen_lt continuous_const hc.fst).mem_nhds (by change 0 < (P p₀).1; rwa [hP])
  have hpst : {p | (P p).1+(P p).2 < 1} ∈ 𝓝 p₀ :=
    (isOpen_lt (hc.fst.add hc.snd) continuous_const).mem_nhds
      (by change (P p₀).1+(P p₀).2 < 1; rwa [hP])
  filter_upwards [hnear,hps,hpst] with p hn hps hpst ht
  have hs' : 0 ≤ (P p).1 := (show 0 < (P p).1 from hps).le
  have hst' : (P p).1+(P p).2 ≤ 1 := (show (P p).1+(P p).2 < 1 from hpst).le
  have hmem : W p ∈ faceWeights (triangleVertexSet (liftedVertices (lift j))) := by
    rw [← (rotated_face_data (lift j) k (S.distinct j)).1]
    exact cornerWeights_supported _ _ _ _ _ hs' ht hst'
  let v : triangleWeightSpace fs := ⟨W p,_,S.mem j,hmem⟩
  have hv : v ∈ U := hsub hn
  refine ⟨v,hv,?_⟩
  have he := intrinsicMap_cornerWeights S x w hw q j k d _ _ v rfl hs' ht hst'
  change development x w q v =
    projectPeriods (periodCoordinates x w (facePoint A B C (P p).1 (P p).2)) at he
  rwa [facePoint_faceParam A B C p hd] at he

private theorem quotient_mem_nhds (x w : ℝ) (hw : w ≠ 0) (p₀ : ℝ × ℝ)
    {S : Set MarkedTorus} (h : ∀ᶠ p in 𝓝 p₀, projectPeriods (periodCoordinates x w p) ∈ S) :
    S ∈ 𝓝 (projectPeriods (periodCoordinates x w p₀)) :=
  Filter.mem_of_superset ((isOpenMap_project_periodCoordinates x w hw).image_mem_nhds h)
    (Set.image_preimage_subset _ _)

private theorem intrinsicMap_open_at_faceInterior (x w : ℝ) (hw : w ≠ 0)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : ι, 0 < periodicFaceArea x w q (lift j))
    (j : ι) (k : Fin 3) (s t : ℝ) (u : triangleWeightSpace fs)
    (hu : u.val = cornerWeights (rotateCorners k (lift j)).1.1
      (rotateCorners k (lift j)).2.1.1 (rotateCorners k (lift j)).2.2.1 s t)
    (hs : 0 < s) (ht : 0 < t) (hst : s+t < 1)
    {U : Set (triangleWeightSpace fs)} (hU : U ∈ 𝓝 u) :
    development x w q '' U ∈ 𝓝 (development x w q u) := by
  let f := rotateCorners k (lift j)
  let A := shiftedCorner x w q 0 f.1
  let B := shiftedCorner x w q 0 f.2.1
  let C := shiftedCorner x w q 0 f.2.2
  let p₀ := facePoint A B C s t
  have hd : Type5.cross (B-A) (C-A) ≠ 0 := by
    rw [shiftedFace_det x w q 0 (lift j) k]
    exact (hpos j).ne'
  have hpoint : development x w q u = projectPeriods (periodCoordinates x w p₀) :=
    intrinsicMap_cornerWeights S x w hw q j k 0 s t u hu hs.le ht.le hst.le
  have hregion : {p | 0 < (faceParam A B C p).2} ∈ 𝓝 p₀ :=
    (isOpen_lt continuous_const (continuous_faceParam A B C).snd).mem_nhds (by
      change 0 < (faceParam A B C p₀).2
      rwa [faceParam_facePoint A B C hd])
  rw [hpoint]
  apply quotient_mem_nhds x w hw p₀
  filter_upwards [eventually_inverse_face S x w hw q hpos j k 0 s t u hu hs hst hU, hregion]
    with p h hside
  exact h (show 0 < (faceParam A B C p).2 from hside).le

private theorem cross_line_reverse (A B p : ℝ × ℝ) :
    Type5.cross (A-B) (p-B) = -Type5.cross (B-A) (p-A) := by
  simp only [Type5.cross,Prod.fst_sub,Prod.snd_sub]
  ring

private theorem intrinsicMap_open_at_edgeInterior (x w : ℝ) (hw : w ≠ 0)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : ι, 0 < periodicFaceArea x w q (lift j))
    (j : ι) (k : Fin 3) (s : ℝ) (u : triangleWeightSpace fs)
    (hu : u.val = cornerWeights (rotateCorners k (lift j)).1.1
      (rotateCorners k (lift j)).2.1.1 (rotateCorners k (lift j)).2.2.1 s 0)
    (hs : 0 < s) (hs' : s < 1) {U : Set (triangleWeightSpace fs)} (hU : U ∈ 𝓝 u) :
    development x w q '' U ∈ 𝓝 (development x w q u) := by
  obtain ⟨l,r,h₁,h₂,hperiod⟩ := S.reverseEdge j k
  let f := rotateCorners k (lift j)
  let g := rotateCorners r (lift l)
  let d := f.2.1.2 - g.1.2
  let A := shiftedCorner x w q 0 f.1
  let B := shiftedCorner x w q 0 f.2.1
  let C := shiftedCorner x w q 0 f.2.2
  let D := shiftedCorner x w q d g.2.2
  let p₀ := facePoint A B C s 0
  have hd₁ : g.1.2+d = f.2.1.2+0 := by dsimp [d]; abel
  have hd₂ : g.2.1.2+d = f.1.2+0 := by
    calc g.2.1.2+d = (g.2.1.2-g.1.2)+f.2.1.2 := by dsimp [d]; abel
      _ = _ := by rw [hperiod]; abel
  have hB : shiftedCorner x w q d g.1 = B := by
    change translatePoint x w (g.1.2+d) (q g.1.1) =
      translatePoint x w (f.2.1.2+0) (q f.2.1.1)
    rw [hd₁,h₁]
  have hA : shiftedCorner x w q d g.2.1 = A := by
    change translatePoint x w (g.2.1.2+d) (q g.2.1.1) =
      translatePoint x w (f.1.2+0) (q f.1.1)
    rw [hd₂,h₂]
  have hdL : 0 < Type5.cross (B-A) (C-A) := by
    rw [shiftedFace_det x w q 0 (lift j) k]
    exact hpos j
  have hdR : 0 < Type5.cross (A-B) (D-B) := by
    rw [← hA, ← hB, shiftedFace_det x w q d (lift l) r]
    exact hpos l
  have hrev : u.val = cornerWeights g.1.1 g.2.1.1 g.2.2.1 (1-s) 0 := by
    calc u.val = cornerWeights f.1.1 f.2.1.1 f.2.2.1 s 0 := hu
      _ = _ := by
        rw [h₁,h₂]
        simp [cornerWeights,add_comm]
        rfl
  have hp₀ : facePoint B A D (1-s) 0 = p₀ := by
    change facePoint B A D (1-s) 0 = facePoint A B C s 0
    unfold facePoint
    module
  have hpoint : development x w q u = projectPeriods (periodCoordinates x w p₀) :=
    intrinsicMap_cornerWeights S x w hw q j k 0 s 0 u hu hs.le le_rfl (by linarith)
  have hleft := eventually_inverse_face S x w hw q hpos j k 0 s 0 u hu hs (by linarith) hU
  have hright :
      ∀ᶠ p in 𝓝 p₀, 0 ≤ (faceParam B A D p).2 →
        projectPeriods (periodCoordinates x w p) ∈ development x w q '' U := by
    have h := eventually_inverse_face S x w hw q hpos l r d (1-s) 0 u hrev (by linarith)
      (by linarith) hU
    change ∀ᶠ p in 𝓝 (facePoint (shiftedCorner x w q d g.1) (shiftedCorner x w q d g.2.1) D (1-s) 0),
      0 ≤ (faceParam (shiftedCorner x w q d g.1) (shiftedCorner x w q d g.2.1) D p).2 →
        projectPeriods (periodCoordinates x w p) ∈ development x w q '' U at h
    rwa [hB,hA,hp₀] at h
  rw [hpoint]
  apply quotient_mem_nhds x w hw p₀
  filter_upwards [hleft,hright] with p hleft hright
  by_cases hp : 0 ≤ Type5.cross (B-A) (p-A)
  · exact hleft (div_nonneg hp hdL.le)
  · have hsR : 0 ≤ Type5.cross (A-B) (p-B) := by
      rw [cross_line_reverse]
      exact neg_nonneg.mpr (le_of_not_ge hp)
    exact hright (div_nonneg hsR hdR.le)

private theorem cornerWeights_dist_lt (a b c : Vertex) (s t δ : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hδ : 0 < δ) (hst : s+t < δ) :
    dist (cornerWeights a b c s t) (Pi.single a 1) < δ := by
  rw [dist_pi_lt_iff hδ]
  intro i
  simp only [cornerWeights,Pi.add_apply,Pi.single_apply,Real.dist_eq]
  split_ifs <;> rw [abs_lt] <;> constructor <;> linarith

private theorem intrinsicMap_at_vertex (x w : ℝ) (hw : w ≠ 0) (q : Vertex → ℝ × ℝ)
    (a : Vertex) (u : triangleWeightSpace fs) (hu : u.val = Pi.single a 1) :
    development x w q u = projectPeriods (periodCoordinates x w (q a)) := by
  obtain ⟨j,hj⟩ := S.cover u
  rw [periodicDevelopment_on_face lift S.cover S.shared x w q j u hj, facePeriodPoint_eq_coordinates x w hw, hu]
  simp only [Pi.single_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [periodCoordinates_translate x w hw, projectPeriods_add_period]

/-- Every neighborhood of a vertex maps onto a neighborhood of
its image in the marked quotient. -/
public theorem open_at_vertex (x w : ℝ) (hw : w ≠ 0)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : ι, 0 < periodicFaceArea x w q (lift j))
    (v : Vertex) (u : triangleWeightSpace fs) (hu : u.val = Pi.single v 1)
    {U : Set (triangleWeightSpace fs)} (hU : U ∈ 𝓝 u) :
    development x w q '' U ∈ 𝓝 (development x w q u) := by
  obtain ⟨ε,hε,hU⟩ := Metric.mem_nhds_iff.mp hU
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  let ns := S.link v
  let ray (i : Fin ns.length) := liftedEdgeDirection S.edgeShift x w q v (ns.get i)
  let F : Set (ℝ × ℝ) := {p | ∃ (i : Fin ns.length) (s t : ℝ), 0 ≤ s ∧ 0 ≤ t ∧ s+t < δ ∧
    p = s • ray i + t • ray (finRotate _ i)}
  have hF : F ∈ 𝓝 0 := vertexFan_mem_nhds S x w q hpos v hδ
  let W := (fun p : ℝ × ℝ => p - q v) ⁻¹' F
  have hW : W ∈ 𝓝 (q v) := by
    have hc : Continuous (fun p : ℝ × ℝ => p - q v) := continuous_id.sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hF)
  rw [intrinsicMap_at_vertex S x w hw q v u hu]
  refine Filter.mem_of_superset ((isOpenMap_project_periodCoordinates x w hw).image_mem_nhds hW) ?_
  rintro _ ⟨p,hp,rfl⟩
  obtain ⟨i,s,t,hs,ht,hst,hcoords⟩ : p-q v ∈ F := hp
  obtain ⟨j,k,hv,ha,hb,hsa,hsb⟩ := S.link_corner v i
  let f := rotateCorners k (lift j)
  obtain ⟨hset,hfa,hfb,hfc⟩ := rotated_face_data (lift j) k (S.distinct j)
  have hsε : s+t < ε := hst.trans_le (min_le_left _ _)
  have hs1 : s+t ≤ 1 := (hst.trans_le (min_le_right _ _)).le
  let weights := cornerWeights f.1.1 f.2.1.1 f.2.2.1 s t
  have hwj : weights ∈ faceWeights (triangleVertexSet (liftedVertices (lift j))) := by
    rw [← hset]
    exact cornerWeights_supported _ _ _ s t hs ht hs1
  let z : triangleWeightSpace fs := ⟨weights,_,S.mem j,hwj⟩
  have hz : z ∈ U := by
    apply hU
    change dist weights u.val < ε
    rw [hu, ← hv]
    exact cornerWeights_dist_lt _ _ _ s t ε hs ht hε hsε
  refine ⟨z,hz,?_⟩
  rw [periodicDevelopment_on_face lift S.cover S.shared x w q j z hwj, facePeriodPoint_eq_coordinates x w hw]
  change projectPeriods (periodCoordinates x w
    (∑ i, cornerWeights f.1.1 f.2.1.1 f.2.2.1 s t i •
      translatePoint x w (facePeriod (lift j) i) (q i))) = _
  rw [sum_cornerWeights,hfa,hfb,hfc]
  let A := translatePoint x w f.1.2 (q f.1.1)
  let B := translatePoint x w f.2.1.2 (q f.2.1.1)
  let C := translatePoint x w f.2.2.2 (q f.2.2.1)
  have he : (1-s-t) • A + s • B + t • C = translatePoint x w f.1.2 p := by
    have hp' : p - q f.1.1 = s • (B-A) + t • (C-A) := by
      change p - q v = s • liftedEdgeDirection S.edgeShift x w q v (ns.get i) +
        t • liftedEdgeDirection S.edgeShift x w q v (ns.get (finRotate _ i)) at hcoords
      rw [← hv, ← ha, ← hb, edgeDirection_eq_sub S.edgeShift x w q _ _ hsa, edgeDirection_eq_sub S.edgeShift x w q _ _ hsb] at hcoords
      exact hcoords
    have hadd : translatePoint x w f.1.2 p = A + (p - q f.1.1) := by
      apply Prod.ext <;> simp only [A,translatePoint,Prod.fst_add,Prod.snd_add,Prod.fst_sub,
        Prod.snd_sub] <;> ring
    rw [hadd,hp']
    module
  change projectPeriods (periodCoordinates x w ((1-s-t) • A + s • B + t • C)) = _
  rw [he, periodCoordinates_translate x w hw, projectPeriods_add_period]
  rfl

include S in
private theorem support_cases (j : ι) (u : triangleWeightSpace fs)
    (hu : u.val ∈ faceWeights (triangleVertexSet (liftedVertices (lift j)))) :
    (∃ v : Vertex, u.val = Pi.single v 1) ∨
      ∃ k : Fin 3, let f := rotateCorners k (lift j)
        0 < u.val f.1.1 ∧ 0 < u.val f.2.1.1 := by
  let f := lift j
  let a := f.1.1
  let b := f.2.1.1
  let c := f.2.2.1
  have hd : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
    simpa [a,b,c,f,rotateCorners] using rotated_labels_distinct (lift j) 0 (S.distinct j)
  have ht := cornerWeights_total a b c u.val hd.1 hd.2.1 hd.2.2 hu
  have hr := cornerWeights_recover a b c u.val hd.1 hd.2.1 hd.2.2 hu
  by_cases ha : 0 < u.val a
  · by_cases hb : 0 < u.val b
    · right
      exact ⟨0, by simpa [rotateCorners,a,b,f] using And.intro ha hb⟩
    · by_cases hc : 0 < u.val c
      · right
        exact ⟨2, by norm_num [rotateCorners,c,a,f] at *; exact ⟨hc,ha⟩⟩
      · left
        refine ⟨a, hr.trans ?_⟩
        have hb₀ : u.val b = 0 := le_antisymm (le_of_not_gt hb) (hu.1 b)
        have hc₀ : u.val c = 0 := le_antisymm (le_of_not_gt hc) (hu.1 c)
        simp [cornerWeights,hb₀,hc₀]
  · have ha₀ : u.val a = 0 := le_antisymm (le_of_not_gt ha) (hu.1 a)
    by_cases hb : 0 < u.val b
    · by_cases hc : 0 < u.val c
      · right
        exact ⟨1, by simpa [rotateCorners,b,c,f] using And.intro hb hc⟩
      · left
        refine ⟨b, hr.trans ?_⟩
        have hc₀ : u.val c = 0 := le_antisymm (le_of_not_gt hc) (hu.1 c)
        have hb₁ : u.val b = 1 := by linarith only [ha₀,hc₀,ht]
        simp [cornerWeights,hb₁,hc₀]
    · left
      refine ⟨c, hr.trans ?_⟩
      have hb₀ : u.val b = 0 := le_antisymm (le_of_not_gt hb) (hu.1 b)
      have hc₁ : u.val c = 1 := by linarith only [ha₀,hb₀,ht]
      simp [cornerWeights,hb₀,hc₁]

/-- Positive face areas and opposite shared edge orientations make the
intrinsic development an open map. -/
public theorem isOpenMap (x w : ℝ) (hw : w ≠ 0)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : ι, 0 < periodicFaceArea x w q (lift j)) :
    IsOpenMap (development x w q) := by
  apply IsOpenMap.of_nhds_le
  intro u V hV
  let U := (development x w q) ⁻¹' V
  have hU : U ∈ 𝓝 u := hV
  suffices h : development x w q '' U ∈ 𝓝 (development x w q u) from
    Filter.mem_of_superset h (Set.image_preimage_subset _ _)
  obtain ⟨j,hj⟩ := S.cover u
  rcases support_cases S j u hj with ⟨v,hv⟩ | ⟨k,ha,hb⟩
  · exact open_at_vertex S x w hw q hpos v u hv hU
  · let f := rotateCorners k (lift j)
    have huf : u.val ∈ faceWeights (triangleVertexSet (liftedVertices f)) := by
      rw [(rotated_face_data (lift j) k (S.distinct j)).1]
      exact hj
    obtain ⟨hab,hac,hbc⟩ := rotated_labels_distinct (lift j) k (S.distinct j)
    have ht := cornerWeights_total f.1.1 f.2.1.1 f.2.2.1 u.val hab hac hbc huf
    have hv := cornerWeights_recover f.1.1 f.2.1.1 f.2.2.1 u.val hab hac hbc huf
    have hadd : u.val f.2.1.1 + u.val f.2.2.1 < 1 := by linarith only [ha,ht]
    rcases lt_or_eq_of_le (huf.1 f.2.2.1) with hpos₂ | he
    · exact intrinsicMap_open_at_faceInterior S x w hw q hpos j k _ _ u hv hb hpos₂ hadd hU
    · rw [← he] at hv hadd
      exact intrinsicMap_open_at_edgeInterior S x w hw q hpos j k _ u hv hb (by simpa using hadd) hU

/-- The compact realization with positive intrinsic face areas
surjects onto its connected lattice quotient. -/
public theorem surjective [Finite ι] [Nonempty ι] (x w : ℝ) (hw : w ≠ 0)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : ι, 0 < periodicFaceArea x w q (lift j)) :
    Function.Surjective (development x w q) := by
  let _ : CompactSpace (triangleWeightSpace fs) :=
    isCompact_iff_compactSpace.mp (isCompact_triangleWeightSpace _)
  have ho := (isOpenMap S x w hw q hpos).isOpen_range
  have hc := (isCompact_range (periodicDevelopment_continuous lift S.cover S.shared x w q)).isClosed
  let j : ι := Classical.choice inferInstance
  let f := lift j
  have hv : cornerWeights f.1.1 f.2.1.1 f.2.2.1 0 0 ∈
      faceWeights (triangleVertexSet (liftedVertices f)) :=
    cornerWeights_supported _ _ _ 0 0 (by norm_num) (by norm_num) (by norm_num)
  let u : triangleWeightSpace fs := ⟨_,_,S.mem j,hv⟩
  have hn : (Set.range (development x w q)).Nonempty :=
    ⟨_,Set.mem_range_self u⟩
  exact Set.range_eq_univ.mp (IsClopen.eq_univ ⟨hc,ho⟩ hn)

end PeriodicFaceSystem

public def type6_periodicFaceSystem : PeriodicFaceSystem type6FlippedFaces liftedFaces where
  mem j := by
    rw [← type6_liftedSidesPair.1, List.map_map]
    exact List.mem_map.mpr ⟨j,by simp,rfl⟩
  cover := weight_has_liftedFace
  shared := type6_shared_periods
  distinct := by decide +kernel
  reverseEdge := type6_reverse_edge_lift
  link := type6_linkCycle
  link_nonempty v := lt_of_lt_of_le (by decide : 0 < 3) (type6_linkCycle_checked v).2.1
  edgeShift v a := (type6_edgeShift v a).getD 0
  link_corner := type6_link_corner_data

public theorem type6_intrinsicMap_eq_development (x w : ℝ) (q : Vertex → ℝ × ℝ) :
    type6_intrinsicMap x w q = periodicDevelopment liftedFaces type6_periodicFaceSystem.cover x w q := by
  unfold type6_intrinsicMap
  rfl

public theorem type6_intrinsicMap_open_at_vertex (x w : ℝ) (hw : w ≠ 0)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : Fin 16, 0 < periodicFaceArea x w q (liftedFaces j))
    (v : Vertex) (u : triangleWeightSpace type6FlippedFaces) (hu : u.val = Pi.single v 1)
    {U : Set (triangleWeightSpace type6FlippedFaces)} (hU : U ∈ 𝓝 u) :
    type6_intrinsicMap x w q '' U ∈ 𝓝 (type6_intrinsicMap x w q u) :=
  type6_periodicFaceSystem.open_at_vertex x w hw q hpos v u hu hU

public theorem type6_intrinsicMap_isOpenMap (x w : ℝ) (hw : w ≠ 0)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : Fin 16, 0 < periodicFaceArea x w q (liftedFaces j)) :
    IsOpenMap (type6_intrinsicMap x w q) :=
  type6_periodicFaceSystem.isOpenMap x w hw q hpos

public theorem type6_intrinsicMap_surjective (x w : ℝ) (hw : w ≠ 0)
    (q : Vertex → ℝ × ℝ) (hpos : ∀ j : Fin 16, 0 < periodicFaceArea x w q (liftedFaces j)) :
    Function.Surjective (type6_intrinsicMap x w q) :=
  type6_periodicFaceSystem.surjective x w hw q hpos

/-- Subtracting two affine points on a face uses the differences of its last
two barycentric weights. -/
public theorem lifted_affine_difference {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : LiftedFace) (hd : f.1.1 ≠ f.2.1.1 ∧ f.1.1 ≠ f.2.2.1 ∧ f.2.1.1 ≠ f.2.2.1)
    (p : Vertex → E) (u v : Vertex → ℝ)
    (hu : u ∈ faceWeights (triangleVertexSet (liftedVertices f)))
    (hv : v ∈ faceWeights (triangleVertexSet (liftedVertices f))) :
    ((∑ i, u i • p i) - ∑ i, v i • p i) =
      (u f.2.1.1 - v f.2.1.1) • (p f.2.1.1 - p f.1.1) +
        (u f.2.2.1 - v f.2.2.1) • (p f.2.2.1 - p f.1.1) := by
  obtain ⟨hab,hac,hbc⟩ := hd
  have shape (z : Vertex → ℝ) (hz : z ∈ faceWeights (triangleVertexSet (liftedVertices f))) :
      (∑ i, z i • p i) = (1-z f.2.1.1-z f.2.2.1) • p f.1.1 +
        (z f.2.1.1) • p f.2.1.1 + (z f.2.2.1) • p f.2.2.1 := by
    have h := cornerWeights_recover f.1.1 f.2.1.1 f.2.2.1 z hab hac hbc hz
    calc
      (∑ i, z i • p i) =
          ∑ i, cornerWeights f.1.1 f.2.1.1 f.2.2.1 (z f.2.1.1) (z f.2.2.1) i • p i :=
        congrArg (fun w : Vertex → ℝ => ∑ i, w i • p i) h
      _ = _ := sum_cornerWeights _ _ _ _ _ _
  rw [shape u hu,shape v hv]
  module

private theorem facePeriodPoint_on_parameters (x w : ℝ) (hw : w ≠ 0) (q : Vertex → ℝ × ℝ)
    (f : LiftedFace) (hd : f.1.1 ≠ f.2.1.1 ∧ f.1.1 ≠ f.2.2.1 ∧ f.2.1.1 ≠ f.2.2.1)
    (u : Vertex → ℝ)
    (hu : u ∈ faceWeights (triangleVertexSet (liftedVertices f))) :
    facePeriodPoint x w q f u = facePoint (latticeCorner x w q f.1)
      (latticeCorner x w q f.2.1) (latticeCorner x w q f.2.2) (u f.2.1.1) (u f.2.2.1) := by
  obtain ⟨hab,hac,hbc⟩ := hd
  have hwts := cornerWeights_recover f.1.1 f.2.1.1 f.2.2.1 u hab hac hbc hu
  calc
    facePeriodPoint x w q f u =
        facePeriodPoint x w q f (cornerWeights f.1.1 f.2.1.1 f.2.2.1 (u f.2.1.1) (u f.2.2.1)) :=
      congrArg (facePeriodPoint x w q f) hwts
    _ = _ := by
      obtain ⟨ha,hb,hc⟩ := facePeriod_correct f ⟨hab,hac,hbc⟩
      unfold facePeriodPoint
      rw [sum_cornerWeights,ha,hb,hc]
      simp_rw [← periodCoordinates_translate x w hw]
      unfold facePoint latticeCorner
      module

public theorem facePeriodPoint_mem_latticeTriangle (x w : ℝ) (hw : w ≠ 0) (q : Vertex → ℝ × ℝ)
    (f : LiftedFace) (hd : f.1.1 ≠ f.2.1.1 ∧ f.1.1 ≠ f.2.2.1 ∧ f.2.1.1 ≠ f.2.2.1)
    (u : Vertex → ℝ)
    (hu : u ∈ faceWeights (triangleVertexSet (liftedVertices f))) :
    facePeriodPoint x w q f u ∈ latticeTriangle x w q f := by
  obtain ⟨hab,hac,hbc⟩ := hd
  have hsum := cornerWeights_total f.1.1 f.2.1.1 f.2.2.1 u hab hac hbc hu
  exact ⟨u f.2.1.1,u f.2.2.1,hu.1 _,hu.1 _,by linarith [(hu.1 f.1.1)],
    facePeriodPoint_on_parameters x w hw q f ⟨hab,hac,hbc⟩ u hu⟩

public theorem facePeriodPoint_injOn (x w : ℝ) (hw : w ≠ 0) (q : Vertex → ℝ × ℝ)
    (f : LiftedFace) (hd : f.1.1 ≠ f.2.1.1 ∧ f.1.1 ≠ f.2.2.1 ∧ f.2.1.1 ≠ f.2.2.1)
    (harea : latticeFaceArea x w q f ≠ 0) :
    Set.InjOn (facePeriodPoint x w q f)
      (faceWeights (triangleVertexSet (liftedVertices f))) := by
  intro u hu v hv h
  let A := latticeCorner x w q f.1
  let B := latticeCorner x w q f.2.1
  let C := latticeCorner x w q f.2.2
  have hdet : Type5.cross (B-A) (C-A) ≠ 0 := harea
  have h₁ : facePeriodPoint x w q f u = facePoint A B C (u f.2.1.1) (u f.2.2.1) :=
    facePeriodPoint_on_parameters x w hw q f hd u hu
  have h₂ : facePeriodPoint x w q f v = facePoint A B C (v f.2.1.1) (v f.2.2.1) :=
    facePeriodPoint_on_parameters x w hw q f hd v hv
  have hpar := congrArg (faceParam A B C) h
  rw [h₁,h₂,faceParam_facePoint A B C hdet,faceParam_facePoint A B C hdet] at hpar
  obtain ⟨hB,hC⟩ := Prod.mk.inj hpar
  obtain ⟨hab,hac,hbc⟩ := hd
  calc
    u = cornerWeights f.1.1 f.2.1.1 f.2.2.1 (u f.2.1.1) (u f.2.2.1) :=
      cornerWeights_recover _ _ _ u hab hac hbc hu
    _ = cornerWeights f.1.1 f.2.1.1 f.2.2.1 (v f.2.1.1) (v f.2.2.1) := by rw [hB,hC]
    _ = v := (cornerWeights_recover _ _ _ v hab hac hbc hv).symm

end OrigamiTorus
