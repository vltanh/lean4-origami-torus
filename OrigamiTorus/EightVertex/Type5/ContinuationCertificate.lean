module

public import OrigamiTorus.EightVertex.Type5.Continuation
import Mathlib.Tactic

/-! The exact interval checks for orientation and separation on the Type 5 box. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus.Type5.Continuation

open Inclusion IntervalDyadicReal

private def shiftBox (d : Period) : Interval Dyadic × Interval Dyadic :=
  ((Interval.singleton (d.1 : Dyadic)).add ((Interval.singleton (d.2 : Dyadic)).mul xInterval),
    (Interval.singleton (d.2 : Dyadic)).mul yInterval)

private def displacementBox (a b : Vertex) : Interval Dyadic × Interval Dyadic :=
  let s := shiftBox (squareShift a b)
  (((coordinateBox b 0).sub (coordinateBox a 0)).add s.1,((coordinateBox b 1).sub (coordinateBox a 1)).add s.2)

private theorem shift_mem {x y : ℝ} (h : ModulusBox x y) (d : Period) :
    (translatePoint x y d (0,0)).1 ∈ (shiftBox d).1 ∧
      (translatePoint x y d (0,0)).2 ∈ (shiftBox d).2 := by
  simp only [shiftBox,translatePoint,zero_add]
  exact ⟨add_mem (intCast_mem _) (mul_mem (intCast_mem _) (xBound h).mem),
    mul_mem (intCast_mem _) (yBound h).mem⟩

private theorem displacement_mem {x y : ℝ} (h : ModulusBox x y) (a b : Vertex) :
    (intrinsic x y b-intrinsic x y a+shift x y a b).1 ∈ (displacementBox a b).1 ∧
    (intrinsic x y b-intrinsic x y a+shift x y a b).2 ∈ (displacementBox a b).2 := by
  obtain ⟨hx,hy⟩ := shift_mem h (squareShift a b)
  exact ⟨add_mem (sub_mem (coordinate_mem h b 0) (coordinate_mem h a 0)) hx,
    add_mem (sub_mem (coordinate_mem h b 1) (coordinate_mem h a 1)) hy⟩

private def intrinsicAreaBox (f : Triangle) : Interval Dyadic :=
  let u := displacementBox f.1 f.2.1
  let v := displacementBox f.1 f.2.2
  (u.1.mul v.2).sub (u.2.mul v.1)

private theorem intrinsic_area_mem {x y : ℝ} (h : ModulusBox x y) (f : Triangle) :
    markedFaceCross (shift x y) (intrinsic x y) f ∈ intrinsicAreaBox f := by
  have hu := displacement_mem h f.1 f.2.1
  have hv := displacement_mem h f.1 f.2.2
  have ho (a b s : Plane ℝ) : b+s-a = b-a+s := by abel
  unfold markedFaceCross
  rw [ho,ho]
  exact sub_mem (mul_mem hu.1 hv.2) (mul_mem hu.2 hv.1)

private def areaBox (a b c : Vertex) : Interval Dyadic :=
  ((coordinateBox b 2).mul ((coordinateBox c 3).sub (coordinateBox a 3))).add
    (((coordinateBox c 2).mul ((coordinateBox a 3).sub (coordinateBox b 3))).add
      ((coordinateBox a 2).mul ((coordinateBox b 3).sub (coordinateBox c 3))))

private theorem area_mem {x y : ℝ} (h : ModulusBox x y) (a b c : Vertex) :
    area (fun v => horizontal (extrinsic x y v)) a b c ∈ areaBox a b c := by
  simp only [area,areaBox,add_assoc]
  exact add_mem (mul_mem (coordinate_mem h b 2) (sub_mem (coordinate_mem h c 3) (coordinate_mem h a 3)))
    (add_mem (mul_mem (coordinate_mem h c 2) (sub_mem (coordinate_mem h a 3) (coordinate_mem h b 3)))
      (mul_mem (coordinate_mem h a 2) (sub_mem (coordinate_mem h b 3) (coordinate_mem h c 3))))

private def volumeBox (a b c d : Vertex) : Interval Dyadic :=
  (((coordinateBox a 4).neg.mul (areaBox b c d)).add ((coordinateBox b 4).mul (areaBox a c d))).sub
    ((coordinateBox c 4).mul (areaBox a b d)) |>.add ((coordinateBox d 4).mul (areaBox a b c))

private theorem volume_mem {x y : ℝ} (h : ModulusBox x y) (a b c d : Vertex) :
    volume (fun v => horizontal (extrinsic x y v)) (fun v => (extrinsic x y v).2.2) a b c d ∈
      volumeBox a b c d := by
  exact add_mem
    (sub_mem (add_mem (mul_mem (neg_mem (coordinate_mem h a 4)) (area_mem h b c d))
      (mul_mem (coordinate_mem h b 4) (area_mem h a c d)))
      (mul_mem (coordinate_mem h c 4) (area_mem h a b d)))
    (mul_mem (coordinate_mem h d 4) (area_mem h a b c))

private def strictSign (I : Interval Dyadic) : ℤ :=
  if I.lb.any fun l => 0 < l then 1 else if I.ub.any fun r => r < 0 then -1 else 0

private theorem sign_pos {v : ℝ} {I : Interval Dyadic} (hv : v ∈ I) (h : 0 < strictSign I) : 0 < v := by
  rw [mem_iff_mem_map,Interval.mem_map_iff] at hv
  rcases I with ⟨_ | a,b⟩
  · simp [strictSign] at h
    split at h <;> omega
  · have ha : 0 < a := by
      simp only [strictSign,Option.any_some,decide_eq_true_eq] at h
      split at h
      · assumption
      · split at h <;> omega
    have hz : 0 < Dyadic.toReal a := by simpa [Dyadic.toReal] using Dyadic.toReal_lt_toReal.mpr ha
    exact hz.trans_le (hv.1 a rfl)

private theorem sign_neg {v : ℝ} {I : Interval Dyadic} (hv : v ∈ I) (h : strictSign I < 0) : v < 0 := by
  rw [mem_iff_mem_map,Interval.mem_map_iff] at hv
  rcases I with ⟨a,_ | b⟩
  · simp [strictSign] at h
    split at h <;> omega
  · have hb : b < 0 := by
      simp only [strictSign,Option.any_some,decide_eq_true_eq] at h
      split at h
      · omega
      · split at h
        · assumption
        · omega
    exact (hv.2 b rfl).trans_lt (by simpa [Dyadic.toReal] using Dyadic.toReal_lt_toReal.mpr hb)

private theorem sign_mul_pos {u v : ℝ} {I J : Interval Dyadic} (hu : u ∈ I) (hv : v ∈ J)
    (h : 0 < strictSign I*strictSign J) : 0 < u*v := by
  rcases mul_pos_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact mul_pos (sign_pos hu ha) (sign_pos hv hb)
  · exact mul_pos_of_neg_of_neg (sign_neg hu ha) (sign_neg hv hb)

private theorem sign_mul_neg {u v : ℝ} {I J : Interval Dyadic} (hu : u ∈ I) (hv : v ∈ J)
    (h : strictSign I*strictSign J < 0) : u*v < 0 := by
  rcases mul_neg_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact mul_neg_of_pos_of_neg (sign_pos hu ha) (sign_neg hv hb)
  · exact mul_neg_of_neg_of_pos (sign_neg hu ha) (sign_pos hv hb)

theorem intrinsic_positive {x y : ℝ} (h : ModulusBox x y) {f : Triangle} (hf : f ∈ faces) :
    0 < markedFaceCross (shift x y) (intrinsic x y) f := by
  have checked : faces.all (fun f => decide (0 < strictSign (intrinsicAreaBox f))) = true := by decide +kernel
  exact sign_pos (intrinsic_area_mem h f) (of_decide_eq_true ((List.all_eq_true.mp checked) f hf))

def nearestDirections : List Period := [(1,0),(0,1),(-1,1)]

private def dotBox (u v : Interval Dyadic × Interval Dyadic) : Interval Dyadic :=
  (u.1.mul v.1).add (u.2.mul v.2)

private theorem dot_mem {u v : Plane ℝ} {A B : Interval Dyadic × Interval Dyadic}
    (hu : u.1 ∈ A.1 ∧ u.2 ∈ A.2) (hv : v.1 ∈ B.1 ∧ v.2 ∈ B.2) :
    dot u v ∈ dotBox A B := add_mem (mul_mem hu.1 hv.1) (mul_mem hu.2 hv.2)

private def nearestCheck (e : Edge) (d : Period) : Bool :=
  let D := shiftBox d
  let N := dotBox D D
  let W := (Interval.singleton (2 : Dyadic)).mul (dotBox (displacementBox e.1 e.2) D)
  decide (0 < strictSign (N.sub W) ∧ 0 < strictSign (N.add W))

set_option maxHeartbeats 0 in
private theorem nearest_checked : edgeList.all (fun e => nearestDirections.all (nearestCheck e)) = true := by
  decide +kernel

/-- The three nearest-direction inequalities are strict on every marked edge. -/
theorem nearest_slack {x y : ℝ} (h : ModulusBox x y) {e : Edge} (he : e ∈ edgeList)
    {d : Period} (hd : d ∈ nearestDirections) :
    let u := intrinsic x y e.2-intrinsic x y e.1+shift x y e.1 e.2
    let v := translatePoint x y d ((0,0) : Plane ℝ)
    2*|dot u v| < squared2 v := by
  have hc := (List.all_eq_true.mp ((List.all_eq_true.mp nearest_checked) e he)) d hd
  simp only [nearestCheck,decide_eq_true_eq] at hc
  have hv := shift_mem h d
  have hN := dot_mem hv hv
  have hW := mul_mem BoxArithmetic.two.mem (dot_mem (displacement_mem h e.1 e.2) hv)
  have hp := sign_pos (sub_mem hN hW) hc.1
  have hm := sign_pos (add_mem hN hW) hc.2
  dsimp only [squared2]
  rw [← abs_of_pos (by norm_num : (0 : ℝ) < 2),← abs_mul,abs_lt]
  exact ⟨by linarith only [hm],by linarith only [hp]⟩

private def volSign (a b c d : Vertex) : ℤ := strictSign (volumeBox a b c d)

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem volume_checked : ∀ a b c d : Vertex, a < b → b < c → c < d → volSign a b c d ≠ 0 := by
  decide +kernel

theorem spatial_generic {x y : ℝ} (h : ModulusBox x y) :
    GenericLift (fun v => horizontal (extrinsic x y v)) (fun v => (extrinsic x y v).2.2) := by
  intro a b c d hab hbc hcd
  rcases lt_or_gt_of_ne (volume_checked a b c d hab hbc hcd) with hneg | hpos
  · exact (sign_neg (volume_mem h a b c d) hneg).ne
  · exact (sign_pos (volume_mem h a b c d) hpos).ne'

private def separationCheck (p : Edge × Triangle) : Bool :=
  let ((a,b),c,d,e) := p
  @decide (separates (volSign b c d e) (volSign a c d e) (volSign a b d e) (volSign a b c e)
    (volSign a b c d)) (by unfold separates; infer_instance)

set_option maxHeartbeats 0 in
set_option maxRecDepth 65536 in
private theorem separation_checked : squareDisjointPairs.all separationCheck = true := by decide +kernel

theorem spatial_separation {x y : ℝ} (h : ModulusBox x y) (p : Edge × Triangle) (hp : p ∈ squareDisjointPairs) :
    isSeparated (fun v => horizontal (extrinsic x y v)) (fun v => (extrinsic x y v).2.2) p := by
  obtain ⟨⟨a,b⟩,c,d,e⟩ := p
  have hc := (List.all_eq_true.mp separation_checked) _ hp
  simp only [separationCheck,decide_eq_true_eq,separates] at hc
  simp only [isSeparated,separates]
  rcases hc with m | m | m | m
  · exact Or.inl (sign_mul_pos (volume_mem h b c d e) (volume_mem h a c d e) m)
  · exact Or.inr (Or.inl (sign_mul_pos (volume_mem h a b d e) (volume_mem h a b c e) m))
  · exact Or.inr (Or.inr (Or.inl (sign_mul_pos (volume_mem h a b c e) (volume_mem h a b c d) m)))
  · exact Or.inr (Or.inr (Or.inr (sign_mul_neg (volume_mem h a b d e) (volume_mem h a b c d) m)))

/-- The radical spatial realization is embedded for every modulus in the box. -/
theorem spatial_embedding {x y : ℝ} (h : ModulusBox x y) :
    Topology.IsClosedEmbedding (evaluateTriangles faces (extrinsic x y)) := by
  let p (i : Vertex) := horizontal (extrinsic x y i)
  let z (i : Vertex) := (extrinsic x y i).2.2
  have hg : GenericLift p z := spatial_generic h
  have hsep : EdgeTriangleSeparated (fun i => ((p i).1,(p i).2,z i)) faces := by
    rintro ⟨a,b⟩ he ⟨c,d,e⟩ hf hi
    have hm : ((a,b),(c,d,e)) ∈ squareDisjointPairs := by
      simpa only [squareDisjointPairs,edgeList] using mem_disjointTests he hf hi
    have hc : squareDisjointPairs.all (fun ((a,b),c,d,e) =>
        decide ([a,b,c,d,e].Pairwise (· ≠ ·))) = true := by decide +kernel
    have hh := of_decide_eq_true ((List.all_eq_true.mp hc) _ hm)
    rw [vertexHull_pair,vertexHull_triangle]
    exact separated_segment_disjoint_triangle p z a b c d e hg hh (spatial_separation h _ hm)
  have hp : (fun i => ((p i).1,(p i).2,z i)) = extrinsic x y := by
    funext i
    exact Prod.ext rfl (Prod.ext rfl rfl)
  exact hp ▸ spatialTriangles_isClosedEmbedding p z _ hg hsep

end OrigamiTorus.Type5.Continuation
