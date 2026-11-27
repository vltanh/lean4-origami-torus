module

public import OrigamiTorus.EightVertex.Type6.Metric
public import OrigamiTorus.EightVertex.Type6.Inflation
import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Fin

/-! Intrinsic lifts of the Type 6 faces and their period pairings. -/

@[expose] public section

namespace OrigamiTorus

abbrev Corner := Vertex × Period
abbrev LiftedFace := Corner × Corner × Corner
abbrev LiftedSide := Vertex × Vertex × Period

def liftedFaces : Fin 16 → LiftedFace :=
  ![((0,(0,0)),(3,(0,0)),(1,(0,0))),
    ((0,(0,0)),(2,(0,0)),(4,(0,-1))),
    ((0,(0,0)),(4,(0,-1)),(3,(0,0))),
    ((1,(0,0)),(3,(0,0)),(6,(0,0))),
    ((1,(0,0)),(4,(0,0)),(5,(0,0))),
    ((1,(0,0)),(7,(0,0)),(4,(0,0))),
    ((1,(0,0)),(6,(0,0)),(7,(0,0))),
    ((2,(1,0)),(6,(0,0)),(4,(1,-1))),
    ((2,(1,0)),(5,(1,0)),(7,(0,0))),
    ((2,(1,0)),(7,(0,0)),(6,(0,0))),
    ((3,(0,1)),(4,(0,0)),(7,(0,0))),
    ((3,(0,0)),(5,(1,-1)),(6,(0,0))),
    ((3,(0,1)),(7,(0,0)),(5,(1,0))),
    ((4,(1,-1)),(6,(0,0)),(5,(1,-1))),
    ((0,(0,0)),(1,(0,0)),(5,(0,0))),
    ((0,(0,0)),(5,(0,0)),(2,(0,0)))]

def liftedVertices (f : LiftedFace) : Triangle := (f.1.1, f.2.1.1, f.2.2.1)

def liftedSide (a b : Corner) : LiftedSide :=
  (a.1, b.1, (b.2.1 - a.2.1, b.2.2 - a.2.2))

def liftedSides (f : LiftedFace) : List LiftedSide :=
  [liftedSide f.1 f.2.1, liftedSide f.2.1 f.2.2, liftedSide f.2.2 f.1]

def reverseSide (e : LiftedSide) : LiftedSide := (e.2.1, e.1, (-e.2.2.1, -e.2.2.2))

theorem type6_liftedSidesPair :
    let f := (List.finRange 16).map liftedFaces
    let ss := f.flatMap liftedSides
    f.map liftedVertices = type6FlippedFaces ∧ ss.Nodup ∧ ss.all (fun e => ss.contains (reverseSide e)) = true := by
  decide +kernel

theorem type6_liftedSides_match_edgePeriod :
    let f := (List.finRange 16).map liftedFaces
    let sides := (f.flatMap liftedSides).filter (fun e => decide (e.1 < e.2.1))
    let table := (List.finRange 24).map (fun i =>
      let e := edgePeriod i
      (e.1.1,e.1.2,e.2))
    sides.all table.contains = true ∧ table.all sides.contains = true := by
  decide +kernel

def cornerPoint {R : Type*} [Field R] (second : Bool) (x w : R) (p : Corner) : R × R :=
  translatePoint x w p.2 (intrinsicPoint second x w p.1)

def signedFaceArea {R : Type*} [Field R] (second : Bool) (x w : R) (f : LiftedFace) : R :=
  let p := cornerPoint second x w
  let a := p f.1
  let b := p f.2.1
  let c := p f.2.2
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

set_option maxHeartbeats 0 in
private theorem areas_false (x h : ℝ) (hl : 0 ≤ x)
    (hu : x ≤ (1 / 6)) (hh : 0 ≤ h) (f : Fin 16) :
    0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces f) := by
  have hx : 0 ≤ x := by linarith only [hl]
  have hsq : x^2 ≤ (1 / 36) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hu) (add_nonneg hx (by norm_num : (0 : ℝ) ≤ (1 / 6)))]
  have hx2 : 0 ≤ x^2 := sq_nonneg x
  have hxh : 0 ≤ x*h := mul_nonneg hx hh
  fin_cases f
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 0)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 0) =
        (3 / 27262976) * (-173472 * x + 43264 * h + 217153) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-173472 * x + 43264 * h + 217153) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 1)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 1) =
        (61 / 256) * (h + 1) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (h + 1) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 2)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 2) =
        (417 / 524288) * (-160 * x + 256 * h + 281) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-160 * x + 256 * h + 281) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 3)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 3) =
        (11 / 6815744) * (-37024 * x + 43264 * h + 51185) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-37024 * x + 43264 * h + 51185) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 4)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 4) =
        (1 / 851968) * (128 * x + 41) * (-2080 * x + 3328 * h + 3389) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (128 * x + 41) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (-2080 * x + 3328 * h + 3389) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 5)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 5) =
        (1 / 16187392) * (-128 * x + 23) * (173472 * x + 63232 * h + 26119) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-128 * x + 23) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (173472 * x + 63232 * h + 26119) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 6)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 6) =
        (11 / 4046848) * (173472 * x + 63232 * h + 26119) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (173472 * x + 63232 * h + 26119) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 7)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 7) =
        (5 / 262144) * (5248 * x + 4096 * h + 5777) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (5248 * x + 4096 * h + 5777) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 8)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 8) =
        (1 / 4096) * (-640 * x + 1024 * h + 819) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-640 * x + 1024 * h + 819) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 9)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 9) =
        (5 / 1245184) * (53376 * x + 19456 * h + 22329) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (53376 * x + 19456 * h + 22329) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 10)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 10) =
        (1 / 39845888) * (-128 * x + 23) * (253536 * x + 92416 * h + 266305) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-128 * x + 23) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (253536 * x + 92416 * h + 266305) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 11)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 11) =
        (1 / 524288) * (-160 * x + 256 * h + 281) * (-416 * x + 89) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-160 * x + 256 * h + 281) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (-416 * x + 89) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 12)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 12) =
        (1 / 622592) * (425984 * x^2 - 128160 * x + 92416 * h + 100337) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (425984 * x^2 - 128160 * x + 92416 * h + 100337) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 13)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 13) =
        (1 / 65536) * (128 * x + 41) * (-160 * x + 256 * h + 281) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (128 * x + 41) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (-160 * x + 256 * h + 281) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 14)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 14) =
        (3 / 851968) * (-2080 * x + 3328 * h + 9021) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-2080 * x + 3328 * h + 9021) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea false x (1 - x^2 + h) (liftedFaces 15)
    have he : signedFaceArea false x (1 - x^2 + h) (liftedFaces 15) =
        (61 / 262144) * (-640 * x + 1024 * h + 819) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-640 * x + 1024 * h + 819) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity

set_option maxHeartbeats 0 in
private theorem areas_true (x h : ℝ) (hl : (1 / 6) ≤ x)
    (hu : x ≤ (1 / 2)) (hh : 0 ≤ h) (f : Fin 16) :
    0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces f) := by
  have hx : 0 ≤ x := by linarith only [hl]
  have hsq : x^2 ≤ (1 / 4) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hu) (add_nonneg hx (by norm_num : (0 : ℝ) ≤ (1 / 2)))]
  have hx2 : 0 ≤ x^2 := sq_nonneg x
  have hxh : 0 ≤ x*h := mul_nonneg hx hh
  fin_cases f
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 0)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 0) =
        (1 / 524288) * (-144 * x + 64 * h + 145) * (1024 * x - 1) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-144 * x + 64 * h + 145) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (1024 * x - 1) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 1)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 1) =
        (1 / 4096) * (h + 1) * (-1024 * x + 1025) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (h + 1) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (-1024 * x + 1025) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 2)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 2) =
        (9 / 4096) * (-112 * x + 64 * h + 113) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-112 * x + 64 * h + 113) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 3)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 3) =
        (1 / 16777216) * (457728 * x + 262144 * h + 461953) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (457728 * x + 262144 * h + 461953) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 4)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 4) =
        (1 / 16777216) * (1024 * x + 129) * (-8192 * x + 4096 * h + 7233) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (1024 * x + 129) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (-8192 * x + 4096 * h + 7233) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 5)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 5) =
        (1 / 16777216) * (4096 * h + 73) * (-1024 * x + 895) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (4096 * h + 73) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (-1024 * x + 895) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 6)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 6) =
        (1 / 131072) * (4096 * h + 73) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (4096 * h + 73) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 7)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 7) =
        (7 / 33554432) * (-1048576 * x^2 + 1048576 * h + 1065217) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-1048576 * x^2 + 1048576 * h + 1065217) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 8)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 8) =
        (1 / 32768) * (-7168 * x + 8192 * h + 7289) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-7168 * x + 8192 * h + 7289) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 9)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 9) =
        (7 / 262144) * (1024 * x + 8192 * h + 1169) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (1024 * x + 8192 * h + 1169) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 10)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 10) =
        (1 / 524288) * (144 * x + 64 * h + 145) * (-1024 * x + 895) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (144 * x + 64 * h + 145) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (-1024 * x + 895) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 11)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 11) =
        (447 / 262144) * (-112 * x + 64 * h + 113) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-112 * x + 64 * h + 113) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 12)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 12) =
        (1 / 2097152) * (-457728 * x + 262144 * h + 461953) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-457728 * x + 262144 * h + 461953) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 13)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 13) =
        (1 / 262144) * (-112 * x + 64 * h + 113) * (1024 * x + 129) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-112 * x + 64 * h + 113) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (1024 * x + 129) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 14)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 14) =
        (1 / 16777216) * (1024 * x - 1) * (-8192 * x + 4096 * h + 8257) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (1024 * x - 1) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (-8192 * x + 4096 * h + 8257) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity
  · change 0 < signedFaceArea true x (1 - x^2 + h) (liftedFaces 15)
    have he : signedFaceArea true x (1 - x^2 + h) (liftedFaces 15) =
        (1 / 33554432) * (-1024 * x + 1025) * (-7168 * x + 8192 * h + 7289) := by
      norm_num [signedFaceArea, cornerPoint, translatePoint, intrinsicPoint, stripPoint, liftedFaces]
      ring
    rw [he]
    have h0 : 0 < (-1024 * x + 1025) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    have h1 : 0 < (-7168 * x + 8192 * h + 7289) := by nlinarith only [hl,hu,hh,hx,hsq,hx2,hxh]
    positivity

/-- Every intrinsic lifted face is positively oriented. -/
theorem type6_intrinsicFacePositive (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    (f : Fin 16) : 0 < signedFaceArea second x w (liftedFaces f) := by
  have hw : 0 ≤ w - (1 - x^2) := sub_nonneg.mpr hd.2.2
  have hw' : 1 - x^2 + (w - (1 - x^2)) = w := by ring
  cases second
  · simpa only [hw'] using areas_false x _ hd.1 hd.2.1 hw f
  · simpa only [hw'] using areas_true x _ hd.1 hd.2.1 hw f

/-- The oriented double area of a face with the same marking after moving its vertices. -/
def periodicFaceArea (x w : ℝ) (q : Vertex → ℝ × ℝ) (f : LiftedFace) : ℝ :=
  let point (p : Corner) := translatePoint x w p.2 (q p.1)
  let a := point f.1
  let b := point f.2.1
  let c := point f.2.2
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)

set_option maxHeartbeats 0 in
/-- The total signed area is still that of a period cell for arbitrary vertex motions. -/
theorem type6_periodicTotalArea (x w : ℝ) (q : Vertex → ℝ × ℝ) :
    ∑ f : Fin 16, periodicFaceArea x w q (liftedFaces f) = 2*w := by
  norm_num [Fin.sum_univ_succ, periodicFaceArea, translatePoint, liftedFaces]
  ring

/-- The total signed area equals that of a period cell at the planar base. -/
theorem type6_intrinsicTotalArea (second : Bool) (x w : ℝ) :
    ∑ f : Fin 16, signedFaceArea second x w (liftedFaces f) = 2*w :=
  type6_periodicTotalArea x w (intrinsicPoint second x w)

open Filter Set
open scoped Topology

noncomputable def movedIntrinsicPoint (second : Bool) (x w : ℝ) (m : SheetMotion) (v : Vertex) :
    ℝ × ℝ := intrinsicPoint second x w v + IntrinsicMotion m v

theorem periodicFaceArea_continuous (second : Bool) (x w : ℝ) (f : LiftedFace) :
    Continuous (fun m : SheetMotion => periodicFaceArea x w (movedIntrinsicPoint second x w m) f) := by
  have hv (v : Vertex) : Continuous (fun m : SheetMotion => movedIntrinsicPoint second x w m v) := by
    fin_cases v <;> simp [movedIntrinsicPoint,IntrinsicMotion]
    all_goals constructor <;> fun_prop
  unfold periodicFaceArea translatePoint
  fun_prop (disch := assumption)

/-- Strict intrinsic orientations survive the same small corrections used by the length equations. -/
theorem type6_eventually_intrinsic_positive (second : Bool) (x w : ℝ) (hd : chartDomain second x w) :
    ∀ᶠ m : SheetMotion in 𝓝 0, ∀ f : Fin 16,
      0 < periodicFaceArea x w (movedIntrinsicPoint second x w m) (liftedFaces f) := by
  simp only [eventually_all]
  intro f
  have hbase : movedIntrinsicPoint second x w 0 = intrinsicPoint second x w := by
    funext v
    fin_cases v <;> simp [movedIntrinsicPoint,IntrinsicMotion]
  apply (isOpen_lt continuous_const (periodicFaceArea_continuous second x w (liftedFaces f))).mem_nhds
  change 0 < periodicFaceArea x w (movedIntrinsicPoint second x w 0) (liftedFaces f)
  rw [hbase]
  exact type6_intrinsicFacePositive second x w hd f

/-- A fixed-period length-matched generic lift with positive corrected intrinsic faces. -/
theorem type6_orientedLengthMatchedLift_regular (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion), 0 < t ∧ m ∈ U ∧
      lengthResidual second x w z (t,m) = 0 ∧
      ((fderiv ℝ (lengthResidual second x w z) (t,m)).comp
        (ContinuousLinearMap.inr ℝ ℝ SheetMotion)).IsInvertible ∧
      (∀ f : Fin 16, 0 < periodicFaceArea x w (movedIntrinsicPoint second x w m) (liftedFaces f)) ∧
      GenericLift (movedFoldedPoint second x w m) (fun v => t*z v) ∧
      ∀ pair ∈ type6DisjointPairs,
        isSeparated (movedFoldedPoint second x w m) (fun v => t*z v) pair := by
  have he := type6_eventually_intrinsic_positive second x w hd
  obtain ⟨V,hV,hopen,hzero⟩ := mem_nhds_iff.mp he
  obtain ⟨z,t,m,ht,hm,hlen,hi,hg,hs⟩ :=
    type6_lengthMatchedLift_regular second x w hd (hopen.inter hU) ⟨hzero,hbase⟩
  exact ⟨z,t,m,ht,hm.2,hlen,hi,hV hm.1,hg,hs⟩

/-- A fixed-period length-matched generic lift with positive corrected intrinsic faces. -/
theorem type6_orientedLengthMatchedLift (second : Bool) (x w : ℝ) (hd : chartDomain second x w)
    {U : Set SheetMotion} (hU : IsOpen U) (hbase : 0 ∈ U) :
    ∃ (z : Vertex → ℝ) (t : ℝ) (m : SheetMotion), 0 < t ∧ m ∈ U ∧
      lengthResidual second x w z (t,m) = 0 ∧
      (∀ f : Fin 16, 0 < periodicFaceArea x w (movedIntrinsicPoint second x w m) (liftedFaces f)) ∧
      GenericLift (movedFoldedPoint second x w m) (fun v => t*z v) ∧
      ∀ pair ∈ type6DisjointPairs,
        isSeparated (movedFoldedPoint second x w m) (fun v => t*z v) pair := by
  obtain ⟨z,t,m,ht,hm,hlen,_,hpos,hg,hs⟩ :=
    type6_orientedLengthMatchedLift_regular second x w hd hU hbase
  exact ⟨z,t,m,ht,hm,hlen,hpos,hg,hs⟩

end OrigamiTorus
