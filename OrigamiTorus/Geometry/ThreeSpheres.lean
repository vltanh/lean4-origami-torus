module

public import OrigamiTorus.Type5.Reconstruction
public import OrigamiTorus.Geometry.TriangleIntersections
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic

/-! The two radical candidates for the intersection of three spheres with
noncollinear centers. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus

open Type5 (dot3 squared3 squared2 dot horizontal atHeight smul3 smul2 signedRoot)

def cross3 (x y : Point3) : Point3 :=
  (x.2.1*y.2.2-x.2.2*y.2.1,x.2.2*y.1-x.1*y.2.2,x.1*y.2.1-x.2.1*y.1)

theorem squared3_nonneg (x : Point3) : 0 ≤ squared3 x := by
  simp only [squared3,squared2,dot,horizontal,← pow_two]
  positivity

theorem squared3_eq_zero_iff (x : Point3) : squared3 x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h₁ := sq_nonneg x.1
    have h₂ := sq_nonneg x.2.1
    have h₃ := sq_nonneg x.2.2
    simp only [squared3,squared2,dot,horizontal,← pow_two] at h
    exact Prod.ext (by change x.1 = 0; nlinarith)
      (Prod.ext (by change x.2.1 = 0; nlinarith) (by change x.2.2 = 0; nlinarith))
  · rintro rfl
    simp [squared3,squared2,dot,horizontal]

theorem squared3_pos {x : Point3} (hx : x ≠ 0) : 0 < squared3 x :=
  lt_of_le_of_ne (squared3_nonneg x) (Ne.symm ((squared3_eq_zero_iff x).not.mpr hx))

def gramDen (u v : Point3) : ℝ := squared3 u*squared3 v-(dot3 u v)^2

theorem gramDen_eq_cross_sq (u v : Point3) : gramDen u v = squared3 (cross3 u v) := by
  simp only [gramDen,cross3,squared3,dot3,squared2,dot,horizontal]
  ring

theorem gramDen_pos_of_noncollinear {a b c : Point3}
    (h : ¬ Collinear ℝ ({a,b,c} : Set Point3)) : 0 < gramDen (b-a) (c-a) := by
  let u := b-a
  let v := c-a
  have hv : v ≠ 0 := by
    intro hz
    have he : c = a := sub_eq_zero.mp hz
    apply h
    have hset : ({a,b,c} : Set Point3) = {a,b} := by rw [he]; ext x; simp; tauto
    rw [hset]
    exact collinear_pair ℝ a b
  have hn : squared3 v ≠ 0 := (squared3_pos hv).ne'
  have hd : gramDen u v ≠ 0 := by
    intro hzero
    let t := dot3 u v / squared3 v
    have ht : t * squared3 v = dot3 u v := div_mul_cancel₀ _ hn
    have hv' : squared3 (u-smul3 t v) * squared3 v = gramDen u v := by
      simp only [gramDen,smul3,smul2,atHeight,squared3,dot3,squared2,dot,horizontal,
        Prod.fst_sub,Prod.snd_sub] at ht ⊢
      linear_combination (t*(v.1^2+v.2.1^2+v.2.2^2)-(u.1*v.1+u.2.1*v.2.1+u.2.2*v.2.2))*ht
    rw [hzero] at hv'
    have hu : u = smul3 t v := sub_eq_zero.mp ((squared3_eq_zero_iff _).mp
      ((mul_eq_zero.mp hv').resolve_right hn))
    apply h
    refine (collinear_iff_exists_forall_eq_smul_vadd _).mpr ⟨a,v,?_⟩
    intro p hp
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
    rcases hp with ha | hb | hc
    · subst p
      exact ⟨0,by simp⟩
    · subst p
      refine ⟨t,?_⟩
      change b = t • v+a
      have he : t • v = smul3 t v := rfl
      rw [he,← hu]
      simp [u]
    · subst p
      exact ⟨1,by simp [v]⟩
  exact lt_of_le_of_ne (by rw [gramDen_eq_cross_sq]; exact squared3_nonneg _) hd.symm

/-- The in-plane displacement determined by its dot products with two
independent side vectors of the plane. -/
def sphereProjection (u v : Point3) (s t : ℝ) : Point3 :=
  smul3 ((s*squared3 v-t*dot3 u v)/gramDen u v) u+
    smul3 ((t*squared3 u-s*dot3 u v)/gramDen u v) v

private theorem sphereProjection_spec (u v : Point3) (s t : ℝ) (h : gramDen u v ≠ 0) :
    dot3 (sphereProjection u v s t) u = s ∧ dot3 (sphereProjection u v s t) v = t := by
  constructor <;>
    simp only [sphereProjection,smul3,smul2,atHeight,dot3,squared3,squared2,dot,horizontal,
      Prod.fst_add,Prod.snd_add] <;>
    field_simp [h] <;> simp only [gramDen,dot3,squared3,squared2,dot,horizontal] <;> ring

private theorem cross3_dot_left (u v : Point3) : dot3 (cross3 u v) u = 0 := by
  simp only [cross3,dot3,dot,horizontal]
  ring

private theorem cross3_dot_right (u v : Point3) : dot3 (cross3 u v) v = 0 := by
  simp only [cross3,dot3,dot,horizontal]
  ring

private theorem orthogonal_component_eq (u v r : Point3)
    (hd : gramDen u v ≠ 0) (hu : dot3 r u = 0) (hv : dot3 r v = 0) :
    r = smul3 (dot3 r (cross3 u v)/gramDen u v) (cross3 u v) := by
  let n := cross3 u v
  have he : smul3 (gramDen u v) r =
      smul3 (dot3 r n) n +
      smul3 (squared3 v*dot3 r u-dot3 u v*dot3 r v) u +
      smul3 (squared3 u*dot3 r v-dot3 u v*dot3 r u) v := by
    ext <;> simp only [n,cross3,smul3,smul2,atHeight,gramDen,dot3,dot,squared3,squared2,horizontal,
      Prod.fst_add,Prod.snd_add] <;> ring
  simp [hu,hv,smul3,smul2,atHeight] at he
  obtain ⟨hx,hy,hz⟩ := he
  exact Prod.ext (by
    change r.1 = (dot3 r n/gramDen u v)*n.1
    field_simp [hd]
    simpa only [horizontal,mul_comm] using hx) (Prod.ext (by
    change r.2.1 = (dot3 r n/gramDen u v)*n.2.1
    field_simp [hd]
    simpa only [horizontal,mul_comm] using hy) (by
    change r.2.2 = (dot3 r n/gramDen u v)*n.2.2
    field_simp [hd]
    simpa only [mul_comm] using hz))

/-- The intersection candidates using squared distances to the three centers.
The sign chooses the side of the oriented plane through those centers. -/
def threeSpherePoint (a b c : Point3) (da db dc : ℝ) (positive : Bool) : Point3 :=
  let u := b-a
  let v := c-a
  let n := cross3 u v
  let p := sphereProjection u v ((da+squared3 u-db)/2) ((da+squared3 v-dc)/2)
  a+p+smul3 (signedRoot positive ((da-squared3 p)/gramDen u v)) n

def threeSphereCandidates (a b c : Point3) (da db dc : ℝ) : List Point3 :=
  [threeSpherePoint a b c da db dc false,threeSpherePoint a b c da db dc true]

/-- A point with the three given squared distances occurs on the two-element list. -/
theorem threeSphereCandidates_complete (a b c x : Point3) (da db dc : ℝ)
    (habc : ¬ Collinear ℝ ({a,b,c} : Set Point3))
    (ha : squared3 (x-a) = da) (hb : squared3 (x-b) = db)
    (hc : squared3 (x-c) = dc) :
    x ∈ threeSphereCandidates a b c da db dc := by
  let u := b-a
  let v := c-a
  let D := gramDen u v
  let n := cross3 u v
  let s := (da+squared3 u-db)/2
  let t := (da+squared3 v-dc)/2
  let p := sphereProjection u v s t
  let r := x-a-p
  have hd : D ≠ 0 := (gramDen_pos_of_noncollinear habc).ne'
  have hxu : dot3 (x-a) u = s := by
    simp only [s,u,squared3,squared2,dot,dot3,horizontal,Prod.fst_sub,Prod.snd_sub] at ha hb ⊢
    linear_combination (ha-hb)/2
  have hxv : dot3 (x-a) v = t := by
    simp only [t,v,squared3,squared2,dot,dot3,horizontal,Prod.fst_sub,Prod.snd_sub] at ha hc ⊢
    linear_combination (ha-hc)/2
  obtain ⟨hpu,hpv⟩ := sphereProjection_spec u v s t hd
  have hru : dot3 r u = 0 := by
    simp only [r,dot3,dot,horizontal,Prod.fst_sub,Prod.snd_sub] at hxu hpu ⊢
    linear_combination hxu-hpu
  have hrv : dot3 r v = 0 := by
    simp only [r,dot3,dot,horizontal,Prod.fst_sub,Prod.snd_sub] at hxv hpv ⊢
    linear_combination hxv-hpv
  let k := dot3 r n / D
  have hr := orthogonal_component_eq u v r hd hru hrv
  have hx : x-a = p+smul3 k n := by
    change x-a-p = smul3 k n at hr
    linear_combination hr
  have hpn : dot3 p n = 0 := by
    have h₁ := cross3_dot_left u v
    have h₂ := cross3_dot_right u v
    change dot3 n u = 0 at h₁
    change dot3 n v = 0 at h₂
    let α := (s*squared3 v-t*dot3 u v)/D
    let β := (t*squared3 u-s*dot3 u v)/D
    change dot3 (smul3 α u+smul3 β v) n = 0
    simp only [dot3,dot,horizontal,smul3,smul2,atHeight,
      Prod.fst_add,Prod.snd_add] at h₁ h₂ ⊢
    linear_combination α*h₁+β*h₂
  have hsq : squared3 (p+smul3 k n) = squared3 p+k^2*squared3 n := by
    simp only [smul3,smul2,squared3,squared2,dot3,dot,horizontal,atHeight,
      Prod.fst_add,Prod.snd_add] at hpn ⊢
    linear_combination (2*k)*hpn
  have hk : (da-squared3 p)/D = k^2 := by
    apply (div_eq_iff hd).mpr
    have hh := ha
    rw [hx,hsq,← gramDen_eq_cross_sq u v] at hh
    linear_combination -hh
  have hsqrt : Real.sqrt ((da-squared3 p)/D) = |k| := by rw [hk,Real.sqrt_sq_eq_abs]
  have hpoint : x = a+p+smul3 k n := by
    calc x = a+(x-a) := by abel
      _ = _ := by rw [hx,add_assoc]
  by_cases hpos : 0 ≤ k
  · have he : threeSpherePoint a b c da db dc true = x := by
      change a+p+smul3 (signedRoot true ((da-squared3 p)/D)) n = x
      simpa only [signedRoot,ite_true,hsqrt,abs_of_nonneg hpos] using hpoint.symm
    exact List.mem_cons_of_mem _ (List.mem_singleton.mpr he.symm)
  · have he : threeSpherePoint a b c da db dc false = x := by
      change a+p+smul3 (signedRoot false ((da-squared3 p)/D)) n = x
      simpa [signedRoot,hsqrt,abs_of_neg (lt_of_not_ge hpos)] using hpoint.symm
    exact List.mem_cons.mpr (Or.inl he.symm)

end OrigamiTorus
