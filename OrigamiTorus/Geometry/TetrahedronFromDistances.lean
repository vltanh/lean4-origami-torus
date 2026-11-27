module

public import OrigamiTorus.Geometry.ThreeSpheres
public import OrigamiTorus.Type5.Normalize
import Mathlib.Tactic

/-! The canonical radical coordinates for a tetrahedron with six given lengths. -/

@[expose] public section

noncomputable section

namespace OrigamiTorus

open Type5 (Plane dot dot3 cross squared2 squared3 horizontal atHeight smul3 smul2 signedRoot)

def anchorSecond (d : Fin 4 → Fin 4 → ℝ) : Plane ℝ := (Real.sqrt (d 0 1),0)

def anchorThird (d : Fin 4 → Fin 4 → ℝ) : Plane ℝ :=
  let x := (d 0 1+d 0 2-d 1 2)/(2*Real.sqrt (d 0 1))
  (x,Real.sqrt (d 0 2-x^2))

/-- Canonical positions for the tetrahedron, with its first three vertices in
the horizontal plane and the chosen fourth vertex on its positive side. -/
def tetrahedronFromDistances (d : Fin 4 → Fin 4 → ℝ) : Fin 4 → Point3 :=
  let a := atHeight (anchorSecond d) 0
  let b := atHeight (anchorThird d) 0
  ![0,a,b,threeSpherePoint 0 a b (d 0 3) (d 1 3) (d 2 3) true]

private def reflectThird : Point3 →ₗ[ℝ] Point3 :=
  { toFun := fun x => (x.1,x.2.1,-x.2.2)
    map_add' := by intros; ext <;> simp [add_comm]
    map_smul' := by intros; ext <;> simp }

private theorem reflectThird_injective : Function.Injective reflectThird := by
  intro a b he
  change (a.1,a.2.1,-a.2.2) = (b.1,b.2.1,-b.2.2) at he
  have hx := congrArg (fun x : Point3 => x.1) he
  have hy := congrArg (fun x : Point3 => x.2.1) he
  have hz := congrArg (fun x : Point3 => x.2.2) he
  exact Prod.ext hx (Prod.ext hy (neg_injective hz))

private theorem reflectThird_squared (x : Point3) : squared3 (reflectThird x) = squared3 x := by
  simp [reflectThird,squared3,squared2,dot,horizontal]

private theorem reflectThird_spherePoint (a b c : Point3)
    (ha : a.2.2 = 0) (hb : b.2.2 = 0) (hc : c.2.2 = 0) (da db dc : ℝ) :
    reflectThird (threeSpherePoint a b c da db dc false) = threeSpherePoint a b c da db dc true := by
  let u := b-a
  let v := c-a
  let p := sphereProjection u v ((da+squared3 u-db)/2) ((da+squared3 v-dc)/2)
  let n := cross3 u v
  let k := Real.sqrt ((da-squared3 p)/gramDen u v)
  have hn₁ : n.1 = 0 := by simp [n,cross3,u,v,ha,hb,hc]
  have hn₂ : n.2.1 = 0 := by simp [n,cross3,u,v,ha,hb,hc]
  have hp : p.2.2 = 0 := by simp [p,sphereProjection,smul3,atHeight,u,v,ha,hb,hc]
  change reflectThird (a+p+smul3 (signedRoot false ((da-squared3 p)/gramDen u v)) n) =
    a+p+smul3 (signedRoot true ((da-squared3 p)/gramDen u v)) n
  have hleft : signedRoot false ((da-squared3 p)/gramDen u v) = -k := by simp [signedRoot,k]
  have hright : signedRoot true ((da-squared3 p)/gramDen u v) = k := by simp [signedRoot,k]
  rw [hleft,hright]
  ext <;> simp [reflectThird,ha,hp,smul3,smul2,atHeight,horizontal,hn₁,hn₂]

private theorem anchorTriangle_lengths (f : Fin 4 → Point3) (d : Fin 4 → Fin 4 → ℝ)
    (h : AffineIndependent ℝ f) (hd : ∀ i j, squared3 (f j-f i) = d i j) :
    cross (anchorSecond d) (anchorThird d) ≠ 0 ∧
      squared2 (anchorSecond d) = d 0 1 ∧ squared2 (anchorThird d) = d 0 2 ∧
      squared2 (anchorThird d-anchorSecond d) = d 1 2 := by
  let u := f 1-f 0
  let v := f 2-f 0
  let l := Real.sqrt (d 0 1)
  let x := (d 0 1+d 0 2-d 1 2)/(2*l)
  let z := d 0 2-x^2
  let y := Real.sqrt z
  have hsub : AffineIndependent ℝ (![f 0,f 1,f 2] : Fin 3 → Point3) := by
    have hh := h.comp_embedding (Fin.castAddEmb 1)
    convert hh using 1
    funext i
    fin_cases i <;> rfl
  have hnc : ¬ Collinear ℝ ({f 0,f 1,f 2} : Set Point3) := affineIndependent_iff_not_collinear_set.mp hsub
  have hpos : 0 < gramDen u v := gramDen_pos_of_noncollinear hnc
  have h₁ : squared3 u = d 0 1 := hd 0 1
  have h₂ : squared3 v = d 0 2 := hd 0 2
  have h₁₂ : squared3 (v-u) = d 1 2 := by
    rw [show v-u = f 2-f 1 by dsimp [u,v]; abel]
    exact hd 1 2
  have h1p : 0 < d 0 1 := h₁ ▸ squared3_pos (sub_ne_zero.mpr (h.injective.ne (by decide)))
  have hlp : 0 < l := Real.sqrt_pos.mpr h1p
  have hl : l^2 = d 0 1 := Real.sq_sqrt h1p.le
  have hinner : dot3 u v = (d 0 1+d 0 2-d 1 2)/2 := by
    simp only [squared3,squared2,dot3,dot,horizontal,Prod.fst_sub,Prod.snd_sub] at h₁ h₂ h₁₂ ⊢
    linear_combination (h₁+h₂-h₁₂)/2
  have hmul : l*x = dot3 u v := by
    rw [hinner]
    dsimp only [x]
    field_simp [hlp.ne']
  have hDz : d 0 1*z = gramDen u v := by
    rw [gramDen,h₁,h₂,← hmul,← hl]
    dsimp only [z]
    ring
  have hDzpos : 0 < d 0 1*z := by rwa [hDz]
  have hz : 0 < z := pos_of_mul_pos_right hDzpos h1p.le
  have hyy : y^2 = z := Real.sq_sqrt hz.le
  have hyp : 0 < y := Real.sqrt_pos.mpr hz
  refine ⟨?_,?_,?_,?_⟩
  · change l*y - 0*x ≠ 0
    simpa only [zero_mul,sub_zero] using (mul_pos hlp hyp).ne'
  · change l*l+0*0 = d 0 1
    simpa [pow_two] using hl
  · change x*x+y*y = d 0 2
    change y^2 = d 0 2-x^2 at hyy
    nlinarith only [hyy]
  · change (x-l)*(x-l)+(y-0)*(y-0) = d 1 2
    change y^2 = d 0 2-x^2 at hyy
    nlinarith only [hl,hyy,hmul,hinner]

/-- Any tetrahedron realizing the six given distances is congruent to the
canonical radical coordinates. Reflection is allowed. -/
theorem tetrahedronFromDistances_congruent (f : Fin 4 → Point3) (d : Fin 4 → Fin 4 → ℝ)
    (h : AffineIndependent ℝ f) (hd : ∀ i j, squared3 (f j-f i) = d i j) :
    ∃ T : Point3 →ₗ[ℝ] Point3, Function.Injective T ∧ (∀ z, squared3 (T z) = squared3 z) ∧
      (∀ i, T (f i-f 0) = tetrahedronFromDistances d i) := by
  let a := anchorSecond d
  let b := anchorThird d
  obtain ⟨hab,ha,hb,hab'⟩ := anchorTriangle_lengths f d h hd
  have hv : squared3 ((f 2-f 0)-(f 1-f 0)) = squared2 (b-a) := by
    rw [show (f 2-f 0)-(f 1-f 0) = f 2-f 1 by abel,hd 1 2,hab']
  obtain ⟨T,hTi,hTq,hTa,hTb⟩ := Type5.rigid_map_of_triangle_lengths (f 1-f 0) (f 2-f 0) a b hab
    ((hd 0 1).trans ha.symm) ((hd 0 2).trans hb.symm) hv
  let r (i : Fin 4) := T (f i-f 0)
  have hr₀ : r 0 = 0 := by simp [r]
  have hr₁ : r 1 = atHeight a 0 := hTa
  have hr₂ : r 2 = atHeight b 0 := hTb
  have hnorm (i j : Fin 4) : squared3 (r j-r i) = d i j := by
    rw [show r j-r i = T (f j-f i) by simp only [r,← map_sub]; congr 1; abel,hTq]
    exact hd i j
  have hnc : ¬ Collinear ℝ ({(0 : Point3),atHeight a 0,atHeight b 0} : Set Point3) := by
    have hsub : AffineIndependent ℝ (![f 0,f 1,f 2] : Fin 3 → Point3) := by
      have hh := h.comp_embedding (Fin.castAddEmb 1)
      convert hh using 1
      funext i
      fin_cases i <;> rfl
    let A := T.toAffineMap.comp (AffineEquiv.constVAdd ℝ Point3 (-f 0)).toAffineMap
    have hAi : Function.Injective A :=
      hTi.comp (AffineEquiv.constVAdd ℝ Point3 (-f 0)).injective
    have hh := hsub.map' A hAi
    have hA (i : Fin 3) : A ((![f 0,f 1,f 2] : Fin 3 → Point3) i) =
        (![0,atHeight a 0,atHeight b 0] : Fin 3 → Point3) i := by
      have he (j : Fin 4) : A (f j) = r j := by
        change T (-f 0 + f j) = T (f j-f 0)
        congr 1
        abel
      fin_cases i
      · exact (he 0).trans hr₀
      · exact (he 1).trans hr₁
      · exact (he 2).trans hr₂
    rw [show A ∘ (![f 0,f 1,f 2] : Fin 3 → Point3) = ![0,atHeight a 0,atHeight b 0] from funext hA] at hh
    exact affineIndependent_iff_not_collinear_set.mp hh
  have hmem := threeSphereCandidates_complete 0 (atHeight a 0) (atHeight b 0) (r 3)
    (d 0 3) (d 1 3) (d 2 3) hnc
    (by rw [← hr₀]; exact hnorm 0 3) (by rw [← hr₁]; exact hnorm 1 3)
    (by rw [← hr₂]; exact hnorm 2 3)
  simp only [threeSphereCandidates,List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with hm | hm
  · let S := reflectThird.comp T
    refine ⟨S,reflectThird_injective.comp hTi,fun z => (reflectThird_squared (T z)).trans (hTq z),?_⟩
    intro j
    change reflectThird (r j) = tetrahedronFromDistances d j
    fin_cases j
    · simp [hr₀,reflectThird,tetrahedronFromDistances]
    · simp [hr₁,reflectThird,atHeight,tetrahedronFromDistances,a]
    · simp [hr₂,reflectThird,atHeight,tetrahedronFromDistances,b]
    · change reflectThird (r 3) = tetrahedronFromDistances d 3
      rw [hm,reflectThird_spherePoint _ _ _ rfl rfl rfl]
      rfl
  · refine ⟨T,hTi,hTq,fun j => ?_⟩
    change r j = tetrahedronFromDistances d j
    fin_cases j
    · exact hr₀
    · exact hr₁
    · exact hr₂
    · exact hm

end OrigamiTorus
