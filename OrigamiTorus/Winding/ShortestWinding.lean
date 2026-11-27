module

public import OrigamiTorus.Type5.Geometry
public import OrigamiTorus.Lattice.LatticeTorus
public import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Tactic

/-! Necessary bounds on the periods of three-edge cycles in a reduced lattice. -/

@[expose] public section

namespace OrigamiTorus.Winding

open Type5 (squared2)
open AffineMap
open scoped Pointwise

/-- A bound on distances within each of finitely many closed pieces of a line
segment implies the same bound between the endpoints. -/
theorem dist_le_of_finite_closed_cover {ι F : Type*} [Finite ι] [MetricSpace F]
    (g : ℝ → F) (hg : Continuous g) (K : ℝ) (T : ι → Set ℝ) (hT : ∀ i, IsClosed (T i))
    (hcover : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ i, t ∈ T i)
    (hlocal : ∀ i, ∀ r ∈ T i, ∀ s ∈ T i, dist (g r) (g s) ≤ |s-r| * K) :
    dist (g 0) (g 1) ≤ K := by
  let C := Set.Icc (0 : ℝ) 1 ∩ {t : ℝ | dist (g 0) (g t) ≤ t*K}
  have hC : IsClosed C := isClosed_Icc.inter
    (isClosed_le (continuous_const.dist hg) (continuous_id.mul continuous_const))
  have h0 : 0 ∈ C := by simp [C]
  have hbd : BddAbove C := ⟨1,fun _ h => h.1.2⟩
  let r := sSup C
  have hr : r ∈ C := hC.csSup_mem ⟨0,h0⟩ hbd
  by_contra! hno
  have hr1 : r < 1 := by
    refine lt_of_le_of_ne hr.1.2 ?_
    intro he
    have hm : (1 : ℝ) ∈ C := he ▸ hr
    exact hno.not_ge (by simpa using hm.2)
  let U := ⋃ i : {i // r ∉ T i}, T i.val
  have hcU : IsClosed U := isClosed_iUnion_of_finite fun i => hT i.val
  have hrU : r ∈ Uᶜ := by
    intro hu
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu
    exact i.property hi
  obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp hcU.isOpen_compl r hrU
  let s := r + min (δ/2) ((1-r)/2)
  have hs : 0 < s-r := by
    have h := lt_min (show 0 < δ/2 by linarith) (show 0 < (1-r)/2 by linarith)
    dsimp [s]
    linarith
  have hsl : s ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by linarith [hr.1.1],?_⟩
    dsimp [s]
    linarith [min_le_right (δ/2) ((1-r)/2)]
  have hsU : s ∉ U := hsub (by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_pos hs]
    dsimp [s]
    linarith [min_le_left (δ/2) ((1-r)/2)])
  obtain ⟨i,hi⟩ := hcover s hsl
  have hri : r ∈ T i := by
    by_contra hn
    exact hsU (Set.mem_iUnion.mpr ⟨⟨i,hn⟩,hi⟩)
  have hstep := hlocal i r hri s hi
  rw [abs_of_pos hs] at hstep
  have hsC : s ∈ C := ⟨hsl,by
    change dist (g 0) (g s) ≤ s*K
    have hprefix : dist (g 0) (g r) ≤ r*K := hr.2
    linarith only [dist_triangle (g 0) (g r) (g s),hprefix,hstep]⟩
  exact (not_lt_of_ge (le_csSup hbd hsC)) (by linarith only [hs])

/-- A continuous periodic map that is short on each of finitely many compact
pieces covering the quotient is short on the entire cover. -/
theorem short_of_periodic_compact_cover {ι E F : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [MetricSpace F]
    (L : AddSubgroup E) [DiscreteTopology L]
    (g : E → F) (hg : Continuous g)
    (hperiod : ∀ p z : E, z ∈ L → g (p+z) = g p)
    (S : ι → Set E) (hS : ∀ i, IsCompact (S i))
    (hcover : ∀ p : E, ∃ i z, z ∈ L ∧ p-z ∈ S i)
    (hlocal : ∀ i, ∀ a ∈ S i, ∀ b ∈ S i, dist (g a) (g b) ≤ dist a b)
    (a b : E) : dist (g a) (g b) ≤ dist a b := by
  let path : ℝ → E := lineMap a b
  have hpath : Continuous path := (lipschitzWith_lineMap a b).continuous
  let K := path '' Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image hpath
  have hsub (i : ι) : IsCompact (K - S i) := by
    have he : K - S i = (fun u : E × E => u.1-u.2) '' (K ×ˢ S i) := by
      ext w
      constructor
      · rintro ⟨p,hp,q,hq,rfl⟩
        exact ⟨(p,q),⟨hp,hq⟩,rfl⟩
      · rintro ⟨⟨p,q⟩,⟨hp,hq⟩,rfl⟩
        exact ⟨p,hp,q,hq,rfl⟩
    rw [he]
    exact (hK.prod (hS i)).image (continuous_fst.sub continuous_snd)
  let D := (⋃ i, K - S i) ∩ (L : Set E)
  have hf : D.Finite := Metric.finite_isBounded_inter_isClosed
    DiscreteTopology.isDiscrete (isCompact_iUnion hsub).isBounded
    L.isClosed_of_discreteTopology
  let : Finite D := hf.to_subtype
  let T (iz : ι × D) : Set ℝ := {t | path t-iz.2.val ∈ S iz.1}
  have hT (iz : ι × D) : IsClosed (T iz) := (hS iz.1).isClosed.preimage
    (hpath.sub continuous_const)
  have hTC (t : ℝ) (ht : t ∈ Set.Icc 0 1) : ∃ iz, t ∈ T iz := by
    obtain ⟨i,z,hz,htz⟩ := hcover (path t)
    have hzi : z ∈ K - S i := Set.mem_sub.mpr ⟨path t,⟨t,ht,rfl⟩,path t-z,htz,by abel⟩
    exact ⟨(i,⟨z,Set.mem_iUnion.mpr ⟨i,hzi⟩,hz⟩),htz⟩
  have hloc (iz : ι × D) (r : ℝ) (hr : r ∈ T iz) (s : ℝ) (hs : s ∈ T iz) :
      dist (g (path r)) (g (path s)) ≤ |s-r| * dist a b := by
    let z := iz.2.val
    have hz : z ∈ L := iz.2.property.2
    have hp (p : E) : g p = g (p-z) := by simpa using hperiod (p-z) z hz
    rw [hp (path r),hp (path s)]
    refine (hlocal iz.1 _ hr _ hs).trans_eq ?_
    rw [dist_sub_right,show path = lineMap a b from rfl,dist_lineMap_lineMap,dist_comm r s,Real.dist_eq]
  have hd := dist_le_of_finite_closed_cover (g ∘ path) (hg.comp hpath) (dist a b) T hT hTC hloc
  simpa [path] using hd

/-- A straight, length-preserving edge in a short periodic map with exactly
the lattice fibers has no second shortest lift. -/
theorem strict_period_comparison {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [StrictConvexSpace ℝ F]
    (L : AddSubgroup E) (hdiscrete : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ L, ‖z‖ < ε → z = 0)
    (g : E → F) (hshort : ∀ a b, dist (g a) (g b) ≤ dist a b)
    (hfib : ∀ a b, g a = g b ↔ b-a ∈ L) {a b : E}
    (hmetric : dist (g a) (g b) = dist a b)
    (hedge : ∀ t ∈ Set.Icc (0 : ℝ) 1, g (lineMap a b t) = lineMap (g a) (g b) t)
    {z : E} (hz : z ∈ L) (hn : z ≠ 0) : dist a b < dist a (b+z) := by
  have hperiod : g (b+z) = g b := by
    apply ((hfib b (b+z)).mpr ?_).symm
    simpa using hz
  have hle := hshort a (b+z)
  rw [hperiod,hmetric] at hle
  by_contra! hge
  have hlen := le_antisymm hge hle
  obtain ⟨ε,hε,hd⟩ := hdiscrete
  let t := min (1/2) (ε/(2*‖z‖))
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hn
  have htp : 0 < t := lt_min (by norm_num) (div_pos hε (by positivity))
  have htu : t ≤ 1 := (min_le_left _ _).trans (by norm_num)
  let p := lineMap a (b+z) t
  have hfirst : dist (g a) (g p) ≤ t*dist a b := by
    refine (hshort a p).trans_eq ?_
    simp only [p,dist_left_lineMap,Real.norm_eq_abs,abs_of_pos htp,hlen]
  have hsecond : dist (g p) (g b) ≤ (1-t)*dist a b := by
    rw [← hperiod]
    refine (hshort p (b+z)).trans_eq ?_
    simp only [p,dist_lineMap_right,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr htu),hlen]
  have htri := dist_triangle (g a) (g p) (g b)
  rw [hmetric] at htri
  have hgp : g p = lineMap (g a) (g b) t := by
    apply eq_lineMap_of_dist_eq_mul_of_dist_eq_mul <;> rw [hmetric] <;>
      linarith only [hfirst,hsecond,htri]
  have heq : g (lineMap a b t) = g p := (hedge t ⟨htp.le,htu⟩).trans hgp.symm
  have hp : p-lineMap a b t = t • z := by
    simp only [p,lineMap_apply_module']
    module
  have hmem := (hfib (lineMap a b t) p).mp heq
  rw [hp] at hmem
  have hsmall : ‖t • z‖ < ε := by
    have ht : t ≤ ε/(2*‖z‖) := min_le_right _ _
    have hp := (le_div_iff₀ (show 0 < 2*‖z‖ by positivity)).mp ht
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos htp]
    linarith only [hp,hε]
  exact (smul_ne_zero htp.ne' hn) (hd _ hmem hsmall)

/-- The strict comparison applies to an affine length-preserving edge of a
periodic map whose compact pieces carry the intrinsic Euclidean metric. -/
theorem strict_period_comparison_of_compact_cover {ι E F : Type*} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [StrictConvexSpace ℝ F]
    (L : AddSubgroup E) [DiscreteTopology L] (g : E → F) (hg : Continuous g)
    (hfib : ∀ a b, g a = g b ↔ b-a ∈ L) (S : ι → Set E) (hS : ∀ i, IsCompact (S i))
    (hcover : ∀ p : E, ∃ i z, z ∈ L ∧ p-z ∈ S i)
    (hlocal : ∀ i, ∀ a ∈ S i, ∀ b ∈ S i, dist (g a) (g b) ≤ dist a b)
    {a b : E} (hmetric : dist (g a) (g b) = dist a b)
    (hedge : ∀ t ∈ Set.Icc (0 : ℝ) 1, g (lineMap a b t) = lineMap (g a) (g b) t)
    {z : E} (hz : z ∈ L) (hn : z ≠ 0) : dist a b < dist a (b+z) := by
  have hdiscrete : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ L, ‖z‖ < ε → z = 0 := by
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (isOpen_discrete ({0} : Set L)) 0 (by simp)
    refine ⟨ε,hε,fun z hz hnz => ?_⟩
    have he : (⟨z,hz⟩ : L) = 0 := hball (by simpa [Metric.mem_ball] using hnz)
    exact congrArg Subtype.val he
  have hperiod (p z : E) (hz : z ∈ L) : g (p+z) = g p := by
    exact ((hfib p (p+z)).mpr (by simpa using hz)).symm
  exact strict_period_comparison L hdiscrete g
    (short_of_periodic_compact_cover L g hg hperiod S hS hcover hlocal) hfib hmetric hedge hz hn

/-- The squared Euclidean norm strictly increases on adding any nonzero period.
The edge has physical displacement `(X, y*V)`. -/
def StrictShortest (x y X V : ℝ) : Prop :=
  ∀ m n : ℤ, (m,n) ≠ (0,0) →
    squared2 (X,y*V) < squared2 (X+(m : ℝ)+(n : ℝ)*x,y*(V+n))

private theorem reduced_lattice_discrete (x y : ℝ) (hy : 0 < y) :
    DiscreteTopology (complexPeriodSubgroup 1 (x+y*Complex.I)) := by
  let L := complexPeriodSubgroup 1 (x+y*Complex.I)
  change DiscreteTopology L
  rw [discreteTopology_iff_isOpen_singleton_zero,Metric.isOpen_iff]
  intro z hz
  have hz₀ : z = 0 := hz
  subst z
  refine ⟨min 1 y,lt_min one_pos hy,?_⟩
  intro u hu
  have hn : ‖u.val‖ < min 1 y := by simpa [Metric.mem_ball] using hu
  obtain ⟨m,n,he⟩ : ∃ m n : ℤ, (m : ℂ)*1+(n : ℂ)*(x+y*Complex.I) = u.val := u.property
  have hni : |(n : ℝ)*y| < y := by
    have hm := (Complex.abs_im_le_norm u.val).trans_lt (hn.trans_le (min_le_right _ _))
    rw [← he] at hm
    simpa [Complex.mul_im] using hm
  rw [abs_mul,abs_of_pos hy] at hni
  have hnr : |(n : ℝ)| < 1 := lt_of_mul_lt_mul_right
    (by simpa only [one_mul] using hni : |(n : ℝ)| * y < 1*y) hy.le
  have hnn : |n| < 1 := by exact_mod_cast hnr
  have hn₀ : n = 0 := by have := abs_lt.mp hnn; omega
  have hmr : |(m : ℝ)| < 1 := by
    have hm := (Complex.abs_re_le_norm u.val).trans_lt (hn.trans_le (min_le_left _ _))
    rw [← he,hn₀] at hm
    simpa using hm
  have hmm : |m| < 1 := by exact_mod_cast hmr
  have hm₀ : m = 0 := by have := abs_lt.mp hmm; omega
  exact Subtype.ext (by rw [← he,hn₀,hm₀]; simp)

/-- Given compact lifted faces covering the quotient, each affine metric edge
of an embedded lattice torus is strictly shorter than every alternative lift. -/
theorem strictShortest_of_lattice_face_cover {ι F : Type*} [Finite ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [StrictConvexSpace ℝ F]
    {x y : ℝ} (hy : 0 < y) (g : ComplexTorus 1 (x+y*Complex.I) → F)
    (hg : Continuous g) (hi : Function.Injective g) (S : ι → Set ℂ) (hS : ∀ i, IsCompact (S i))
    (hcover : ∀ p : ComplexTorus 1 (x+y*Complex.I), ∃ i z, z ∈ S i ∧
      complexTorusProjection 1 (x+y*Complex.I) z = p)
    (hlocal : ∀ i, ∀ a ∈ S i, ∀ b ∈ S i,
      dist (g (complexTorusProjection 1 (x+y*Complex.I) a))
        (g (complexTorusProjection 1 (x+y*Complex.I) b)) ≤ dist a b)
    {a b : ℂ}
    (hmetric : dist (g (complexTorusProjection 1 (x+y*Complex.I) a))
      (g (complexTorusProjection 1 (x+y*Complex.I) b)) = dist a b)
    (hedge : ∀ t ∈ Set.Icc (0 : ℝ) 1, g (complexTorusProjection 1 (x+y*Complex.I) (lineMap a b t)) =
      lineMap (g (complexTorusProjection 1 (x+y*Complex.I) a))
        (g (complexTorusProjection 1 (x+y*Complex.I) b)) t) :
    StrictShortest x y (b-a).re ((b-a).im/y) := by
  let L := complexPeriodSubgroup 1 (x+y*Complex.I)
  let : DiscreteTopology L := reduced_lattice_discrete x y hy
  let π := complexTorusProjection 1 (x+y*Complex.I)
  have hπ : Continuous π := QuotientAddGroup.continuous_mk
  have hq (p q : ℂ) : π p = π q ↔ q-p ∈ L := by
    change (p : ℂ ⧸ L) = q ↔ q-p ∈ L
    rw [eq_comm,QuotientAddGroup.eq_iff_sub_mem]
  have hfib (p q : ℂ) : (g ∘ π) p = (g ∘ π) q ↔ q-p ∈ L := by
    exact hi.eq_iff.trans (hq p q)
  have htranslate (p : ℂ) : ∃ i z, z ∈ L ∧ p-z ∈ S i := by
    obtain ⟨i,q,hiq,he⟩ := hcover (π p)
    exact ⟨i,p-q,(hq q p).mp he,by simpa using hiq⟩
  intro m n hne
  let z : ℂ := (m : ℂ)*1+(n : ℂ)*(x+y*Complex.I)
  have hz : z ∈ L := ⟨m,n,rfl⟩
  have hre : z.re = m+(n : ℝ)*x := by simp [z,Complex.mul_re]
  have him : z.im = (n : ℝ)*y := by simp [z,Complex.mul_im]
  have hnz : z ≠ 0 := by
    intro he
    have hn₀ : n = 0 := by
      have h := (by simpa [he] using him : 0 = (n : ℝ)*y)
      have hn := (mul_eq_zero.mp h.symm).resolve_right hy.ne'
      exact_mod_cast hn
    have hm₀ : m = 0 := by
      have h := (by simpa [he,hn₀] using hre : (0 : ℝ) = m)
      exact_mod_cast h.symm
    exact hne (by simp [hm₀,hn₀])
  have hlt := strict_period_comparison_of_compact_cover L (g ∘ π) (hg.comp hπ) hfib S hS htranslate
    hlocal hmetric hedge hz hnz
  rw [dist_eq_norm',dist_eq_norm'] at hlt
  have hsquare (u : ℂ) : squared2 (u.re,u.im) = ‖u‖^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    rfl
  have hlt' := pow_lt_pow_left₀ hlt (norm_nonneg _) (by decide : 2 ≠ 0)
  rw [← hsquare,← hsquare] at hlt'
  have heim : y*((b-a).im/y) = (b-a).im := by field_simp
  have heR : (b+z-a).re = (b-a).re+m+(n : ℝ)*x := by
    simp only [show b+z-a = b-a+z by abel,Complex.add_re,hre]
    ring
  have heI : (b+z-a).im = y*((b-a).im/y+n) := by
    simp only [show b+z-a = b-a+z by abel,Complex.add_im,him,mul_add,heim]
    ring
  rw [heim]
  rwa [← heR,← heI]

private theorem nearest_comparison {x y X V : ℝ} (h : StrictShortest x y X V)
    (m n : ℤ) (hn : (m,n) ≠ (0,0)) :
    |((m : ℝ)+(n : ℝ)*x)*X+(n : ℝ)*y^2*V| <
      (((m : ℝ)+(n : ℝ)*x)^2+(n : ℝ)^2*y^2)/2 := by
  have hp := h m n hn
  have hm := h (-m) (-n) (by simpa [Prod.mk.injEq] using hn)
  simp only [squared2,Type5.dot,Int.cast_neg] at hp hm
  rw [abs_lt]
  constructor <;> nlinarith only [hp,hm]

/-- The first and second normalized coordinate bounds use only three lattice
comparisons and the reduced-basis inequalities. -/
theorem edge_bounds {x y X V : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hr : 1 ≤ x^2+y^2) (h : StrictShortest x y X V) : |X| < 1/2 ∧ |V| < 2/3 := by
  have h1 := nearest_comparison h 1 0 (by decide)
  have h2 := nearest_comparison h 0 1 (by decide)
  have h3 := nearest_comparison h (-1) 1 (by decide)
  norm_num at h1 h2 h3
  refine ⟨h1,?_⟩
  have h₁x : 0 < 1-x := by linarith
  have hw : 0 < y^2 := by nlinarith [mul_nonneg hx (sub_nonneg.mpr hx')]
  have hxw : 3*(x*(1-x)) ≤ y^2 := by nlinarith [mul_nonneg h₁x.le (show 0 ≤ 1-2*x by linarith)]
  have hcomb : |y^2*V| < (y^2+x*(1-x))/2 := by
    rw [abs_lt] at h2 h3 ⊢
    constructor
    · nlinarith only [mul_lt_mul_of_pos_left h2.1 h₁x, mul_le_mul_of_nonneg_left h3.1.le hx]
    · nlinarith only [mul_lt_mul_of_pos_left h2.2 h₁x, mul_le_mul_of_nonneg_left h3.2.le hx]
  rw [abs_mul,abs_of_pos hw] at hcomb
  exact lt_of_mul_lt_mul_left (hcomb.trans_le (by linarith)) hw.le

/-- The eight possible nonzero winding vectors, with two removed on the sharp
boundary `x = 1/2`. -/
def allowed (sharp : Bool) : Finset (ℤ × ℤ) :=
  let common : Finset (ℤ × ℤ) := {(1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1)}
  if sharp then common else insert (1,1) (insert (-1,-1) common)

theorem allowed_card (sharp : Bool) : (allowed sharp).card = if sharp then 6 else 8 := by
  cases sharp <;> decide +kernel

/-- The arithmetic period bound for a noncontractible three-edge cycle. -/
theorem triangle_mem_allowed {x y : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hr : 1 ≤ x^2+y^2) {X₁ X₂ X₃ V₁ V₂ V₃ : ℝ}
    (h₁ : StrictShortest x y X₁ V₁) (h₂ : StrictShortest x y X₂ V₂)
    (h₃ : StrictShortest x y X₃ V₃) {m n : ℤ} (hne : (m,n) ≠ (0,0))
    (hX : X₁+X₂+X₃ = (m : ℝ)+(n : ℝ)*x) (hV : V₁+V₂+V₃ = n) :
    (m,n) ∈ allowed (decide (x = 1/2)) := by
  obtain ⟨a₁,b₁⟩ := edge_bounds hx hx' hr h₁
  obtain ⟨a₂,b₂⟩ := edge_bounds hx hx' hr h₂
  obtain ⟨a₃,b₃⟩ := edge_bounds hx hx' hr h₃
  have ha : |(m : ℝ)+(n : ℝ)*x| < 3/2 := by
    rw [← hX]
    exact (abs_add_le _ _).trans_lt (by linarith [abs_add_le X₁ X₂])
  have hnR : |(n : ℝ)| < 2 := by
    rw [← hV]
    exact (abs_add_le _ _).trans_lt (by linarith [abs_add_le V₁ V₂])
  have hn : |n| < 2 := by exact_mod_cast hnR
  have hn₁ : |n| ≤ 1 := by omega
  have hnR₁ : |(n : ℝ)| ≤ 1 := by exact_mod_cast hn₁
  have hnx : |(n : ℝ)*x| ≤ 1/2 := by
    rw [abs_mul,abs_of_nonneg hx]
    exact (mul_le_mul_of_nonneg_right hnR₁ hx).trans (by simpa using hx')
  have hmR : |(m : ℝ)| < 2 := by
    have he : (m : ℝ) = (m+(n : ℝ)*x) - (n : ℝ)*x := by ring
    conv_lhs => rw [he]
    exact (abs_sub _ _).trans_lt (by linarith)
  have hm : |m| < 2 := by exact_mod_cast hmR
  have ⟨hml,hmu⟩ := abs_lt.mp hm
  have ⟨hnl,hnu⟩ := abs_lt.mp hn
  by_cases hs : x = 1/2
  · subst x
    interval_cases m <;> interval_cases n <;> norm_num at hne <;> norm_num [allowed]
    all_goals norm_num at ha
  · simp only [hs,decide_false]
    interval_cases m <;> interval_cases n <;> norm_num at hne <;> norm_num [allowed]

end OrigamiTorus.Winding
