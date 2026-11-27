module

public import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! A dense rational coefficient calculation for sign inequalities on
(0 \le t < 1), (h \ge 0). The substitution (t=u/(1+u)) sends the
interval to the nonnegative ray and clears the denominator homogeneously. -/

@[expose] public section

namespace OrigamiTorus.StripPolynomial

def addSeries {A : Type*} (add : A → A → A) : List A → List A → List A
  | [], q => q
  | p, [] => p
  | a::as, b::bs => add a b :: addSeries add as bs

def mulSeries {A : Type*} (zero : A) (add mul : A → A → A) :
    List A → List A → List A
  | [], _ => []
  | a::as, q => addSeries add (q.map (mul a)) (zero :: mulSeries zero add mul as q)

noncomputable def evalSeries {A : Type*} (value : A → ℝ) (x : ℝ) : List A → ℝ
  | [] => 0
  | a::as => value a+x*evalSeries value x as

private theorem evalSeries_add {A : Type*} (add : A → A → A) (value : A → ℝ)
    (hadd : ∀ a b, value (add a b) = value a + value b) (x : ℝ) (p q : List A) :
    evalSeries value x (addSeries add p q) = evalSeries value x p + evalSeries value x q := by
  induction p generalizing q with
  | nil => simp [addSeries,evalSeries]
  | cons a p ih =>
    cases q with
    | nil => simp [addSeries,evalSeries]
    | cons b q =>
      simp only [addSeries,evalSeries,hadd,ih]
      ring

private theorem evalSeries_scale {A : Type*} (mul : A → A → A) (value : A → ℝ)
    (hmul : ∀ a b, value (mul a b) = value a * value b) (x : ℝ) (a : A) (p : List A) :
    evalSeries value x (p.map (mul a)) = value a * evalSeries value x p := by
  induction p with
  | nil => simp [evalSeries]
  | cons b p ih =>
    simp only [List.map_cons,evalSeries,hmul,ih]
    ring

private theorem evalSeries_mul {A : Type*} (zero : A) (add mul : A → A → A) (value : A → ℝ)
    (hzero : value zero = 0) (hadd : ∀ a b, value (add a b) = value a + value b)
    (hmul : ∀ a b, value (mul a b) = value a * value b) (x : ℝ) (p q : List A) :
    evalSeries value x (mulSeries zero add mul p q) = evalSeries value x p * evalSeries value x q := by
  induction p with
  | nil => simp [mulSeries,evalSeries]
  | cons a p ih =>
    simp only [mulSeries,evalSeries_add add value hadd,evalSeries_scale mul value hmul,evalSeries,hzero,ih]
    ring

private theorem evalSeries_nonneg {A : Type*} (value : A → ℝ) {x : ℝ} (hx : 0 ≤ x) (p : List A)
    (hp : ∀ a ∈ p, 0 ≤ value a) : 0 ≤ evalSeries value x p := by
  induction p with
  | nil => exact le_rfl
  | cons a p ih =>
    exact add_nonneg (hp a (List.mem_cons_self ..))
      (mul_nonneg hx (ih fun b hb => hp b (List.mem_cons_of_mem a hb)))

/-- A row lists ascending powers of (h), and rows list ascending powers of (t). -/
abbrev Coefficients := List (List ℚ)

noncomputable def evalRow (h : ℝ) : List ℚ → ℝ := evalSeries (fun q : ℚ => (q : ℝ)) h

def addRow : List ℚ → List ℚ → List ℚ := addSeries (· + ·)
def mulRow : List ℚ → List ℚ → List ℚ := mulSeries 0 (· + ·) (· * ·)

private theorem evalRow_add (h : ℝ) (p q : List ℚ) :
    evalRow h (addRow p q) = evalRow h p + evalRow h q :=
  evalSeries_add (· + ·) (fun r : ℚ => (r : ℝ)) Rat.cast_add h p q

private theorem evalRow_mul (h : ℝ) (p q : List ℚ) :
    evalRow h (mulRow p q) = evalRow h p * evalRow h q :=
  evalSeries_mul 0 (· + ·) (· * ·) (fun r : ℚ => (r : ℝ)) Rat.cast_zero
    Rat.cast_add Rat.cast_mul h p q

noncomputable def eval (p : Coefficients) (t h : ℝ) : ℝ := evalSeries (evalRow h) t p

def C (q : ℚ) : Coefficients := [[q]]
def T : Coefficients := [[],[1]]
def H : Coefficients := [[0,1]]

def add : Coefficients → Coefficients → Coefficients := addSeries addRow
def mul : Coefficients → Coefficients → Coefficients := mulSeries [] addRow mulRow

def neg (p : Coefficients) : Coefficients :=
  mul (C (-1)) p

def sub (p q : Coefficients) : Coefficients :=
  add p (neg q)

def pow (p : Coefficients) : Nat → Coefficients
  | 0 => C 1
  | n+1 => mul p (pow p n)

@[simp] theorem eval_C (q : ℚ) (t h : ℝ) : eval (C q) t h = q := by
  simp [eval,C,evalSeries,evalRow]

@[simp] theorem eval_T (t h : ℝ) : eval T t h = t := by simp [eval,T,evalSeries,evalRow]
@[simp] theorem eval_H (t h : ℝ) : eval H t h = h := by simp [eval,H,evalSeries,evalRow]

@[simp] theorem eval_add (p q : Coefficients) (t h : ℝ) :
    eval (add p q) t h = eval p t h + eval q t h :=
  evalSeries_add addRow (evalRow h) (evalRow_add h) t p q

@[simp] theorem eval_mul (p q : Coefficients) (t h : ℝ) :
    eval (mul p q) t h = eval p t h * eval q t h :=
  evalSeries_mul [] addRow mulRow (evalRow h) rfl (evalRow_add h) (evalRow_mul h) t p q

@[simp] theorem eval_neg (p : Coefficients) (t h : ℝ) : eval (neg p) t h = -eval p t h := by
  simp [neg]

@[simp] theorem eval_sub (p q : Coefficients) (t h : ℝ) :
    eval (sub p q) t h = eval p t h - eval q t h := by
  simp [sub,sub_eq_add_neg]

@[simp] theorem eval_pow (p : Coefficients) (n : ℕ) (t h : ℝ) : eval (pow p n) t h = (eval p t h)^n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow,ih,pow_succ']

/-- The second component is the coefficient list for ((1+u)^{p.length}).
Keeping it alongside the first avoids rebuilding that power at each step. -/
def transformWithPower : Coefficients → Coefficients × Coefficients
  | [] => ([], C 1)
  | a::as =>
    let (rest, power) := transformWithPower as
    (add (power.map (mulRow a)) ([] :: rest), add power ([] :: power))

def transform (p : Coefficients) : Coefficients := (transformWithPower p).1

private theorem eval_shift (p : Coefficients) (u h : ℝ) :
    eval ([] :: p) u h = u*eval p u h := by
  simp [eval,evalSeries,evalRow]

private theorem eval_transformPower (p : Coefficients) (u h : ℝ) :
    eval (transformWithPower p).2 u h = (1+u)^p.length := by
  induction p with
  | nil => simp [transformWithPower]
  | cons a p ih =>
    simp only [transformWithPower,eval_add,eval_shift,ih,List.length_cons,pow_succ]
    ring

private theorem eval_transform (p : Coefficients) (u h : ℝ) (hu : 1+u ≠ 0) :
    eval (transform p) u h = (1+u)^(p.length-1) * eval p (u/(1+u)) h := by
  induction p with
  | nil => simp [transform,transformWithPower,eval,evalSeries]
  | cons a p ih =>
    have hscale : eval ((transformWithPower p).2.map (mulRow a)) u h =
        evalRow h a * eval (transformWithPower p).2 u h :=
      evalSeries_scale mulRow (evalRow h) (evalRow_mul h) u a (transformWithPower p).2
    simp only [transform,transformWithPower,eval_add,eval_shift,hscale,eval_transformPower,
      List.length_cons,Nat.add_sub_cancel] at ih ⊢
    rw [ih]
    cases p with
    | nil => simp [eval,evalSeries]
    | cons b p =>
      simp only [List.length_cons,Nat.add_sub_cancel,eval,evalSeries]
      rw [pow_succ]
      field_simp [hu]

def rowsNonneg (p : Coefficients) : Bool := p.all (fun row => row.all (fun c => 0 ≤ c))

private theorem evalRow_nonneg (p : List ℚ) {h : ℝ} (hh : 0 ≤ h)
    (hp : p.all (fun c => 0 ≤ c) = true) : 0 ≤ evalRow h p :=
  evalSeries_nonneg _ hh p (fun a ha => by
    exact_mod_cast (show 0 ≤ a from of_decide_eq_true ((List.all_eq_true.mp hp) a ha)))

private theorem evalRow_pos (p : List ℚ) {h : ℝ} (hh : 0 ≤ h)
    (hp : p.all (fun c => 0 ≤ c) = true)
    (h₀ : 0 < p.headD 0) : 0 < evalRow h p := by
  cases p with
  | nil => simp at h₀
  | cons a p =>
    have ha : 0 < (a : ℝ) := by exact_mod_cast h₀
    have hp' : p.all (fun c => 0 ≤ c) = true := by
      simp only [List.all_cons,Bool.and_eq_true] at hp
      exact hp.2
    exact add_pos_of_pos_of_nonneg ha (mul_nonneg hh (evalRow_nonneg p hh hp'))

private theorem eval_pos (p : Coefficients) {t h : ℝ} (ht : 0 ≤ t) (hh : 0 ≤ h)
    (hp : rowsNonneg p = true) (h₀ : 0 < (p.headD []).headD 0) : 0 < eval p t h := by
  cases p with
  | nil => simp at h₀
  | cons a p =>
    have ha : a.all (fun c => 0 ≤ c) = true := List.all_eq_true.mp hp _ (List.mem_cons_self ..)
    have hp' : ∀ b ∈ p, 0 ≤ evalRow h b := fun b hb =>
      evalRow_nonneg b hh (List.all_eq_true.mp hp _ (List.mem_cons_of_mem _ hb))
    exact add_pos_of_pos_of_nonneg (evalRow_pos a hh ha h₀)
      (mul_nonneg ht (evalSeries_nonneg _ ht p hp'))

def strictOnOpen (p : Coefficients) : Bool :=
  let q := transform p
  rowsNonneg q && decide (0 < (q.headD []).headD 0)

theorem eval_pos_of_strictOnOpen (p : Coefficients) {t h : ℝ}
    (ht : 0 ≤ t) (ht' : t < 1) (hh : 0 ≤ h) (hp : strictOnOpen p = true) : 0 < eval p t h := by
  simp only [strictOnOpen,Bool.and_eq_true,decide_eq_true_eq] at hp
  obtain ⟨hn,ha⟩ := hp
  let u := t/(1-t)
  have hu : 0 ≤ u := div_nonneg ht (sub_nonneg.mpr ht'.le)
  have h1u : 0 < 1+u := by linarith
  have htu : u/(1+u) = t := by
    unfold u
    field_simp [(sub_pos.mpr ht').ne',h1u.ne']
    ring
  have he := eval_pos (transform p) hu hh hn ha
  rw [eval_transform _ _ _ h1u.ne',htu] at he
  exact pos_of_mul_pos_right he (pow_nonneg h1u.le _)

def atOne : Coefficients → List ℚ := List.foldr addRow []

private theorem eval_atOne (p : Coefficients) (h : ℝ) : evalRow h (atOne p) = eval p 1 h := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [atOne,List.foldr_cons,evalRow_add,eval,evalSeries,one_mul] at ih ⊢
    rw [ih]

/-- A closed-interval certificate also checks the surviving row at (t=1). -/
def strictOnClosed (p : Coefficients) : Bool :=
  strictOnOpen p && (atOne p).all (fun c => 0 ≤ c) && decide (0 < (atOne p).headD 0)

theorem eval_pos_of_strictOnClosed (p : Coefficients) {t h : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ 1) (hh : 0 ≤ h) (hp : strictOnClosed p = true) : 0 < eval p t h := by
  simp only [strictOnClosed,Bool.and_eq_true,decide_eq_true_eq] at hp
  rcases ht'.lt_or_eq with hlt | rfl
  · exact eval_pos_of_strictOnOpen p ht hlt hh hp.1.1
  · rw [← eval_atOne]
    exact evalRow_pos _ hh hp.1.2 hp.2

end OrigamiTorus.StripPolynomial
