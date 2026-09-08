/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Presentations.Presentations

/-!
# Fourier Motzkin

A rational Fourier–Motzkin algorithm with correctness over every ordered field.
The same Boolean computation therefore decides both rational and real feasibility.
No oracle or floating-point computation is used.
-/

namespace Kourovka.MetabelianEnumeration.FourierMotzkin

structure Row (n : ℕ) where
  coeff : Fin n → ℚ
  constant : ℚ
  deriving DecidableEq

def Row.eval {n : ℕ} (r : Row n) {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (x : Fin n → K) : K :=
  (∑ i, (r.coeff i : K) * x i) + (r.constant : K)

def Satisfies {n : ℕ} (rows : List (Row n)) {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (x : Fin n → K) : Prop :=
  ∀ r ∈ rows, r.eval x ≤ 0

def Feasible {n : ℕ} (rows : List (Row n)) (K : Type*) [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : Prop := ∃ x : Fin n → K, Satisfies rows x

def Row.head {n : ℕ} (r : Row (n + 1)) : ℚ := r.coeff 0

def Row.tail {n : ℕ} (r : Row (n + 1)) : Row n :=
  ⟨fun i => r.coeff i.succ, r.constant⟩

def Row.combine {n : ℕ} (l u : Row (n + 1)) : Row n :=
  ⟨fun i => u.head * l.coeff i.succ - l.head * u.coeff i.succ,
    u.head * l.constant - l.head * u.constant⟩

def negatives {n : ℕ} (rows : List (Row (n + 1))) : List (Row (n + 1)) :=
  rows.filter fun r => r.head < 0

def positives {n : ℕ} (rows : List (Row (n + 1))) : List (Row (n + 1)) :=
  rows.filter fun r => 0 < r.head

def eliminate {n : ℕ} (rows : List (Row (n + 1))) : List (Row n) :=
  (rows.filter (fun r => r.head = 0)).map Row.tail ++
    (negatives rows).flatMap fun l => (positives rows).map (Row.combine l)

theorem Row.eval_cons {n : ℕ} (r : Row (n + 1)) {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (t : K) (x : Fin n → K) :
    r.eval (Fin.cons t x) = (r.head : K) * t + r.tail.eval x := by
  simp [Row.eval, Row.head, Row.tail, Fin.sum_univ_succ, add_assoc]

theorem Row.eval_combine {n : ℕ} (l u : Row (n + 1)) {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (x : Fin n → K) :
    (l.combine u).eval x = (u.head : K) * l.tail.eval x -
      (l.head : K) * u.tail.eval x := by
  simp only [Row.eval, Row.combine, Row.tail, Rat.cast_sub, Rat.cast_mul]
  simp_rw [sub_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem exists_common_lower_bound {K : Type*} [LinearOrder K] [Zero K]
    (upper : List K) : ∃ t : K, ∀ u ∈ upper, t ≤ u := by
  induction upper with
  | nil => exact ⟨0, by simp⟩
  | cons u upper ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨min u t, ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ht v hv)

theorem finite_interval {K : Type*} [LinearOrder K] [Zero K]
    (lower upper : List K) :
    (∃ t : K, (∀ l ∈ lower, l ≤ t) ∧ (∀ u ∈ upper, t ≤ u)) ↔
      ∀ l ∈ lower, ∀ u ∈ upper, l ≤ u := by
  constructor
  · rintro ⟨t, hl, hu⟩ l hl' u hu'
    exact (hl l hl').trans (hu u hu')
  · induction lower with
    | nil =>
      intro _
      obtain ⟨t, ht⟩ := exists_common_lower_bound upper
      exact ⟨t, by simp, ht⟩
    | cons l lower ih =>
      intro h
      obtain ⟨t, ht, htu⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      refine ⟨max l t, ?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact le_max_left _ _
        · exact (ht a ha).trans (le_max_right _ _)
      · intro u hu
        exact max_le (h l List.mem_cons_self u hu) (htu u hu)

theorem lower_constraint {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b t : K} (ha : a < 0) :
    a * t + b ≤ 0 ↔ -b / a ≤ t := by
  rw [div_le_iff_of_neg ha]
  constructor <;> intro h <;> nlinarith

theorem upper_constraint {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b t : K} (ha : 0 < a) :
    a * t + b ≤ 0 ↔ t ≤ -b / a := by
  rw [le_div_iff₀ ha]
  constructor <;> intro h <;> nlinarith

theorem pair_constraint {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b c d : K} (ha : a < 0) (hc : 0 < c) :
    c * b - a * d ≤ 0 ↔ -b / a ≤ -d / c := by
  have hrewrite : -b / a = b / -a := by ring
  rw [hrewrite, div_le_div_iff₀ (neg_pos.mpr ha) hc]
  constructor <;> intro h <;> nlinarith

theorem satisfies_eliminate_iff {n : ℕ} (rows : List (Row (n + 1)))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x : Fin n → K) :
    Satisfies (eliminate rows) x ↔
      (∀ r ∈ rows, r.head = 0 → r.tail.eval x ≤ 0) ∧
      (∀ l ∈ rows, l.head < 0 → ∀ u ∈ rows, 0 < u.head →
        (l.combine u).eval x ≤ 0) := by
  constructor
  · intro h
    constructor
    · intro r hr hz
      apply h _
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simpa⟩, rfl⟩
    · intro l hl hneg u hu hpos
      apply h _
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨l, List.mem_filter.mpr ⟨hl, by simpa⟩,
        List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu, by simpa⟩, rfl⟩⟩
  · rintro ⟨hz, hp⟩ r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hsmem, hsz⟩ := List.mem_filter.mp hs
      exact hz s hsmem (of_decide_eq_true hsz)
    · obtain ⟨l, hl, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hlmem, hlneg⟩ := List.mem_filter.mp hl
      obtain ⟨humem, hupos⟩ := List.mem_filter.mp hu
      exact hp l hlmem (of_decide_eq_true hlneg) u humem (of_decide_eq_true hupos)

theorem elimination_step {n : ℕ} (rows : List (Row (n + 1)))
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x : Fin n → K) :
    Satisfies (eliminate rows) x ↔ ∃ t : K, Satisfies rows (Fin.cons t x) := by
  rw [satisfies_eliminate_iff]
  constructor
  · rintro ⟨hz, hp⟩
    let lower : List K := (negatives rows).map fun r => -r.tail.eval x / (r.head : K)
    let upper : List K := (positives rows).map fun r => -r.tail.eval x / (r.head : K)
    have hcross : ∀ l ∈ lower, ∀ u ∈ upper, l ≤ u := by
      intro l hl u hu
      obtain ⟨lr, hlr, rfl⟩ := List.mem_map.mp hl
      obtain ⟨ur, hur, rfl⟩ := List.mem_map.mp hu
      obtain ⟨hlmem, hlneg⟩ := List.mem_filter.mp hlr
      obtain ⟨humem, hupos⟩ := List.mem_filter.mp hur
      have hlneg' : lr.head < 0 := of_decide_eq_true hlneg
      have hupos' : 0 < ur.head := of_decide_eq_true hupos
      have hlcast : (lr.head : K) < 0 := by exact_mod_cast hlneg'
      have hucast : (0 : K) < ur.head := by exact_mod_cast hupos'
      apply (pair_constraint hlcast hucast).mp
      simpa only [Row.eval_combine] using hp lr hlmem hlneg' ur humem hupos'
    obtain ⟨t, htlow, htup⟩ := (finite_interval lower upper).mpr hcross
    refine ⟨t, ?_⟩
    intro r hr
    rw [Row.eval_cons]
    rcases lt_trichotomy r.head 0 with hneg | hzero | hpos
    · have hcast : (r.head : K) < 0 := by exact_mod_cast hneg
      apply (lower_constraint hcast).mpr
      exact htlow _ (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simpa⟩, rfl⟩)
    · simpa only [hzero, Rat.cast_zero, zero_mul, zero_add] using hz r hr hzero
    · have hcast : (0 : K) < r.head := by exact_mod_cast hpos
      apply (upper_constraint hcast).mpr
      exact htup _ (List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨hr, by simpa⟩, rfl⟩)
  · rintro ⟨t, ht⟩
    constructor
    · intro r hr hzero
      have h := ht r hr
      simpa only [Row.eval_cons, hzero, Rat.cast_zero, zero_mul, zero_add] using h
    · intro l hl hlneg u hu hupos
      have hlcast : (l.head : K) < 0 := by exact_mod_cast hlneg
      have hucast : (0 : K) < u.head := by exact_mod_cast hupos
      rw [Row.eval_combine]
      apply (pair_constraint hlcast hucast).mpr
      exact ((lower_constraint hlcast).mp (by simpa only [Row.eval_cons] using ht l hl)).trans
        ((upper_constraint hucast).mp (by simpa only [Row.eval_cons] using ht u hu))

theorem feasible_eliminate_iff {n : ℕ} (rows : List (Row (n + 1)))
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    Feasible (eliminate rows) K ↔ Feasible rows K := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨t, ht⟩ := (elimination_step rows x).mp hx
    exact ⟨Fin.cons t x, ht⟩
  · rintro ⟨x, hx⟩
    refine ⟨Fin.tail x, (elimination_step rows (Fin.tail x)).mpr ⟨x 0, ?_⟩⟩
    simpa only [Fin.cons_self_tail] using hx

/-- An executable rational algorithm; recursion eliminates one variable at a time. -/
def check : (n : ℕ) → List (Row n) → Bool
  | 0, rows => rows.all fun r => r.constant ≤ 0
  | n + 1, rows => check n (eliminate rows)

theorem check_correct (n : ℕ) (rows : List (Row n))
    (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    check n rows = true ↔ Feasible rows K := by
  induction n with
  | zero =>
    simp only [check, List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨Fin.elim0, ?_⟩
      intro r hr
      have hcast : (r.constant : K) ≤ 0 := by exact_mod_cast h r hr
      simpa [Row.eval] using hcast
    · rintro ⟨x, hx⟩ r hr
      have hcast : (r.constant : K) ≤ 0 := by simpa [Row.eval] using hx r hr
      exact_mod_cast hcast
  | succ n ih =>
    rw [check, ih, feasible_eliminate_iff]

/-- Rational inequalities have a rational solution exactly when they have a real solution. -/
theorem rational_iff_real {n : ℕ} (rows : List (Row n)) :
    Feasible rows ℚ ↔ Feasible rows ℝ :=
  (check_correct n rows ℚ).symm.trans (check_correct n rows ℝ)

end Kourovka.MetabelianEnumeration.FourierMotzkin
