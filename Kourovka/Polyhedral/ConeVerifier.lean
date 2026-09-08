/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Polyhedral.FourierMotzkin

/-!
# Cone Verifier

The finite rational cone test used in the Bieri–Strebel certificate.
All support choices and all faces of the infinity-norm unit sphere are checked.
The Boolean test is proved equivalent to the quantified real cone condition.
-/

namespace Kourovka.MetabelianEnumeration.ConeVerifier

open FourierMotzkin

abbrev Vec (n : ℕ) := Fin n → ℚ
abbrev Supports (n : ℕ) := List (List (Vec n))

def dot {n : ℕ} (u : Vec n) (x : Fin n → ℝ) : ℝ := ∑ i, (u i : ℝ) * x i

def supportRow {n : ℕ} (u : Vec n) (epsilon : ℚ) : Row n := ⟨u, -epsilon⟩

theorem supportRow_iff {n : ℕ} (u : Vec n) (epsilon : ℚ) (x : Fin n → ℝ) :
    (supportRow u epsilon).eval x ≤ 0 ↔ dot u x ≤ epsilon := by
  simp only [supportRow, Row.eval, Rat.cast_neg, dot]
  constructor <;> intro h <;> linarith

/-- Enumerate one nonpositive support witness for each polynomial. -/
def search (n : ℕ) (epsilon : ℚ) : Supports n → List (Row n) → Bool
  | [], rows => check n rows
  | support :: rest, rows =>
    support.any fun u => search n epsilon rest (supportRow u epsilon :: rows)

theorem search_correct {n : ℕ} (epsilon : ℚ) (supports : Supports n)
    (rows : List (Row n)) : search n epsilon supports rows = true ↔
    ∃ x : Fin n → ℝ, Satisfies rows x ∧
      ∀ support ∈ supports, ∃ u ∈ support, dot u x ≤ epsilon := by
  induction supports generalizing rows with
  | nil => simpa [search, Feasible] using check_correct n rows ℝ
  | cons support rest ih =>
    simp only [search, List.any_eq_true, ih]
    constructor
    · rintro ⟨u, hu, x, hx, hrest⟩
      have hu' := (supportRow_iff u epsilon x).mp (hx _ List.mem_cons_self)
      refine ⟨x, fun r hr => hx r (List.mem_cons_of_mem _ hr), ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ⟨u, hu, hu'⟩
      · exact hrest s hs
    · rintro ⟨x, hx, hs⟩
      obtain ⟨u, hu, hu'⟩ := hs support List.mem_cons_self
      refine ⟨u, hu, x, ?_, fun s h => hs s (List.mem_cons_of_mem _ h)⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact (supportRow_iff u epsilon x).mpr hu'
      · exact hx r hr

def coordinate {n : ℕ} (i : Fin n) (a b : ℚ) : Row n :=
  ⟨fun j => if j = i then a else 0, b⟩

theorem coordinate_eval {n : ℕ} (i : Fin n) (a b : ℚ) (x : Fin n → ℝ) :
    (coordinate i a b).eval x = (a : ℝ) * x i + b := by
  simp [coordinate, Row.eval, apply_ite, ite_mul]

def cubeRows (n : ℕ) : List (Row n) :=
  (List.finRange n).flatMap fun i => [coordinate i 1 (-1), coordinate i (-1) (-1)]

theorem cubeRows_iff {n : ℕ} (x : Fin n → ℝ) :
    Satisfies (cubeRows n) x ↔ ∀ i, -1 ≤ x i ∧ x i ≤ 1 := by
  constructor
  · intro h i
    have hu := h (coordinate i 1 (-1))
      (List.mem_flatMap.mpr ⟨i, by simp, by simp⟩)
    have hl := h (coordinate i (-1) (-1))
      (List.mem_flatMap.mpr ⟨i, by simp, by simp⟩)
    simp only [coordinate_eval, Rat.cast_one, Rat.cast_neg, one_mul, neg_mul] at hu hl
    constructor <;> linarith
  · intro h r hr
    obtain ⟨i, _, hr⟩ := List.mem_flatMap.mp hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      simp only [coordinate_eval, Rat.cast_one, Rat.cast_neg, one_mul, neg_mul] <;>
      obtain ⟨hl, hu⟩ := h i <;> linarith

def faceRows {n : ℕ} (i : Fin n) (sign : ℚ) : List (Row n) :=
  [coordinate i 1 (-sign), coordinate i (-1) sign] ++ cubeRows n

theorem faceRows_iff {n : ℕ} (i : Fin n) (sign : ℚ) (x : Fin n → ℝ) :
    Satisfies (faceRows i sign) x ↔ x i = sign ∧ ∀ j, -1 ≤ x j ∧ x j ≤ 1 := by
  constructor
  · intro h
    have hu := h (coordinate i 1 (-sign)) (by simp [faceRows])
    have hl := h (coordinate i (-1) sign) (by simp [faceRows])
    simp only [coordinate_eval, Rat.cast_one, Rat.cast_neg, one_mul, neg_mul] at hu hl
    exact ⟨by linarith, (cubeRows_iff x).mp (fun r hr => h r (by simp [faceRows, hr]))⟩
  · rintro ⟨hi, hcube⟩ r hr
    simp only [faceRows, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | hr
    · simp [coordinate_eval, hi]
    · simp [coordinate_eval, hi]
    · exact (cubeRows_iff x).mpr hcube r hr

def CubeSphere {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, -1 ≤ x i ∧ x i ≤ 1) ∧ ∃ i, x i = -1 ∨ x i = 1

def badDirection {n : ℕ} (supports : Supports n) (epsilon : ℚ) : Bool :=
  (List.finRange n).any fun i =>
    ([-1, 1] : List ℚ).any fun sign => search n epsilon supports (faceRows i sign)

theorem badDirection_correct {n : ℕ} (supports : Supports n) (epsilon : ℚ) :
    badDirection supports epsilon = true ↔
      ∃ x : Fin n → ℝ, CubeSphere x ∧
        ∀ support ∈ supports, ∃ u ∈ support, dot u x ≤ epsilon := by
  simp only [badDirection, List.any_eq_true, List.mem_finRange, true_and,
    search_correct, faceRows_iff]
  constructor
  · rintro ⟨i, sign, hsign, x, ⟨hx, hc⟩, hs⟩
    refine ⟨x, ⟨hc, i, ?_⟩, hs⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsign
    rcases hsign with rfl | rfl
    · exact Or.inl (by simpa using hx)
    · exact Or.inr (by simpa using hx)
  · rintro ⟨x, ⟨hc, i, hi⟩, hs⟩
    rcases hi with hi | hi
    · exact ⟨i, -1, by simp, x, ⟨by simpa using hi, hc⟩, hs⟩
    · exact ⟨i, 1, by simp, x, ⟨by simpa using hi, hc⟩, hs⟩

def CubeMargin {n : ℕ} (supports : Supports n) (epsilon : ℚ) : Prop :=
  ∀ x : Fin n → ℝ, CubeSphere x →
    ∃ support ∈ supports, ∀ u ∈ support, (epsilon : ℝ) < dot u x

def checkMargin {n : ℕ} (supports : Supports n) (epsilon : ℚ) : Bool :=
  !(badDirection supports epsilon)

theorem checkMargin_correct {n : ℕ} (supports : Supports n) (epsilon : ℚ) :
    checkMargin supports epsilon = true ↔ CubeMargin supports epsilon := by
  rw [checkMargin, Bool.not_eq_true']
  rw [← Bool.not_eq_true, badDirection_correct]
  constructor
  · intro h x hx
    by_contra hn
    push_neg at hn
    exact h ⟨x, hx, hn⟩
  · intro h
    rintro ⟨x, hx, hn⟩
    obtain ⟨s, hs, hpos⟩ := h x hx
    obtain ⟨u, hu, hle⟩ := hn s hs
    exact (not_lt_of_ge hle) (hpos u hu)

def ConeCover {n : ℕ} (supports : Supports n) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 → ∃ support ∈ supports, ∀ u ∈ support, 0 < dot u x

theorem cubeSphere_ne_zero {n : ℕ} {x : Fin n → ℝ} (hx : CubeSphere x) : x ≠ 0 := by
  obtain ⟨i, hi⟩ := hx.2
  intro h
  simp only [h, Pi.zero_apply] at hi
  rcases hi with hi | hi <;> linarith

theorem normalize_to_cube {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ CubeSphere (fun i => x i / c) := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
    ⟨j, Finset.mem_univ j⟩
  have hc : 0 < |x i| := (abs_pos.mpr hj).trans_le (hmax j (Finset.mem_univ j))
  refine ⟨|x i|, hc, ?_, i, ?_⟩
  · intro k
    have hle : |x k / (|x i|)| ≤ 1 := by
      rw [abs_div, abs_abs, div_le_one hc]
      exact hmax k (Finset.mem_univ k)
    exact abs_le.mp hle
  · have habs : |x i / (|x i|)| = 1 := by
      rw [abs_div, abs_abs, div_self (ne_of_gt hc)]
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem dot_div {n : ℕ} (u : Vec n) (x : Fin n → ℝ) (c : ℝ) :
    dot u (fun i => x i / c) = dot u x / c := by
  simp only [dot, mul_div_assoc, Finset.sum_div]

theorem coneCover_iff_cubeMargin {n : ℕ} (supports : Supports n) :
    ConeCover supports ↔ CubeMargin supports 0 := by
  constructor
  · intro h x hx
    simpa only [Rat.cast_zero] using h x (cubeSphere_ne_zero hx)
  · intro h x hx
    obtain ⟨c, hc, hx'⟩ := normalize_to_cube x hx
    obtain ⟨s, hs, hpos⟩ := h _ hx'
    refine ⟨s, hs, ?_⟩
    intro u hu
    have hp := hpos u hu
    rw [Rat.cast_zero, dot_div] at hp
    exact (div_pos_iff_of_pos_right hc).mp hp

/-- The exact universally quantified cone-cover condition is decided by rational arithmetic. -/
theorem coneCheck_correct {n : ℕ} (supports : Supports n) :
    checkMargin supports 0 = true ↔ ConeCover supports :=
  (checkMargin_correct supports 0).trans (coneCover_iff_cubeMargin supports).symm

end Kourovka.MetabelianEnumeration.ConeVerifier
