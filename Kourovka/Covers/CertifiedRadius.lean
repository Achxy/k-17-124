/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Polyhedral.Radius
import Kourovka.Polyhedral.ConeMargin

/-!
# Certified Radius

The manuscript's explicit radius bound uses exact rational arithmetic.
-/

namespace Kourovka.MetabelianEnumeration.FiniteCover

def certifiedRadius (k : ℕ) (C D : ℚ) : ℕ :=
  1 + ⌈2 * (k : ℚ) * (1 + D + D ^ 2 / C)⌉₊

theorem certifiedRadius_large {k : ℕ} (hk : 1 ≤ k) {C D : ℚ}
    (hC : 0 < C) (hD : 1 ≤ D) (hCD : C ≤ D) :
    2 * (k : ℚ) < certifiedRadius k C D ∧
    2 * (k : ℚ) * D < certifiedRadius k C D ∧
    C < certifiedRadius k C D ∧
    D ^ 2 < C * certifiedRadius k C D := by
  have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hquot : 0 ≤ D ^ 2 / C := div_nonneg (sq_nonneg D) (le_of_lt hC)
  have hceil := Nat.le_ceil (2 * (k : ℚ) * (1 + D + D ^ 2 / C))
  have hmain : 2 * (k : ℚ) * (1 + D + D ^ 2 / C) < certifiedRadius k C D := by
    simp only [certifiedRadius, Nat.cast_add, Nat.cast_one]
    linarith
  have hbase : 0 < 2 * (k : ℚ) * (1 + D + D ^ 2 / C) := by positivity
  have hfirst : 2 * (k : ℚ) < certifiedRadius k C D := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℚ) by linarith) hquot]
  have hsecond : 2 * (k : ℚ) * D < certifiedRadius k C D := by
    nlinarith [mul_nonneg (show 0 ≤ (k : ℚ) by linarith) hquot]
  have hthird : C < certifiedRadius k C D := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * (k : ℚ) - 1 by linarith)
      (show 0 ≤ D by linarith)]
  have hfourth : D ^ 2 / C < certifiedRadius k C D := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * (k : ℚ) - 1 by linarith) hquot,
      mul_nonneg (show 0 ≤ (k : ℚ) by linarith) (show 0 ≤ D by linarith)]
  exact ⟨hfirst, hsecond, hthird, by
    have := (div_lt_iff₀ hC).mp hfourth
    nlinarith⟩

def certifiedDelta (k : ℕ) (C : ℚ) : ℚ := min (C / 4) (1 / (4 * (k : ℚ)))

theorem certifiedDelta_bounds {k : ℕ} (hk : 1 ≤ k) {C : ℚ} (hC : 0 < C) :
    0 < certifiedDelta k C ∧ certifiedDelta k C ≤ C / 4 ∧
      certifiedDelta k C < 1 / (2 * (k : ℚ)) := by
  have hk' : (0 : ℚ) < k := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hk
  refine ⟨lt_min (by positivity) (by positivity), min_le_left _ _, ?_⟩
  apply (min_le_right _ _).trans_lt
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith

end Kourovka.MetabelianEnumeration.FiniteCover
