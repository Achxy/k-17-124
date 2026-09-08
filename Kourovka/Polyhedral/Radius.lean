/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# A quantitative Euclidean descent estimate

Subtracting a bounded lattice vector with a sufficiently positive scalar product
strictly decreases squared norm. This is the geometric step in cover soundness.
-/

namespace Kourovka.MetabelianEnumeration

/-- The strict scalar estimate in (17.124.5), including the radius margin. -/
theorem radius_shrink (C D ρ δ r s : ℝ)
    (_hC : 0 < C) (hρC : C < ρ) (hρD : D ^ 2 < C * ρ)
    (hδ : 0 < δ) (hδC : δ ≤ C / 4)
    (hr : ρ ≤ r) (hr' : r < ρ + δ)
    (hs : s ≤ r ^ 2 - 2 * C * r + D ^ 2) : s < ρ ^ 2 := by
  have hsum : 0 < ρ + δ + r - 2 * C := by linarith
  have hstep := mul_pos (sub_pos.mpr hr') hsum
  have hδquad : δ ^ 2 - 2 * C * δ ≤ 0 := by
    nlinarith [mul_nonneg (le_of_lt hδ) (show 0 ≤ 2 * C - δ by linarith)]
  have hmargin := mul_nonneg (show 0 ≤ C / 4 - δ by linarith)
    (show 0 ≤ ρ by linarith)
  nlinarith

/-- The dot-product estimate gives the required squared-norm shrinkage. -/
theorem vector_radius_shrink {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v u : E) (C D ρ δ : ℝ)
    (hC : 0 < C) (hρC : C < ρ) (hρD : D ^ 2 < C * ρ)
    (hδ : 0 < δ) (hδC : δ ≤ C / 4)
    (hr : ρ ≤ ‖v‖) (hr' : ‖v‖ < ρ + δ)
    (hu : ‖u‖ ^ 2 ≤ D ^ 2) (hdot : inner ℝ v u ≤ -C * ‖v‖) :
    ‖v + u‖ < ρ := by
  have hs : ‖v + u‖ ^ 2 ≤ ‖v‖ ^ 2 - 2 * C * ‖v‖ + D ^ 2 := by
    rw [norm_add_sq_real]
    nlinarith
  have h := radius_shrink C D ρ δ ‖v‖ (‖v + u‖ ^ 2)
    hC hρC hρD hδ hδC hr hr' hs
  nlinarith [norm_nonneg (v + u)]

end Kourovka.MetabelianEnumeration
