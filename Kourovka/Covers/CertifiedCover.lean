/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Covers.CoverSoundness
import Kourovka.Covers.CoverMargin

/-!
# Certified Cover

An accepted rational cone-margin certificate produces an explicit
ordinary finite presentation defining a metabelian group.
-/

namespace Kourovka.MetabelianEnumeration.FiniteCover

open Collection ConeVerifier TamenessCompactness

def marginConstant (k r : ℕ) : ℚ := min ((1 / 2 : ℚ) ^ r / k) 1

def coneRadius {k a : ℕ} (data : Datum k a) (r : ℕ) : ℕ :=
  certifiedRadius k (marginConstant k r) (supportBound data)

/-- Soundness for the computable margin checker and explicit integer radius. -/
theorem checked_cover_metabelian {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k) (r : ℕ)
    (hr : checkMargin (data.polynomials.map polynomialSupport) ((1 / 2 : ℚ) ^ r) = true) :
    Metabelian (GroupOf data (coneRadius data r)) := by
  let ε : ℚ := (1 / 2) ^ r
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hC : 0 < marginConstant k r := lt_min (div_pos hε hk0) (by norm_num)
  have hD := supportBound_ge_one data
  apply certified_cover_metabelian data hk (marginConstant k r) (supportBound data)
    hC hD ((min_le_right _ _).trans hD) (supportBound_norm data)
  intro v hv
  obtain ⟨p, hp, hdir⟩ := cube_margin_direction data hk ε hε
    ((checkMargin_correct _ _).mp hr) v hv
  refine ⟨p, hp, ?_⟩
  intro term ht
  have hCle : ((marginConstant k r : ℚ) : ℝ) ≤ ((ε / k : ℚ) : ℝ) := by
    exact_mod_cast (min_le_left (ε / k) 1)
  exact (hdir term ht).trans (by nlinarith [norm_nonneg (euclidean v)])

/-- Every finite cone cover has an explicit integer radius at which its
ordinary finite group presentation is metabelian. -/
theorem exists_metabelian_cover_radius {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k)
    (hc : ConeCover (data.polynomials.map polynomialSupport)) :
    ∃ R : ℕ, Metabelian (GroupOf data R) := by
  obtain ⟨r, hr⟩ := dyadic_margin_search_terminates _ hc
  exact ⟨coneRadius data r, checked_cover_metabelian data hk r hr⟩

end Kourovka.MetabelianEnumeration.FiniteCover
