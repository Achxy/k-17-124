/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Polyhedral.ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Cone Margin

A positive rational margin exists for every accepted cone cover. Hence the
dyadic margin search in the manuscript terminates; this is not a numerical test.
-/

namespace Kourovka.MetabelianEnumeration.ConeVerifier

def supportScore {n : ℕ} : List (Vec n) → (Fin n → ℝ) → ℝ
  | [], _ => 1
  | u :: rest, x => min (dot u x) (supportScore rest x)

def coverScore {n : ℕ} : Supports n → (Fin n → ℝ) → ℝ
  | [], _ => 0
  | support :: rest, x => max (supportScore support x) (coverScore rest x)

theorem supportScore_gt_iff {n : ℕ} (support : List (Vec n)) (x : Fin n → ℝ)
    (epsilon : ℝ) (he : epsilon < 1) :
    epsilon < supportScore support x ↔ ∀ u ∈ support, epsilon < dot u x := by
  induction support with
  | nil => simp [supportScore, he]
  | cons u rest ih => simp [supportScore, ih]

theorem coverScore_gt_iff {n : ℕ} (supports : Supports n) (x : Fin n → ℝ)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) :
    epsilon < coverScore supports x ↔
      ∃ support ∈ supports, ∀ u ∈ support, epsilon < dot u x := by
  induction supports with
  | nil => simp [coverScore, not_lt.mpr he0]
  | cons support rest ih =>
    simp [coverScore, supportScore_gt_iff support x epsilon he1, ih]

theorem continuous_dot {n : ℕ} (u : Vec n) : Continuous (dot u) := by
  unfold dot
  fun_prop

theorem continuous_supportScore {n : ℕ} (support : List (Vec n)) :
    Continuous (supportScore support) := by
  induction support with
  | nil => exact continuous_const
  | cons u rest ih => exact (continuous_dot u).min ih

theorem continuous_coverScore {n : ℕ} (supports : Supports n) :
    Continuous (coverScore supports) := by
  induction supports with
  | nil => exact continuous_const
  | cons support rest ih => exact (continuous_supportScore support).max ih

theorem isCompact_cubeSphere (n : ℕ) : IsCompact {x : Fin n → ℝ | CubeSphere x} := by
  have hface : IsClosed {x : Fin n → ℝ | ∃ i, x i = -1 ∨ x i = 1} := by
    have h := isClosed_iUnion_of_finite (fun i : Fin n =>
      (isClosed_eq (continuous_apply i) continuous_const).union
        (isClosed_eq (continuous_apply i) continuous_const) :
      ∀ i : Fin n, IsClosed ({x : Fin n → ℝ | x i = -1} ∪ {x | x i = 1}))
    convert h using 1
    ext x
    simp
  have hcube : IsCompact (Set.Icc (-1 : Fin n → ℝ) 1) := isCompact_Icc
  convert hcube.inter_right hface using 1
  ext x
  simp only [Set.mem_setOf_eq, CubeSphere, Set.mem_inter_iff, Set.mem_Icc,
    Pi.le_def, Pi.neg_apply, Pi.one_apply]
  aesop

theorem exists_uniform_margin {n : ℕ} (supports : Supports n) (hc : ConeCover supports) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 ∧
      ∀ x : Fin n → ℝ, CubeSphere x →
        ∃ support ∈ supports, ∀ u ∈ support, epsilon < dot u x := by
  have hp : ∀ x ∈ {x : Fin n → ℝ | CubeSphere x}, 0 < coverScore supports x := by
    intro x hx
    exact (coverScore_gt_iff supports x 0 le_rfl (by norm_num)).mpr
      (hc x (cubeSphere_ne_zero hx))
  obtain ⟨a, ha, hbound⟩ := (isCompact_cubeSphere n).exists_forall_le'
    (continuous_coverScore supports).continuousOn hp
  refine ⟨min (a / 2) (1 / 2), lt_min (by linarith) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro x hx
  apply (coverScore_gt_iff supports x _ (le_of_lt (lt_min (by linarith) (by norm_num)))
    ((min_le_right _ _).trans_lt (by norm_num))).mp
  exact (min_le_left _ _).trans_lt (by linarith [hbound x hx])

/-- There is an accepted dyadic margin, so sequential search through these
finite computations terminates for every cone cover. -/
theorem dyadic_margin_search_terminates {n : ℕ} (supports : Supports n)
    (hc : ConeCover supports) : ∃ r : ℕ, checkMargin supports ((1 / 2 : ℚ) ^ r) = true := by
  obtain ⟨epsilon, he0, _, hmargin⟩ := exists_uniform_margin supports hc
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one he0 (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨r, (checkMargin_correct supports _).mpr ?_⟩
  intro x hx
  obtain ⟨s, hs, hpos⟩ := hmargin x hx
  refine ⟨s, hs, ?_⟩
  intro u hu
  have hcast : (((1 / 2 : ℚ) ^ r : ℚ) : ℝ) < epsilon := by
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hr
  exact hcast.trans (hpos u hu)

end Kourovka.MetabelianEnumeration.ConeVerifier
