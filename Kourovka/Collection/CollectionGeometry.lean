/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Collection.Collection

/-!
# Collection Geometry

Euclidean lattice geometry used by finite-radius collection.
-/

namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection

def euclidean {k : ℕ} (v : Lattice k) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun i => (v i : ℝ))

@[simp] theorem euclidean_add {k : ℕ} (v w : Lattice k) :
    euclidean (v + w) = euclidean v + euclidean w := by
  ext i; simp [euclidean]

@[simp] theorem euclidean_neg {k : ℕ} (v : Lattice k) :
    euclidean (-v) = -euclidean v := by
  ext i; simp [euclidean]

theorem euclidean_norm_sq {k : ℕ} (v : Lattice k) :
    ‖euclidean v‖ ^ 2 = ∑ i, (v i : ℝ) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, euclidean, Real.norm_eq_abs]

theorem euclidean_norm_le_sum {k : ℕ} (v : Lattice k) :
    ‖euclidean v‖ ≤ ∑ i, |(v i : ℝ)| := by
  have h : euclidean v = ∑ i, EuclideanSpace.single i (v i : ℝ) := by
    ext j
    change (v j : ℝ) = (EuclideanSpace.projₗ j) (∑ i, EuclideanSpace.single i (v i : ℝ))
    rw [map_sum]
    change (v j : ℝ) = ∑ i, (EuclideanSpace.single i (v i : ℝ)) j
    simp [EuclideanSpace.single_apply]
  rw [h]
  exact (norm_sum_le _ _).trans_eq (by simp [EuclideanSpace.norm_single, Real.norm_eq_abs])

def latticeAbs {k : ℕ} (v : Lattice k) : Lattice k := fun i => |v i|

@[simp] theorem euclidean_norm_abs {k : ℕ} (v : Lattice k) :
    ‖euclidean (latticeAbs v)‖ = ‖euclidean v‖ := by
  have h : ‖euclidean (latticeAbs v)‖ ^ 2 = ‖euclidean v‖ ^ 2 := by
    simp [euclidean_norm_sq, latticeAbs]
  nlinarith [norm_nonneg (euclidean v), norm_nonneg (euclidean (latticeAbs v))]

def ball {k : ℕ} (ρ : ℝ) : Set (Lattice k) := {v | ‖euclidean v‖ < ρ}

theorem ball_solid {k : ℕ} (ρ : ℝ) : Solid (ball (k := k) ρ) := by
  intro v w hw h
  have hsq : ‖euclidean v‖ ^ 2 ≤ ‖euclidean w‖ ^ 2 := by
    rw [euclidean_norm_sq, euclidean_norm_sq]
    apply Finset.sum_le_sum
    intro i _
    have hi : |(v i : ℝ)| ≤ |(w i : ℝ)| := by exact_mod_cast h i
    exact sq_le_sq.mpr hi
  have hnorm : ‖euclidean v‖ ≤ ‖euclidean w‖ := by
    nlinarith [norm_nonneg (euclidean v), norm_nonneg (euclidean w)]
  exact hnorm.trans_lt hw

def unitSign (z : ℤ) : ℤ := if 0 < z then 1 else -1

@[simp] theorem abs_unitSign (z : ℤ) : |unitSign z| = 1 := by
  unfold unitSign; split <;> norm_num

theorem unitSign_sq_step (z : ℤ) :
    ((z - unitSign z : ℤ) : ℝ) ^ 2 = (z : ℝ) ^ 2 - 2 * |(z : ℝ)| + 1 := by
  by_cases hz : 0 < z
  · have hz' : (0 : ℝ) < z := by exact_mod_cast hz
    simp [unitSign, hz, abs_of_pos hz']
    ring
  · have hz' : (z : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hz)
    simp [unitSign, hz, abs_of_nonpos hz']
    ring

def precedes {k : ℕ} (reverse : Bool) (i j : Fin k) : Prop :=
  if reverse then j < i else i < j

instance {k : ℕ} (reverse : Bool) (i j : Fin k) : Decidable (precedes reverse i j) :=
  inferInstanceAs (Decidable (if reverse then j < i else i < j))

@[simp] theorem not_precedes_self {k : ℕ} (reverse : Bool) (i : Fin k) :
    ¬ precedes reverse i i := by cases reverse <;> simp [precedes]

def prefixStep {k : ℕ} (reverse : Bool) (v : Lattice k) (j : Fin k) : Lattice k :=
  fun i => if precedes reverse i j then v i else if i = j then unitSign (v j) else 0

def tailStep {k : ℕ} (reverse : Bool) (v : Lattice k) (j : Fin k) : Lattice k :=
  v - prefixStep reverse v j

theorem prefix_add_tail {k : ℕ} (reverse : Bool) (v : Lattice k) (j : Fin k) :
    prefixStep reverse v j + tailStep reverse v j = v := by dsimp [tailStep]; abel

theorem tailStep_norm_sq_le {k : ℕ} (reverse : Bool) (v : Lattice k) (j : Fin k) :
    ‖euclidean (tailStep reverse v j)‖ ^ 2 ≤ ‖euclidean v‖ ^ 2 - 2 * |(v j : ℝ)| + 1 := by
  rw [euclidean_norm_sq, euclidean_norm_sq]
  have hj : j ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ j
  have htail : ((tailStep reverse v j j : ℤ) : ℝ) ^ 2 =
      (v j : ℝ) ^ 2 - 2 * |(v j : ℝ)| + 1 := by
    simpa [tailStep, prefixStep] using unitSign_sq_step (v j)
  calc
    ∑ i, (tailStep reverse v j i : ℝ) ^ 2 =
        (∑ i ∈ Finset.univ.erase j, (tailStep reverse v j i : ℝ) ^ 2) + (tailStep reverse v j j : ℝ) ^ 2 :=
      (Finset.sum_erase_add _ _ hj).symm
    _ ≤ (∑ i ∈ Finset.univ.erase j, (v i : ℝ) ^ 2) +
        ((v j : ℝ) ^ 2 - 2 * |(v j : ℝ)| + 1) := by
      apply add_le_add _ htail.le
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      by_cases h : precedes reverse i j
      · simpa [tailStep, prefixStep, h] using sq_nonneg (v i : ℝ)
      · simp [tailStep, prefixStep, h, hij]
    _ = (∑ i, (v i : ℝ) ^ 2) - 2 * |(v j : ℝ)| + 1 := by
      have hh := Finset.sum_erase_add (s := Finset.univ) (f := fun i : Fin k => (v i : ℝ) ^ 2) hj
      linarith

theorem prefixStep_sum_bound {k : ℕ} (hk : 1 ≤ k) (reverse : Bool) (v : Lattice k) (j : Fin k)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hsmall : ∀ i, precedes reverse i j → |(v i : ℝ)| < ρ / k) :
    (∑ i, |(prefixStep reverse v j i : ℝ)|) ≤ ((k : ℝ) - 1) * (ρ / k) + 1 := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hp : 0 ≤ ρ / k := div_nonneg hρ hk'.le
  calc
    (∑ i, |(prefixStep reverse v j i : ℝ)|) ≤ ∑ i : Fin k, if i = j then (1 : ℝ) else ρ / k := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hij : i = j
      · subst i
        simp [prefixStep, ← Int.cast_abs]
      · by_cases hi : precedes reverse i j
        · simpa [prefixStep, hi, hij] using (hsmall i hi).le
        · simpa [prefixStep, hi, hij] using hp
    _ = ((k : ℝ) - 1) * (ρ / k) + 1 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      have he : (∑ i ∈ Finset.univ.erase j, if i = j then (1 : ℝ) else ρ / k) =
          (k - 1 : ℕ) * (ρ / k) := by
        calc
          _ = ∑ _i ∈ (Finset.univ : Finset (Fin k)).erase j, ρ / k := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [(Finset.mem_erase.mp hi).1]
          _ = _ := by simp
      rw [he]
      simp [Nat.cast_sub hk]

theorem exists_extreme_large {k : ℕ} (hk : 1 ≤ k) (reverse : Bool)
    (v : Lattice k) (ρ : ℝ) (hv : ρ ≤ ‖euclidean v‖) :
    ∃ j : Fin k, ρ / k ≤ |(v j : ℝ)| ∧
      ∀ i, precedes reverse i j → |(v i : ℝ)| < ρ / k := by
  classical
  have hk0 : k ≠ 0 := by omega
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  let S : Finset (Fin k) := Finset.univ.filter fun i => ρ / k ≤ |(v i : ℝ)|
  have hS : S.Nonempty := by
    by_contra h
    have hs : ∀ i : Fin k, |(v i : ℝ)| < ρ / k := by
      intro i
      have hi : i ∉ S := fun hi => h ⟨i, hi⟩
      simpa [S] using hi
    have ht : (∑ _i : Fin k, ρ / k) = ρ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hh : (∑ i : Fin k, |(v i : ℝ)|) < ∑ _i : Fin k, ρ / k :=
      Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun i _ => hs i)
    rw [ht] at hh
    exact (not_lt_of_ge hv) ((euclidean_norm_le_sum v).trans_lt hh)
  cases reverse
  · refine ⟨S.min' hS, (Finset.mem_filter.mp (Finset.min'_mem S hS)).2, ?_⟩
    intro i hi
    change i < S.min' hS at hi
    by_contra! hn
    have hm : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn⟩
    exact (not_le_of_gt hi) (Finset.min'_le S i hm)
  · refine ⟨S.max' hS, (Finset.mem_filter.mp (Finset.max'_mem S hS)).2, ?_⟩
    intro i hi
    change S.max' hS < i at hi
    by_contra! hn
    have hm : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn⟩
    exact (not_le_of_gt hi) (Finset.le_max' S i hm)

theorem tailStep_norm_lt {k : ℕ} (hk : 1 ≤ k) (reverse : Bool) (v : Lattice k)
    (j : Fin k) (ρ : ℝ) (hρ : 2 * (k : ℝ) < ρ)
    (hlarge : ρ / k ≤ |(v j : ℝ)|)
    (hv : ‖euclidean v‖ < ρ + 1 / (2 * k)) :
    ‖euclidean (tailStep reverse v j)‖ < ρ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hρ0 : 0 < ρ := by linarith
  let α : ℝ := 1 / (2 * k)
  have hα0 : 0 < α := by dsimp [α]; positivity
  have hα1 : α ≤ 1 / 2 := by
    dsimp [α]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
    linarith
  have hrk : 2 < ρ / k := (lt_div_iff₀ hk0).mpr (by nlinarith)
  have he : (ρ + α) ^ 2 - 2 * (ρ / k) + 1 = ρ ^ 2 - ρ / k + 1 + α ^ 2 := by
    dsimp [α]
    field_simp
    ring
  have hcalc : (ρ + α) ^ 2 - 2 * (ρ / k) + 1 < ρ ^ 2 := by
    rw [he]
    nlinarith
  have hv2 : ‖euclidean v‖ ^ 2 < (ρ + α) ^ 2 := by
    change ‖euclidean v‖ < ρ + α at hv
    nlinarith [norm_nonneg (euclidean v)]
  have ht := tailStep_norm_sq_le reverse v j
  have ht2 : ‖euclidean (tailStep reverse v j)‖ ^ 2 < ρ ^ 2 := by nlinarith
  nlinarith [norm_nonneg (euclidean (tailStep reverse v j))]

theorem prefixStep_sum_lt {k : ℕ} (hk : 1 ≤ k) (reverse : Bool)
    (v : Lattice k) (j : Fin k) (ρ : ℝ) (hρ : 2 * (k : ℝ) < ρ)
    (hsmall : ∀ i, precedes reverse i j → |(v i : ℝ)| < ρ / k) :
    (∑ i, |(prefixStep reverse v j i : ℝ)|) < ρ - ρ / (2 * k) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have h := prefixStep_sum_bound hk reverse v j ρ hρ0 hsmall
  have hh : 1 < ρ / (2 * k) := (lt_div_iff₀ (by positivity)).mpr (by linarith)
  have he : ((k : ℝ) - 1) * (ρ / k) + 1 = ρ - 2 * (ρ / (2 * k)) + 1 := by
    field_simp

  rw [he] at h
  linarith

/-- A near-boundary ordered word can be split into a short initial part
and a tail strictly inside the ball. Either block order is supported. -/
theorem exists_radius_split {k : ℕ} (hk : 1 ≤ k) (reverse : Bool)
    (u v : Lattice k) (ρ : ℝ) (hρ : 2 * (k : ℝ) < ρ)
    (hu : ‖euclidean u‖ ≤ ρ / (2 * k))
    (hv : ρ ≤ ‖euclidean v‖) (hv' : ‖euclidean v‖ < ρ + 1 / (2 * k)) :
    ∃ j : Fin k,
      ‖euclidean (latticeAbs u + latticeAbs (prefixStep reverse v j))‖ < ρ ∧
      ‖euclidean (tailStep reverse v j)‖ < ρ := by
  obtain ⟨j, hj, hsmall⟩ := exists_extreme_large hk reverse v ρ hv
  refine ⟨j, ?_, tailStep_norm_lt hk reverse v j ρ hρ hj hv'⟩
  have hp := prefixStep_sum_lt hk reverse v j ρ hρ hsmall
  have hnorm : ‖euclidean (latticeAbs u + latticeAbs (prefixStep reverse v j))‖ ≤
      ‖euclidean u‖ + ‖euclidean (prefixStep reverse v j)‖ := by
    rw [euclidean_add, ← euclidean_norm_abs u, ← euclidean_norm_abs (prefixStep reverse v j)]
    exact norm_add_le _ _
  have hp' := euclidean_norm_le_sum (prefixStep reverse v j)
  linarith

end Kourovka.MetabelianEnumeration.FiniteCover.Collection
