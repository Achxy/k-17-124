/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Collection.CollectionGeometry
import Kourovka.Modules.TamenessCompactness

/-!
# Cover Margin

Rational numerical data extracted from an accepted finite cone cover.
-/

namespace Kourovka.MetabelianEnumeration.FiniteCover

open Collection ConeVerifier TamenessCompactness

def supportLength {k : ℕ} (v : Lattice k) : ℚ := ∑ i, |(v i : ℚ)|

def supportLengths {k a : ℕ} (data : Datum k a) : List ℚ :=
  data.polynomials.flatMap fun p => p.2.map fun term => supportLength term.1

def supportBound {k a : ℕ} (data : Datum k a) : ℚ := 1 + (supportLengths data).sum

theorem supportLength_nonneg {k : ℕ} (v : Lattice k) : 0 ≤ supportLength v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem supportLengths_nonneg {k a : ℕ} (data : Datum k a) :
    ∀ x ∈ supportLengths data, 0 ≤ x := by
  intro x hx
  obtain ⟨p, _, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨term, _, rfl⟩ := List.mem_map.mp hx
  exact supportLength_nonneg term.1

theorem supportBound_ge_one {k a : ℕ} (data : Datum k a) : 1 ≤ supportBound data := by
  have h := List.sum_nonneg (supportLengths_nonneg data)
  dsimp [supportBound]
  linarith

theorem supportBound_norm {k a : ℕ} (data : Datum k a) :
    ∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ (supportBound data : ℝ) := by
  intro p hp term ht
  have hmem : supportLength term.1 ∈ supportLengths data :=
    List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨term, ht, rfl⟩⟩
  have h := List.single_le_sum (supportLengths_nonneg data) _ hmem
  have hlen : supportLength term.1 ≤ supportBound data := by dsimp [supportBound]; linarith
  dsimp [supportLength] at hlen
  have hlen' : (∑ i, |(term.1 i : ℝ)|) ≤ (supportBound data : ℝ) := by
    exact_mod_cast hlen
  exact (euclidean_norm_le_sum term.1).trans hlen'

theorem inner_lattice {k : ℕ} (v u : Lattice k) :
    inner ℝ (euclidean v) (euclidean u) = ∑ i, (u i : ℝ) * (v i : ℝ) := by
  simp [PiLp.inner_apply, euclidean, mul_comm]

/-- A positive cube margin gives a homogeneous Euclidean shrinking margin.
The factor k uses the elementary bound of the Euclidean norm by the 1-norm. -/
theorem cube_margin_direction {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k)
    (ε : ℚ) (hε : 0 < ε)
    (hm : CubeMargin (data.polynomials.map polynomialSupport) ε) :
    ∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
      ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤
        -((ε / k : ℚ) : ℝ) * ‖euclidean v‖ := by
  intro v hv
  let x : Fin k → ℝ := fun i => -(v i : ℝ)
  have hx : x ≠ 0 := by
    intro h
    apply hv
    ext i
    have hi := congrFun h i
    dsimp [x] at hi
    exact_mod_cast (show (v i : ℝ) = 0 by simpa using hi)
  obtain ⟨c, hc, hcube⟩ := normalize_to_cube x hx
  obtain ⟨support, hs, hpos⟩ := hm (fun i => x i / c) hcube
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
  refine ⟨p, hp, ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hε0 : (0 : ℝ) < ε := by exact_mod_cast hε
  have hcoord : ∀ i, |(v i : ℝ)| ≤ c := by
    intro i
    have hi := hcube.1 i
    have h := abs_le.mpr hi
    rw [abs_div, abs_of_pos hc] at h
    have h' := (div_le_one hc).mp h
    simpa [x] using h'
  have hnorm : ‖euclidean v‖ ≤ (k : ℝ) * c := by
    apply (euclidean_norm_le_sum v).trans
    calc
      (∑ i, |(v i : ℝ)|) ≤ ∑ _i : Fin k, c := Finset.sum_le_sum (fun i _ => hcoord i)
      _ = _ := by simp
  intro term ht
  have hterm := hpos (fun i => (term.1 i : ℚ)) (List.mem_map.mpr ⟨term, ht, rfl⟩)
  rw [dot_div] at hterm
  have he : dot (fun i => (term.1 i : ℚ)) x =
      -inner ℝ (euclidean v) (euclidean term.1) := by
    simp [dot, x, inner_lattice, Finset.sum_neg_distrib]
  rw [he] at hterm
  have hdot := (lt_div_iff₀ hc).mp hterm
  have hm : (ε : ℝ) / k * ‖euclidean v‖ ≤ (ε : ℝ) * c := by
    calc
      _ ≤ (ε : ℝ) / k * ((k : ℝ) * c) :=
        mul_le_mul_of_nonneg_left hnorm (div_nonneg hε0.le hk0.le)
      _ = _ := by field_simp
  push_cast
  nlinarith

/-- Every accepted cone cover supplies positive rational margins and a
rational bound for all support lengths. -/
theorem cone_cover_numerical_data {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k)
    (hc : ConeCover (data.polynomials.map polynomialSupport)) :
    ∃ C D : ℚ, 0 < C ∧ 1 ≤ D ∧ C ≤ D ∧
      (∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ (D : ℝ)) ∧
      (∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
        ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤ -(C : ℝ) * ‖euclidean v‖) := by
  obtain ⟨r, hr⟩ := dyadic_margin_search_terminates _ hc
  let ε : ℚ := (1 / 2) ^ r
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  let C : ℚ := min (ε / k) 1
  let D := supportBound data
  have hC : 0 < C := lt_min (div_pos hε hk0) (by norm_num)
  have hD : 1 ≤ D := supportBound_ge_one data
  refine ⟨C, D, hC, hD, (min_le_right _ _).trans hD, supportBound_norm data, ?_⟩
  intro v hv
  obtain ⟨p, hp, hdir⟩ := cube_margin_direction data hk ε hε
    ((checkMargin_correct _ _).mp hr) v hv
  refine ⟨p, hp, ?_⟩
  intro term ht
  have hCle : (C : ℝ) ≤ ((ε / k : ℚ) : ℝ) := by exact_mod_cast (min_le_left (ε / k) 1)
  exact (hdir term ht).trans (by nlinarith [norm_nonneg (euclidean v)])

end Kourovka.MetabelianEnumeration.FiniteCover
