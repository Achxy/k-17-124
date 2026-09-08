/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Collection.CollectionFinite
import Kourovka.Collection.CollectionGeometry

/-!
# Collection Radius

Finite-radius Bieri–Strebel collection for the two word shapes used
by the presentation enumerator.
-/

namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection

variable {G : Type*} [Group G]

/-- Three-point collection is invariant under replacing either word by
another word having the same conjugation action on the relevant generator. -/
theorem collection_three_points_words {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p q : Fin a) (x y : Lattice k) (hx : x ∈ B) (hy : y ∈ B) (hxy : x + y ∈ B)
    (U V : G)
    (hU : conjugate (A q) U = conjugate (A q) (orderedWord t x))
    (hV : conjugate (A p) V⁻¹ = conjugate (A p) (orderedWord t (-y))) :
    Commute (A p) (conjugate (A q) (U * V)) := by
  have h := collection_three_points A t designated B hB ht hs p q x y hx hy hxy
  rw [conjugate_mul, commute_conjugate_iff] at h
  have he := collect_ordered_inverse_box A t designated B hB ht hs p 0 y y hy
    (by intro i; simp) (by intro i; simp)
  simp only [orderedWord_zero, one_mul, zero_sub] at he
  rw [he] at h
  rw [conjugate_mul, commute_conjugate_iff, hU, hV]
  exact h

def cutLeft {k : ℕ} (v : Lattice k) (j : Fin k) (m : ℤ) : Lattice k :=
  fun i => if i < j then v i else if i = j then m else 0

def cutRight {k : ℕ} (v : Lattice k) (j : Fin k) (m : ℤ) : Lattice k :=
  v - cutLeft v j m

/-- Split an ordered word inside any chosen block. This is an exact group
identity, without commutativity assumptions. -/
theorem orderedWord_cut {k : ℕ} (t : Fin k → G) (v : Lattice k) (j : Fin k) (m : ℤ) :
    orderedWord t v = orderedWord t (cutLeft v j m) * orderedWord t (cutRight v j m) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    cases j using Fin.lastCases with
    | last =>
      have hl : (fun i : Fin k => cutLeft v (Fin.last k) m i.castSucc) =
          fun i => v i.castSucc := by
        ext i; simp [cutLeft]
      have hr : (fun i : Fin k => cutRight v (Fin.last k) m i.castSucc) = 0 := by
        ext i; simp [cutRight, cutLeft]
      rw [orderedWord_snoc t v, orderedWord_snoc t (cutLeft v (Fin.last k) m),
        orderedWord_snoc t (cutRight v (Fin.last k) m), hl, hr]
      simp only [orderedWord_zero, one_mul]
      simp only [cutLeft, lt_self_iff_false, ↓reduceIte, cutRight, Pi.sub_apply]
      rw [mul_assoc, ← zpow_add]
      congr 2
      omega
    | cast j =>
      have hl : (fun i : Fin k => cutLeft v j.castSucc m i.castSucc) =
          cutLeft (fun i => v i.castSucc) j m := by
        ext i; simp [cutLeft]
      have hr : (fun i : Fin k => cutRight v j.castSucc m i.castSucc) =
          cutRight (fun i => v i.castSucc) j m := by
        ext i; simp [cutRight, cutLeft]
      have hlast : cutLeft v j.castSucc m (Fin.last k) = 0 := by
        have hlt : ¬ Fin.last k < j.castSucc := not_lt_of_ge (Fin.castSucc_lt_last j).le
        have hne : Fin.last k ≠ j.castSucc := ne_of_gt (Fin.castSucc_lt_last j)
        simp [cutLeft, hlt, hne]
      rw [orderedWord_snoc t v, orderedWord_snoc t (cutLeft v j.castSucc m),
        orderedWord_snoc t (cutRight v j.castSucc m), hl, hr, hlast]
      simp only [zpow_zero, mul_one, cutRight, Pi.sub_apply, hlast, sub_zero]
      rw [ih (fun i => t i.castSucc) (fun i => v i.castSucc) j, mul_assoc]
      rfl

theorem orderedWord_prefix_tail {k : ℕ} (t : Fin k → G) (v : Lattice k) (j : Fin k) :
    orderedWord t v = orderedWord t (prefixStep false v j) *
      orderedWord t (tailStep false v j) := by
  simpa [prefixStep, tailStep, precedes, cutLeft, cutRight] using
    orderedWord_cut t v j (unitSign (v j))

theorem orderedWord_tail_prefix {k : ℕ} (t : Fin k → G) (v : Lattice k) (j : Fin k) :
    orderedWord t v = orderedWord t (tailStep true v j) *
      orderedWord t (prefixStep true v j) := by
  have hl : cutLeft v j (v j - unitSign (v j)) = tailStep true v j := by
    ext i
    by_cases hij : i < j
    · have hji : ¬ j < i := by omega
      have hne : i ≠ j := by omega
      simp [cutLeft, tailStep, prefixStep, precedes, hij, hji, hne]
    · by_cases he : i = j
      · subst i; simp [cutLeft, tailStep, prefixStep, precedes]
      · have hji : j < i := by omega
        simp [cutLeft, tailStep, prefixStep, precedes, hij, hji, he]
  have hr : cutRight v j (v j - unitSign (v j)) = prefixStep true v j := by
    rw [cutRight, hl]
    dsimp [tailStep]
    abel
  simpa [hl, hr] using orderedWord_cut t v j (v j - unitSign (v j))

theorem collect_inverse {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p : Fin a) (v : Lattice k) (hv : v ∈ B) :
    conjugate (A p) (orderedWord t v)⁻¹ = conjugate (A p) (orderedWord t (-v)) := by
  simpa using collect_ordered_inverse_box A t designated B hB ht hs p 0 v v hv
    (by intro i; simp) (by intro i; simp)

@[simp] theorem neg_mem_ball {k : ℕ} (v : Lattice k) (ρ : ℝ) :
    -v ∈ ball ρ ↔ v ∈ ball ρ := by simp [ball]

theorem small_mem_ball {k : ℕ} (hk : 1 ≤ k) (u : Lattice k) (ρ : ℝ)
    (hρ : 2 * (k : ℝ) < ρ) (hu : ‖euclidean u‖ ≤ ρ / (2 * k)) : u ∈ ball ρ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < 2 * k := by linarith
  have hρ0 : 0 < ρ := by linarith
  exact hu.trans_lt ((div_lt_iff₀ hk0).mpr (by nlinarith))

theorem abs_sum_box {k : ℕ} (u v : Lattice k) (i : Fin k) :
    |(latticeAbs u + latticeAbs v) i| = |u i| + |v i| := by
  exact abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem abs_le_sum_box {k : ℕ} (u v : Lattice k) (i : Fin k) :
    |u i| ≤ |(latticeAbs u + latticeAbs v) i| := by
  rw [abs_sum_box]
  exact le_add_of_nonneg_right (abs_nonneg _)

theorem add_abs_le_sum_box {k : ℕ} (u v : Lattice k) (i : Fin k) :
    |u i + v i| ≤ |(latticeAbs u + latticeAbs v) i| := by
  rw [abs_sum_box]
  exact abs_add_le _ _

/-- The finite-radius collection statement for two ordered words. -/
theorem collection_radius {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (hk : 1 ≤ k) (ρ : ℝ)
    (hρ : 2 * (k : ℝ) < ρ)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ ball ρ → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p q : Fin a) (u v : Lattice k)
    (hu : ‖euclidean u‖ ≤ ρ / (2 * k))
    (hv : ‖euclidean v‖ < ρ + 1 / (2 * k))
    (huv : ‖euclidean (u + v)‖ < ρ) :
    Commute (A p) (conjugate (A q) (orderedWord t u * orderedWord t v)) := by
  have huB := small_mem_ball hk u ρ hρ hu
  by_cases hvB : v ∈ ball ρ
  · exact collection_three_points A t designated (ball ρ) (ball_solid ρ) ht hs
      p q u v huB hvB huv
  have hvge : ρ ≤ ‖euclidean v‖ := le_of_not_gt hvB
  obtain ⟨j, hD, hd⟩ := exists_radius_split hk false u v ρ hρ hu hvge hv
  let c := prefixStep false v j
  let d := tailStep false v j
  let D := latticeAbs u + latticeAbs c
  have hDB : D ∈ ball ρ := hD
  have hdB : d ∈ ball ρ := hd
  have hcd : c + d = v := prefix_add_tail false v j
  have huc : u + c ∈ ball ρ :=
    ball_solid ρ _ D hDB (add_abs_le_sum_box u c)
  have hsum : (u + c) + d ∈ ball ρ := by simpa only [add_assoc, hcd] using huv
  have hU := collect_ordered_box A t designated (ball ρ) (ball_solid ρ) ht hs q u c D hDB
    (abs_le_sum_box u c) (add_abs_le_sum_box u c)
  have hV := collect_inverse A t designated (ball ρ) (ball_solid ρ) ht hs p d hdB
  have h := collection_three_points_words A t designated (ball ρ) (ball_solid ρ) ht hs
    p q (u + c) d huc hdB hsum (orderedWord t u * orderedWord t c) (orderedWord t d) hU hV
  rw [orderedWord_prefix_tail t v j, ← mul_assoc]
  exact h

/-- The second finite-radius statement keeps the literal inverse words,
including their reversed block order. -/
theorem collection_radius_inverse {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (hk : 1 ≤ k) (ρ : ℝ)
    (hρ : 2 * (k : ℝ) < ρ)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ ball ρ → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p q : Fin a) (u v : Lattice k)
    (hu : ‖euclidean u‖ ≤ ρ / (2 * k))
    (hv : ‖euclidean v‖ < ρ + 1 / (2 * k))
    (huv : ‖euclidean (u + v)‖ < ρ) :
    Commute (A p) (conjugate (A q) ((orderedWord t u)⁻¹ * (orderedWord t v)⁻¹)) := by
  have huB := small_mem_ball hk u ρ hρ hu
  have hU0 := collect_inverse A t designated (ball ρ) (ball_solid ρ) ht hs q u huB
  by_cases hvB : v ∈ ball ρ
  · apply collection_three_points_words A t designated (ball ρ) (ball_solid ρ) ht hs
      p q (-u) (-v) (by simpa using huB) (by simpa using hvB)
      (by simpa only [← neg_add, neg_mem_ball] using huv)
      (orderedWord t u)⁻¹ (orderedWord t v)⁻¹ hU0
    simp
  have hvge : ρ ≤ ‖euclidean v‖ := le_of_not_gt hvB
  obtain ⟨j, hD, hd⟩ := exists_radius_split hk true u v ρ hρ hu hvge hv
  let c := prefixStep true v j
  let d := tailStep true v j
  let D := latticeAbs u + latticeAbs c
  have hDB : D ∈ ball ρ := hD
  have hdB : d ∈ ball ρ := hd
  have hcd : c + d = v := prefix_add_tail true v j
  have hstart : ∀ i, |(-u) i| ≤ |D i| := by simpa using abs_le_sum_box u c
  have hend : ∀ i, |(-u) i - c i| ≤ |D i| := by
    intro i
    simpa only [Pi.neg_apply, ← neg_add, sub_eq_add_neg, abs_neg] using add_abs_le_sum_box u c i
  have hx : -u - c ∈ ball ρ := ball_solid ρ _ D hDB hend
  have hy : -d ∈ ball ρ := by simpa using hdB
  have hsum : (-u - c) + -d ∈ ball ρ := by
    have he : (-u - c) + -d = -(u + v) := by rw [← hcd]; abel
    simpa only [he, neg_mem_ball] using huv
  have hU : conjugate (A q) ((orderedWord t u)⁻¹ * (orderedWord t c)⁻¹) =
      conjugate (A q) (orderedWord t (-u - c)) := by
    rw [conjugate_mul, hU0, ← conjugate_mul]
    exact collect_ordered_inverse_box A t designated (ball ρ) (ball_solid ρ) ht hs q
      (-u) c D hDB hstart hend
  have hV : conjugate (A p) ((orderedWord t d)⁻¹)⁻¹ =
      conjugate (A p) (orderedWord t (-(-d))) := by simp
  have h := collection_three_points_words A t designated (ball ρ) (ball_solid ρ) ht hs
    p q (-u - c) (-d) hx hy hsum
    ((orderedWord t u)⁻¹ * (orderedWord t c)⁻¹) (orderedWord t d)⁻¹ hU hV
  rw [orderedWord_tail_prefix t v j, mul_inv_rev, ← mul_assoc]
  exact h

end Kourovka.MetabelianEnumeration.FiniteCover.Collection
