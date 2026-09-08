/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Halfspaces.SchreierHeights
import Kourovka.Schreier.KernelPresentation

/-!
# Halfspace Relators

Every relator of the Schreier presentation is confined
to one of the two overlapping halfspaces.
-/

namespace Kourovka.MetabelianEnumeration.SchreierHeights

open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal

variable {X Q : Type*} [CommGroup Q]

theorem pathIn_length_bound (f : X → ℝ) (D p : ℝ) (xs : List X)
    (hD0 : 0 ≤ D) (hD : ∀ x ∈ xs, |f x| ≤ D) :
    PathIn f (fun z => p - xs.length * D ≤ z ∧ z ≤ p + xs.length * D) p xs := by
  induction xs generalizing p with
  | nil => simp [PathIn]
  | cons x xs ih =>
    have hx := abs_le.mp (hD x List.mem_cons_self)
    have ht := ih (p + f x) (fun y hy => hD y (List.mem_cons_of_mem _ hy))
    constructor
    · have : (0 : ℝ) ≤ (x :: xs).length * D := mul_nonneg (Nat.cast_nonneg _) hD0
      exact ⟨by linarith, by linarith⟩
    · apply ht.mono
      intro z hz
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      constructor <;> nlinarith

theorem symbols_cover (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (D μ : ℝ)
    (hD : ∀ x, |value (χ.comp π) (FreeGroup.of x)| ≤ D) (hμ : D ≤ μ)
    (z : S.Edge) :
    z ∈ symbolsIn (χ.comp π) S (fun x => 0 ≤ x) ∨
      z ∈ symbolsIn (χ.comp π) S (fun x => x ≤ μ) := by
  change (0 ≤ value (χ.comp π) z.1.val ∧ 0 ≤ value (χ.comp π)
    (z.1.val * FreeGroup.of z.2)) ∨ _
  by_cases h : 0 ≤ value (χ.comp π) z.1.val ∧ 0 ≤ value (χ.comp π)
      (z.1.val * FreeGroup.of z.2)
  · exact Or.inl h
  · right
    change value (χ.comp π) z.1.val ≤ μ ∧ value (χ.comp π)
      (z.1.val * FreeGroup.of z.2) ≤ μ
    rw [value_mul] at h ⊢
    have hb := abs_le.mp (hD z.2)
    push_neg at h
    constructor <;> by_contra! hh <;> have := h (by linarith) <;> linarith

/-- Lifted defining relators and section-path relators are each confined
to one of the two overlapping halfspaces. -/
theorem augmented_relators_one_side [DecidableEq X]
    (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (R : Set (FreeGroup X))
    (D B μ : ℝ) (hD0 : 0 ≤ D) (hDB : D ≤ B) (hμ : 2 * B ≤ μ)
    (hD : ∀ x, |value (χ.comp π) (FreeGroup.of x)| ≤ D)
    (hR : ∀ r ∈ R, (r.toWord.length : ℝ) * D ≤ B)
    (hsafe : ∀ t : S.vertices,
      PathIn (letterHeight fun x => value (χ.comp π) (FreeGroup.of x))
        (fun z => min 0 (value (χ.comp π) t.val) ≤ z ∧
          z ≤ max μ (value (χ.comp π) t.val)) 0 t.val.toWord)
    (r : FreeGroup (S.Edge))
    (hr : r ∈ S.relators R) :
    r ∈ Subgroup.closure (FreeGroup.of '' symbolsIn (χ.comp π) S (fun z => 0 ≤ z)) ∨
      r ∈ Subgroup.closure (FreeGroup.of '' symbolsIn (χ.comp π) S (fun z => z ≤ μ)) := by
  rcases hr with hr | hr
  · obtain ⟨t, w, hw, rfl⟩ := hr
    have hp := pathIn_length_bound
      (letterHeight fun x => value (χ.comp π) (FreeGroup.of x)) D
      (value (χ.comp π) t.val) w.toWord hD0 (by
        rintro ⟨x, b⟩ _
        cases b <;> simpa only [letterHeight, Bool.false_eq_true, if_false, if_true, abs_neg]
          using hD x)
    have hb := hR w hw
    by_cases hlo : B ≤ value (χ.comp π) t.val
    · left
      rw [S.rewrite_eq_word]
      apply rewrite_mem_closure
      apply hp.mono
      intro z hz
      linarith [hz.1]
    · right
      rw [S.rewrite_eq_word]
      apply rewrite_mem_closure
      apply hp.mono
      intro z hz
      linarith [hz.2]
  · obtain ⟨t, rfl⟩ := hr
    dsimp only
    have hp := hsafe t
    by_cases ht : 0 ≤ value (χ.comp π) t.val
    · left
      rw [S.rewrite_eq_word]
      apply rewrite_mem_closure
      rw [value_one]
      apply hp.mono
      intro z hz
      simpa only [min_eq_left ht] using hz.1
    · right
      rw [S.rewrite_eq_word]
      apply rewrite_mem_closure
      rw [value_one]
      apply hp.mono
      intro z hz
      have hμ0 : 0 ≤ μ := by linarith
      simpa only [max_eq_left (by linarith : value (χ.comp π) t.val ≤ μ)] using hz.2

end Kourovka.MetabelianEnumeration.SchreierHeights
