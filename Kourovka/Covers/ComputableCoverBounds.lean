/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Covers.ComputableCoverWords

/-!
# Computable Cover Bounds

Every generated natural-alphabet cover relator uses only its announced
finite alphabet. Reduction, inversion, products and integer powers preserve
this bound.
-/

namespace Kourovka.MetabelianEnumeration.ComputableCoverBounds

open ComputableCoverData ComputableCoverWords

def bounded (n : ℕ) : Subgroup WordGroup where
  carrier := {w | ∀ letter ∈ w.toWord, letter.1 < n}
  one_mem' := by
    change ∀ letter ∈ (1 : WordGroup).toWord, letter.1 < n
    simp only [FreeGroup.toWord_one, List.not_mem_nil, false_implies, forall_const]
  mul_mem' := by
    intro x y hx hy letter hletter
    rcases List.mem_append.mp ((FreeGroup.toWord_mul_sublist x y).subset hletter) with h | h
    · exact hx letter h
    · exact hy letter h
  inv_mem' := by
    intro x hx letter hletter
    rw [FreeGroup.toWord_inv] at hletter
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hletter)
    exact hx z hz

theorem of_mem {n i : ℕ} (h : i < n) : FreeGroup.of i ∈ bounded n := by
  intro letter hletter
  obtain rfl := List.mem_singleton.mp (FreeGroup.toWord_of i ▸ hletter)
  exact h

theorem conjugate_mem {n : ℕ} {x w : WordGroup} (hx : x ∈ bounded n)
    (hw : w ∈ bounded n) : FiniteCover.conjugate x w ∈ bounded n :=
  (bounded n).mul_mem ((bounded n).mul_mem ((bounded n).inv_mem hw) hx) hw

theorem rightComm_mem {n : ℕ} {x y : WordGroup} (hx : x ∈ bounded n)
    (hy : y ∈ bounded n) : FiniteCover.rightComm x y ∈ bounded n :=
  (bounded n).mul_mem ((bounded n).mul_mem
    ((bounded n).mul_mem ((bounded n).inv_mem hx) ((bounded n).inv_mem hy)) hx) hy

theorem ordered_mem {k n : ℕ} (hk : k ≤ n) (v : List ℤ) : ordered k v ∈ bounded n := by
  apply (bounded n).list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact (bounded n).zpow_mem (of_mem ((List.mem_range.mp hi).trans_le hk)) _

theorem polynomial_mem {k n : ℕ} (hk : k ≤ n) {x : WordGroup}
    (hx : x ∈ bounded n) (p : PolynomialCode) : polynomial k x p ∈ bounded n := by
  apply (bounded n).list_prod_mem
  intro w hw
  obtain ⟨term, _, rfl⟩ := List.mem_map.mp hw
  apply conjugate_mem ((bounded n).zpow_mem hx _)
  cases p.1
  · exact (bounded n).inv_mem (ordered_mem hk _)
  · exact ordered_mem hk _

theorem relators_mem (data : DatumCode) (R : ℕ) :
    ∀ w ∈ relators data R, w ∈ bounded (dimension data + alphabet data) := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
      have hi' := List.mem_range.mp hi
      have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
      apply (bounded _).mul_mem
      · exact rightComm_mem (of_mem (by omega)) (of_mem (by omega))
      · apply (bounded _).inv_mem
        apply of_mem
        exact Nat.add_lt_add_left (Nat.mod_lt _ (Nat.succ_pos _)) _
    · obtain ⟨i, hi, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨j, hj, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
      have hi' := List.mem_range.mp hi
      have hj' := List.mem_range.mp hj
      apply rightComm_mem (of_mem (by omega))
      exact conjugate_mem (of_mem (by omega)) (ordered_mem (Nat.le_add_right _ _) _)
  · obtain ⟨i, hi, hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hw
    have hi' := List.mem_range.mp hi
    have hx := of_mem (n := dimension data + alphabet data)
      (i := dimension data + i) (by omega)
    exact (bounded _).mul_mem ((bounded _).inv_mem hx)
      (polynomial_mem (Nat.le_add_right _ _) hx p)

theorem presentation_wellFormed (data : DatumCode) (R : ℕ) :
    WellFormed (presentation data R) := by
  intro w hw
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
  exact relators_mem data R r hr

end Kourovka.MetabelianEnumeration.ComputableCoverBounds
