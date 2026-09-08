/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Halfspaces.SchreierKernel

/-!
# Schreier Paths

Actual words realizing halfspace Schreier generators.
-/

namespace Kourovka.MetabelianEnumeration.SchreierHeights

open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal

variable {X : Type*}

abbrev step (θ : FreeGroup X →* Multiplicative ℝ) : X × Bool → ℝ :=
  letterHeight fun x => value θ (FreeGroup.of x)

theorem path_inverse (θ : FreeGroup X →* Multiplicative ℝ) (P : ℝ → Prop)
    (p : ℝ) (xs : List (X × Bool)) (h : PathIn (step θ) P p xs) :
    PathIn (step θ) P (p + value θ (FreeGroup.mk xs)) (FreeGroup.invRev xs) := by
  induction xs generalizing p with
  | nil =>
    change P (p + value θ 1)
    simpa using h
  | cons z xs ih =>
    rcases z with ⟨x, b⟩
    rw [FreeGroup.invRev_cons]
    apply PathIn.append
    · have hh := ih (p + step θ (x, b)) h.2
      cases b <;> simpa [step, letterHeight, mk_cons_false, mk_cons_true, add_assoc] using hh
    · rw [← value_mk, ← FreeGroup.inv_mk, value_inv]
      cases b <;>
        simpa [FreeGroup.invRev, PathIn, step, letterHeight, mk_cons_false, mk_cons_true,
          add_assoc] using And.intro h.2.start h.1

theorem path_shift (θ : FreeGroup X →* Multiplicative ℝ) {P Q : ℝ → Prop}
    (c : ℝ) {p : ℝ} {xs : List (X × Bool)} (h : PathIn (step θ) P p xs)
    (hc : ∀ z, P z → Q (c + z)) : PathIn (step θ) Q (c + p) xs := by
  induction xs generalizing p with
  | nil => exact hc p h
  | cons x xs ih =>
    exact ⟨hc p h.1, by simpa only [add_assoc] using ih h.2⟩

/-- The standard Schreier generator is represented by the outgoing section
path, its edge, and the returning section path. -/
def generatorWord [DecidableEq X] {L : Subgroup (FreeGroup X)}
    (S : Transversal L) (z : S.Edge) :
    List (X × Bool) :=
  z.1.val.toWord ++ [(z.2, true)] ++
    FreeGroup.invRev (S.rep (z.1.val * FreeGroup.of z.2)).toWord

@[simp] theorem generatorWord_eval [DecidableEq X] {L : Subgroup (FreeGroup X)}
    (S : Transversal L) (z : S.Edge) :
    FreeGroup.mk (generatorWord S z) = S.edgeValue z := by
  simp only [generatorWord, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, FreeGroup.mk_toWord]
  rfl

theorem generatorWord_path [DecidableEq X] {L : Subgroup (FreeGroup X)}
    (θ : FreeGroup X →* Multiplicative ℝ) (S : Transversal L)
    (hheight : ∀ w, value θ (S.rep w) = value θ w)
    (P : ℝ → Prop) (z : S.Edge)
    (hz : z ∈ symbolsIn θ S P)
    (hfrom : PathIn (step θ) P 0 z.1.val.toWord)
    (hto : PathIn (step θ) P 0 (S.rep (z.1.val * FreeGroup.of z.2)).toWord) :
    PathIn (step θ) P 0 (generatorWord S z) := by
  unfold generatorWord
  rw [pathIn_append_iff, pathIn_append_iff]
  refine ⟨⟨hfrom, ?_⟩, ?_⟩
  · rw [← value_mk, FreeGroup.mk_toWord, zero_add]
    change P (value θ z.1.val) ∧ P (value θ z.1.val + value θ (FreeGroup.of z.2))
    simpa only [symbolsIn, Set.mem_setOf_eq, value_mul] using hz
  · have hp := path_inverse θ P 0 _ hto
    simpa only [List.map_append, List.sum_append, ← value_mk, FreeGroup.mk_toWord, hheight, zero_add, List.map_singleton,
      List.sum_singleton, step, letterHeight, if_true, value_mul] using hp

end Kourovka.MetabelianEnumeration.SchreierHeights
