/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Halfspaces.HalfspaceGeneration

/-!
# Halfspace Shift

Moving a bounded halfspace cutoff to zero by an actual kernel
conjugation.
-/

noncomputable section

namespace Kourovka.MetabelianEnumeration.SchreierHeights

open HalfspaceGeometry HalfspaceLoops
open Kourovka.Schreier.Discrete.SchreierRewriting

variable {X L : Type} [AddCommGroup L] [DecidableEq X]

omit [DecidableEq X] in
theorem negative_letter_of_nonzero (R : Set (FreeGroup X))
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) :
    ∃ z : X × Bool,
      step (χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))) z < 0 := by
  let θ := χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))
  have hn : ∃ x : X, value θ (FreeGroup.of x) ≠ 0 := by
    by_contra! hh
    have heq : θ = 1 := by
      apply FreeGroup.ext_hom
      intro x
      apply Multiplicative.toAdd.injective
      exact hh x
    apply hχ
    ext l
    obtain ⟨g, hg⟩ := hπ (Multiplicative.ofAdd l)
    obtain ⟨w, hw⟩ := PresentedGroup.mk_surjective R g
    have hz := congrArg (fun f : FreeGroup X →* Multiplicative ℝ => (f w).toAdd) heq
    simpa [θ, MonoidHom.comp_apply, hw, hg] using hz
  obtain ⟨x, hx⟩ := hn
  rcases lt_or_gt_of_ne hx with h | h
  · exact ⟨(x, true), h⟩
  · exact ⟨(x, false), by change -value θ (FreeGroup.of x) < 0; linarith⟩

omit [DecidableEq X] in
theorem path_replicate_nonpositive (θ : FreeGroup X →* Multiplicative ℝ)
    (z : X × Bool) (hz : step θ z ≤ 0) (n : ℕ) :
    PathIn (step θ) (fun x => x ≤ 0) 0 (List.replicate n z) := by
  have hgen : ∀ p : ℝ, p ≤ 0 →
      PathIn (step θ) (fun x => x ≤ 0) p (List.replicate n z) := by
    induction n with
    | zero => intro p hp; exact hp
    | succ n ih =>
      intro p hp
      exact ⟨hp, ih (p + step θ z) (by linarith)⟩
  exact hgen 0 le_rfl

omit [DecidableEq X] in
theorem exists_negative_path (R : Set (FreeGroup X))
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (μ : ℝ) :
    ∃ s : List (X × Bool),
      PathIn (letterHeight (fun x => χ (π (PresentedGroup.of x)).toAdd)) (fun h => h ≤ 0) 0 s ∧
      χ (π (PresentedGroup.mk R (FreeGroup.mk s))).toAdd + μ ≤ 0 := by
  let θ := χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))
  obtain ⟨z, hz⟩ := negative_letter_of_nonzero R π hπ χ hχ
  have hz' : 0 < -step θ z := by linarith
  obtain ⟨n, hn⟩ := exists_lt_nsmul hz' μ
  refine ⟨List.replicate n z, path_replicate_nonpositive θ z (le_of_lt hz) n, ?_⟩
  change value θ (FreeGroup.mk (List.replicate n z)) + μ ≤ 0
  rw [value_mk, List.map_replicate, List.sum_replicate]
  rw [nsmul_eq_mul] at hn ⊢
  nlinarith

omit [DecidableEq X] in
theorem lower_cutoff_to_zero (R : Set (FreeGroup X))
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (μ : ℝ)
    (hgen : Subgroup.closure (loopSet π χ PresentedGroup.of (fun h => h ≤ μ)) = ⊤) :
    Subgroup.closure (loopSet π χ PresentedGroup.of (fun h => h ≤ 0)) = ⊤ := by
  let θ := χ.toMultiplicative.comp (π.comp (PresentedGroup.mk R))
  obtain ⟨s, hs, hshift⟩ := exists_negative_path R π hπ χ hχ μ
  change PathIn (step θ) (fun h => h ≤ 0) 0 s at hs
  let v := PresentedGroup.mk R (FreeGroup.mk s)
  let e : MulAut π.ker := MulAut.conjNormal v
  apply transfer_generation e _ _ hgen
  intro n hn
  obtain ⟨w, hw, hp⟩ := hn
  change PathIn (step θ) (fun h => h ≤ μ) 0 w at hp
  refine ⟨s ++ w ++ FreeGroup.invRev s, ?_, ?_⟩
  · rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_mul, map_inv, hw]
    have heval : FreeGroup.lift (PresentedGroup.of : X → PresentedGroup R) (FreeGroup.mk s) = v :=
      (FreeGroup.lift_unique (PresentedGroup.mk R) (fun _ => rfl)).symm
    rw [heval]
    rfl
  · change PathIn (step θ) (fun h => h ≤ 0) 0 (s ++ w ++ FreeGroup.invRev s)
    have hwheight : value θ (FreeGroup.mk w) = 0 := by
      have hval : PresentedGroup.mk R (FreeGroup.mk w) = n.val := by
        rw [FreeGroup.lift_unique (PresentedGroup.mk R) (fun _ => rfl)]
        exact hw
      change χ (π (PresentedGroup.mk R (FreeGroup.mk w))).toAdd = 0
      rw [hval, n.property]
      exact χ.map_zero
    have hp' : PathIn (step θ) (fun h => h ≤ 0) (value θ (FreeGroup.mk s)) w := by
      have hh := path_shift θ (P := fun h => h ≤ μ) (Q := fun h => h ≤ 0)
        (value θ (FreeGroup.mk s)) hp (fun z hz => by
          change value θ (FreeGroup.mk s) + μ ≤ 0 at hshift
          linarith)
      simpa only [add_zero] using hh
    apply (hs.append (by simpa only [← value_mk, zero_add] using hp')).append
    have hi := path_inverse θ (fun h => h ≤ 0) 0 s hs
    simpa only [List.map_append, List.sum_append, ← value_mk, zero_add, hwheight, add_zero] using hi

/-- Both halfspaces are based at zero; the cutoff is removed by conjugation,
using the nonzero character and the actual finite generating alphabet. -/
theorem finite_presentation_zero_halfspace_generation [Fintype X]
    (R : Set (FreeGroup X)) (hRfinite : R.Finite)
    (π : PresentedGroup R →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (habelian : ∀ a b : π.ker, Commute a b) :
    Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => 0 ≤ z)) = ⊤ ∨
      Subgroup.closure (loopSet π χ PresentedGroup.of (fun z => z ≤ 0)) = ⊤ := by
  obtain ⟨μ, _, h | h⟩ := finite_presentation_halfspace_generation R hRfinite π hπ χ habelian
  · exact Or.inl h
  · exact Or.inr (lower_cutoff_to_zero R π hπ χ hχ μ h)

end Kourovka.MetabelianEnumeration.SchreierHeights
