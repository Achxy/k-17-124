/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Halfspaces.HalfspaceShift
import Kourovka.Halfspaces.HalfspaceLoopModule

/-!
# Bieri Strebel Necessity

The finite-presentation necessity direction of the Bieri–Strebel theorem.
The proof uses the actual Schreier kernel presentation, the two-halfspace
Britton obstruction, and the actual conjugation module of the kernel.
-/

noncomputable section

namespace Kourovka.MetabelianEnumeration.BieriStrebelNecessity

open HalfspaceGeometry HalfspaceLoops SchreierHeights ValuationModule
open CommutatorModule SignedTameness

variable {X E L : Type} [Group E] [AddCommGroup L]

private theorem path_neg {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs : List X}
    (h : PathIn f P p xs) : PathIn (fun x => -f x) (fun z => P (-z)) (-p) xs := by
  induction xs generalizing p with
  | nil => simpa [PathIn] using h
  | cons x xs ih =>
    constructor
    · simpa using h.1
    · simpa only [neg_add_rev, add_comm] using ih h.2

theorem upper_loops_eq_negative_lower (π : E →* Multiplicative L)
    (χ : L →+ ℝ) (g : X → E) :
    loopSet π χ g (fun z => 0 ≤ z) = loopSet π (-χ) g (fun z => z ≤ 0) := by
  have hstep : letterHeight (fun x => (-χ) (π (g x)).toAdd) =
      fun z => -letterHeight (fun x => χ (π (g x)).toAdd) z := by
    funext z
    rcases z with ⟨x, b⟩
    cases b <;> simp [letterHeight]
  ext n
  constructor
  · rintro ⟨w, hw, hp⟩
    refine ⟨w, hw, ?_⟩
    rw [hstep]
    simpa only [neg_zero, neg_nonneg] using path_neg hp
  · rintro ⟨w, hw, hp⟩
    refine ⟨w, hw, ?_⟩
    rw [hstep] at hp
    simpa only [neg_neg, neg_zero, neg_nonpos] using path_neg hp

/-- Transport the actual quotient kernel through a group isomorphism. -/
def kernelEquiv {G : Type} [Group G] (e : G ≃* E) (π : E →* Multiplicative L) :
    (π.comp e.toMonoidHom).ker ≃* π.ker where
  toFun n := ⟨e n.val, n.property⟩
  invFun n := ⟨e.symm n.val, by
    change π (e (e.symm n.val)) = 1
    rw [e.apply_symm_apply]
    exact n.property⟩
  left_inv n := Subtype.ext (e.symm_apply_apply n.val)
  right_inv n := Subtype.ext (e.apply_symm_apply n.val)
  map_mul' a b := Subtype.ext (e.map_mul a.val b.val)

theorem kernel_loop_transport {G : Type} [Group G] (e : G ≃* E)
    (π : E →* Multiplicative L) (χ : L →+ ℝ) (g : X → G) (P : ℝ → Prop)
    (n : (π.comp e.toMonoidHom).ker) (hn : n ∈ loopSet (π.comp e.toMonoidHom) χ g P) :
    kernelEquiv e π n ∈ loopSet π χ (fun x => e (g x)) P := by
  obtain ⟨w, hw, hp⟩ := hn
  refine ⟨w, ?_, hp⟩
  have hh : FreeGroup.lift (fun x => e (g x)) = e.toMonoidHom.comp (FreeGroup.lift g) := by
    apply FreeGroup.ext_hom
    intro x
    simp
  rw [hh, MonoidHom.comp_apply, hw]
  rfl

/-- The halfspace-generation conclusion is invariant under the chosen finite
ordinary presentation of the group. -/
theorem zero_halfspace_generation [DecidableEq X] [Fintype X]
    (R : Set (FreeGroup X)) (hR : R.Finite) (e : PresentedGroup R ≃* E)
    (π : E →* Multiplicative L) (hπ : Function.Surjective π)
    (χ : L →+ ℝ) (hχ : χ ≠ 0) [IsMulCommutative π.ker] :
    Subgroup.closure (loopSet π χ (fun x : X => e (PresentedGroup.of x)) (fun z => 0 ≤ z)) = ⊤ ∨
      Subgroup.closure (loopSet π χ (fun x : X => e (PresentedGroup.of x)) (fun z => z ≤ 0)) = ⊤ := by
  let π₀ := π.comp e.toMonoidHom
  let ek := kernelEquiv e π
  have hab : ∀ a b : π₀.ker, Commute a b := by
    intro a b
    apply (commute_map_iff ek.injective).mp
    exact mul_comm _ _
  have h := finite_presentation_zero_halfspace_generation R hR π₀
    (hπ.comp e.surjective) χ hχ hab
  have ht (P : ℝ → Prop) (hgen : Subgroup.closure (loopSet π₀ χ PresentedGroup.of P) = ⊤) :
      Subgroup.closure (loopSet π χ (fun x : X => e (PresentedGroup.of x)) P) = ⊤ :=
    transfer_generation ek _ _ hgen (kernel_loop_transport e π χ PresentedGroup.of P)
  exact h.imp (ht _) (ht _)

/-- Genuine finite presentation implies directional finiteness on at least
one side of every nonzero character for the actual Laurent conjugation action.
The full-ring finite-generation input is independently obtained from finite
normal kernel generators. -/
theorem signed_finite [DecidableEq X] [Fintype X] [DecidableEq L]
    (R : Set (FreeGroup X)) (hR : R.Finite) (e : PresentedGroup R ≃* E)
    (π : E →* Multiplicative L) (hπ : Function.Surjective π)
    [IsMulCommutative π.ker] (χ : L →+ ℝ) (hχ : χ ≠ 0) :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative L))
    Module.Finite (GroupRing L) (Additive π.ker) →
    Module.Finite (nonnegativeRing χ) (Additive π.ker) ∨
      Module.Finite (nonnegativeRing (-χ)) (Additive π.ker) := by
  letI := laurentModule π hπ (MonoidHom.id (Multiplicative L))
  intro hf
  obtain h | h := zero_halfspace_generation R hR e π hπ χ hχ
  · right
    rw [upper_loops_eq_negative_lower] at h
    exact finite_of_lower_loops_laurent π (-χ) (neg_ne_zero.mpr hχ) hπ _ hf h
  · left
    exact finite_of_lower_loops_laurent π χ hχ hπ _ hf h

/-- The actual Bieri–Strebel tameness property for a lattice quotient. -/
theorem tame_of_finite_presentation {k : ℕ} [DecidableEq X] [Fintype X]
    (R : Set (FreeGroup X)) (hR : R.Finite) (e : PresentedGroup R ≃* E)
    (π : E →* Multiplicative (FiniteCover.Lattice k)) (hπ : Function.Surjective π)
    [IsMulCommutative π.ker] :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative (FiniteCover.Lattice k)))
    Module.Finite (GroupRing (FiniteCover.Lattice k)) (Additive π.ker) →
      Tame (k := k) (Additive π.ker) := by
  letI := laurentModule π hπ (MonoidHom.id (Multiplicative (FiniteCover.Lattice k)))
  intro hf x hx
  exact signed_finite R hR e π hπ (character x) (character_ne_zero hx) hf

end Kourovka.MetabelianEnumeration.BieriStrebelNecessity
