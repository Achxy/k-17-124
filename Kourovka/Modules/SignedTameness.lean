/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Modules.ValuationModule

/-!
# Signed Tameness

From directional module finiteness to finitely many signed centralizer
polynomials. Tameness here retains its mathematical module-finiteness meaning;
the claim that ordinary finite presentation implies tameness is separate.
-/

noncomputable section

namespace Kourovka.MetabelianEnumeration.SignedTameness

open FiniteCover ConeVerifier ValuationModule TamenessCompactness

def character {k : ℕ} (x : Fin k → ℝ) : Lattice k →+ ℝ where
  toFun u := ∑ i, x i * (u i : ℝ)
  map_zero' := by simp
  map_add' u v := by simp [mul_add, Finset.sum_add_distrib]

theorem character_ne_zero {k : ℕ} {x : Fin k → ℝ} (hx : x ≠ 0) : character x ≠ 0 := by
  intro h
  apply hx
  funext i
  have hi := DFunLike.congr_fun h (Pi.single i 1)
  simpa [character, Pi.single_apply, mul_ite] using hi

abbrev SignedPolynomial (k : ℕ) := Bool × GroupRing (Lattice k)

def signedSupport {k : ℕ} (p : SignedPolynomial k) : List (Vec k) :=
  p.2.support.toList.map fun u => fun i => if p.1 then (u i : ℚ) else -(u i : ℚ)

variable {k : ℕ} {M : Type*} [AddCommGroup M] [Module (GroupRing (Lattice k)) M]

def Tame (M : Type*) [AddCommGroup M] [Module (GroupRing (Lattice k)) M] : Prop :=
  ∀ x : Fin k → ℝ, x ≠ 0 →
    Module.Finite (nonnegativeRing (character x)) M ∨
    Module.Finite (nonnegativeRing (-character x)) M

theorem positive_signed_support {x : Fin k → ℝ} (p : GroupRing (Lattice k))
    (hp : ∀ u ∈ p.support, 0 < character x u) :
    ∀ u ∈ signedSupport (true, p), 0 < dot u x := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  simpa [dot, character, mul_comm] using hp v (Finset.mem_toList.mp hv)

theorem negative_signed_support {x : Fin k → ℝ} (p : GroupRing (Lattice k))
    (hp : ∀ u ∈ p.support, 0 < (-character x) u) :
    ∀ u ∈ signedSupport (false, p), 0 < dot u x := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
  simpa [dot, character, mul_comm, Finset.sum_neg_distrib] using hp v (Finset.mem_toList.mp hv)

/-- Compactness converts the directional criterion into a finite signed
centralizer family, preserving the action of every selected Laurent polynomial. -/
theorem finite_signed_centralizers [Module.Finite (GroupRing (Lattice k)) M]
    (ht : Tame (k := k) M) :
    ∃ ps : List (SignedPolynomial k),
      (∀ p ∈ ps, ∀ m : M, p.2 • m = m) ∧ ConeCover (ps.map signedSupport) := by
  apply finite_support_selection signedSupport (fun p => ∀ m : M, p.2 • m = m)
  intro x hx
  rcases ht x hx with hp | hn
  · letI := hp
    obtain ⟨p, hpos, hact⟩ := positive_centralizer_of_finite (M := M)
      (character x) (character_ne_zero hx)
    exact ⟨(true, p), hact, positive_signed_support p hpos⟩
  · letI := hn
    obtain ⟨p, hpos, hact⟩ := positive_centralizer_of_finite (M := M)
      (-character x) (neg_ne_zero.mpr (character_ne_zero hx))
    exact ⟨(false, p), hact, negative_signed_support p hpos⟩

end Kourovka.MetabelianEnumeration.SignedTameness
