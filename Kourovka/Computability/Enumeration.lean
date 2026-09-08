/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Mathlib.Computability.Halting
import Mathlib.Tactic

/-!
# Recursive enumerability from finite certificates

The search below is unbounded only when the input has no certificate.
`recursively_enumerable_of_certificates` proves the general computability reduction;
the application to metabelian groups is in `Kourovka.Paper`.
-/

namespace Kourovka.MetabelianEnumeration

/-- Search all certificates below the supplied bound. -/
def boundedSearch (check : ℕ → ℕ → Bool) (presentation bound : ℕ) : Bool :=
  (List.range bound).any (check presentation)

theorem boundedSearch_iff (check : ℕ → ℕ → Bool) (p n : ℕ) :
    boundedSearch check p n = true ↔ ∃ c < n, check p c = true := by
  simp [boundedSearch, List.any_eq_true, List.mem_range]

theorem boundedSearch_sound (check : ℕ → ℕ → Bool) (P : ℕ → Prop)
    (sound : ∀ p c, check p c = true → P p) (p n : ℕ)
    (h : boundedSearch check p n = true) : P p := by
  obtain ⟨c, _, hc⟩ := (boundedSearch_iff check p n).mp h
  exact sound p c hc

theorem boundedSearch_complete (check : ℕ → ℕ → Bool) (P : ℕ → Prop)
    (complete : ∀ p, P p → ∃ c, check p c = true) (p : ℕ) (hp : P p) :
    ∃ n, boundedSearch check p n = true := by
  obtain ⟨c, hc⟩ := complete p hp
  exact ⟨c + 1, (boundedSearch_iff check p (c + 1)).mpr ⟨c, by omega, hc⟩⟩

/-- Explicit proof of recursive enumerability from a computable, sound and
complete certificate predicate. Instantiating this with Bieri--Strebel
certificates is a separate obligation. -/
theorem recursively_enumerable_of_certificates
    (check : ℕ → ℕ → Bool) (hc : Computable₂ check) (P : ℕ → Prop)
    (correct : ∀ p, P p ↔ ∃ c, check p c = true) : REPred P := by
  have hp : Partrec (fun p => Nat.rfind (fun c => (check p c : Part Bool))) :=
    Partrec.rfind hc.partrec.to₂
  apply hp.dom_re.of_eq
  intro p
  rw [Nat.rfind_dom, correct]
  simp

end Kourovka.MetabelianEnumeration
