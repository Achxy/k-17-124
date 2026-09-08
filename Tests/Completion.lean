import Kourovka.Paper
import Kourovka.Enumeration.Main

open Kourovka.MetabelianEnumeration

/-!
# Completion checks

The main group property is expanded here without `MainClaim`,
`DefinesMetabelian`, `WellFormed`, `GroupOf`, or `Metabelian`.
This checks that the exported result speaks about ordinary presented groups
and the identity `[a,b][c,d] = [c,d][a,b]` for all group elements.
-/

example : REPred (fun n : ℕ =>
    let p := decodePresentation n
    (∀ w ∈ p.2, ∀ letter ∈ w, letter.1 < p.1) ∧
      ∀ a b c d : PresentedGroup {r | r ∈ p.2.map (interpretWord p.1)},
        ⁅a, b⁆ * ⁅c, d⁆ = ⁅c, d⁆ * ⁅a, b⁆) :=
  kourovka_17_124

example : Primrec₂ ComputableEnumeration.check := ComputableEnumeration.check_primrec

example (p : ℕ) :
    DefinesMetabelian p ↔ ∃ c, ComputableEnumeration.check p c = true :=
  ComputableEnumeration.check_correct p

#print axioms Kourovka.MetabelianEnumeration.kourovka_17_124

/- The shorter certificate route checks only a finite cover and an epimorphism. -/
example : REPred (fun n : ℕ =>
    let p := decodePresentation n
    (∀ w ∈ p.2, ∀ letter ∈ w, letter.1 < p.1) ∧
    ∀ a b c d : PresentedGroup {r | r ∈ p.2.map (interpretWord p.1)},
      ⁅a, b⁆ * ⁅c, d⁆ = ⁅c, d⁆ * ⁅a, b⁆) :=
  EpimorphismEnumeration.kourovka_17_124_via_epimorphisms

example : Primrec₂ EpimorphismEnumeration.check :=
  EpimorphismEnumeration.check_primrec

example (p : ℕ) : DefinesMetabelian p ↔ ∃ c, EpimorphismEnumeration.check p c = true :=
  EpimorphismEnumeration.check_correct p

#print axioms Kourovka.MetabelianEnumeration.EpimorphismEnumeration.kourovka_17_124_via_epimorphisms
