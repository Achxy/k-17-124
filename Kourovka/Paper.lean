/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Enumeration.EpimorphismEnumeration

/-!
# The paper's main theorem

For an ordinary finite presentation `P`, Theorem 1.1 constructs a
primitive-recursive Boolean predicate `V` such that

  `DefinesMetabelian P ↔ ∃ c, V P c = true`.

A certificate supplies finite Laurent data, a dyadic margin, and a surjection
from the resulting metabelian cover onto the input group. Soundness follows
because quotients of metabelian groups are metabelian. Completeness follows
from cofinality of the finite-cover family.

## Reading order

* `Kourovka.Presentations.Presentations`: the input codes and their group semantics.
* `Kourovka.Enumeration.EpimorphismEnumeration`: the checker and its correctness.
* `Kourovka.Cofinality.Cofinality`: the geometric completeness argument.

The root `README.md` links the remaining statements of the paper to their proofs.
-/

namespace Kourovka.MetabelianEnumeration.Paper

/-- The paper's predicate `V(P, c)`, on encoded presentations and certificates. -/
abbrev certificateCheck : ℕ → ℕ → Bool := EpimorphismEnumeration.check

/-- Checking a proposed certificate is primitive recursive in both inputs. -/
theorem certificateCheck_primrec : Primrec₂ certificateCheck :=
  EpimorphismEnumeration.check_primrec

/-- Theorem 1.1: a valid presentation defines a metabelian group exactly when
some finite certificate is accepted. -/
theorem metabelian_iff_certificate (p : ℕ) :
    DefinesMetabelian p ↔ ∃ c : ℕ, certificateCheck p c = true :=
  EpimorphismEnumeration.check_correct p

/-- Ordinary finite presentations of metabelian groups are recursively enumerable. -/
theorem metabelian_presentations_re : REPred DefinesMetabelian :=
  EpimorphismEnumeration.kourovka_17_124_via_epimorphisms

end Kourovka.MetabelianEnumeration.Paper
