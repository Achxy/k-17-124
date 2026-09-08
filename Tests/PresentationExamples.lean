/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Paper

/-!
# Reading and checking small presentations

Generator indices begin at zero. The first examples distinguish a valid alphabet
from an out-of-range generator. The final examples exercise the zero-generator
branch and show that every certificate for a malformed input is rejected.
All assertions below are proved by the Lean kernel.
-/

namespace Kourovka.MetabelianEnumeration.PresentationExamples

/-- The ordinary presentation with one generator and no relators. -/
def infiniteCyclic : PresentationCode := (1, [])

/-- The relation is `x₀² = 1`, with both letters in the declared alphabet. -/
def cyclicOrderTwo : PresentationCode := (1, [[(0, true), (0, true)]])

/-- The letter `x₁` is outside a one-generator alphabet. -/
def malformed : PresentationCode := (1, [[(1, true)]])

example : WellFormed infiniteCyclic := by decide +kernel
example : WellFormed cyclicOrderTwo := by decide +kernel
example : ¬ WellFormed malformed := by decide +kernel

/-- Every finite input presentation survives its own encode-decode round trip. -/
example : decodePresentation (Encodable.encode cyclicOrderTwo) = cyclicOrderTwo :=
  decode_encode_presentation cyclicOrderTwo

/-- The empty presentation has a certificate without needing a positive-rank cover. -/
example : EpimorphismEnumeration.checkData (0, [])
    EpimorphismEnumeration.defaultCertificate = true := by
  decide +kernel

/-- No choice of certificate can bypass the alphabet check. -/
example (certificate : EpimorphismEnumeration.Certificate) :
    EpimorphismEnumeration.checkData malformed certificate = false := by
  simp [EpimorphismEnumeration.checkData, WellFormed, malformed]

end Kourovka.MetabelianEnumeration.PresentationExamples
