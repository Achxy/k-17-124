/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Covers.FiniteCover
import Kourovka.Covers.CertifiedRadius

/-!
# Verifier Examples

Kernel-checked boundary examples for the executable certificate machinery.
-/

namespace Kourovka.MetabelianEnumeration.VerifierExamples

open ConeVerifier FiniteCover

def oppositeRays : Supports 1 := [[fun _ => 1], [fun _ => -1]]

theorem oppositeRays_cover : checkMargin oppositeRays 0 = true := by decide +kernel

theorem oppositeRays_margin : checkMargin oppositeRays (1 / 2) = true := by decide +kernel

theorem strict_margin_rejected : checkMargin oppositeRays 1 = false := by decide +kernel

theorem uncovered_ray_rejected : checkMargin ([[fun _ => 1]] : Supports 1) 0 = false := by
  decide +kernel

def acuteCones : Supports 2 :=
  [[![1, 0], ![1, 1]], [![0, 1], ![-1, 1]],
    [![-1, 0], ![-1, -1]], [![0, -1], ![1, -1]]]

theorem acuteCones_cover : checkMargin acuteCones 0 = true := by decide +kernel

def bsDatum : Datum 1 1 where
  designated := fun _ _ => 0
  polynomials := [(true, [(fun _ => 1, 2)]), (false, [(fun _ => -1, 2)])]

theorem bs_radius : certifiedRadius 1 (1 / 2) 1 = 9 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem bs_relator_count : (relators bsDatum 9).length = 19 := by
  simp only [relators, tRelations, shortRelations, polynomialRelations, List.length_append,
    List.length_flatMap, List.length_map, latticeBallList, Finset.length_sort]
  decide +kernel

end Kourovka.MetabelianEnumeration.VerifierExamples
