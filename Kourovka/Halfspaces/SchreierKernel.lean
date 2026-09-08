/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Halfspaces.HalfspaceRelators

/-!
# Schreier Kernel

The augmented Schreier presentation is a presentation of the actual kernel
inside the original ordinary presented group.
-/

noncomputable section

namespace Kourovka.MetabelianEnumeration.SchreierHeights

open HalfspaceGeometry
open Kourovka.Schreier.Discrete
open Kourovka.Schreier.Discrete.SchreierRewriting

variable {X Q : Type*} [Group Q] (R : Set (FreeGroup X))
  (π : PresentedGroup R →* Q)

abbrev preKernel := (π.comp (PresentedGroup.mk R)).ker

def kernelMap : preKernel R π →* π.ker where
  toFun w := ⟨PresentedGroup.mk R w.val, w.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _u _v := Subtype.ext (map_mul _ _ _)

theorem kernelMap_surjective : Function.Surjective (kernelMap R π) := by
  intro x
  obtain ⟨w, hw⟩ := PresentedGroup.mk_surjective R x.val
  refine ⟨⟨w, ?_⟩, Subtype.ext hw⟩
  change π (PresentedGroup.mk R w) = 1
  rw [hw]
  exact x.property

theorem kernelMap_ker : (kernelMap R π).ker = relatorSubgroup (L := preKernel R π) R := by
  ext w
  change kernelMap R π w = 1 ↔ w.val ∈ Subgroup.normalClosure R
  rw [← PresentedGroup.mk_eq_one_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

def kernelQuotientEquiv : preKernel R π ⧸ relatorSubgroup (L := preKernel R π) R ≃* π.ker :=
  (QuotientGroup.quotientMulEquivOfEq (kernelMap_ker R π).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (kernelMap R π) (kernelMap_surjective R π))

theorem normalClosure_le_preKernel : Subgroup.normalClosure R ≤ preKernel R π := by
  apply Subgroup.normalClosure_le_normal
  intro w hw
  change π (PresentedGroup.mk R w) = 1
  rw [PresentedGroup.one_of_mem hw, map_one]

variable [DecidableEq X]

def schreierKernelEquiv (S : RightSchreierRepresentative (preKernel R π)) :
    PresentedGroup (representativeAugmentedPresentationRelators S R) ≃* π.ker :=
  (representativeAugmentedPresentedGroupEquiv (S := S) (normalClosure_le_preKernel R π)).trans
    (kernelQuotientEquiv R π)

@[simp] theorem schreierKernelEquiv_of (S : RightSchreierRepresentative (preKernel R π))
    (z : RepresentativeSchreierSymbol S) :
    (schreierKernelEquiv R π S (PresentedGroup.of z)).val =
      PresentedGroup.mk R (representativeSymbolEval S z) := by
  simp [schreierKernelEquiv, representativeAugmentedPresentedGroupEquiv,
    representativeAugmentedPresentationQuotientEquiv,
    representativeSymbolEvalAugmentedPresentationQuotientHom, kernelQuotientEquiv,
    kernelMap, PresentedGroup.of, PresentedGroup.mk,
    QuotientGroup.quotientKerEquivOfSurjective, QuotientGroup.quotientKerEquivOfRightInverse,
    QuotientGroup.coe_mk', representativeSymbolEvalSubgroupHom]

end Kourovka.MetabelianEnumeration.SchreierHeights
