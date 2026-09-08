/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Presentations.PullbackPresentation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# The Laurent module of an abelian kernel

Conjugation factors through the abelian quotient. Finite normal generators of the
kernel become generators of its additive Laurent module.
-/

namespace Kourovka.MetabelianEnumeration.CommutatorModule

variable {α : Type} [Fintype α]

theorem commutator_finite_normal_generators (R : List (FreeGroup α)) :
    ∃ s : Finset (PresentedGroup (CentralExtension.relSet R)),
      Subgroup.normalClosure (s : Set (PresentedGroup (CentralExtension.relSet R))) =
        commutator (PresentedGroup (CentralExtension.relSet R)) := by
  classical
  let f := PresentedGroup.mk (CentralExtension.relSet R)
  let S := (CentralExtension.abelianRelations α).map f
  refine ⟨S.toFinset, ?_⟩
  have himage : f '' CentralExtension.relSet (CentralExtension.abelianRelations α) =
      (S.toFinset : Set (PresentedGroup (CentralExtension.relSet R))) := by
    ext x
    simp only [Set.mem_image, CentralExtension.relSet, Set.mem_setOf_eq,
      Finset.mem_coe, List.mem_toFinset, S, List.mem_map]
  have hsurj := PresentedGroup.mk_surjective (CentralExtension.relSet R)
  rw [← himage, ← Subgroup.map_normalClosure _ f hsurj,
    CentralExtension.abelian_relations_normalClosure, map_commutator_eq,
    MonoidHom.range_eq_top.mpr hsurj]
  rfl

theorem commutator_commutative {G : Type} [Group G] (hG : Metabelian G) :
    IsMulCommutative (commutator G) := by
  let C := Subgroup.closure (commutatorSet G)
  letI : CommGroup C := Subgroup.closureCommGroupOfComm (by
    rintro x ⟨a, b, rfl⟩ y ⟨c, d, rfl⟩
    exact (hG a b c d).eq)
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have hx : x.val ∈ C := by
    change x.val ∈ Subgroup.closure (commutatorSet G)
    rw [← commutator_eq_closure]
    exact x.property
  have hy : y.val ∈ C := by
    change y.val ∈ Subgroup.closure (commutatorSet G)
    rw [← commutator_eq_closure]
    exact y.property
  exact congrArg (fun z : C => z.val) (mul_comm (⟨x.val, hx⟩ : C) (⟨y.val, hy⟩ : C))

section KernelAction

variable {E Q : Type} [Group E] [CommGroup Q]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]

theorem kernel_le_conjugation_kernel :
    π.ker ≤ (MulAut.conjNormal (H := π.ker)).ker := by
  intro g hg
  change MulAut.conjNormal g = 1
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  change g * a.val * g⁻¹ = a.val
  have h := congrArg Subtype.val (mul_comm (⟨g, hg⟩ : π.ker) a)
  change g * a.val = a.val * g at h
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

/-- The action of the actual abelian quotient on its abelian kernel. -/
noncomputable def quotientConjugation : Q →* MulAut π.ker :=
  (QuotientGroup.lift π.ker (MulAut.conjNormal (H := π.ker))
    (kernel_le_conjugation_kernel π)).comp
      (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toMonoidHom

theorem quotientConjugation_image (g : E) :
    quotientConjugation π hπ (π g) = MulAut.conjNormal g := by
  have h := (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm_apply_apply
    (QuotientGroup.mk g)
  change (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g) =
    QuotientGroup.mk g at h
  change QuotientGroup.lift π.ker (MulAut.conjNormal (H := π.ker))
    (kernel_le_conjugation_kernel π)
    ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g)) = _
  rw [h]
  rfl

/-- Right conjugation is a homomorphism on the abelian quotient. -/
noncomputable def rightConjugation : Q →* MulAut π.ker :=
  (quotientConjugation π hπ).comp (MulEquiv.inv Q).toMonoidHom

theorem rightConjugation_image (g : E) (a : π.ker) :
    (rightConjugation π hπ (π g) a).val = g⁻¹ * a.val * g := by
  change (quotientConjugation π hπ ((π g)⁻¹) a).val = _
  rw [← map_inv, quotientConjugation_image, MulAut.conjNormal_apply, inv_inv]

noncomputable def rightRepresentation : Representation ℤ Q (Additive π.ker) where
  toFun q := (rightConjugation π hπ q).toAdditive.toAddMonoidHom.toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro a
    change Additive.ofMul (rightConjugation π hπ 1 a.toMul) = a
    rw [map_one]
    rfl
  map_mul' q r := by
    apply LinearMap.ext
    intro a
    change Additive.ofMul (rightConjugation π hπ (q * r) a.toMul) =
      Additive.ofMul (rightConjugation π hπ q (rightConjugation π hπ r a.toMul))
    rw [map_mul]
    rfl

theorem rightRepresentation_image (g : E) (a : Additive π.ker) :
    (rightRepresentation π hπ (π g) a).toMul.val = g⁻¹ * a.toMul.val * g :=
  rightConjugation_image π hπ g a.toMul

end KernelAction

end Kourovka.MetabelianEnumeration.CommutatorModule
