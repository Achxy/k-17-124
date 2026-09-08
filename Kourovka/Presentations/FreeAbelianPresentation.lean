/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Presentations.CentralExtensionPresentation
import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# A finite ordinary presentation of a free abelian group

Commutator relators identify the presented group with the integer lattice.
-/

namespace Kourovka.MetabelianEnumeration.CentralExtension

variable (α : Type) [Fintype α]

/-- The finite ordinary presentation with one commutation relation for each
pair of generators. -/
noncomputable def abelianRelations : List (FreeGroup α) :=
  (Finset.univ : Finset (α × α)).toList.map
    (fun p => ⁅FreeGroup.of p.1, FreeGroup.of p.2⁆)

abbrev AbelianPresentation := PresentedGroup (relSet (abelianRelations α))

theorem abelianPresentation_generators_commute (a b : α) :
    Commute (PresentedGroup.of (rels := relSet (abelianRelations α)) a)
      (PresentedGroup.of b) := by
  apply commutatorElement_eq_one_iff_commute.mp
  change ⁅PresentedGroup.mk _ (FreeGroup.of a), PresentedGroup.mk _ (FreeGroup.of b)⁆ = 1
  rw [← map_commutatorElement]
  apply PresentedGroup.one_of_mem
  change ⁅FreeGroup.of a, FreeGroup.of b⁆ ∈ abelianRelations α
  exact List.mem_map.mpr ⟨(a, b), by simp, rfl⟩

theorem abelianPresentation_center : Subgroup.center (AbelianPresentation α) = ⊤ := by
  apply top_unique
  intro x _
  apply PresentedGroup.generated_by
  intro a
  apply Subgroup.mem_center_iff.mpr
  intro y
  have hy : y ∈ Subgroup.centralizer
      {PresentedGroup.of (rels := relSet (abelianRelations α)) a} := by
    apply PresentedGroup.generated_by
    intro b
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact (abelianPresentation_generators_commute α a b).eq
  exact (show PresentedGroup.of a * y = y * PresentedGroup.of a from
    by simpa only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq] using hy).symm

noncomputable instance : CommGroup (AbelianPresentation α) :=
  Group.commGroupOfCenterEqTop (abelianPresentation_center α)

theorem abelian_relations_normalClosure :
    Subgroup.normalClosure (relSet (abelianRelations α)) = commutator (FreeGroup α) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro r hr
    obtain ⟨⟨a, b⟩, _, rfl⟩ := List.mem_map.mp hr
    exact Subgroup.subset_closure ⟨FreeGroup.of a, Subgroup.mem_top _,
      FreeGroup.of b, Subgroup.mem_top _, rfl⟩
  · have h := Abelianization.commutator_subset_ker
      (PresentedGroup.mk (relSet (abelianRelations α)))
    intro w hw
    exact PresentedGroup.mk_eq_one_iff.mp (h hw)

/-- The isomorphism is established by equality of the actual normal relation
subgroup and the commutator subgroup of the free group. -/
noncomputable def freeAbelianPresentationEquiv :
    AbelianPresentation α ≃* Multiplicative (FreeAbelianGroup α) := by
  change (FreeGroup α ⧸ Subgroup.normalClosure (relSet (abelianRelations α))) ≃*
    Multiplicative (FreeAbelianGroup α)
  refine (QuotientGroup.quotientMulEquivOfEq (abelian_relations_normalClosure α)).trans ?_
  exact {
    toFun := fun x => Multiplicative.ofAdd (Additive.ofMul x)
    invFun := fun x => Additive.toMul (Multiplicative.toAdd x)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }

end Kourovka.MetabelianEnumeration.CentralExtension
