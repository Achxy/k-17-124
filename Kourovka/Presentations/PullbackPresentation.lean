/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Cofinality.CofinalCover
import Kourovka.Presentations.FreeAbelianPresentation
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite presentations of the abelian pullback

The pullback replaces the abelian quotient by a free abelian group. Its central
structure allows the finite-presentation theorem to be applied.
-/

namespace Kourovka.MetabelianEnumeration.CofinalCover

variable {α : Type} [Fintype α]

/-- The kernel of a homomorphism from a finite-rank free abelian group is
itself free abelian of finite rank.  A PID basis supplies the isomorphism. -/
theorem kernel_free_abelian {Q : Type} [CommGroup Q]
    (q : Multiplicative (FreeAbelianGroup α) →* Q) :
    ∃ (β : Type) (finiteβ : Fintype β), letI := finiteβ
      Nonempty (Multiplicative (FreeAbelianGroup β) ≃* q.ker) := by
  let K : Submodule ℤ (FreeAbelianGroup α) := LinearMap.ker (q.toAdditiveRight.toIntLinearMap)
  let β := Module.Free.ChooseBasisIndex ℤ K
  let b := Module.Free.chooseBasis ℤ K
  let eadd : K ≃+ FreeAbelianGroup β :=
    b.repr.toAddEquiv.trans (FreeAbelianGroup.equivFinsupp β).symm
  let etag : Multiplicative K ≃* q.ker := {
    toFun := fun x => ⟨Multiplicative.ofAdd x.toAdd.val, x.toAdd.property⟩
    invFun := fun x => Multiplicative.ofAdd ⟨x.val.toAdd, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  exact ⟨β, inferInstance, ⟨eadd.symm.toMultiplicative.trans etag⟩⟩

/-- The central pullback of an ordinary finitely presented group along a
surjective finite-rank free abelian map has an actual finite presentation. -/
theorem pullback_finitely_presented
    (R : List (FreeGroup α)) {γ Q : Type} [Fintype γ] [CommGroup Q]
    (p : PresentedGroup (CentralExtension.relSet R) →* Q)
    (q : Multiplicative (FreeAbelianGroup γ) →* Q) (hq : Function.Surjective q) :
    ∃ (δ : Type) (finiteδ : Fintype δ), letI := finiteδ
      ∃ T : List (FreeGroup δ),
        Nonempty (PresentedGroup (CentralExtension.relSet T) ≃* pullback p q) := by
  letI : IsMulCommutative (Multiplicative (FreeAbelianGroup γ)) := ⟨⟨mul_comm⟩⟩
  obtain ⟨β, hβ, ⟨eβ⟩⟩ := kernel_free_abelian q
  letI := hβ
  let e := ((CentralExtension.freeAbelianPresentationEquiv β).trans eβ).trans
    (firstKernelEquiv p q).symm
  let ι := (first p q).ker.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp e.injective
  have hexact : ι.range = (first p q).ker := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e y).property
    · intro hx
      refine ⟨e.symm ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
  have hcentral : ι.range ≤ Subgroup.center (pullback p q) := by
    rw [hexact]
    exact first_kernel_central p q
  obtain ⟨T, hT⟩ := CentralExtension.finite_presentation_of_central_extension
    R (CentralExtension.abelianRelations β) (first p q) ι
      (first_surjective p q hq) hι hexact hcentral
  exact ⟨α ⊕ β, inferInstance, T, hT⟩

/-- In particular the pullback used in the manuscript is finitely presented;
this statement does not assume metabelianity to obtain finite presentation. -/
theorem abelian_pullback_finitely_presented (R : List (FreeGroup α)) :
    ∃ (δ : Type) (finiteδ : Fintype δ), letI := finiteδ
      ∃ T : List (FreeGroup δ),
        Nonempty (PresentedGroup (CentralExtension.relSet T) ≃*
          pullback Abelianization.of (abelianQuotientMap R)) :=
  pullback_finitely_presented R Abelianization.of (abelianQuotientMap R)
    (abelianQuotientMap_surjective R)

/-- Reindexing a finite alphabet yields the ordinary generator-count format. -/
theorem finite_presentation_on_fin (T : List (FreeGroup α)) {E : Type} [Group E]
    (hT : Nonempty (PresentedGroup (CentralExtension.relSet T) ≃* E)) :
    ∃ (n : ℕ) (S : List (FreeGroup (Fin n))),
      Nonempty (PresentedGroup (CentralExtension.relSet S) ≃* E) := by
  classical
  let e := Fintype.equivFin α
  let S := T.map (FreeGroup.freeGroupCongr e)
  have he : FreeGroup.freeGroupCongr e '' CentralExtension.relSet T =
      CentralExtension.relSet S := by
    ext w
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact List.mem_map.mpr ⟨r, hr, rfl⟩
    · intro hw
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
      exact ⟨r, hr, rfl⟩
  have h : Nonempty (PresentedGroup (CentralExtension.relSet T) ≃*
      PresentedGroup (CentralExtension.relSet S)) := by
    rw [← he]
    exact ⟨PresentedGroup.equivPresentedGroup _ e⟩
  exact ⟨Fintype.card α, S, ⟨h.some.symm.trans hT.some⟩⟩

theorem abelian_pullback_finitely_presented_on_fin (R : List (FreeGroup α)) :
    ∃ (n : ℕ) (S : List (FreeGroup (Fin n))),
      Nonempty (PresentedGroup (CentralExtension.relSet S) ≃*
        pullback Abelianization.of (abelianQuotientMap R)) := by
  obtain ⟨δ, hδ, T, hT⟩ := abelian_pullback_finitely_presented R
  letI := hδ
  exact finite_presentation_on_fin T hT

end Kourovka.MetabelianEnumeration.CofinalCover
