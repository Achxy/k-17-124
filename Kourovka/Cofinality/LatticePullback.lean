/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Presentations.KernelGenerators
import Kourovka.Modules.LaurentAction
import Kourovka.Covers.FiniteCover

/-!
# Lattice Pullback

The central pullback, with its quotient expressed as the manuscript's
integer lattice. Its finite presentation and finite Laurent module are actual
constructions, independent of the tameness theorem.
-/

noncomputable section

namespace Kourovka.MetabelianEnumeration.CofinalCover

open FiniteCover CommutatorModule

def freeAbelianLatticeEquiv (k : ℕ) : FreeAbelianGroup (Fin k) ≃+ Lattice k :=
  (FreeAbelianGroup.equivFinsupp (Fin k)).trans
    (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin k)).toAddEquiv

def latticeProjection {k : ℕ} (R : List (FreeGroup (Fin k))) :
    pullback Abelianization.of (abelianQuotientMap R) →* Multiplicative (Lattice k) :=
  (freeAbelianLatticeEquiv k).toMultiplicative.toMonoidHom.comp
    (second Abelianization.of (abelianQuotientMap R))

theorem latticeProjection_surjective {k : ℕ} (R : List (FreeGroup (Fin k))) :
    Function.Surjective (latticeProjection R) :=
  (freeAbelianLatticeEquiv k).toMultiplicative.surjective.comp
    (second_surjective _ _ (fun x => QuotientGroup.mk_surjective x))

def latticeKernelEquiv {k : ℕ} (R : List (FreeGroup (Fin k))) :
    (latticeProjection R).ker ≃*
      (second Abelianization.of (abelianQuotientMap R)).ker where
  toFun x := ⟨x.val, by
    apply (freeAbelianLatticeEquiv k).toMultiplicative.injective
    simpa only [map_one] using x.property⟩
  invFun x := ⟨x.val, by
    change (freeAbelianLatticeEquiv k).toMultiplicative
      (second Abelianization.of (abelianQuotientMap R) x.val) = 1
    rw [show second Abelianization.of (abelianQuotientMap R) x.val = 1 from x.property,
      map_one]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem lattice_kernel_commutative {k : ℕ} (R : List (FreeGroup (Fin k)))
    (hG : Metabelian (PresentedGroup (CentralExtension.relSet R))) :
    IsMulCommutative (latticeProjection R).ker := by
  letI := abelian_kernel_commutative hG
  letI := pullback_second_kernel_commutative Abelianization.of (abelianQuotientMap R)
  let e := latticeKernelEquiv R
  refine ⟨⟨fun x y => e.injective ?_⟩⟩
  rw [map_mul, map_mul]
  exact mul_comm _ _

theorem lattice_kernel_finite_normal_generators {k : ℕ} (R : List (FreeGroup (Fin k))) :
    ∃ s : Finset (latticeProjection R).ker,
      Subgroup.normalClosure (Subtype.val '' (s : Set (latticeProjection R).ker)) =
        (latticeProjection R).ker := by
  let e := (latticeKernelEquiv R).trans
    (secondKernelEquiv Abelianization.of (abelianQuotientMap R))
  apply finite_normal_generators_of_kernel_equiv
    (first Abelianization.of (abelianQuotientMap R))
    (first_surjective _ _ (abelianQuotientMap_surjective R)) _
    (Abelianization.of (G := PresentedGroup (CentralExtension.relSet R))).ker e
  · intro x
    rfl
  · rw [Abelianization.ker_of]
    exact commutator_finite_normal_generators R

theorem lattice_kernel_finite_module {k : ℕ} (R : List (FreeGroup (Fin k)))
    (hG : Metabelian (PresentedGroup (CentralExtension.relSet R))) :
    letI := lattice_kernel_commutative R hG
    letI := laurentModule (latticeProjection R) (latticeProjection_surjective R)
      (MonoidHom.id (Multiplicative (Lattice k)))
    Module.Finite (AddMonoidAlgebra ℤ (Lattice k)) (Additive (latticeProjection R).ker) := by
  letI := lattice_kernel_commutative R hG
  obtain ⟨s, hs⟩ := lattice_kernel_finite_normal_generators R
  exact laurent_finite_of_normal_generators (latticeProjection R)
    (latticeProjection_surjective R) (MonoidHom.id (Multiplicative (Lattice k)))
    Function.surjective_id s hs

end Kourovka.MetabelianEnumeration.CofinalCover
