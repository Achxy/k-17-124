/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Cofinality.CofinalRealization
import Kourovka.Halfspaces.BieriStrebelNecessity

/-!
# Cofinality

Every actual finitely presented metabelian group is a quotient of one of
the finite ordinary cover presentations, at every selected radius.
-/

noncomputable section

set_option autoImplicit false

namespace Kourovka.MetabelianEnumeration.CofinalCover

open FiniteCover CommutatorModule ValuationModule SignedTameness
open TamenessCompactness

/-- Cofinality of the concrete finite-cover family. The lattice rank is the
original number of generators and the kernel alphabet is nonempty. Neither
tameness nor any presentation theorem is assumed in the conclusion. -/
theorem finite_presentation_cover_cofinal {k : ℕ} (R : List (FreeGroup (Fin k)))
    (hG : Metabelian (PresentedGroup (CentralExtension.relSet R))) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ data : Datum k a,
      ConeVerifier.ConeCover (data.polynomials.map polynomialSupport) ∧
      ∀ radius : ℕ, ∃ f : FiniteCover.GroupOf data radius →*
        PresentedGroup (CentralExtension.relSet R), Function.Surjective f := by
  classical
  -- Replace the abelian quotient by a free abelian lattice via a central pullback.
  let π := latticeProjection R
  have hπ : Function.Surjective π := latticeProjection_surjective R
  letI := lattice_kernel_commutative R hG
  letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
  -- Finite normal generation gives a finitely generated Laurent module.
  have hf : Module.Finite (GroupRing (Lattice k)) (Additive π.ker) :=
    lattice_kernel_finite_module R hG
  obtain ⟨n, S, ⟨e⟩⟩ := abelian_pullback_finitely_presented_on_fin R
  -- Finite presentation forces the directional finiteness used by Bieri-Strebel.
  have ht : Tame (k := k) (Additive π.ker) :=
    BieriStrebelNecessity.tame_of_finite_presentation (CentralExtension.relSet S)
      (List.finite_toSet S) e π hπ hf
  -- Extract finitely many Laurent relations whose supports cover all directions.
  obtain ⟨a, ha, data, hcone, hmaps⟩ := exists_tame_cover_data π hπ hf ht
  refine ⟨a, ha, data, hcone, ?_⟩
  intro radius
  obtain ⟨f, hsurj⟩ := hmaps radius
  -- Compose with the pullback projection to recover the original group.
  exact ⟨(first Abelianization.of (abelianQuotientMap R)).comp f,
    (first_surjective _ _ (abelianQuotientMap_surjective R)).comp hsurj⟩

end Kourovka.MetabelianEnumeration.CofinalCover
