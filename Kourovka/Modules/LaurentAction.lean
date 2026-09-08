/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Modules.CommutatorModule

/-!
# Conjugation as an action of a Laurent group ring

The ring action describes how lifts of quotient elements conjugate the abelian
kernel. The construction is independent of the chosen lifts.
-/

namespace Kourovka.MetabelianEnumeration.CommutatorModule

variable {E Q L : Type} [Group E] [CommGroup Q] [AddCommGroup L]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
variable (q : Multiplicative L →* Q)

/-- The actual Laurent group-ring action, induced by right conjugation. -/
noncomputable def laurentModule : Module (AddMonoidAlgebra ℤ L) (Additive π.ker) :=
  Module.compHom (Additive π.ker)
    ((Representation.asAlgebraHom ((rightRepresentation π hπ).comp q)).toRingHom.comp
      (AddMonoidAlgebra.toMultiplicative ℤ L).toRingHom)

theorem laurent_single (u : L) (a : Additive π.ker) :
    letI := laurentModule π hπ q
    (((AddMonoidAlgebra.single u 1 : AddMonoidAlgebra ℤ L) • a) : Additive π.ker).toMul =
      rightConjugation π hπ (q (Multiplicative.ofAdd u)) a.toMul := by
  letI := laurentModule π hπ q
  change ((Representation.asAlgebraHom ((rightRepresentation π hπ).comp q))
    ((AddMonoidAlgebra.toMultiplicative ℤ L) (AddMonoidAlgebra.single u 1)) a).toMul = _
  have hsingle : (AddMonoidAlgebra.toMultiplicative ℤ L) (AddMonoidAlgebra.single u 1) =
      MonoidAlgebra.single (Multiplicative.ofAdd u) 1 :=
    Finsupp.equivMapDomain_single _ _ _
  rw [hsingle, Representation.asAlgebraHom_single_one]
  rfl

theorem laurent_single_image (u : L) (g : E)
    (hu : q (Multiplicative.ofAdd u) = π g) (a : Additive π.ker) :
    letI := laurentModule π hπ q
    (((AddMonoidAlgebra.single u 1 : AddMonoidAlgebra ℤ L) • a) : Additive π.ker).toMul.val =
      g⁻¹ * a.toMul.val * g := by
  letI := laurentModule π hπ q
  rw [laurent_single, hu]
  exact rightConjugation_image π hπ g a.toMul

/-- Finite normal generators become finite generators for the concrete
Laurent action.  Surjectivity of the quotient map supplies every conjugation
as a monomial action. -/
theorem laurent_finite_of_normal_generators (hq : Function.Surjective q)
    (s : Finset π.ker)
    (hs : Subgroup.normalClosure (Subtype.val '' (s : Set π.ker)) = π.ker) :
    letI := laurentModule π hπ q
    Module.Finite (AddMonoidAlgebra ℤ L) (Additive π.ker) := by
  classical
  letI := laurentModule π hπ q
  let fs : Finset (Additive π.ker) := s.image Additive.ofMul
  let V : Submodule (AddMonoidAlgebra ℤ L) (Additive π.ker) :=
    Submodule.span _ (fs : Set (Additive π.ker))
  let B : Subgroup E := V.toAddSubgroup.toSubgroup'.map π.ker.subtype
  have hconj (g : E) (a : π.ker) (ha : Additive.ofMul a ∈ V) :
      Additive.ofMul (MulAut.conjNormal g a) ∈ V := by
    obtain ⟨u, hu⟩ := hq (π g⁻¹)
    have hact : (((AddMonoidAlgebra.single u.toAdd 1 : AddMonoidAlgebra ℤ L) •
        Additive.ofMul a) : Additive π.ker) =
        Additive.ofMul (MulAut.conjNormal g a) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [laurent_single_image π hπ q u.toAdd g⁻¹ hu, inv_inv]
      rfl
    rw [← hact]
    exact V.smul_mem _ ha
  letI : B.Normal := {
    conj_mem := by
      rintro _ ⟨a, ha, rfl⟩ g
      exact ⟨MulAut.conjNormal g a, hconj g a ha, rfl⟩ }
  have hsub : Subtype.val '' (s : Set π.ker) ⊆ B := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a, ?_, rfl⟩
    change Additive.ofMul a ∈ V
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hker : π.ker ≤ B := by
    rw [← hs]
    exact Subgroup.normalClosure_le_normal hsub
  have hspan : V = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b, hb, hba⟩ := hker a.toMul.property
    have hba' : b = a.toMul := Subtype.ext hba
    simpa only [hba'] using hb
  exact ⟨fs, hspan⟩

end Kourovka.MetabelianEnumeration.CommutatorModule
