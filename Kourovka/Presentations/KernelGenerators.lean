/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Modules.CommutatorModule

/-!
# Normal generators for kernels between finite presentations

The kernel of a surjection admits finitely many normal generators, which later
supply generators for the conjugation module.
-/

namespace Kourovka.MetabelianEnumeration.CommutatorModule

variable {E G : Type} [Group E] [Group G]

theorem finite_normal_generators_of_kernel_equiv
    (f : E →* G) (hf : Function.Surjective f)
    (N : Subgroup E) [N.Normal] (M : Subgroup G) [M.Normal]
    (e : N ≃* M) (he : ∀ x : N, f x.val = (e x).val)
    (hM : ∃ s : Finset G, Subgroup.normalClosure (s : Set G) = M) :
    ∃ s : Finset N, Subgroup.normalClosure (Subtype.val '' (s : Set N)) = N := by
  classical
  obtain ⟨s, hs⟩ := hM
  have hsm (g : s) : g.val ∈ M := by
    rw [← hs]
    exact Subgroup.subset_normalClosure g.property
  let gen : s → N := fun g => e.symm ⟨g.val, hsm g⟩
  let t : Finset N := Finset.univ.image gen
  have hgen (g : s) : f (gen g).val = g.val := by
    rw [he]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨g.val, hsm g⟩)
  have himage : f '' (Subtype.val '' (t : Set N)) = (s : Set G) := by
    ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hy
      rw [hgen]
      exact g.property
    · intro hx
      refine ⟨(gen ⟨x, hx⟩).val, ⟨gen ⟨x, hx⟩, ?_, rfl⟩, hgen ⟨x, hx⟩⟩
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  let C := Subgroup.normalClosure (Subtype.val '' (t : Set N))
  have hCN : C ≤ N := Subgroup.normalClosure_le_normal (by
    rintro _ ⟨x, _, rfl⟩
    exact x.property)
  have hmap : C.map f = M := by
    change (Subgroup.normalClosure _).map f = M
    rw [Subgroup.map_normalClosure _ f hf, himage, hs]
  refine ⟨t, le_antisymm hCN ?_⟩
  intro x hx
  have hfx : f x ∈ C.map f := by
    rw [hmap, he ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  obtain ⟨y, hy, hyx⟩ := hfx
  have heq : (⟨y, hCN hy⟩ : N) = ⟨x, hx⟩ := e.injective (by
    apply Subtype.ext
    rw [← he, ← he]
    exact hyx)
  have hyx' : y = x := congrArg Subtype.val heq
  simpa only [← hyx'] using hy

theorem abelian_kernel_commutative (hG : Metabelian G) :
    IsMulCommutative (Abelianization.of (G := G)).ker := by
  letI := commutator_commutative hG
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have hx : x.val ∈ commutator G := by
    rw [← Abelianization.ker_of]
    exact x.property
  have hy : y.val ∈ commutator G := by
    rw [← Abelianization.ker_of]
    exact y.property
  exact congrArg (fun z : commutator G => z.val)
    (mul_comm (⟨x.val, hx⟩ : commutator G) (⟨y.val, hy⟩ : commutator G))

theorem pullback_second_kernel_commutative {Q H : Type} [Group Q] [Group H]
    (p : G →* Q) (q : H →* Q) [IsMulCommutative p.ker] :
    IsMulCommutative (CofinalCover.second p q).ker := by
  let e := CofinalCover.secondKernelEquiv p q
  refine ⟨⟨fun x y => e.injective ?_⟩⟩
  rw [map_mul, map_mul]
  exact mul_comm _ _

theorem abelian_pullback_kernel_finite_generators {α : Type} [Fintype α]
    (R : List (FreeGroup α)) :
    ∃ s : Finset (CofinalCover.second Abelianization.of
      (CofinalCover.abelianQuotientMap R)).ker,
      Subgroup.normalClosure (Subtype.val '' (s : Set (CofinalCover.second Abelianization.of
        (CofinalCover.abelianQuotientMap R)).ker)) =
        (CofinalCover.second Abelianization.of (CofinalCover.abelianQuotientMap R)).ker := by
  apply finite_normal_generators_of_kernel_equiv
    (CofinalCover.first Abelianization.of (CofinalCover.abelianQuotientMap R))
    (CofinalCover.first_surjective _ _ (CofinalCover.abelianQuotientMap_surjective R)) _
    (Abelianization.of (G := PresentedGroup (CentralExtension.relSet R))).ker
    (CofinalCover.secondKernelEquiv _ _)
  · intro x
    rfl
  · rw [Abelianization.ker_of]
    exact commutator_finite_normal_generators R

end Kourovka.MetabelianEnumeration.CommutatorModule
