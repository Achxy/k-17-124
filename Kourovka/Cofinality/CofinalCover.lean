/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Presentations.CentralExtensionPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Cofinal Cover

The actual central pullback used to replace an abelian quotient by a free
abelian quotient.  Both kernels and both surjective projections are explicit.
-/

namespace Kourovka.MetabelianEnumeration.CofinalCover

variable {G H Q : Type} [Group G] [Group H] [Group Q]

def pullback (p : G →* Q) (q : H →* Q) : Subgroup (G × H) where
  carrier := {x | p x.1 = q x.2}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change p (x.1 * y.1) = q (x.2 * y.2)
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change p x.1⁻¹ = q x.2⁻¹
    rw [map_inv, map_inv, hx]

def first (p : G →* Q) (q : H →* Q) : pullback p q →* G :=
  (MonoidHom.fst G H).comp (pullback p q).subtype

def second (p : G →* Q) (q : H →* Q) : pullback p q →* H :=
  (MonoidHom.snd G H).comp (pullback p q).subtype

@[simp] theorem first_apply (p : G →* Q) (q : H →* Q) (x : pullback p q) :
    first p q x = x.val.1 := rfl

@[simp] theorem second_apply (p : G →* Q) (q : H →* Q) (x : pullback p q) :
    second p q x = x.val.2 := rfl

theorem first_surjective (p : G →* Q) (q : H →* Q) (hq : Function.Surjective q) :
    Function.Surjective (first p q) := by
  intro g
  obtain ⟨h, hh⟩ := hq (p g)
  exact ⟨⟨(g, h), hh.symm⟩, rfl⟩

theorem second_surjective (p : G →* Q) (q : H →* Q) (hp : Function.Surjective p) :
    Function.Surjective (second p q) := by
  intro h
  obtain ⟨g, hg⟩ := hp (q h)
  exact ⟨⟨(g, h), hg⟩, rfl⟩

def firstKernelEquiv (p : G →* Q) (q : H →* Q) : (first p q).ker ≃* q.ker where
  toFun x := ⟨x.val.val.2, by
    have hx : x.val.val.1 = 1 := x.property
    change q x.val.val.2 = 1
    rw [← x.val.property, hx, map_one]⟩
  invFun h := ⟨⟨(1, h.val), by
    change p 1 = q h.val
    rw [map_one]
    exact h.property.symm⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (show x.val.val.1 = 1 from x.property).symm
    · rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def secondKernelEquiv (p : G →* Q) (q : H →* Q) : (second p q).ker ≃* p.ker where
  toFun x := ⟨x.val.val.1, by
    have hx : x.val.val.2 = 1 := x.property
    change p x.val.val.1 = 1
    rw [x.val.property, hx, map_one]⟩
  invFun g := ⟨⟨(g.val, 1), by
    change p g.val = q 1
    rw [map_one]
    exact g.property⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (show x.val.val.2 = 1 from x.property).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem first_kernel_central [IsMulCommutative H] (p : G →* Q) (q : H →* Q) :
    (first p q).ker ≤ Subgroup.center (pullback p q) := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Prod.ext
  · change y.val.1 * x.val.1 = x.val.1 * y.val.1
    have hx' : x.val.1 = 1 := hx
    simp [hx']
  · exact mul_comm _ _

theorem metabelian_of_injective {E : Type} [Group E] (f : E →* G)
    (hf : Function.Injective f) (hG : Metabelian G) : Metabelian E := by
  intro a b c d
  apply hf
  simpa only [map_mul, map_commutatorElement] using (hG (f a) (f b) (f c) (f d)).eq

theorem metabelian_prod (hG : Metabelian G) (hH : Metabelian H) : Metabelian (G × H) := by
  intro a b c d
  apply Prod.ext
  · exact (hG a.1 b.1 c.1 d.1).eq
  · exact (hH a.2 b.2 c.2 d.2).eq

theorem pullback_metabelian [IsMulCommutative H] (p : G →* Q) (q : H →* Q)
    (hG : Metabelian G) : Metabelian (pullback p q) :=
  metabelian_of_injective (pullback p q).subtype Subtype.val_injective
    (metabelian_prod hG (fun _ _ _ _ => mul_comm _ _))

/-- The free abelian group on the given finite generators maps onto the actual
abelianization of any ordinary finite presentation on those generators. -/
noncomputable def abelianQuotientMap {α : Type} (R : List (FreeGroup α)) :
    Multiplicative (FreeAbelianGroup α) →* Abelianization (PresentedGroup {r | r ∈ R}) :=
  (FreeAbelianGroup.lift (fun a => Additive.ofMul
    (Abelianization.of (PresentedGroup.of (rels := {r | r ∈ R}) a)))).toMultiplicativeLeft

theorem abelianQuotientMap_of {α : Type} (R : List (FreeGroup α)) (a : α) :
    abelianQuotientMap R (Multiplicative.ofAdd (FreeAbelianGroup.of a)) =
      Abelianization.of (PresentedGroup.of a) := by
  change Additive.toMul ((FreeAbelianGroup.lift (fun a => Additive.ofMul
    (Abelianization.of (PresentedGroup.of (rels := {r | r ∈ R}) a))))
      (FreeAbelianGroup.of a)) = _
  rw [FreeAbelianGroup.lift_apply_of]
  rfl

theorem abelianQuotientMap_surjective {α : Type} (R : List (FreeGroup α)) :
    Function.Surjective (abelianQuotientMap R) := by
  intro g
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  have h : g ∈ (abelianQuotientMap R).range.comap Abelianization.of := by
    apply PresentedGroup.generated_by
    intro a
    exact ⟨Multiplicative.ofAdd (FreeAbelianGroup.of a), abelianQuotientMap_of R a⟩
  exact h

end Kourovka.MetabelianEnumeration.CofinalCover
