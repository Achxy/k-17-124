/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Halfspaces.HalfspaceLoops

/-!
# Halfspace Loop Module

Commutator expansion along genuine halfspace paths, followed by the
positive-shift argument, proves finite generation over a valuation half-ring.
-/

noncomputable section

namespace Kourovka.MetabelianEnumeration.HalfspaceLoops

open HalfspaceGeometry HalfspaceModule ValuationModule

variable {E L X : Type} [Group E] [AddCommGroup L]
variable (π : E →* Multiplicative L)

def difference (u g : E) : Additive π.ker :=
  Additive.ofMul ⟨⁅u, g⁆, by simp [commutatorElement_def]⟩

def conjugate (g : E) (n : Additive π.ker) : Additive π.ker :=
  Additive.ofMul (MulAut.conjNormal g n.toMul)

variable [IsMulCommutative π.ker]

omit [IsMulCommutative ↥π.ker] in
@[simp] theorem difference_one (u : E) : difference π u 1 = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp [difference]

omit [IsMulCommutative ↥π.ker] in
theorem difference_mul (u p x : E) :
    difference π u (p * x) = difference π u p + conjugate π p (difference π u x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ⁅u, p * x⁆ = ⁅u, p⁆ * (p * ⁅u, x⁆ * p⁻¹)
  group

omit [IsMulCommutative ↥π.ker] in
theorem difference_inv (u x : E) :
    difference π u x⁻¹ = -conjugate π x⁻¹ (difference π u x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change ⁅u, x⁻¹⁆ = (x⁻¹ * ⁅u, x⁆ * (x⁻¹)⁻¹)⁻¹
  group

theorem conjugate_neg (g : E) (n : Additive π.ker) :
    conjugate π g (-n) = -conjugate π g n := by
  apply Additive.toMul.injective
  exact map_inv (MulAut.conjNormal g) n.toMul

omit [IsMulCommutative ↥π.ker] in
theorem conjugate_conjugate (p x : E) (n : Additive π.ker) :
    conjugate π p (conjugate π x n) = conjugate π (p * x) n := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change p * (x * n.toMul.val * x⁻¹) * p⁻¹ =
    (p * x) * n.toMul.val * (p * x)⁻¹
  group

def height (χ : L →+ ℝ) (g : E) : ℝ := χ (π g).toAdd

omit [IsMulCommutative ↥π.ker] in
@[simp] theorem height_one (χ : L →+ ℝ) : height π χ 1 = 0 := by
  simp [height]

omit [IsMulCommutative ↥π.ker] in
@[simp] theorem height_mul (χ : L →+ ℝ) (g h : E) :
    height π χ (g * h) = height π χ g + height π χ h := by
  simp [height]

omit [IsMulCommutative ↥π.ker] in
@[simp] theorem height_inv (χ : L →+ ℝ) (g : E) :
    height π χ g⁻¹ = -height π χ g := by
  simp [height]

def letter (g : X → E) (z : X × Bool) : E := if z.2 then g z.1 else (g z.1)⁻¹

def evalWord (g : X → E) (w : List (X × Bool)) : E :=
  FreeGroup.lift g (FreeGroup.mk w)

@[simp] theorem evalWord_nil (g : X → E) : evalWord g [] = 1 := by
  simp [evalWord]

@[simp] theorem evalWord_cons (g : X → E) (z : X × Bool) (w : List (X × Bool)) :
    evalWord g (z :: w) = letter g z * evalWord g w := by
  rcases z with ⟨x, b⟩
  cases b <;> simp [evalWord, FreeGroup.lift_mk, letter]

omit [IsMulCommutative ↥π.ker] in
@[simp] theorem height_letter (χ : L →+ ℝ) (g : X → E) (z : X × Bool) :
    height π χ (letter g z) = letterHeight (fun x => height π χ (g x)) z := by
  cases z with
  | mk x b => cases b <;> simp [letter, letterHeight]

section CompatibleAction

variable [DecidableEq L] [Module (GroupRing L) (Additive π.ker)]

/- The compatibility hypothesis is later discharged by the explicitly
constructed Laurent action of the actual quotient. -/
variable (hact : ∀ (p : E) (n : Additive π.ker),
  conjugate π p n = shift (-(π p).toAdd) n)

include hact

omit [DecidableEq L] in
theorem difference_kernel (u : E) (n : π.ker) :
    difference π u n.val = shift (-(π u).toAdd) (Additive.ofMul n) - Additive.ofMul n := by
  rw [← hact]
  apply Additive.toMul.injective
  apply Subtype.ext
  change ⁅u, n.val⁆ = (u * n.val * u⁻¹) / n.val
  rw [div_eq_mul_inv, commutatorElement_def]

/-- Expanding a commutator along a lower-halfspace word only uses
nonnegative-height conjugates of the finitely many letter commutators.
For an inverse letter the coefficient is taken at its ending vertex. -/
theorem path_difference_mem (χ : L →+ ℝ) (g : X → E) (u : E)
    (V : Submodule (nonnegativeRing χ) (Additive π.ker))
    (hletters : ∀ x, difference π u (g x) ∈ V)
    (w : List (X × Bool)) (p : E) (hp : difference π u p ∈ V)
    (hw : PathIn (letterHeight (fun x => height π χ (g x)))
      (fun h => h ≤ 0) (height π χ p) w) :
    difference π u (p * evalWord g w) ∈ V := by
  induction w generalizing p with
  | nil => simpa using hp
  | cons z w ih =>
    have hnext : PathIn (letterHeight (fun x => height π χ (g x)))
        (fun h => h ≤ 0) (height π χ (p * letter g z)) w := by
      simpa only [height_mul, height_letter] using hw.2
    have hpnext : difference π u (p * letter g z) ∈ V := by
      rcases z with ⟨x, b⟩
      cases b with
      | true =>
        change difference π u (p * g x) ∈ V
        rw [difference_mul, hact]
        apply V.add_mem hp
        apply shift_mem χ V _ _ _ (hletters x)
        have h := hw.1
        change height π χ p ≤ 0 at h
        simpa only [map_neg, neg_nonneg, height] using h
      | false =>
        change difference π u (p * (g x)⁻¹) ∈ V
        rw [difference_mul, difference_inv, conjugate_neg, conjugate_conjugate, hact]
        apply V.add_mem hp
        apply V.neg_mem
        apply shift_mem χ V _ _ _ (hletters x)
        have h := hnext.start
        change height π χ (p * (g x)⁻¹) ≤ 0 at h
        simpa only [map_neg, neg_nonneg, height] using h
    simpa only [evalWord_cons, mul_assoc] using ih (p * letter g z) hpnext hnext

theorem loop_difference_mem (χ : L →+ ℝ) (g : X → E) (u : E)
    (V : Submodule (nonnegativeRing χ) (Additive π.ker))
    (hletters : ∀ x, difference π u (g x) ∈ V) (n : π.ker)
    (hn : n ∈ loopSet π χ g (fun h => h ≤ 0)) : difference π u n.val ∈ V := by
  obtain ⟨w, hw, hp⟩ := hn
  have h := path_difference_mem π hact χ g u V hletters w 1
    (by simp) (by simpa [height] using hp)
  simpa only [one_mul, evalWord, hw] using h

/-- If lower-halfspace loops generate the kernel, all commutator differences
belong to the half-module generated by the letter differences. -/
theorem all_differences_mem (χ : L →+ ℝ) (g : X → E) (u : E)
    (V : Submodule (nonnegativeRing χ) (Additive π.ker))
    (hletters : ∀ x, difference π u (g x) ∈ V)
    (hloops : Subgroup.closure (loopSet π χ g (fun h => h ≤ 0)) = ⊤) :
    ∀ m : Additive π.ker, shift (-(π u).toAdd) m - m ∈ V := by
  let F : AddMonoid.End (Additive π.ker) := {
    toFun := fun m => shift (-(π u).toAdd) m - m
    map_zero' := by simp [shift]
    map_add' := by intro x y; simp only [shift_add]; abel }
  let B : Subgroup π.ker := (V.toAddSubgroup.comap F).toSubgroup'
  have hsub : loopSet π χ g (fun h => h ≤ 0) ⊆ B := by
    intro n hn
    change shift (-(π u).toAdd) (Additive.ofMul n) - Additive.ofMul n ∈ V
    rw [← difference_kernel π hact u n]
    exact loop_difference_mem π hact χ g u V hletters n hn
  have htop : B = ⊤ := by
    apply top_unique
    rw [← hloops]
    exact (Subgroup.closure_le B).2 hsub
  intro m
  have hm : m.toMul ∈ B := by rw [htop]; trivial
  exact hm

/-- Bieri–Strebel's halfspace-loop lemma: genuine loop generation implies
finite generation over the corresponding valuation half-ring. -/
theorem finite_of_lower_loops [Fintype X]
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (hπ : Function.Surjective π) (g : X → E)
    [Module.Finite (GroupRing L) (Additive π.ker)]
    (hloops : Subgroup.closure (loopSet π χ g (fun h => h ≤ 0)) = ⊤) :
    Module.Finite (nonnegativeRing χ) (Additive π.ker) := by
  classical
  obtain ⟨v, hv⟩ := exists_positive χ hχ
  obtain ⟨u, hu⟩ := hπ (Multiplicative.ofAdd (-v))
  have hupos : 0 < χ (-(π u).toAdd) := by simpa [hu] using hv
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := GroupRing L) (M := Additive π.ker)
  let d : Finset (Additive π.ker) := Finset.univ.image (fun x => difference π u (g x))
  apply finite_of_shift_difference χ (-(π u).toAdd) hupos s d hs
  apply all_differences_mem π hact χ g u _ _ hloops
  intro x
  apply Submodule.subset_span
  exact Finset.mem_union_right s (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)

end CompatibleAction

/-- The preceding theorem for the actual quotient action; no compatibility
or module-action hypothesis is left to the caller. -/
theorem finite_of_lower_loops_laurent [Fintype X] [DecidableEq L]
    (χ : L →+ ℝ) (hχ : χ ≠ 0) (hπ : Function.Surjective π) (g : X → E) :
    letI := CommutatorModule.laurentModule π hπ (MonoidHom.id (Multiplicative L))
    Module.Finite (GroupRing L) (Additive π.ker) →
    Subgroup.closure (loopSet π χ g (fun h => h ≤ 0)) = ⊤ →
    Module.Finite (nonnegativeRing χ) (Additive π.ker) := by
  letI := CommutatorModule.laurentModule π hπ (MonoidHom.id (Multiplicative L))
  intro hfinite hloops
  letI := hfinite
  apply finite_of_lower_loops π _ χ hχ hπ g hloops
  intro p n
  have h := CommutatorModule.laurent_single_image π hπ
    (MonoidHom.id (Multiplicative L)) (-(π p).toAdd) p⁻¹ (by simp) n
  apply Additive.toMul.injective
  apply Subtype.ext
  change p * n.toMul.val * p⁻¹ = _
  simpa only [inv_inv] using h.symm

end Kourovka.MetabelianEnumeration.HalfspaceLoops
