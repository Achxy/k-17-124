/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Modules.ValuationModule

/-!
# Halfspace Module

Clearing negative Laurent coefficients by a positive monomial, and the
telescoping argument needed for finite generation by halfspace loops.
-/

namespace Kourovka.MetabelianEnumeration.HalfspaceModule

open ValuationModule

variable {Q M : Type} [AddCommGroup Q] [DecidableEq Q]
variable [AddCommGroup M] [Module (GroupRing Q) M]

noncomputable def monomial (q : Q) : GroupRing Q := AddMonoidAlgebra.single q 1
noncomputable def shift (q : Q) (m : M) : M := monomial q • m

omit [DecidableEq Q] in
@[simp] theorem monomial_zero : monomial (0 : Q) = 1 := by
  simp [monomial, ← AddMonoidAlgebra.one_def]

omit [DecidableEq Q] in
theorem monomial_add (q r : Q) : monomial (q + r) = monomial q * monomial r := by
  simp [monomial, AddMonoidAlgebra.single_mul_single]

omit [DecidableEq Q] in
@[simp] theorem shift_zero (m : M) : shift (0 : Q) m = m := by simp [shift]
omit [DecidableEq Q] in
@[simp] theorem shift_add (q : Q) (m n : M) : shift q (m + n) = shift q m + shift q n :=
  smul_add _ _ _
omit [DecidableEq Q] in
@[simp] theorem shift_sub (q : Q) (m n : M) : shift q (m - n) = shift q m - shift q n :=
  smul_sub _ _ _
omit [DecidableEq Q] in
theorem shift_shift (q r : Q) (m : M) : shift q (shift r m) = shift (q + r) m := by
  simp only [shift, monomial_add, mul_smul]

noncomputable def halfMonomial (χ : Q →+ ℝ) (q : Q) (hq : 0 ≤ χ q) : nonnegativeRing χ :=
  ⟨monomial q, by
    intro v hv
    have hvq : v = q := by
      simpa [monomial, AddMonoidAlgebra.single_apply, eq_comm] using hv
    simpa only [hvq] using hq⟩

theorem shift_mem (χ : Q →+ ℝ) (V : Submodule (nonnegativeRing χ) M)
    (q : Q) (hq : 0 ≤ χ q) (m : M) (hm : m ∈ V) : shift q m ∈ V :=
  V.smul_mem (halfMonomial χ q hq) hm

theorem shift_nsmul_mem (χ : Q →+ ℝ) (V : Submodule (nonnegativeRing χ) M)
    (u : Q) (hu : 0 ≤ χ u) (n : ℕ) (m : M) (hm : m ∈ V) : shift (n • u) m ∈ V := by
  apply shift_mem χ V _ _ m hm
  simpa only [map_nsmul, nsmul_eq_mul] using mul_nonneg (Nat.cast_nonneg n) hu

theorem monomial_lower_bound (χ : Q →+ ℝ) (q : Q) :
    LowerBound χ (monomial q) (χ q) := by
  intro u hu
  have : u = q := by
    simpa [monomial, AddMonoidAlgebra.single_apply, eq_comm] using hu
  simp [this]

/-- Every Laurent coefficient becomes nonnegative after a sufficiently large
positive monomial shift. -/
theorem shifted_coefficient (χ : Q →+ ℝ) (u : Q) (hu : 0 < χ u)
    (r : GroupRing Q) : ∃ n : ℕ, monomial (n • u) * r ∈ nonnegativeRing χ := by
  obtain ⟨c, hc⟩ := lowerBound_exists χ r
  obtain ⟨n, hn⟩ := exists_nat_gt (-c / χ u)
  have hpos : 0 ≤ (n : ℝ) * χ u + c := by
    have := (div_lt_iff₀ hu).mp hn
    linarith
  refine ⟨n, ?_⟩
  intro q hq
  have h := lowerBound_mul χ (monomial_lower_bound χ (n • u)) hc q hq
  simp only [map_nsmul, nsmul_eq_mul] at h
  exact hpos.trans h

/-- A vector in the full Laurent span of a half-module can be shifted into
that half-module. -/
theorem eventually_shift_mem (χ : Q →+ ℝ) (u : Q) (hu : 0 < χ u)
    (V : Submodule (nonnegativeRing χ) M) (m : M)
    (hm : m ∈ Submodule.span (GroupRing Q) (V : Set M)) :
    ∃ n : ℕ, shift (n • u) m ∈ V := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    refine ⟨i + j, ?_⟩
    rw [shift_add]
    apply V.add_mem
    · have h := shift_nsmul_mem χ V u hu.le j _ hi
      simpa only [shift_shift, add_nsmul, add_comm] using h
    · have h := shift_nsmul_mem χ V u hu.le i _ hj
      simpa only [shift_shift, add_nsmul] using h
  | smul r x _ hx =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := shifted_coefficient χ u hu r
    refine ⟨j + i, ?_⟩
    have h := V.smul_mem (⟨monomial (j • u) * r, hj⟩ : nonnegativeRing χ) hi
    have heq : shift ((j + i) • u) (r • x) =
        (⟨monomial (j • u) * r, hj⟩ : nonnegativeRing χ) • shift (i • u) x := by
      change monomial ((j + i) • u) • (r • x) =
        (monomial (j • u) * r) • (monomial (i • u) • x)
      rw [add_nsmul, monomial_add, mul_smul, mul_smul]
      rw [smul_comm (monomial (i • u)) r x]
    exact heq.symm ▸ h

theorem shift_difference_mem (χ : Q →+ ℝ) (u : Q) (hu : 0 ≤ χ u)
    (V : Submodule (nonnegativeRing χ) M) (m : M)
    (hm : shift u m - m ∈ V) (n : ℕ) : shift (n • u) m - m ∈ V := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := V.add_mem (shift_nsmul_mem χ V u hu n _ hm) ih
    have heq : shift (n • u) (shift u m - m) + (shift (n • u) m - m) =
        shift ((n + 1) • u) m - m := by
      rw [shift_sub, shift_shift, add_nsmul, one_nsmul]
      abel
    exact heq ▸ h

theorem eq_top_of_shift_difference (χ : Q →+ ℝ) (u : Q) (hu : 0 < χ u)
    (V : Submodule (nonnegativeRing χ) M)
    (hspan : Submodule.span (GroupRing Q) (V : Set M) = ⊤)
    (hdiff : ∀ m : M, shift u m - m ∈ V) : V = ⊤ := by
  apply top_unique
  intro m _
  obtain ⟨n, hn⟩ := eventually_shift_mem χ u hu V m (by rw [hspan]; trivial)
  have hd := shift_difference_mem χ u hu.le V m (hdiff m) n
  have h := V.sub_mem hn hd
  simpa only [sub_sub_cancel] using h

/-- A finite spanning family plus finitely many difference generators suffices
to generate over the nonnegative valuation ring. -/
theorem finite_of_shift_difference [DecidableEq M] (χ : Q →+ ℝ) (u : Q) (hu : 0 < χ u)
    (s d : Finset M) (hs : Submodule.span (GroupRing Q) (s : Set M) = ⊤)
    (hdiff : ∀ m : M, shift u m - m ∈
      Submodule.span (nonnegativeRing χ) ((s ∪ d : Finset M) : Set M)) :
    Module.Finite (nonnegativeRing χ) M := by
  classical
  let V := Submodule.span (nonnegativeRing χ) ((s ∪ d : Finset M) : Set M)
  have hspan : Submodule.span (GroupRing Q) (V : Set M) = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Submodule.span_mono
    intro m hm
    exact Submodule.subset_span (Finset.mem_union_left d hm)
  exact ⟨s ∪ d, eq_top_of_shift_difference χ u hu V hspan hdiff⟩

end Kourovka.MetabelianEnumeration.HalfspaceModule
