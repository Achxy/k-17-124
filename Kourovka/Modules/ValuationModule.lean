/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Modules.TamenessCompactness
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.RingTheory.Finiteness.Nakayama

/-!
# Valuation Module

The algebraic direction of Bieri–Strebel Proposition 2.1.
A module finite over a valuation half-ring has a centralizing Laurent polynomial
with strictly positive support. The determinant argument is supplied by the
kernel-checked Nakayama lemma.
-/

noncomputable section

namespace Kourovka.MetabelianEnumeration.ValuationModule

variable {Q : Type*} [AddCommGroup Q] [DecidableEq Q]

abbrev GroupRing (Q : Type*) [AddCommGroup Q] := AddMonoidAlgebra ℤ Q

def nonnegativeRing (χ : Q →+ ℝ) : Subring (GroupRing Q) where
  carrier := {p | ∀ u ∈ p.support, 0 ≤ χ u}
  zero_mem' := by simp
  one_mem' := by
    intro u hu
    have : u = 0 := by simpa [AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply, eq_comm] using hu
    simp [this]
  add_mem' := by
    intro p q hp hq u hu
    rcases Finset.mem_union.mp (Finsupp.support_add hu) with hu | hu
    · exact hp u hu
    · exact hq u hu
  neg_mem' := by
    intro p hp u hu
    exact hp u (by simpa using hu)
  mul_mem' := by
    intro p q hp hq u hu
    obtain ⟨v, hv, w, hw, rfl⟩ := Finset.mem_image₂.mp (AddMonoidAlgebra.support_mul p q hu)
    simpa using add_nonneg (hp v hv) (hq w hw)

def positiveIdeal (χ : Q →+ ℝ) : Ideal (nonnegativeRing χ) where
  carrier := {p | ∀ u ∈ (p : GroupRing Q).support, 0 < χ u}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq u hu
    rcases Finset.mem_union.mp (Finsupp.support_add hu) with hu | hu
    · exact hp u hu
    · exact hq u hu
  smul_mem' := by
    intro p q hq u hu
    obtain ⟨v, hv, w, hw, rfl⟩ :=
      Finset.mem_image₂.mp (AddMonoidAlgebra.support_mul (p : GroupRing Q) q hu)
    simpa using add_pos_of_nonneg_of_pos (p.2 v hv) (hq w hw)

omit [DecidableEq Q] in
theorem exists_positive (χ : Q →+ ℝ) (hχ : χ ≠ 0) : ∃ q, 0 < χ q := by
  have h : ∃ q, χ q ≠ 0 := by
    by_contra! h
    apply hχ
    ext q
    exact h q
  obtain ⟨q, hq⟩ := h
  rcases lt_or_gt_of_ne hq with hq | hq
  · exact ⟨-q, by simpa using neg_pos.mpr hq⟩
  · exact ⟨q, hq⟩

def positiveMonomial (χ : Q →+ ℝ) (q : Q) (hq : 0 < χ q) : nonnegativeRing χ :=
  ⟨AddMonoidAlgebra.single q 1, by
    intro u hu
    have : u = q := by simpa [AddMonoidAlgebra.single_apply, eq_comm] using hu
    exact this.symm ▸ hq.le⟩

theorem positiveMonomial_mem (χ : Q →+ ℝ) (q : Q) (hq : 0 < χ q) :
    positiveMonomial χ q hq ∈ positiveIdeal χ := by
  intro u hu
  have : u = q := by simpa [positiveMonomial, AddMonoidAlgebra.single_apply, eq_comm] using hu
  exact this.symm ▸ hq

variable {M : Type*} [AddCommGroup M] [Module (GroupRing Q) M]

theorem top_le_positive_smul (χ : Q →+ ℝ) (hχ : χ ≠ 0) :
    (⊤ : Submodule (nonnegativeRing χ) M) ≤ positiveIdeal χ • ⊤ := by
  obtain ⟨q, hq⟩ := exists_positive χ hχ
  intro m _
  have heq : positiveMonomial χ q hq • ((AddMonoidAlgebra.single (-q) 1 : GroupRing Q) • m) = m := by
    change (AddMonoidAlgebra.single q 1 : GroupRing Q) •
      ((AddMonoidAlgebra.single (-q) 1 : GroupRing Q) • m) = m
    rw [← mul_smul, AddMonoidAlgebra.single_mul_single]
    simp [← AddMonoidAlgebra.one_def]
  rw [← heq]
  exact Submodule.smul_mem_smul (positiveMonomial_mem χ q hq) (Submodule.mem_top)

/-- The positive-centralizer half of Bieri–Strebel Proposition 2.1, for the
actual group ring and its support-defined valuation subring. -/
theorem positive_centralizer_of_finite (χ : Q →+ ℝ) (hχ : χ ≠ 0)
    [Module.Finite (nonnegativeRing χ) M] :
    ∃ p : GroupRing Q, (∀ u ∈ p.support, 0 < χ u) ∧ ∀ m : M, p • m = m := by
  obtain ⟨p, hp, hact⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul
    (positiveIdeal χ) (⊤ : Submodule (nonnegativeRing χ) M) Module.Finite.fg_top
      (top_le_positive_smul (M := M) χ hχ)
  exact ⟨p, hp, fun m => hact m (Submodule.mem_top)⟩

def LowerBound (χ : Q →+ ℝ) (p : GroupRing Q) (c : ℝ) : Prop :=
  ∀ u ∈ p.support, c ≤ χ u

theorem lowerBound_mul (χ : Q →+ ℝ) {p q : GroupRing Q} {c d : ℝ}
    (hp : LowerBound χ p c) (hq : LowerBound χ q d) : LowerBound χ (p * q) (c + d) := by
  intro u hu
  obtain ⟨v, hv, w, hw, rfl⟩ := Finset.mem_image₂.mp (AddMonoidAlgebra.support_mul p q hu)
  simpa using add_le_add (hp v hv) (hq w hw)

theorem lowerBound_pow (χ : Q →+ ℝ) {p : GroupRing Q} {c : ℝ}
    (hp : LowerBound χ p c) (n : ℕ) : LowerBound χ (p ^ n) (n * c) := by
  induction n with
  | zero =>
    intro u hu
    have : u = 0 := by simpa [AddMonoidAlgebra.one_def, AddMonoidAlgebra.single_apply, eq_comm] using hu
    simp [this]
  | succ n ih =>
    simpa [pow_succ, Nat.cast_add, add_mul] using lowerBound_mul χ ih hp

omit [DecidableEq Q] in
theorem lowerBound_exists (χ : Q →+ ℝ) (p : GroupRing Q) : ∃ c, LowerBound χ p c := by
  obtain ⟨c, hc⟩ := FourierMotzkin.exists_common_lower_bound (p.support.toList.map χ)
  exact ⟨c, fun u hu => hc _ (List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu, rfl⟩)⟩

theorem positive_lowerBound_exists (χ : Q →+ ℝ) (p : GroupRing Q)
    (hp : ∀ u ∈ p.support, 0 < χ u) : ∃ c, 0 < c ∧ LowerBound χ p c := by
  have hf : ∀ s : Finset Q, (∀ u ∈ s, 0 < χ u) →
      ∃ c : ℝ, 0 < c ∧ ∀ u ∈ s, c ≤ χ u := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨1, by norm_num, by simp⟩
    | @insert u s hu ih =>
      intro h
      obtain ⟨c, hc, hb⟩ := ih (fun v hv => h v (Finset.mem_insert_of_mem hv))
      refine ⟨min (χ u) c, lt_min (h u (Finset.mem_insert_self _ _)) hc, ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hb v hv)
  exact hf p.support hp

omit [DecidableEq Q] in
theorem centralizer_pow {p : GroupRing Q} (hp : ∀ m : M, p • m = m) (n : ℕ) :
    ∀ m : M, (p ^ n) • m = m := by
  induction n with
  | zero => simp
  | succ n ih => intro m; rw [pow_succ, mul_smul, hp, ih]

/-- Multiplying by enough copies of a positive centralizer moves every Laurent
coefficient into the valuation half-ring without changing its action. -/
theorem scalar_replacement (χ : Q →+ ℝ) (p : GroupRing Q)
    (hp : ∀ u ∈ p.support, 0 < χ u) (hact : ∀ m : M, p • m = m)
    (r : GroupRing Q) : ∃ s : nonnegativeRing χ, ∀ m : M, s • m = r • m := by
  obtain ⟨c, hc⟩ := lowerBound_exists χ r
  obtain ⟨d, hd, hdp⟩ := positive_lowerBound_exists χ p hp
  obtain ⟨n, hn⟩ := exists_nat_gt (-c / d)
  have hcn : 0 ≤ c + n * d := by
    have := (div_lt_iff₀ hd).mp hn
    linarith
  have hprod := lowerBound_mul χ hc (lowerBound_pow χ hdp n)
  refine ⟨⟨r * p ^ n, fun u hu => hcn.trans (hprod u hu)⟩, ?_⟩
  intro m
  change (r * p ^ n) • m = r • m
  rw [mul_smul, centralizer_pow hact]

theorem span_eq_half_span (χ : Q →+ ℝ) (p : GroupRing Q)
    (hp : ∀ u ∈ p.support, 0 < χ u) (hact : ∀ m : M, p • m = m)
    (s : Set M) : ∀ m ∈ Submodule.span (GroupRing Q) s,
      m ∈ Submodule.span (nonnegativeRing χ) s := by
  intro m hm
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    obtain ⟨r', hr'⟩ := scalar_replacement χ p hp hact r
    rw [← hr' x]
    exact Submodule.smul_mem _ r' hx

/-- The converse direction preserves any chosen finite generating family. -/
theorem finite_of_positive_centralizer (χ : Q →+ ℝ) [Module.Finite (GroupRing Q) M]
    (p : GroupRing Q) (hp : ∀ u ∈ p.support, 0 < χ u) (hact : ∀ m : M, p • m = m) :
    Module.Finite (nonnegativeRing χ) M := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := GroupRing Q) (M := M)
  refine ⟨s, top_unique ?_⟩
  intro m _
  exact span_eq_half_span χ p hp hact s m (by rw [hs]; trivial)

/-- Bieri–Strebel's directional centralizer criterion, proved for the actual
Laurent module rather than assumed as a certificate field. -/
theorem finite_iff_positive_centralizer (χ : Q →+ ℝ) (hχ : χ ≠ 0)
    [Module.Finite (GroupRing Q) M] :
    Module.Finite (nonnegativeRing χ) M ↔
      ∃ p : GroupRing Q, (∀ u ∈ p.support, 0 < χ u) ∧ ∀ m : M, p • m = m := by
  constructor
  · intro h
    letI := h
    exact positive_centralizer_of_finite χ hχ
  · rintro ⟨p, hp, hact⟩
    exact finite_of_positive_centralizer χ p hp hact

end Kourovka.MetabelianEnumeration.ValuationModule
