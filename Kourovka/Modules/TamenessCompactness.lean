/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Covers.FiniteCover

/-!
# Tameness Compactness

The finite extraction in the Bieri–Strebel centralizer criterion.
Pointwise centralizing polynomials need not come from an a priori finite family.
Compactness supplies a finite family while retaining its algebraic identities.
-/

namespace Kourovka.MetabelianEnumeration.TamenessCompactness

open ConeVerifier FiniteCover

def polynomialSupport {k : ℕ} (p : Polynomial k) : List (Vec k) :=
  p.2.map fun term => fun i => (term.1 i : ℚ)

/-- Any family of finite supports covering the nonzero directions admits a
finite subfamily. The selected indices retain an arbitrary original property. -/
theorem finite_support_selection {k : ℕ} {ι : Type*}
    (support : ι → List (Vec k)) (admissible : ι → Prop)
    (h : ∀ x : Fin k → ℝ, x ≠ 0 →
      ∃ i, admissible i ∧ ∀ u ∈ support i, 0 < dot u x) :
    ∃ selected : List ι, (∀ i ∈ selected, admissible i) ∧
      ConeCover (selected.map support) := by
  classical
  let U (i : {i // admissible i}) : Set (Fin k → ℝ) :=
    {x | 0 < supportScore (support i.1) x}
  have ho : ∀ i, IsOpen (U i) := fun i =>
    isOpen_lt continuous_const (continuous_supportScore (support i.1))
  have hcover : {x : Fin k → ℝ | CubeSphere x} ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨i, hi, hpos⟩ := h x (cubeSphere_ne_zero hx)
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i, hi⟩, ?_⟩
    exact (supportScore_gt_iff (support i) x 0 (by norm_num)).mpr hpos
  obtain ⟨selected, hs⟩ := (isCompact_cubeSphere k).elim_finite_subcover U ho hcover
  refine ⟨selected.toList.map Subtype.val, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact j.2
  · apply (coneCover_iff_cubeMargin _).mpr
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs hx)
    obtain ⟨his, hix⟩ := Set.mem_iUnion.mp hi
    refine ⟨support i.1, List.mem_map.mpr ⟨i.1,
      List.mem_map.mpr ⟨i, Finset.mem_toList.mpr his, rfl⟩, rfl⟩, ?_⟩
    simpa only [Rat.cast_zero] using
      (supportScore_gt_iff (support i.1) x 0 (by norm_num)).mp hix

/-- The finite geometric extraction retains every signed polynomial identity
in the target group, with the literal inverse word used for negative tags. -/
theorem finite_polynomial_identities {k a : ℕ} {G : Type*} [Group G]
    (t : Fin k → G) (A : Fin a → G)
    (h : ∀ x : Fin k → ℝ, x ≠ 0 → ∃ p : Polynomial k,
      (∀ i, A i = polynomialWord t (A i) p) ∧
      ∀ u ∈ polynomialSupport p, 0 < dot u x) :
    ∃ polynomials : List (Polynomial k),
      (∀ p ∈ polynomials, ∀ i, A i = polynomialWord t (A i) p) ∧
        ConeCover (polynomials.map polynomialSupport) :=
  finite_support_selection polynomialSupport (fun p => ∀ i, A i = polynomialWord t (A i) p) h

end Kourovka.MetabelianEnumeration.TamenessCompactness
