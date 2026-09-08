/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Covers.ComputableCoverWords

/-!
# Computable Cover Semantics

The natural-alphabet relators realize exactly the three ordinary cover families.
-/

namespace Kourovka.MetabelianEnumeration.ComputableCoverSemantics

open ComputableCoverData ComputableCoverWords FiniteCover

variable {G : Type*} [Group G]

theorem map_ordered (k : ℕ) (v : List ℤ) (f : FreeGroup ℕ →* G)
    (t : Fin k → G) (ht : ∀ i : Fin k, f (FreeGroup.of i.val) = t i) :
    f (ordered k v) = orderedWord t (fun i => v.getD i.val 0) := by
  rw [ordered, map_list_prod, List.map_map, ← List.map_coe_finRange k]
  simp only [← List.ofFn_eq_map, List.map_ofFn, Function.comp_def,
    map_zpow, ht, orderedWord]

theorem map_polynomial (k : ℕ) (x : FreeGroup ℕ) (p : PolynomialCode)
    (f : FreeGroup ℕ →* G) (t : Fin k → G)
    (ht : ∀ i : Fin k, f (FreeGroup.of i.val) = t i) :
    f (ComputableCoverWords.polynomial k x p) =
      polynomialWord t (f x) (decodePolynomial k p) := by
  simp only [ComputableCoverWords.polynomial, polynomialWord, decodePolynomial,
    map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro term _
  simp only [Function.comp_def, map_conjugate, map_zpow]
  cases p.1 <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.cond_false, Bool.cond_true, map_inv,
    map_ordered k term.1 f t ht]

theorem relators_realizes (data : DatumCode) (R : ℕ) (f : FreeGroup ℕ →* G)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G)
    (ht : ∀ i, f (FreeGroup.of i.val) = t i)
    (hA : ∀ i, f (FreeGroup.of (dimension data + i.val)) = A i) :
    (∀ r ∈ ComputableCoverWords.relators data R, f r = 1) ↔
      Realizes (decode data) R t A := by
  have htm (i j : Fin (dimension data)) :
      f (tRelator (data, (i.val, j.val))) =
        rightComm (t i) (t j) * (A ((decode data).designated i j))⁻¹ := by
    simp only [tRelator, map_mul, map_inv, map_rightComm, ht]
    exact congrArg (fun x => rightComm (t i) (t j) * x⁻¹)
      (hA ((decode data).designated i j))
  have hsm (i j : Fin (alphabet data)) (v : Fin (dimension data) → ℤ) :
      f (shortRelator (data, ((i.val, j.val), List.ofFn v))) =
        rightComm (A i) (conjugate (A j) (orderedWord t v)) := by
    simp only [shortRelator, map_rightComm, map_conjugate, hA,
      map_ordered _ _ f t ht, getD_ofFn]
  have hpm (i : Fin (alphabet data)) (p : PolynomialCode) :
      f (polynomialRelator ((data, i.val), p)) =
        (A i)⁻¹ * polynomialWord t (A i) (decodePolynomial (dimension data) p) := by
    simp only [polynomialRelator, map_mul, map_inv, hA, map_polynomial _ _ p f t ht]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      have hm : tRelator (data, (i.val, j.val)) ∈ ComputableCoverWords.relators data R := by
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_flatMap.mpr
        refine ⟨i.val, List.mem_range.mpr i.isLt, List.mem_map.mpr ?_⟩
        exact ⟨j.val, List.mem_filter.mpr ⟨List.mem_range.mpr j.isLt,
          decide_eq_true hij⟩, rfl⟩
      have he := h _ hm
      rw [htm] at he
      exact mul_inv_eq_one.mp he
    · intro i j v hv
      have hm : shortRelator (data, ((i.val, j.val), List.ofFn v)) ∈
          ComputableCoverWords.relators data R := by
        apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨i.val, List.mem_range.mpr i.isLt, List.mem_flatMap.mpr ?_⟩
        refine ⟨j.val, List.mem_range.mpr j.isLt, List.mem_map.mpr ?_⟩
        exact ⟨List.ofFn v, (ComputableLatticeBall.mem_ball_ofFn v).mpr hv, rfl⟩
      simpa only [hsm] using h _ hm
    · intro i p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      have hm : polynomialRelator ((data, i.val), q) ∈
          ComputableCoverWords.relators data R := by
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        exact ⟨i.val, List.mem_range.mpr i.isLt, List.mem_map.mpr ⟨q, hq, rfl⟩⟩
      have he := h _ hm
      rw [hpm] at he
      exact inv_mul_eq_one.mp he
  · intro h r hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
        obtain ⟨hj, hij⟩ := List.mem_filter.mp hj
        let i' : Fin (dimension data) := ⟨i, List.mem_range.mp hi⟩
        let j' : Fin (dimension data) := ⟨j, List.mem_range.mp hj⟩
        change f (tRelator (data, (i'.val, j'.val))) = 1
        rw [htm, h.t_comm i' j' (of_decide_eq_true hij), mul_inv_cancel]
      · obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
        obtain ⟨j, hj, hr⟩ := List.mem_flatMap.mp hr
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
        obtain ⟨w, rfl, hw⟩ := ComputableLatticeBall.mem_ball _ _ _ |>.mp hv
        let i' : Fin (alphabet data) := ⟨i, List.mem_range.mp hi⟩
        let j' : Fin (alphabet data) := ⟨j, List.mem_range.mp hj⟩
        change f (shortRelator (data, ((i'.val, j'.val), List.ofFn w))) = 1
        rw [hsm]
        exact h.short_comm i' j' w hw
    · obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
      let i' : Fin (alphabet data) := ⟨i, List.mem_range.mp hi⟩
      change f (polynomialRelator ((data, i'.val), p)) = 1
      rw [hpm, ← h.polynomial i' _ (List.mem_map.mpr ⟨p, hp, rfl⟩), inv_mul_cancel]


def codeT (data : DatumCode) (R : ℕ) (i : Fin (dimension data)) :
    MetabelianEnumeration.GroupOf (presentation data R) :=
  PresentedGroup.of (Fin.castAdd (alphabet data) i)

def codeA (data : DatumCode) (R : ℕ) (i : Fin (alphabet data)) :
    MetabelianEnumeration.GroupOf (presentation data R) :=
  PresentedGroup.of (Fin.natAdd (dimension data) i)

theorem code_generators (data : DatumCode) (R : ℕ) :
    Subgroup.closure (Set.range (codeT data R) ∪ Set.range (codeA data R)) = ⊤ := by
  have he : Set.range (codeT data R) ∪ Set.range (codeA data R) =
      Set.range (PresentedGroup.of (rels := relations (presentation data R))) := by
    ext x
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Fin.castAdd (alphabet data) i, rfl⟩
      · exact ⟨Fin.natAdd (dimension data) i, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i using Fin.addCases with
      | left j => exact Or.inl ⟨j, rfl⟩
      | right j => exact Or.inr ⟨j, rfl⟩
  rw [he]
  exact PresentedGroup.closure_range_of _

def naturalAssignment (data : DatumCode)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G) : FreeGroup ℕ →* G :=
  (FreeGroup.lift (generatorAssignment t A)).comp
    (ComputablePresentations.restrictGenerators (dimension data + alphabet data))

theorem naturalAssignment_t (data : DatumCode)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G) (i : Fin (dimension data)) :
    naturalAssignment data t A (FreeGroup.of i.val) = t i := by
  have hi : i.val < dimension data + alphabet data := lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)
  simp only [naturalAssignment, MonoidHom.comp_apply, ComputablePresentations.restrictGenerators,
    FreeGroup.lift_apply_of, dif_pos hi]
  change generatorAssignment t A (Fin.castAdd (alphabet data) i) = _
  simp [generatorAssignment]

theorem naturalAssignment_A (data : DatumCode)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G) (i : Fin (alphabet data)) :
    naturalAssignment data t A (FreeGroup.of (dimension data + i.val)) = A i := by
  have hi : dimension data + i.val < dimension data + alphabet data := Nat.add_lt_add_left i.isLt _
  simp only [naturalAssignment, MonoidHom.comp_apply, ComputablePresentations.restrictGenerators,
    FreeGroup.lift_apply_of, dif_pos hi]
  change generatorAssignment t A (Fin.natAdd (dimension data) i) = _
  simp [generatorAssignment]

theorem code_realizes (data : DatumCode) (R : ℕ) :
    Realizes (decode data) R (codeT data R) (codeA data R) := by
  let f := (PresentedGroup.mk (relations (presentation data R))).comp
    (ComputablePresentations.restrictGenerators (dimension data + alphabet data))
  have he : FreeGroup.lift (generatorAssignment (codeT data R) (codeA data R)) =
      PresentedGroup.mk (relations (presentation data R)) := by
    apply FreeGroup.ext_hom
    intro i
    cases i using Fin.addCases <;>
      simp [generatorAssignment, codeT, codeA, PresentedGroup.of] <;> rfl
  have ht : ∀ i : Fin (dimension data), f (FreeGroup.of i.val) = codeT data R i := by
    intro i
    dsimp only [f]
    rw [← he]
    exact naturalAssignment_t data _ _ i
  have hA : ∀ i : Fin (alphabet data),
      f (FreeGroup.of (dimension data + i.val)) = codeA data R i := by
    intro i
    dsimp only [f]
    rw [← he]
    exact naturalAssignment_A data _ _ i
  apply (relators_realizes data R f _ _ ht hA).mp
  intro r hr
  change PresentedGroup.mk (relations (presentation data R))
    (ComputablePresentations.restrictGenerators _ r) = 1
  rw [← FreeGroup.mk_toWord (x := r), ComputablePresentations.restrict_mk]
  apply PresentedGroup.one_of_mem
  exact List.mem_map.mpr ⟨r.toWord, List.mem_map.mpr ⟨r, hr, rfl⟩, rfl⟩

theorem checked_presentation_metabelian (data : DatumCode) (r : ℕ)
    (hcheck : ComputableCoverData.check data r = true) :
    Metabelian (MetabelianEnumeration.GroupOf (presentation data (radius data r))) := by
  exact metabelian_surjective
    (realizationHom (decode data) (radius data r) _ _ (code_realizes data (radius data r)))
    (realizationHom_surjective (decode data) (radius data r) _ _
      (code_realizes data (radius data r)) (code_generators data (radius data r)))
    (ComputableCoverData.check_sound data r hcheck)

def codeRealizationHom (data : DatumCode) (R : ℕ)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G)
    (h : Realizes (decode data) R t A) :
    MetabelianEnumeration.GroupOf (presentation data R) →* G :=
  PresentedGroup.toGroup (f := generatorAssignment t A) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    rw [← ComputablePresentations.restrict_mk, FreeGroup.mk_toWord]
    exact (relators_realizes data R (naturalAssignment data t A) t A
      (naturalAssignment_t data t A) (naturalAssignment_A data t A)).mpr h v hv)

theorem codeRealizationHom_generator (data : DatumCode) (R : ℕ)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G)
    (h : Realizes (decode data) R t A) (i : Fin (dimension data + alphabet data)) :
    codeRealizationHom data R t A h (PresentedGroup.of i) = generatorAssignment t A i :=
  PresentedGroup.toGroup.of _

theorem codeRealizationHom_surjective (data : DatumCode) (R : ℕ)
    (t : Fin (dimension data) → G) (A : Fin (alphabet data) → G)
    (h : Realizes (decode data) R t A)
    (hgen : Subgroup.closure (Set.range t ∪ Set.range A) = ⊤) :
    Function.Surjective (codeRealizationHom data R t A h) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen, Subgroup.closure_le]
  rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · refine ⟨PresentedGroup.of (Fin.castAdd (alphabet data) i), ?_⟩
    simp only [codeRealizationHom_generator, generatorAssignment, Fin.addCases_left]
  · refine ⟨PresentedGroup.of (Fin.natAdd (dimension data) i), ?_⟩
    simp only [codeRealizationHom_generator, generatorAssignment, Fin.addCases_right]

theorem presentation_epimorphism (data : DatumCode) (R : ℕ) :
    ∃ f : MetabelianEnumeration.GroupOf (presentation data R) →*
      FiniteCover.GroupOf (decode data) R, Function.Surjective f := by
  exact ⟨codeRealizationHom data R _ _ (FiniteCover.group_realizes (decode data) R),
    codeRealizationHom_surjective data R _ _ (FiniteCover.group_realizes (decode data) R)
      (FiniteCover.group_generators (decode data) R)⟩

end Kourovka.MetabelianEnumeration.ComputableCoverSemantics
