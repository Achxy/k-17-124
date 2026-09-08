/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Collection.CollectionRadius
import Kourovka.Covers.CertifiedRadius
import Kourovka.Modules.TamenessCompactness

/-!
# Cover Soundness

Soundness of the actual finite Bieri–Strebel group presentation.
-/

namespace Kourovka.MetabelianEnumeration.FiniteCover

open Collection

variable {G : Type*} [Group G]

theorem conjugate_list_prod (l : List G) (w : G) :
    conjugate l.prod w = (l.map fun x => conjugate x w).prod := by
  simpa [MulAut.conj_apply, conjugate] using
    (MulAut.conj w⁻¹).toMonoidHom.map_list_prod l

theorem conjugate_zpow (x w : G) (n : ℤ) :
    conjugate (x ^ n) w = conjugate x w ^ n := by
  simpa [MulAut.conj_apply, conjugate] using
    (MulAut.conj w⁻¹).toMonoidHom.map_zpow x n

theorem commute_polynomial_conjugate {k : ℕ} (t : Fin k → G)
    (x b V : G) (p : Polynomial k)
    (h : ∀ term ∈ p.2, Commute x (conjugate b
      ((if p.1 then orderedWord t term.1 else (orderedWord t term.1)⁻¹) * V))) :
    Commute x (conjugate (polynomialWord t b p) V) := by
  rw [polynomialWord, conjugate_list_prod, List.map_map]
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨term, ht, rfl⟩ := List.mem_map.mp hy
  simpa only [Function.comp_apply, ← conjugate_mul, conjugate_zpow] using
    (h term ht).zpow_right term.2

/-- A single uniform increase of radius follows from either sign of the
polynomial identity and the certified shrinking direction. -/
theorem radius_step {k a : ℕ} (data : Datum k a) (t : Fin k → G) (A : Fin a → G)
    (hk : 1 ≤ k) (C D ρ δ : ℝ)
    (hC : 0 < C) (hρk : 2 * (k : ℝ) < ρ) (hρD : 2 * (k : ℝ) * D < ρ)
    (hρC : C < ρ) (hρD2 : D ^ 2 < C * ρ)
    (hδ : 0 < δ) (hδC : δ ≤ C / 4) (hδk : δ < 1 / (2 * (k : ℝ)))
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (data.designated i j))
    (hs : ∀ p q v, v ∈ ball ρ → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hp : ∀ i p, p ∈ data.polynomials → A i = polynomialWord t (A i) p)
    (hbound : ∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ D)
    (hdir : ∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
      ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤ -C * ‖euclidean v‖) :
    ∀ p q v, v ∈ ball (ρ + δ) → Commute (A p) (conjugate (A q) (orderedWord t v)) := by
  intro p q v hv
  by_cases hv0 : v ∈ ball ρ
  · exact hs p q v hv0
  have hvge : ρ ≤ ‖euclidean v‖ := le_of_not_gt hv0
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hρ0 : 0 < ρ := by linarith
  have hvne : v ≠ 0 := by
    intro he
    have hzero : euclidean v = 0 := by ext i; simp [he, euclidean]
    rw [hzero, norm_zero] at hvge
    linarith
  obtain ⟨poly, hpoly, hdot⟩ := hdir v hvne
  have hshort : ∀ term ∈ poly.2, ‖euclidean term.1‖ ≤ ρ / (2 * k) := by
    intro term hterm
    exact (hbound poly hpoly term hterm).trans
      ((le_div_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr (by nlinarith))
  have hsum : ∀ term ∈ poly.2, ‖euclidean (term.1 + v)‖ < ρ := by
    intro term hterm
    have hu := hbound poly hpoly term hterm
    have hD0 : 0 ≤ D := (norm_nonneg _).trans hu
    have h := vector_radius_shrink (euclidean v) (euclidean term.1) C D ρ δ
      hC hρC hρD2 hδ hδC hvge hv (by nlinarith [norm_nonneg (euclidean term.1)])
      (hdot term hterm)
    simpa only [euclidean_add, add_comm] using h
  have hv' : ‖euclidean v‖ < ρ + 1 / (2 * k) := lt_of_lt_of_le hv (by linarith)
  cases hsign : poly.1
  · apply (commute_conjugate_iff _ _ _).mpr
    apply Commute.symm
    rw [hp p poly hpoly]
    apply commute_polynomial_conjugate
    intro term hterm
    simp only [hsign, Bool.false_eq_true, ↓reduceIte]
    exact collection_radius_inverse A t data.designated hk ρ hρk ht hs q p term.1 v
      (hshort term hterm) hv' (hsum term hterm)
  · rw [hp q poly hpoly]
    apply commute_polynomial_conjugate
    intro term hterm
    simp only [hsign, ↓reduceIte]
    exact collection_radius A t data.designated hk ρ hρk ht hs p q term.1 v
      (hshort term hterm) hv' (hsum term hterm)

/-- Repeated uniform radius increases prove every ordered commutator relation. -/
theorem all_ordered_commute {k a : ℕ} (data : Datum k a) (t : Fin k → G) (A : Fin a → G)
    (hk : 1 ≤ k) (C D R δ : ℝ)
    (hC : 0 < C) (hRk : 2 * (k : ℝ) < R) (hRD : 2 * (k : ℝ) * D < R)
    (hRC : C < R) (hRD2 : D ^ 2 < C * R)
    (hδ : 0 < δ) (hδC : δ ≤ C / 4) (hδk : δ < 1 / (2 * (k : ℝ)))
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (data.designated i j))
    (hs : ∀ p q v, v ∈ ball R → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hp : ∀ i p, p ∈ data.polynomials → A i = polynomialWord t (A i) p)
    (hbound : ∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ D)
    (hdir : ∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
      ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤ -C * ‖euclidean v‖) :
    ∀ p q v, Commute (A p) (conjugate (A q) (orderedWord t v)) := by
  have hstep : ∀ n : ℕ, ∀ p q v, v ∈ ball (R + n * δ) →
      Commute (A p) (conjugate (A q) (orderedWord t v)) := by
    intro n
    induction n with
    | zero => simpa using hs
    | succ n ih =>
      have hn : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg n) hδ.le
      have h := radius_step data t A hk C D (R + n * δ) δ hC
        (by linarith) (by linarith) (by linarith)
        (by nlinarith [mul_nonneg hC.le hn]) hδ hδC hδk ht ih hp hbound hdir
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_assoc] using h
  intro p q v
  obtain ⟨n, hn⟩ := exists_nat_gt ((‖euclidean v‖ - R) / δ)
  exact hstep n p q v (by
    change ‖euclidean v‖ < R + n * δ
    have := (div_lt_iff₀ hδ).mp hn
    linarith)

/-- Commutativity of the images of generators extends to the whole group. -/
theorem commute_hom_of_generators {H : Type*} [Group H] (f : G →* H) (S : Set G)
    (hS : Subgroup.closure S = ⊤)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, Commute (f x) (f y)) :
    ∀ x y : G, Commute (f x) (f y) := by
  have hfirst : ∀ x ∈ S, ∀ y : G, Commute (f x) (f y) := by
    intro x hx y
    have hle : Subgroup.closure S ≤ (Subgroup.centralizer {f x}).comap f := by
      apply (Subgroup.closure_le _).mpr
      intro z hz
      change ∀ w ∈ ({f x} : Set H), w * f z = f z * w
      intro w hw
      rcases Set.mem_singleton_iff.mp hw with rfl
      exact hpair x hx z hz
    have hy := hle (show y ∈ Subgroup.closure S by rw [hS]; trivial)
    exact hy (f x) (Set.mem_singleton _)
  intro x y
  have hle : Subgroup.closure S ≤ (Subgroup.centralizer {f y}).comap f := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    change ∀ w ∈ ({f y} : Set H), w * f z = f z * w
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact (hfirst z hz y).symm
  have hx := hle (show x ∈ Subgroup.closure S by rw [hS]; trivial)
  exact (hx (f y) (Set.mem_singleton _)).symm

/-- The designated commutators make the quotient by the normal closure
abelian, while infinite collection makes that normal closure abelian. -/
theorem metabelian_of_all_ordered_commute {k a : ℕ} (data : Datum k a)
    (t : Fin k → G) (A : Fin a → G)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (data.designated i j))
    (hs : ∀ p q v, Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hgen : Subgroup.closure (Set.range t ∪ Set.range A) = ⊤) : Metabelian G := by
  let N := Subgroup.normalClosure (Set.range A)
  let f := QuotientGroup.mk' N
  have hA : ∀ i, f (A i) = 1 := by
    intro i
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨i, rfl⟩)
  have htt : ∀ i j, Commute (f (t i)) (f (t j)) := by
    have hlt : ∀ i j, i < j → Commute (f (t i)) (f (t j)) := by
      intro i j hij
      apply (rightComm_eq_one_iff _ _).mp
      rw [← map_rightComm, ht i j hij, hA]
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hlt i j hij
    · exact Commute.refl _
    · exact (hlt j i hji).symm
  have hf := commute_hom_of_generators f (Set.range t ∪ Set.range A) hgen (by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩) y (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact htt i j
    · simp [hA]
    · simp [hA]
    · simp [hA])
  have hmem : ∀ x y : G, ⁅x, y⁆ ∈ N := by
    intro x y
    apply (QuotientGroup.eq_one_iff _).mp
    change f ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hf x y
  intro x y z w
  exact normalClosure_abelian A t data.designated ht hs hgen _ (hmem x y) _ (hmem z w)

theorem realizes_of_relators {k a : ℕ} (data : Datum k a) (R : ℕ)
    (t : Fin k → G) (A : Fin a → G)
    (h : ∀ r ∈ relators data R, FreeGroup.lift (generatorAssignment t A) r = 1) :
    Realizes data R t A := by
  constructor
  · intro i j hij
    have hr := h (rightComm (tGenerator k a i) (tGenerator k a j) *
      (aGenerator k a (data.designated i j))⁻¹) (by
        simp only [relators, List.mem_append]
        left; left
        simp only [tRelations, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
          List.mem_filter, true_and]
        exact ⟨i, j, by simpa using hij, rfl⟩)
    simpa only [map_mul, map_inv, map_rightComm, lift_tGenerator, lift_aGenerator,
      mul_inv_eq_one] using hr
  · intro i j v hv
    have hr := h (rightComm (aGenerator k a i) (conjugate (aGenerator k a j)
      (orderedWord (tGenerator k a) v))) (by
        simp only [relators, List.mem_append]
        left; right
        simp only [shortRelations, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
        exact ⟨i, j, v, (mem_latticeBallList v).mpr hv, rfl⟩)
    simpa only [map_rightComm, map_conjugate, map_orderedWord, lift_tGenerator,
      lift_aGenerator] using hr
  · intro i p hp
    have hr := h ((aGenerator k a i)⁻¹ * polynomialWord (tGenerator k a) (aGenerator k a i) p) (by
      simp only [relators, List.mem_append]
      right
      simp only [polynomialRelations, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
      exact ⟨i, p, hp, rfl⟩)
    have he : (A i)⁻¹ * polynomialWord t (A i) p = 1 := by
      simpa only [map_mul, map_inv, map_polynomialWord, lift_tGenerator, lift_aGenerator] using hr
    exact inv_mul_eq_one.mp he

def groupT {k a : ℕ} (data : Datum k a) (R : ℕ) (i : Fin k) : GroupOf data R :=
  PresentedGroup.of (Fin.castAdd a i)

def groupA {k a : ℕ} (data : Datum k a) (R : ℕ) (i : Fin a) : GroupOf data R :=
  PresentedGroup.of (Fin.natAdd k i)

theorem group_realizes {k a : ℕ} (data : Datum k a) (R : ℕ) :
    Realizes data R (groupT data R) (groupA data R) := by
  apply realizes_of_relators
  have he : FreeGroup.lift (generatorAssignment (groupT data R) (groupA data R)) =
      PresentedGroup.mk (WordCertificates.relSet (relators data R)) := by
    apply FreeGroup.ext_hom
    intro i
    cases i using Fin.addCases <;> simp [generatorAssignment, groupT, groupA, PresentedGroup.of] <;> rfl
  intro r hr
  rw [he]
  exact PresentedGroup.one_of_mem hr

theorem group_generators {k a : ℕ} (data : Datum k a) (R : ℕ) :
    Subgroup.closure (Set.range (groupT data R) ∪ Set.range (groupA data R)) = ⊤ := by
  have he : Set.range (groupT data R) ∪ Set.range (groupA data R) =
      Set.range (PresentedGroup.of (rels := WordCertificates.relSet (relators data R))) := by
    ext x
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨Fin.castAdd a i, rfl⟩
      · exact ⟨Fin.natAdd k i, rfl⟩
    · rintro ⟨i, rfl⟩
      cases i using Fin.addCases with
      | left j => exact Or.inl ⟨j, rfl⟩
      | right j => exact Or.inr ⟨j, rfl⟩
  rw [he]
  exact PresentedGroup.closure_range_of _

/-- Explicit numerical certificates establish metabelianity of the actual
finite presented group, with no assumed infinite commutation relations. -/
theorem certified_cover_metabelian {k a : ℕ} (data : Datum k a) (hk : 1 ≤ k)
    (C D : ℚ) (hC : 0 < C) (hD : 1 ≤ D) (hCD : C ≤ D)
    (hbound : ∀ p ∈ data.polynomials, ∀ term ∈ p.2, ‖euclidean term.1‖ ≤ (D : ℝ))
    (hdir : ∀ v : Lattice k, v ≠ 0 → ∃ p ∈ data.polynomials,
      ∀ term ∈ p.2, inner ℝ (euclidean v) (euclidean term.1) ≤ -(C : ℝ) * ‖euclidean v‖) :
    Metabelian (GroupOf data (certifiedRadius k C D)) := by
  let R := certifiedRadius k C D
  let t := groupT data R
  let A := groupA data R
  have hrel := group_realizes data R
  have hlarge := certifiedRadius_large hk hC hD hCD
  have hdelta := certifiedDelta_bounds hk hC
  have hδkr : ((certifiedDelta k C : ℚ) : ℝ) < 1 / (2 * (k : ℝ)) := by
    have hh : ((certifiedDelta k C : ℚ) : ℝ) < ((1 / (2 * (k : ℚ)) : ℚ) : ℝ) :=
      Rat.cast_lt.mpr hdelta.2.2
    simpa using hh
  have hcomm := all_ordered_commute data t A hk C D R (certifiedDelta k C)
    (by exact_mod_cast hC) (by exact_mod_cast hlarge.1) (by exact_mod_cast hlarge.2.1)
    (by exact_mod_cast hlarge.2.2.1) (by exact_mod_cast hlarge.2.2.2)
    (by exact_mod_cast hdelta.1) (by exact_mod_cast hdelta.2.1) hδkr
    hrel.t_comm (by
      intro p q v hv
      apply (rightComm_eq_one_iff _ _).mp
      apply hrel.short_comm
      have hv2 : (∑ i, (v i : ℝ) ^ 2) < (R : ℝ) ^ 2 := by
        rw [← euclidean_norm_sq]
        change ‖euclidean v‖ < R at hv
        nlinarith [norm_nonneg (euclidean v)]
      exact_mod_cast hv2) hrel.polynomial hbound hdir
  exact metabelian_of_all_ordered_commute data t A hrel.t_comm hcomm (group_generators data R)

end Kourovka.MetabelianEnumeration.FiniteCover
