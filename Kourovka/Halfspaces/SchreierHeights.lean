/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Halfspaces.HalfspaceGeometry
import Kourovka.Schreier.PathLifting

/-!
# Schreier Heights

Height-controlled Schreier representatives and rewriting.
-/

noncomputable section

namespace Kourovka.MetabelianEnumeration.SchreierHeights

open HalfspaceGeometry
open Kourovka.Schreier
open Kourovka.Schreier.Transversal

variable {X Q : Type*} [CommGroup Q]

def value (θ : FreeGroup X →* Multiplicative ℝ) (w : FreeGroup X) : ℝ := (θ w).toAdd

@[simp] theorem value_one (θ : FreeGroup X →* Multiplicative ℝ) : value θ 1 = 0 := by
  simp [value]

@[simp] theorem value_mul (θ : FreeGroup X →* Multiplicative ℝ) (u v : FreeGroup X) :
    value θ (u * v) = value θ u + value θ v := by simp [value]

@[simp] theorem value_inv (θ : FreeGroup X →* Multiplicative ℝ) (u : FreeGroup X) :
    value θ u⁻¹ = -value θ u := by simp [value]

theorem value_mk (θ : FreeGroup X →* Multiplicative ℝ) (xs : List (X × Bool)) :
    value θ (FreeGroup.mk xs) = (xs.map (letterHeight fun x => value θ (FreeGroup.of x))).sum := by
  induction xs with
  | nil => exact value_one θ
  | cons z xs ih =>
    rcases z with ⟨x, b⟩
    cases b <;> simp [mk_cons_false, mk_cons_true, letterHeight, ih]

theorem map_mk_of_perm (π : FreeGroup X →* Q) {xs ys : List (X × Bool)}
    (h : xs.Perm ys) : π (FreeGroup.mk xs) = π (FreeGroup.mk ys) := by
  rw [FreeGroup.lift_unique π (fun _ => rfl), FreeGroup.lift_unique π (fun _ => rfl)]
  simp only [FreeGroup.lift_mk]
  exact (h.map _).prod_eq

/-- A section of the quotient map, chosen with paths in the correct halfspace;
representatives of overlap vertices stay inside the overlap. -/
theorem exists_safe_section [DecidableEq X] (π : FreeGroup X →* Q)
    (hπ : Function.Surjective π) (χ : Q →* Multiplicative ℝ)
    (D μ : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ x, |value (χ.comp π) (FreeGroup.of x)| ≤ D) (hμ : 2 * D ≤ μ) :
    ∃ r : Q → FreeGroup X, (∀ q, π (r q) = q) ∧ r 1 = 1 ∧
      ∀ q, PathIn (letterHeight fun x => value (χ.comp π) (FreeGroup.of x))
        (fun z => min 0 (χ q).toAdd ≤ z ∧ z ≤ max μ (χ q).toAdd) 0 (r q).toWord := by
  classical
  have hex : ∀ q : Q, ∃ w : FreeGroup X,
      π w = q ∧ (q = 1 → w = 1) ∧
      PathIn (letterHeight fun x => value (χ.comp π) (FreeGroup.of x))
        (fun z => min 0 (χ q).toAdd ≤ z ∧ z ≤ max μ (χ q).toAdd) 0 w.toWord := by
    intro q
    by_cases hq : q = 1
    · subst q
      refine ⟨1, map_one π, fun _ => rfl, ?_⟩
      simp [PathIn]
    obtain ⟨w, hw⟩ := hπ q
    obtain ⟨ys, hperm, hpath⟩ := reorder_halfspaces
      (letterHeight fun x => value (χ.comp π) (FreeGroup.of x)) D μ w.toWord
      (fun z _ => by rcases z with ⟨x, b⟩; cases b <;> simpa [letterHeight] using hD x)
      hD0 hμ
    have hsum : (w.toWord.map (letterHeight fun x => value (χ.comp π) (FreeGroup.of x))).sum =
        (χ q).toAdd := by
      rw [← value_mk, FreeGroup.mk_toWord]
      simp only [value, MonoidHom.comp_apply, hw]
    refine ⟨FreeGroup.mk ys, ?_, fun h => (hq h).elim, ?_⟩
    · rw [map_mk_of_perm π hperm, FreeGroup.mk_toWord, hw]
    · simpa only [hsum] using hpath.pathIn.toWord_mk
  choose r hr hnormal hpath using hex
  exact ⟨r, hr, hnormal 1 rfl, hpath⟩

/-- Every normalized section defines the genuine Schreier representative
system of the actual quotient kernel. -/
def representativeOfSection (π : FreeGroup X →* Q) (r : Q → FreeGroup X)
    (hr : ∀ q, π (r q) = q) (h1 : r 1 = 1) : Transversal π.ker where
  rep w := r (π w)
  sameCoset w := by simp [MonoidHom.mem_ker, hr]
  constantOnCosets := by
    intro g h hgh
    have heq : π g = π h := by
      apply mul_inv_eq_one.mp
      simpa [MonoidHom.mem_ker] using hgh
    rw [heq]
  rep_one := by rw [map_one, h1]

theorem representative_height (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (w : FreeGroup X) :
    value (χ.comp π) (S.rep w) = value (χ.comp π) w := by
  have h := S.sameCoset w
  have heq : π w = π (S.rep w) := by
    apply mul_inv_eq_one.mp
    simpa [MonoidHom.mem_ker] using h
  simp only [value, MonoidHom.comp_apply, heq]

/-- Schreier symbols whose two endpoint heights satisfy the given predicate. -/
def symbolsIn (θ : FreeGroup X →* Multiplicative ℝ)
    {L : Subgroup (FreeGroup X)} (S : Transversal L) (P : ℝ → Prop) :
    Set (S.Edge) :=
  {z | P (value θ z.1.val) ∧ P (value θ (z.1.val * FreeGroup.of z.2))}

/-- Rewriting a path confined to a height region uses only symbols of that
region. This includes the literal negative-letter Schreier convention. -/
theorem rewrite_mem_closure (π : FreeGroup X →* Q) (χ : Q →* Multiplicative ℝ)
    (S : Transversal π.ker) (P : ℝ → Prop)
    (p : FreeGroup X) (xs : List (X × Bool))
    (hpath : PathIn (letterHeight fun x => value (χ.comp π) (FreeGroup.of x)) P
      (value (χ.comp π) p) xs) :
    S.rewriteWord p xs ∈
      Subgroup.closure (FreeGroup.of '' symbolsIn (χ.comp π) S P) := by
  induction xs generalizing p with
  | nil => exact Subgroup.one_mem _
  | cons z xs ih =>
    rcases z with ⟨x, b⟩
    cases b
    · apply Subgroup.mul_mem
      · apply Subgroup.inv_mem
        apply Subgroup.subset_closure
        refine ⟨S.edge (p * (FreeGroup.of x)⁻¹) x, ?_, rfl⟩
        change P (value (χ.comp π) (S.rep (p * (FreeGroup.of x)⁻¹))) ∧ _
        rw [representative_height]
        constructor
        · simpa only [value_mul, value_inv, letterHeight, Bool.false_eq_true, if_false] using
            hpath.2.start
        · simpa only [edge, value_mul, representative_height, value_inv,
          neg_add_cancel_right] using
            hpath.1
      · apply ih
        simpa only [value_mul, value_inv, letterHeight, Bool.false_eq_true, if_false] using hpath.2
    · apply Subgroup.mul_mem
      · apply Subgroup.subset_closure
        refine ⟨S.edge p x, ?_, rfl⟩
        change P (value (χ.comp π) (S.rep p)) ∧ _
        rw [representative_height]
        constructor
        · exact hpath.1
        · simpa only [edge, value_mul, representative_height, letterHeight, if_true] using hpath.2.start
      · apply ih
        simpa only [value_mul, letterHeight, if_true] using hpath.2

end Kourovka.MetabelianEnumeration.SchreierHeights
