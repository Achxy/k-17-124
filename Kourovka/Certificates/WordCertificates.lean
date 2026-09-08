/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Presentations.Presentations
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Word Certificates

Finite, executable normal-closure derivations for ordinary group presentations.
The certificate checker solves no word problem in the presented group: its only
equality comparisons are in a free group, using free reduction.
-/

namespace Kourovka.MetabelianEnumeration.WordCertificates

abbrev Word (n : ℕ) := List (Fin n × Bool)

inductive Derivation (n : ℕ) where
  | one
  | relator (w : Word n)
  | mul (left right : Derivation n)
  | inv (body : Derivation n)
  | conjugate (w : Word n) (body : Derivation n)
  deriving DecidableEq

def Derivation.eval {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Derivation n → FreeGroup (Fin n)
  | .one => 1
  | .relator w => if FreeGroup.mk w ∈ rels then FreeGroup.mk w else 1
  | .mul left right => left.eval rels * right.eval rels
  | .inv body => (body.eval rels)⁻¹
  | .conjugate w body => FreeGroup.mk w * body.eval rels * (FreeGroup.mk w)⁻¹

theorem Derivation.eval_mem {n : ℕ} (rels : List (FreeGroup (Fin n)))
    (d : Derivation n) : d.eval rels ∈ Subgroup.normalClosure {r | r ∈ rels} := by
  induction d with
  | one => exact Subgroup.one_mem _
  | relator w =>
    simp only [Derivation.eval]
    split
    · exact Subgroup.subset_normalClosure (by assumption)
    · exact Subgroup.one_mem _
  | mul l r hl hr => exact Subgroup.mul_mem _ hl hr
  | inv d hd => exact Subgroup.inv_mem _ hd
  | conjugate w d hd => exact Subgroup.Normal.conj_mem inferInstance _ hd _

def derivableSubgroup {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Subgroup (FreeGroup (Fin n)) where
  carrier := {r | ∃ d : Derivation n, d.eval rels = r}
  one_mem' := ⟨.one, rfl⟩
  mul_mem' := by
    rintro a b ⟨da, rfl⟩ ⟨db, rfl⟩
    exact ⟨.mul da db, rfl⟩
  inv_mem' := by
    rintro a ⟨da, rfl⟩
    exact ⟨.inv da, rfl⟩

instance derivableSubgroup_normal {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    (derivableSubgroup rels).Normal where
  conj_mem := by
    rintro a ⟨da, rfl⟩ g
    refine ⟨.conjugate g.toWord da, ?_⟩
    simp only [Derivation.eval, FreeGroup.mk_toWord]

theorem normalClosure_le_derivable {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Subgroup.normalClosure {r | r ∈ rels} ≤ derivableSubgroup rels := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  change r ∈ rels at hr
  refine ⟨.relator r.toWord, ?_⟩
  simp only [Derivation.eval, FreeGroup.mk_toWord, if_pos hr]

theorem hasDerivation_iff {n : ℕ} (rels : List (FreeGroup (Fin n)))
    (r : FreeGroup (Fin n)) :
    (∃ d : Derivation n, d.eval rels = r) ↔ r ∈ Subgroup.normalClosure {r | r ∈ rels} := by
  constructor
  · rintro ⟨d, rfl⟩
    exact d.eval_mem rels
  · intro h
    exact normalClosure_le_derivable rels h

def checkWord {n : ℕ} (rels : List (FreeGroup (Fin n))) (w : Word n)
    (d : Derivation n) : Bool := decide (d.eval rels = FreeGroup.mk w)

/-- Every trivial word has a finite accepted certificate, and accepted certificates
always certify actual triviality in the ordinary presented group. -/
theorem checkWord_correct {n : ℕ} (rels : List (FreeGroup (Fin n))) (w : Word n) :
    (∃ d, checkWord rels w d = true) ↔
      PresentedGroup.mk {r | r ∈ rels} (FreeGroup.mk w) = 1 := by
  simp only [checkWord, decide_eq_true_eq, PresentedGroup.mk_eq_one_iff]
  exact hasDerivation_iff rels (FreeGroup.mk w)

end Kourovka.MetabelianEnumeration.WordCertificates
