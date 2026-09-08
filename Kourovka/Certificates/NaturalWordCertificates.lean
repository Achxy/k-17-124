/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Certificates.NaturalWordSubstitution

/-!
# Natural Word Certificates

One finite natural-number certificate verifies an arbitrary finite list
of ordinary-presentation word equations.
-/

namespace Kourovka.MetabelianEnumeration.NaturalWordCertificates

open ComputablePresentations NaturalWordSubstitution

abbrev Input := PresentationCode × Word

def checkList (inputs : List Input) (certs : List ℕ) : Bool :=
  decide (∀ i ∈ List.range inputs.length,
    checkTrivial (inputs.getD i ((0, []), [])) (certs.getD i 0) = true)

theorem checkList_primrec : Primrec₂ checkList := by
  have hinput : Primrec (fun p : ℕ × (List Input × List ℕ) => p.2.1.getD p.1 ((0, []), [])) :=
    (Primrec.list_getD ((0, []), [])).comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hcert : Primrec (fun p : ℕ × (List Input × List ℕ) => p.2.2.getD p.1 0) :=
    (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.snd) Primrec.fst
  have hrel : PrimrecRel (fun i : ℕ => fun p : List Input × List ℕ =>
      checkTrivial (p.1.getD i ((0, []), [])) (p.2.getD i 0) = true) :=
    Primrec.eq.comp (checkTrivial_primrec.comp hinput hcert) (Primrec.const true)
  exact (hrel.forall_mem_list.comp
    (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) Primrec.id).decide

def Good (input : Input) : Prop :=
  validInput input ∧ PresentedGroup.mk (relations input.1) (interpretWord input.1.1 input.2) = 1

theorem checkList_correct (inputs : List Input) :
    (∃ certs, checkList inputs certs = true) ↔ ∀ input ∈ inputs, Good input := by
  constructor
  · rintro ⟨cs, hcs⟩ input hi
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hi
    have h := of_decide_eq_true hcs i.val (List.mem_range.mpr i.isLt)
    have he : inputs.getD i.val ((0, []), []) = inputs.get i := by
      simp only [List.getD_eq_getElem _ _ i.isLt, List.get_eq_getElem]
    rw [he] at h
    exact (checkTrivial_correct _).mp ⟨_, h⟩
  · intro h
    choose cs hcs using fun i : Fin inputs.length =>
      (checkTrivial_correct (inputs.get i)).mpr (h _ (List.get_mem _ _))
    refine ⟨List.ofFn cs, ?_⟩
    apply decide_eq_true
    intro i hi
    have hi' : i < inputs.length := List.mem_range.mp hi
    have hcget : (List.ofFn cs).getD i 0 = cs ⟨i, hi'⟩ := by
      rw [List.getD_eq_getElem (List.ofFn cs) 0 (by simpa using hi')]
      simp
    simpa only [List.getD_eq_getElem inputs _ hi', hcget, List.get_eq_getElem] using hcs ⟨i, hi'⟩

end Kourovka.MetabelianEnumeration.NaturalWordCertificates
