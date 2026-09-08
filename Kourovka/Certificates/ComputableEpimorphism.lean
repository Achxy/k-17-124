/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Certificates.ComputableIsomorphism

/-!
# Computable Epimorphism

Finite epimorphism certificates for ordinary finite presentations.
Only the source relators and the target-generator preimage equations are
checked. The words giving preimages need not induce a reverse homomorphism.
-/

namespace Kourovka.MetabelianEnumeration.ComputableEpimorphism

open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

abbrev Maps := ComputableIsomorphism.Maps
abbrev MapInput := ComputableIsomorphism.MapInput
abbrev Certificate := ComputableIsomorphism.Certificate
abbrev validMaps := ComputableIsomorphism.validMaps

def obligations (d : MapInput) : List Input :=
  ComputableIsomorphism.relatorChecks (d.1.1, (d.1.2, d.2.1)) ++
    ComputableIsomorphism.inverseChecks (d.1.2, (d.2.2, d.2.1))

theorem obligations_primrec : Primrec obligations := by
  let p : Primrec (fun d : MapInput => d.1.1) := Primrec.fst.comp Primrec.fst
  let q : Primrec (fun d : MapInput => d.1.2) := Primrec.snd.comp Primrec.fst
  let f : Primrec (fun d : MapInput => d.2.1) := Primrec.fst.comp Primrec.snd
  let g : Primrec (fun d : MapInput => d.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_append.comp
    (ComputableIsomorphism.relatorChecks_primrec.comp (p.pair (q.pair f)))
    (ComputableIsomorphism.inverseChecks_primrec.comp (q.pair (g.pair f)))

def checkData (pq : PresentationCode × PresentationCode) (c : Certificate) : Bool :=
  decide (validMaps (pq, c.1)) && checkList (obligations (pq, c.1)) c.2

theorem checkData_primrec : Primrec₂ checkData := by
  let d : Primrec (fun p : (PresentationCode × PresentationCode) × Certificate => (p.1, p.2.1)) :=
    Primrec.fst.pair (Primrec.fst.comp Primrec.snd)
  exact Primrec.and.comp (ComputableIsomorphism.validMaps_primrec.decide.comp d)
    (checkList_primrec.comp (obligations_primrec.comp d) (Primrec.snd.comp Primrec.snd))

def decodeCertificate (n : ℕ) : Certificate := (Encodable.decode n).getD (([], []), [])

def checkEpi (pq : PresentationCode × PresentationCode) (n : ℕ) : Bool :=
  checkData pq (decodeCertificate n)

theorem checkEpi_primrec : Primrec₂ checkEpi :=
  checkData_primrec.comp Primrec.fst
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const (([], []), [])))

theorem checkData_correct (pq : PresentationCode × PresentationCode) (fg : Maps) :
    (∃ cs, checkData pq (fg, cs) = true) ↔
      validMaps (pq, fg) ∧ ∀ input ∈ obligations (pq, fg), Good input := by
  simp only [checkData, Bool.and_eq_true, decide_eq_true_eq, exists_and_left]
  rw [checkList_correct]

end Kourovka.MetabelianEnumeration.ComputableEpimorphism
