/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Certificates.NaturalWordCertificates

/-!
# Computable Isomorphism

Natural-number isomorphism certificates for arbitrary ordinary finite
presentation codes. All equations are checked by the proved word checker.
-/

namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism

open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

abbrev Maps := Images × Images
abbrev MapInput := (PresentationCode × PresentationCode) × Maps
abbrev Certificate := Maps × List ℕ

def validMaps (d : MapInput) : Prop :=
  WellFormed d.1.1 ∧ WellFormed d.1.2 ∧
    d.2.1.length = d.1.1.1 ∧ d.2.2.length = d.1.2.1 ∧
      WellFormed (d.1.2.1, d.2.1) ∧ WellFormed (d.1.1.1, d.2.2)

instance : DecidablePred validMaps := fun d => by
  unfold validMaps WellFormed
  infer_instance

theorem validMaps_primrec : PrimrecPred validMaps := by
  let p : Primrec (fun d : MapInput => d.1.1) := Primrec.fst.comp Primrec.fst
  let q : Primrec (fun d : MapInput => d.1.2) := Primrec.snd.comp Primrec.fst
  let f : Primrec (fun d : MapInput => d.2.1) := Primrec.fst.comp Primrec.snd
  let g : Primrec (fun d : MapInput => d.2.2) := Primrec.snd.comp Primrec.snd
  exact (wellFormed_primrec.comp p).and ((wellFormed_primrec.comp q).and
    ((Primrec.eq.comp (Primrec.list_length.comp f) (Primrec.fst.comp p)).and
      ((Primrec.eq.comp (Primrec.list_length.comp g) (Primrec.fst.comp q)).and
        ((wellFormed_primrec.comp ((Primrec.fst.comp q).pair f)).and
          (wellFormed_primrec.comp ((Primrec.fst.comp p).pair g))))))

def relatorChecks (d : PresentationCode × (PresentationCode × Images)) : List Input :=
  d.1.2.map fun w => (d.2.1, substitute d.2.2 w)

theorem relatorChecks_primrec : Primrec relatorChecks :=
  Primrec.list_map (Primrec.snd.comp Primrec.fst)
    (((Primrec.fst.comp Primrec.snd).comp Primrec.fst).pair
      (substitute_primrec.comp ((Primrec.snd.comp Primrec.snd).comp Primrec.fst)
        Primrec.snd)).to₂

def inverseChecks (d : PresentationCode × Maps) : List Input :=
  (List.range d.1.1).map fun i =>
    (d.1, substitute d.2.2 (d.2.1.getD i []) ++ [(i, false)])

theorem inverseChecks_primrec : Primrec inverseChecks := by
  have hf : Primrec (fun d : (PresentationCode × Maps) × ℕ => d.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hg : Primrec (fun d : (PresentationCode × Maps) × ℕ => d.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hword := substitute_primrec.comp hg ((Primrec.list_getD []).comp hf Primrec.snd)
  have hletter : Primrec (fun d : (PresentationCode × Maps) × ℕ => [(d.2, false)]) :=
    Primrec.list_cons.comp (Primrec.snd.pair (Primrec.const false)) (Primrec.const [])
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst))
    (((Primrec.fst.comp Primrec.fst).pair (Primrec.list_append.comp hword hletter)).to₂)

def obligations (d : MapInput) : List Input :=
  relatorChecks (d.1.1, (d.1.2, d.2.1)) ++
    relatorChecks (d.1.2, (d.1.1, d.2.2)) ++
      inverseChecks (d.1.1, (d.2.1, d.2.2)) ++
        inverseChecks (d.1.2, (d.2.2, d.2.1))

theorem obligations_primrec : Primrec obligations := by
  let p : Primrec (fun d : MapInput => d.1.1) := Primrec.fst.comp Primrec.fst
  let q : Primrec (fun d : MapInput => d.1.2) := Primrec.snd.comp Primrec.fst
  let f : Primrec (fun d : MapInput => d.2.1) := Primrec.fst.comp Primrec.snd
  let g : Primrec (fun d : MapInput => d.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (relatorChecks_primrec.comp (p.pair (q.pair f)))
    (relatorChecks_primrec.comp (q.pair (p.pair g))))
    (inverseChecks_primrec.comp (p.pair (f.pair g))))
    (inverseChecks_primrec.comp (q.pair (g.pair f)))

def checkData (pq : PresentationCode × PresentationCode) (c : Certificate) : Bool :=
  decide (validMaps (pq, c.1)) && checkList (obligations (pq, c.1)) c.2

theorem checkData_primrec : Primrec₂ checkData := by
  let d : Primrec (fun p : (PresentationCode × PresentationCode) × Certificate => (p.1, p.2.1)) :=
    Primrec.fst.pair (Primrec.fst.comp Primrec.snd)
  exact Primrec.and.comp (validMaps_primrec.decide.comp d)
    (checkList_primrec.comp (obligations_primrec.comp d) (Primrec.snd.comp Primrec.snd))

def decodeCertificate (n : ℕ) : Certificate := (Encodable.decode n).getD (([], []), [])

def checkIso (pq : PresentationCode × PresentationCode) (n : ℕ) : Bool :=
  checkData pq (decodeCertificate n)

theorem checkIso_primrec : Primrec₂ checkIso :=
  checkData_primrec.comp Primrec.fst
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const (([], []), [])))

theorem checkData_correct (pq : PresentationCode × PresentationCode) (fg : Maps) :
    (∃ cs, checkData pq (fg, cs) = true) ↔
      validMaps (pq, fg) ∧ ∀ input ∈ obligations (pq, fg), Good input := by
  simp only [checkData, Bool.and_eq_true, decide_eq_true_eq, exists_and_left]
  rw [checkList_correct]

end Kourovka.MetabelianEnumeration.ComputableIsomorphism
