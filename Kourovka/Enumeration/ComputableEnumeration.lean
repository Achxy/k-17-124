/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Covers.ComputableCoverWords
import Kourovka.Presentations.QuotientCodes

/-!
# Computable Enumeration

The actual primitive-recursive certificate predicate for metabelian
ordinary finite presentations.
-/

set_option autoImplicit false

namespace Kourovka.MetabelianEnumeration.ComputableEnumeration

abbrev DatumCode := ComputableCoverData.DatumCode
abbrev ExtraRelators := List (List (ℕ × Bool))
abbrev Certificate := (DatumCode × ℕ) × (ExtraRelators × ℕ)

instance (p : PresentationCode) : Decidable (WellFormed p) := by
  unfold WellFormed
  infer_instance

def source (c : Certificate) : PresentationCode :=
  ComputableCoverWords.presentation c.1.1 (ComputableCoverData.radius c.1.1 c.1.2)

def extended (c : Certificate) : PresentationCode :=
  QuotientCodes.appendRelators (source c) c.2.1

def checkData (p : PresentationCode) (c : Certificate) : Bool :=
  decide (WellFormed p) && (decide (p.1 = 0) ||
    (ComputableCoverData.check c.1.1 c.1.2 &&
      ComputableIsomorphism.checkIso (extended c, p) c.2.2))

theorem source_primrec : Primrec source :=
  ComputableCoverWords.presentation_primrec.comp (Primrec.fst.comp Primrec.fst)
    (ComputableCoverData.radius_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst))

theorem extended_primrec : Primrec extended :=
  QuotientCodes.appendRelators_primrec.comp source_primrec (Primrec.fst.comp Primrec.snd)

theorem checkData_primrec : Primrec₂ checkData := by
  let hd : Primrec (fun z : PresentationCode × Certificate => z.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  let hr : Primrec (fun z : PresentationCode × Certificate => z.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  let hi : Primrec (fun z : PresentationCode × Certificate => z.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.and.comp (ComputablePresentations.wellFormed_primrec.decide.comp Primrec.fst)
    (Primrec.or.comp
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)).decide)
      (Primrec.and.comp (ComputableCoverData.check_primrec.comp hd hr)
        (ComputableIsomorphism.checkIso_primrec.comp
          ((extended_primrec.comp Primrec.snd).pair Primrec.fst) hi)))

def defaultCertificate : Certificate := ((((0, 0), ([], [])), 0), ([], 0))

def decodeCertificate (c : ℕ) : Certificate :=
  (@Encodable.decode Certificate (inferInstance : Primcodable Certificate).toEncodable c).getD
    defaultCertificate

def encodeCertificate (c : Certificate) : ℕ :=
  @Encodable.encode Certificate (inferInstance : Primcodable Certificate).toEncodable c

theorem decodeDefault_primrec {α : Type} [Primcodable α] (fallback : α) :
    Primrec (fun n : ℕ => (Encodable.decode (α := α) n).getD fallback) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const fallback)

theorem decodeCertificate_primrec : Primrec decodeCertificate :=
  decodeDefault_primrec defaultCertificate

theorem decode_encode_certificate (c : Certificate) :
    decodeCertificate (encodeCertificate c) = c := by
  simp [decodeCertificate, encodeCertificate]

def check (p c : ℕ) : Bool := checkData (decodePresentation p) (decodeCertificate c)

/-- The combined finite checker is primitive recursive, including dimension
decoding, cone margins, cover relators, and the isomorphism equations. -/
theorem check_primrec : Primrec₂ check :=
  checkData_primrec.comp (ComputablePresentations.decodePresentation_primrec.comp Primrec.fst)
    (decodeCertificate_primrec.comp Primrec.snd)

end Kourovka.MetabelianEnumeration.ComputableEnumeration
