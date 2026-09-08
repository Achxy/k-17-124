/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Certificates.EpimorphismSemantics
import Kourovka.Enumeration.EnumerationCofinality
import Kourovka.Covers.ComputableCoverSemantics
import Kourovka.Covers.ComputableCoverBounds

/-!
# Epimorphism Enumeration

A direct metabelianity certificate: a checked finite cover and a finite
epimorphism certificate onto the input presentation. The finite-cover construction supplies soundness, and cofinality supplies completeness.

The proof is organised in three steps: construction and computability of the
checker, soundness and completeness for structured data, and natural-number encoding.
-/

set_option autoImplicit false

namespace Kourovka.MetabelianEnumeration.EpimorphismEnumeration

/-- Finite list representation of the signed Laurent data. -/
abbrev DatumCode := ComputableCoverData.DatumCode
/-- A triple `((data, r), e)`: Laurent data, a dyadic-margin exponent,
and a natural-number code for an epimorphism certificate. -/
abbrev Certificate := (DatumCode × ℕ) × ℕ

/-- The finite cover presentation determined by the data and the certified radius. -/
def source (c : Certificate) : PresentationCode :=
  ComputableCoverWords.presentation c.1.1 (ComputableCoverData.radius c.1.1 c.1.2)

/-- Verify the alphabet, then accept either the trivial zero-generator case
or a checked metabelian cover with a certified epimorphism onto the input. -/
def checkData (p : PresentationCode) (c : Certificate) : Bool :=
  decide (WellFormed p) && (decide (p.1 = 0) ||
    (ComputableCoverData.check c.1.1 c.1.2 &&
      ComputableEpimorphism.checkEpi (source c, p) c.2))

/-- The source presentation can be constructed primitive recursively. -/
theorem source_primrec : Primrec source :=
  ComputableCoverWords.presentation_primrec.comp (Primrec.fst.comp Primrec.fst)
    (ComputableCoverData.radius_primrec.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst))

/-- Every component of the structured certificate check is primitive recursive. -/
theorem checkData_primrec : Primrec₂ checkData := by
  let dataProjection : Primrec (fun z : PresentationCode × Certificate => z.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  let marginProjection : Primrec (fun z : PresentationCode × Certificate => z.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  exact Primrec.and.comp (ComputablePresentations.wellFormed_primrec.decide.comp Primrec.fst)
    (Primrec.or.comp
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)).decide)
      (Primrec.and.comp (ComputableCoverData.check_primrec.comp dataProjection marginProjection)
        (ComputableEpimorphism.checkEpi_primrec.comp
          ((source_primrec.comp Primrec.snd).pair Primrec.fst)
          (Primrec.snd.comp Primrec.snd))))

/-- A total-decoding fallback; it also witnesses the zero-generator branch. -/
def defaultCertificate : Certificate := ((((0, 0), ([], [])), 0), 0)

/-- Decode finite certificate data, using `defaultCertificate` on decoding failure. -/
def decodeCertificate (c : ℕ) : Certificate :=
  (@Encodable.decode Certificate (inferInstance : Primcodable Certificate).toEncodable c).getD
    defaultCertificate

/-- Encode the finite certificate by the pinned `Primcodable` representation. -/
def encodeCertificate (c : Certificate) : ℕ :=
  @Encodable.encode Certificate (inferInstance : Primcodable Certificate).toEncodable c

/-- Total decoding preserves primitive recursiveness. -/
theorem decodeCertificate_primrec : Primrec decodeCertificate :=
  ComputableEnumeration.decodeDefault_primrec defaultCertificate

/-- Encoding and then decoding recovers the original certificate. -/
theorem decode_encode_certificate (c : Certificate) :
    decodeCertificate (encodeCertificate c) = c := by
  simp [decodeCertificate, encodeCertificate]

/-- The paper's natural-number predicate, obtained by decoding both arguments. -/
def check (p c : ℕ) : Bool := checkData (decodePresentation p) (decodeCertificate c)

/-- The two-input Boolean predicate of Theorem 1.1 is primitive recursive. -/
theorem check_primrec : Primrec₂ check :=
  checkData_primrec.comp (ComputablePresentations.decodePresentation_primrec.comp Primrec.fst)
    (decodeCertificate_primrec.comp Primrec.snd)

/-- Soundness: an accepted certificate defines a metabelian group. -/
theorem checkData_sound (p : PresentationCode) (c : Certificate)
    (h : checkData p c = true) : WellFormed p ∧ Metabelian (GroupOf p) := by
  rw [checkData, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  -- The zero-generator group is trivial; every other accepted input is a quotient of a cover.
  rcases h.2 with hz | ⟨hc, he⟩
  · exact QuotientCodes.zero_generators_metabelian p hz
  · obtain ⟨_, _, f, hf⟩ := (ComputableEpimorphism.checkEpi_correct (source c, p)).mp ⟨c.2, he⟩
    exact metabelian_surjective f hf
      (ComputableCoverSemantics.checked_presentation_metabelian c.1.1 c.1.2 hc)

/-- Completeness: every well-formed metabelian presentation has a certificate. -/
theorem checkData_complete (p : PresentationCode) (hp : WellFormed p)
    (hG : Metabelian (GroupOf p)) : ∃ c : Certificate, checkData p c = true := by
  classical
  by_cases hz : p.1 = 0
  · exact ⟨defaultCertificate, by simp [checkData, hp, hz]⟩
  -- Cofinality supplies a cover, a checked margin, and a surjection onto the input group.
  obtain ⟨data, r, hc, f, hf⟩ := ComputableEnumeration.encoded_cover_cofinal p hG hz
  let R := ComputableCoverData.radius data r
  let q := ComputableCoverWords.presentation data R
  have hq : WellFormed q := ComputableCoverBounds.presentation_wellFormed data R
  -- Move from the finite-alphabet cover to its natural-word presentation.
  obtain ⟨g, hg⟩ := ComputableCoverSemantics.presentation_epimorphism data R
  -- Surjectivity has a finite word certificate, so it can be checked by the predicate.
  obtain ⟨n, hn⟩ := (ComputableEpimorphism.checkEpi_correct (q, p)).mpr
    ⟨hq, hp, f.comp g, hf.comp hg⟩
  refine ⟨((data, r), n), ?_⟩
  simpa only [checkData, source, R, q, hp, hz, decide_true, decide_false,
    Bool.true_and, Bool.false_or, hc, Bool.true_and] using hn

/-- The main certificate equivalence, including well-formedness of the input. -/
theorem check_correct (p : ℕ) : DefinesMetabelian p ↔ ∃ c, check p c = true := by
  constructor
  · rintro ⟨hp, hG⟩
    obtain ⟨c, hc⟩ := checkData_complete (decodePresentation p) hp hG
    exact ⟨encodeCertificate c, by simpa only [check, decode_encode_certificate] using hc⟩
  · rintro ⟨c, hc⟩
    exact checkData_sound (decodePresentation p) (decodeCertificate c) hc

/-- The full ordinary-presentation result, proved through direct epimorphism
certificates rather than finite quotient presentations and isomorphisms. -/
theorem kourovka_17_124_via_epimorphisms : MainClaim :=
  completion_of_certificates check check_primrec.to_comp check_correct

end Kourovka.MetabelianEnumeration.EpimorphismEnumeration
