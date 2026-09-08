/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Enumeration.EnumerationCofinality
import Kourovka.Covers.ComputableCoverSemantics
import Kourovka.Covers.ComputableCoverBounds

/-!
# Enumeration Correctness

Soundness and completeness of the actual combined certificate checker,
and the unconditional solution of the original recursive-enumerability target.
-/

set_option autoImplicit false

namespace Kourovka.MetabelianEnumeration

namespace ComputableEnumeration

theorem checkData_sound (p : PresentationCode) (c : Certificate)
    (h : checkData p c = true) : WellFormed p ∧ Metabelian (GroupOf p) := by
  rw [checkData, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  rcases h.2 with hz | ⟨hc, hi⟩
  · exact QuotientCodes.zero_generators_metabelian p hz
  · obtain ⟨_, _, ⟨e⟩⟩ := (ComputableIsomorphism.checkIso_correct (extended c, p)).mp ⟨c.2.2, hi⟩
    exact metabelian_surjective e.toMonoidHom e.surjective
      (QuotientCodes.metabelian_append (source c) c.2.1
        (ComputableCoverSemantics.checked_presentation_metabelian c.1.1 c.1.2 hc))

theorem checkData_complete (p : PresentationCode) (hp : WellFormed p)
    (hG : Metabelian (GroupOf p)) : ∃ c : Certificate, checkData p c = true := by
  classical
  by_cases hz : p.1 = 0
  · exact ⟨defaultCertificate, by simp [checkData, hp, hz]⟩
  obtain ⟨data, r, hc, f, hf⟩ := encoded_cover_cofinal p hG hz
  let R := ComputableCoverData.radius data r
  let q := ComputableCoverWords.presentation data R
  have hq : WellFormed q := ComputableCoverBounds.presentation_wellFormed data R
  obtain ⟨g, hg⟩ := ComputableCoverSemantics.presentation_epimorphism data R
  obtain ⟨extra, he, hiso⟩ := QuotientCodes.finite_quotient_codes q p hq hp
    (f.comp g) (hf.comp hg)
  obtain ⟨n, hn⟩ := (ComputableIsomorphism.checkIso_correct
    (QuotientCodes.appendRelators q extra, p)).mpr ⟨he, hp, hiso⟩
  refine ⟨((data, r), (extra, n)), ?_⟩
  simpa only [checkData, source, extended, R, q, hp, hz, decide_true, decide_false,
    Bool.true_and, Bool.false_or, hc, Bool.true_and] using hn

theorem check_correct (p : ℕ) : DefinesMetabelian p ↔ ∃ c, check p c = true := by
  constructor
  · rintro ⟨hp, hG⟩
    obtain ⟨c, hc⟩ := checkData_complete (decodePresentation p) hp hG
    exact ⟨encodeCertificate c, by simpa only [check, decode_encode_certificate] using hc⟩
  · rintro ⟨c, hc⟩
    exact checkData_sound (decodePresentation p) (decodeCertificate c) hc

end ComputableEnumeration

/-- The full original statement for actual finite ordinary presentations. -/
theorem kourovka_17_124 : MainClaim :=
  completion_of_certificates ComputableEnumeration.check
    ComputableEnumeration.check_primrec.to_comp ComputableEnumeration.check_correct

end Kourovka.MetabelianEnumeration
