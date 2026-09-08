/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Enumeration.ComputableEnumeration
import Kourovka.Cofinality.Cofinality

/-!
# From geometric covers to finite certificate data

A finitely presented metabelian group is covered by finite Laurent data.
A dyadic margin certificate supplies an effective radius for those data.
-/

set_option autoImplicit false

namespace Kourovka.MetabelianEnumeration.ComputableEnumeration

/-- Every nonzero-generator metabelian presentation is a quotient of a
concrete encoded cover at an accepted, finitely checked dyadic radius. -/
theorem encoded_cover_cofinal (p : PresentationCode) (hG : Metabelian (GroupOf p))
    (hp : p.1 ≠ 0) :
    ∃ (data : DatumCode) (r : ℕ), ComputableCoverData.check data r = true ∧
      ∃ f : FiniteCover.GroupOf (ComputableCoverData.decode data)
        (ComputableCoverData.radius data r) →* GroupOf p, Function.Surjective f := by
  classical
  rcases p with ⟨k, rels⟩
  cases k with
  | zero => exact (hp rfl).elim
  | succ k =>
    obtain ⟨a, ha, data, hcone, hmaps⟩ :=
      CofinalCover.finite_presentation_cover_cofinal
        (rels.map (interpretWord (k + 1))) hG
    cases a with
    | zero => omega
    | succ a =>
      let code := ComputableCoverData.encode data
      obtain ⟨r, hr⟩ := ConeVerifier.dyadic_margin_search_terminates
        (data.polynomials.map TamenessCompactness.polynomialSupport) hcone
      have hcheck : ComputableCoverData.check code r = true := by
        simpa only [ComputableCoverData.check, ComputableCone.checkMargin_eq,
          ComputableCoverData.decode_supports, code, ComputableCoverData.decode_encode] using hr
      obtain ⟨f, hf⟩ := hmaps (ComputableCoverData.radius code r)
      refine ⟨code, r, hcheck, ?_⟩
      rw [show ComputableCoverData.decode code = data from ComputableCoverData.decode_encode data]
      exact ⟨f, hf⟩

end Kourovka.MetabelianEnumeration.ComputableEnumeration
