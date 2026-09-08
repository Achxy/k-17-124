/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Certificates.ComputableEpimorphism
import Kourovka.Certificates.IsomorphismSemantics

/-!
# Epimorphism Semantics

Soundness and completeness of finite epimorphism certificates.
-/

namespace Kourovka.MetabelianEnumeration.WordCertificates

/-- Source-relator identities and one preimage for each target generator
suffice for a surjective homomorphism. No reverse relator identities occur. -/
theorem exists_epi_of_maps {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (g : Fin m → FreeGroup (Fin n))
    (hf : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (hfg : ∀ i, FreeGroup.lift f (g i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet target)) :
    ∃ F : PresentedGroup (relSet source) →* PresentedGroup (relSet target),
      Function.Surjective F := by
  let F := descend source target f hf
  refine ⟨F, ?_⟩
  intro y
  apply PresentedGroup.generated_by (relSet target) F.range
  · intro i
    refine ⟨PresentedGroup.mk (relSet source) (g i), ?_⟩
    rw [show F = descend source target f hf from rfl, descend_mk]
    have h := PresentedGroup.mk_eq_one_iff.mpr (hfg i)
    simpa only [map_mul, map_inv, mul_inv_eq_one, PresentedGroup.of] using h
end Kourovka.MetabelianEnumeration.WordCertificates

namespace Kourovka.MetabelianEnumeration.ComputableEpimorphism

open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations
open ComputableIsomorphism (eval_substitute encodeImages encodeImages_length
  encodeImages_wellFormed interpret_encodeImages_getD)

def GoodMaps (pq : PresentationCode × PresentationCode) (fg : Maps) : Prop :=
  (∀ w ∈ pq.1.2, Good (pq.2, substitute fg.1 w)) ∧
    (∀ i < pq.2.1, Good (pq.2, substitute fg.1 (fg.2.getD i []) ++ [(i, false)]))

theorem good_obligations (pq : PresentationCode × PresentationCode) (fg : Maps) :
    (∀ input ∈ obligations (pq, fg), Good input) ↔ GoodMaps pq fg := by
  simp only [obligations, List.forall_mem_append, ComputableIsomorphism.relatorChecks,
    ComputableIsomorphism.inverseChecks, List.forall_mem_map, List.mem_range, GoodMaps]

theorem goodMaps_sound (pq : PresentationCode × PresentationCode) (fg : Maps)
    (hv : validMaps (pq, fg)) (hg : GoodMaps pq fg) :
    ∃ F : GroupOf pq.1 →* GroupOf pq.2, Function.Surjective F := by
  rcases hv with ⟨hp, _, _, _, _, hgvalid⟩
  rcases hg with ⟨hforward, hfg⟩
  apply WordCertificates.exists_epi_of_maps
    (pq.1.2.map (interpretWord pq.1.1)) (pq.2.2.map (interpretWord pq.2.1))
    (fun i => interpretWord pq.2.1 (fg.1.getD i.val []))
    (fun i => interpretWord pq.1.1 (fg.2.getD i.val []))
  · intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_substitute pq.1.1 pq.2.1 fg.1 w (hp w hw)]
    exact (hforward w hw).2
  · intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_inverseCheck pq.2.1 pq.1.1 fg.2 fg.1 hgvalid i.val i.isLt]
    exact (hfg i.val i.isLt).2

/-- Every actual surjection has finite words witnessing its generator images
and preimages, and hence finite proofs of all checker obligations. -/
theorem goodMaps_complete (p q : PresentationCode) (hp : WellFormed p) (hq : WellFormed q)
    (e : GroupOf p →* GroupOf q) (he : Function.Surjective e) :
    ∃ fg : Maps, validMaps ((p, q), fg) ∧ GoodMaps (p, q) fg := by
  classical
  choose f hf using fun i : Fin p.1 =>
    PresentedGroup.mk_surjective (relations q) (e (PresentedGroup.of i))
  choose y hy using fun i : Fin q.1 => he (PresentedGroup.of i)
  choose g hg using fun i : Fin q.1 => PresentedGroup.mk_surjective (relations p) (y i)
  let F := encodeImages f
  let G := encodeImages g
  have hF : WellFormed (q.1, F) := encodeImages_wellFormed f
  have hG : WellFormed (p.1, G) := encodeImages_wellFormed g
  have hf' : ∀ i : Fin p.1, PresentedGroup.mk (relations q)
      (interpretWord q.1 (F.getD i.val [])) = e (PresentedGroup.of i) := by
    intro i
    simpa only [F, interpret_encodeImages_getD] using hf i
  have hg' : ∀ i : Fin q.1, e (PresentedGroup.mk (relations p)
      (interpretWord p.1 (G.getD i.val []))) = PresentedGroup.of i := by
    intro i
    simpa only [G, interpret_encodeImages_getD, hg] using hy i
  refine ⟨(F, G), ⟨hp, hq, encodeImages_length f, encodeImages_length g, hF, hG⟩, ?_⟩
  constructor
  · intro w hw
    refine ⟨⟨hq, valid_substitute q.1 F hF w⟩, ?_⟩
    rw [eval_substitute p q e F hf' w (hp w hw)]
    rw [PresentedGroup.one_of_mem (List.mem_map.mpr ⟨w, hw, rfl⟩), map_one]
  · intro i hi
    have hvi : ValidWord q.1 [(i, false)] := by
      intro z hz
      simpa using List.mem_singleton.mp hz ▸ hi
    refine ⟨⟨hq, valid_append (valid_substitute q.1 F hF _) hvi⟩, ?_⟩
    rw [interpret_append, map_mul, interpret_singleton_false q.1 i hi, map_inv,
      eval_substitute p q e F hf' _ (valid_getD p.1 G hG i), hg' ⟨i, hi⟩]
    exact mul_inv_cancel _

theorem checkEpi_correct (pq : PresentationCode × PresentationCode) :
    (∃ n, checkEpi pq n = true) ↔
      WellFormed pq.1 ∧ WellFormed pq.2 ∧
        ∃ F : GroupOf pq.1 →* GroupOf pq.2, Function.Surjective F := by
  constructor
  · rintro ⟨n, hn⟩
    let c := decodeCertificate n
    have hd : checkData pq c = true := hn
    have h := (checkData_correct pq c.1).mp ⟨c.2, hd⟩
    exact ⟨h.1.1, h.1.2.1, goodMaps_sound pq c.1 h.1 ((good_obligations pq c.1).mp h.2)⟩
  · rintro ⟨hp, hq, e, he⟩
    obtain ⟨fg, hv, hg⟩ := goodMaps_complete pq.1 pq.2 hp hq e he
    obtain ⟨cs, hcs⟩ := (checkData_correct pq fg).mpr ⟨hv, (good_obligations pq fg).mpr hg⟩
    refine ⟨Encodable.encode (fg, cs), ?_⟩
    simpa only [checkEpi, decodeCertificate, Encodable.encodek, Option.getD_some] using hcs

end Kourovka.MetabelianEnumeration.ComputableEpimorphism
