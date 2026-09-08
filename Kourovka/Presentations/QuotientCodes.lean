/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Certificates.IsomorphismSemantics
import Kourovka.Presentations.FiniteQuotient

/-!
# Quotient Codes

Appending finite natural-word relators realizes every quotient between
ordinary finite presentations. The zero-generator case is handled directly.
-/

namespace Kourovka.MetabelianEnumeration.QuotientCodes

open NaturalWordSubstitution WordCertificates

def appendRelators (p : PresentationCode) (extra : List (List (ℕ × Bool))) :
    PresentationCode := (p.1, p.2 ++ extra)

theorem appendRelators_primrec : Primrec₂ appendRelators :=
  (Primrec.fst.comp Primrec.fst).pair
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem relations_subset_append (p : PresentationCode) (extra : List (List (ℕ × Bool))) :
    relations p ⊆ relations (appendRelators p extra) := by
  intro r hr
  change r ∈ (p.2 ++ extra).map (interpretWord p.1)
  rw [List.map_append]
  exact List.mem_append_left _ hr

def quotientHom (p : PresentationCode) (extra : List (List (ℕ × Bool))) :
    GroupOf p →* GroupOf (appendRelators p extra) :=
  QuotientGroup.map (Subgroup.normalClosure (relations p))
    (Subgroup.normalClosure (relations (appendRelators p extra))) (MonoidHom.id _) (by
      simpa only [Subgroup.comap_id] using
        Subgroup.normalClosure_mono (relations_subset_append p extra))

theorem quotientHom_surjective (p : PresentationCode) (extra : List (List (ℕ × Bool))) :
    Function.Surjective (quotientHom p extra) := by
  intro x
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective (relations (appendRelators p extra)) x
  exact ⟨PresentedGroup.mk (relations p) w, rfl⟩

theorem metabelian_append (p : PresentationCode) (extra : List (List (ℕ × Bool)))
    (h : Metabelian (GroupOf p)) : Metabelian (GroupOf (appendRelators p extra)) :=
  metabelian_surjective (quotientHom p extra) (quotientHom_surjective p extra) h

/-- Every actual finite-presentation quotient has finitely many additional
natural-word relators on the unchanged source alphabet. -/
theorem finite_quotient_codes (p q : PresentationCode) (hp : WellFormed p)
    (_hq : WellFormed q) (f : GroupOf p →* GroupOf q) (hf : Function.Surjective f) :
    ∃ extra : List (List (ℕ × Bool)), WellFormed (appendRelators p extra) ∧
      Nonempty (GroupOf (appendRelators p extra) ≃* GroupOf q) := by
  classical
  obtain ⟨rels, ⟨e⟩⟩ := finite_relator_quotient_of_surjection
    (p.2.map (interpretWord p.1)) (q.2.map (interpretWord q.1)) f hf
  let extra := (encodeRelators rels).2
  have he : WellFormed (p.1, extra) := encodeRelators_wellFormed rels
  have hm : extra.map (interpretWord p.1) = rels := by
    simp [extra, encodeRelators, List.map_map, Function.comp_def,
      interpret_encodeWord, FreeGroup.mk_toWord]
  have hr : relations (appendRelators p extra) =
      relSet (p.2.map (interpretWord p.1) ++ rels) := by
    simp only [relations, appendRelators, List.map_append, hm, relSet]
  have ei : GroupOf (appendRelators p extra) ≃*
      PresentedGroup (relSet (p.2.map (interpretWord p.1) ++ rels)) := by
    change PresentedGroup (relations (appendRelators p extra)) ≃* _
    rw [hr]
  refine ⟨extra, ?_, ⟨ei.trans e⟩⟩
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact hp w hw
  · exact he w hw

theorem zero_generators_metabelian (p : PresentationCode) (h : p.1 = 0) :
    Metabelian (GroupOf p) := by
  rcases p with ⟨n, rels⟩
  dsimp only at h
  subst n
  have hone (x : GroupOf (0, rels)) : x = 1 := by
    exact Subgroup.mem_bot.mp (PresentedGroup.generated_by (relations (0, rels)) ⊥
      (fun i => Fin.elim0 i) x)
  letI : Subsingleton (GroupOf (0, rels)) := ⟨fun x y => (hone x).trans (hone y).symm⟩
  intro a b c d
  change _ * _ = _ * _
  exact Subsingleton.elim _ _

end Kourovka.MetabelianEnumeration.QuotientCodes
