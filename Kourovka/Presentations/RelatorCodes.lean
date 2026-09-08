/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Certificates.PresentationIsomorphism

/-!
# Relator Codes

Passage between finite relator lists and the ordinary presentation codes
used in the exact recursive-enumerability target.
-/

namespace Kourovka.MetabelianEnumeration.WordCertificates

def encodeWord {n : ℕ} (w : Word n) : List (ℕ × Bool) :=
  w.map fun letter => (letter.1.val, letter.2)

theorem interpret_encodeWord {n : ℕ} (w : Word n) :
    interpretWord n (encodeWord w) = FreeGroup.mk w := by
  rw [← FreeGroup.lift_of_apply (FreeGroup.mk w), FreeGroup.lift_mk]
  simp only [interpretWord, encodeWord, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  rintro ⟨i, b⟩ _
  cases b <;> simp [i.isLt]

def encodeRelators {n : ℕ} (rels : List (FreeGroup (Fin n))) : PresentationCode :=
  (n, rels.map fun r => encodeWord r.toWord)

theorem encodeRelators_wellFormed {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    WellFormed (encodeRelators rels) := by
  intro w hw
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hw
  intro letter hletter
  obtain ⟨⟨i, b⟩, _, rfl⟩ := List.mem_map.mp hletter
  exact i.isLt

theorem relations_encodeRelators {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    relations (encodeRelators rels) = relSet rels := by
  ext r
  simp [relations, encodeRelators, List.map_map, relSet, Function.comp_def,
    interpret_encodeWord, FreeGroup.mk_toWord]

def codeGroupEquiv {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Kourovka.MetabelianEnumeration.GroupOf (encodeRelators rels) ≃*
      PresentedGroup (relSet rels) := by
  change PresentedGroup (relations (encodeRelators rels)) ≃* PresentedGroup (relSet rels)
  rw [relations_encodeRelators]

theorem code_metabelian_iff {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    Metabelian (Kourovka.MetabelianEnumeration.GroupOf (encodeRelators rels)) ↔
      Metabelian (PresentedGroup (relSet rels)) := by
  constructor
  · exact metabelian_surjective (codeGroupEquiv rels).toMonoidHom (codeGroupEquiv rels).surjective
  · exact metabelian_surjective (codeGroupEquiv rels).symm.toMonoidHom
      (codeGroupEquiv rels).symm.surjective

end Kourovka.MetabelianEnumeration.WordCertificates
