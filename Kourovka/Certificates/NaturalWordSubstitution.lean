/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Computability.ComputablePresentations
import Kourovka.Presentations.RelatorCodes
import Mathlib.Data.List.GetD

/-!
# Natural Word Substitution

Uniform substitution of natural-alphabet words, with primitive-recursive
code and the exact finite-generator semantics.
-/

namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution

open ComputableWords ComputablePresentations

abbrev Word := List (ℕ × Bool)
abbrev Images := List Word

def substitute (f : Images) (w : Word) : Word :=
  w.flatMap fun z => if z.2 then f.getD z.1 [] else FreeGroup.invRev (f.getD z.1 [])

theorem substitute_primrec : Primrec₂ substitute := by
  have hlookup : Primrec (fun p : (Images × Word) × (ℕ × Bool) => p.1.1.getD p.2.1 []) :=
    (Primrec.list_getD []).comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  exact Primrec.list_flatMap Primrec.snd
    ((Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const true))
      hlookup (invRev_primrec.comp hlookup)).to₂)

def ValidWord (n : ℕ) (w : Word) : Prop := ∀ z ∈ w, z.1 < n

theorem interpret_append (n : ℕ) (u v : Word) :
    interpretWord n (u ++ v) = interpretWord n u * interpretWord n v := by
  simp only [interpretWord, List.map_append, List.prod_append]

theorem interpret_inverse (n : ℕ) (w : Word) :
    interpretWord n (FreeGroup.invRev w) = (interpretWord n w)⁻¹ := by
  rw [← restrict_mk, ← FreeGroup.inv_mk, map_inv, restrict_mk]

theorem interpret_cons (n : ℕ) (z : ℕ × Bool) (w : Word) (hz : z.1 < n) :
    interpretWord n (z :: w) =
      (if z.2 then FreeGroup.of ⟨z.1, hz⟩ else (FreeGroup.of ⟨z.1, hz⟩)⁻¹) *
        interpretWord n w := by simp [interpretWord, hz]

theorem interpret_substitute (n m : ℕ) (f : Images) (w : Word) (hw : ValidWord n w) :
    interpretWord m (substitute f w) =
      FreeGroup.lift (fun i : Fin n => interpretWord m (f.getD i.val [])) (interpretWord n w) := by
  induction w with
  | nil => simp [substitute, interpretWord]
  | cons z w ih =>
    have hz := hw z List.mem_cons_self
    have ht : ValidWord n w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    rw [interpret_cons n z w hz]
    have hs : interpretWord m
        (w.flatMap fun z => if z.2 then f.getD z.1 [] else FreeGroup.invRev (f.getD z.1 [])) =
          FreeGroup.lift (fun i : Fin n => interpretWord m (f.getD i.val [])) (interpretWord n w) := ih ht
    simp only [substitute, List.flatMap_cons, interpret_append, map_mul, hs]
    cases z.2 <;> simp only [Bool.false_eq_true, if_false, if_true,
      interpret_inverse, map_inv, FreeGroup.lift_apply_of]

theorem valid_encode {n : ℕ} (w : WordCertificates.Word n) :
    ValidWord n (WordCertificates.encodeWord w) := by
  intro z hz
  obtain ⟨⟨i, b⟩, _, rfl⟩ := List.mem_map.mp hz
  exact i.isLt

theorem valid_getD (n : ℕ) (f : Images) (hf : WellFormed (n, f)) (i : ℕ) :
    ValidWord n (f.getD i []) := by
  by_cases hi : i < f.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hf _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro z hz
    exact False.elim (List.not_mem_nil hz)

theorem valid_inverse {n : ℕ} {w : Word} (h : ValidWord n w) :
    ValidWord n (FreeGroup.invRev w) := by
  intro z hz
  simp only [FreeGroup.invRev, List.mem_reverse, List.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact h y hy

theorem valid_substitute (m : ℕ) (f : Images) (hf : WellFormed (m, f)) (w : Word) :
    ValidWord m (substitute f w) := by
  intro z hz
  obtain ⟨x, _, hz⟩ := List.mem_flatMap.mp hz
  have hv := valid_getD m f hf x.1
  cases hb : x.2
  · exact valid_inverse hv z (by simpa [hb] using hz)
  · exact hv z (by simpa [hb] using hz)


theorem valid_append {n : ℕ} {u v : Word} (hu : ValidWord n u) (hv : ValidWord n v) :
    ValidWord n (u ++ v) := by
  intro z hz
  exact (List.mem_append.mp hz).elim (hu z) (hv z)

theorem interpret_singleton_false (n i : ℕ) (hi : i < n) :
    interpretWord n [(i, false)] = (FreeGroup.of ⟨i, hi⟩)⁻¹ := by
  simp [interpretWord, hi]

theorem interpret_inverseCheck (n m : ℕ) (f g : Images) (hf : WellFormed (m, f))
    (i : ℕ) (hi : i < n) :
    interpretWord n (substitute g (f.getD i []) ++ [(i, false)]) =
      FreeGroup.lift (fun j : Fin m => interpretWord n (g.getD j.val []))
        (interpretWord m (f.getD i [])) * (FreeGroup.of ⟨i, hi⟩)⁻¹ := by
  rw [interpret_append, interpret_substitute m n g _ (valid_getD m f hf i),
    interpret_singleton_false n i hi]


end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
