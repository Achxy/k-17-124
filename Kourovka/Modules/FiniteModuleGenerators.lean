/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Modules.ModuleRealization

/-!
# Finite module generators and their concrete lists

These lemmas turn abstract module finiteness into finite data used in cover
constructions.
-/

noncomputable section

set_option maxHeartbeats 50000

namespace Kourovka.MetabelianEnumeration.CofinalCover

open FiniteCover ValuationModule

/-- Enlarge any finite spanning family by specified elements and zero, then
index it by a nonempty finite ordinal. -/
theorem finite_generators_with_designated {k : ℕ} {M : Type} [AddCommGroup M]
    [Module (GroupRing (Lattice k)) M] [Module.Finite (GroupRing (Lattice k)) M]
    (c : Fin k × Fin k → M) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ (A : Fin a → M) (designated : Fin k → Fin k → Fin a),
      Submodule.span (GroupRing (Lattice k)) (Set.range A) = ⊤ ∧
      ∀ i j, A (designated i j) = c (i, j) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := GroupRing (Lattice k)) (M := M)
  let d : Finset M := Finset.univ.image c
  let b : Finset M := insert 0 (s ∪ d)
  let e := Fintype.equivFin b
  let a := Fintype.card b
  let A : Fin a → M := fun i => (e.symm i).val
  have hbzero : (0 : M) ∈ b := Finset.mem_insert_self _ _
  have ha : 1 ≤ a := by
    letI : Nonempty b := ⟨⟨0, hbzero⟩⟩
    exact Fintype.card_pos_iff.mpr inferInstance
  have hc (i j : Fin k) : c (i, j) ∈ b :=
    Finset.mem_insert_of_mem (Finset.mem_union_right s
      (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
  let designated : Fin k → Fin k → Fin a := fun i j => e ⟨c (i, j), hc i j⟩
  refine ⟨a, ha, A, designated, ?_, ?_⟩
  · apply top_unique
    rw [← hs]
    apply Submodule.span_mono
    intro m hm
    have hmb : m ∈ b := Finset.mem_insert_of_mem (Finset.mem_union_left d hm)
    exact ⟨e ⟨m, hmb⟩, congrArg Subtype.val (e.symm_apply_apply ⟨m, hmb⟩)⟩
  · intro i j
    exact congrArg Subtype.val (e.symm_apply_apply ⟨c (i, j), hc i j⟩)

end Kourovka.MetabelianEnumeration.CofinalCover
