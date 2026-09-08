/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Computability.ComputableClosure

/-!
# Computable Presentations

Uniform natural-alphabet word certificates for ordinary finite presentations.
The generator bound is validated separately, and the semantics is the original
`GroupOf` on `Fin p.1`, including presentations with no generators.
-/

namespace Kourovka.MetabelianEnumeration.ComputablePresentations

open ComputableWords

theorem wellFormed_primrec : PrimrecPred WellFormed := by
  have hletter : PrimrecRel (fun letter : ℕ × Bool => fun n => letter.1 < n) :=
    Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact hletter.forall_mem_list.forall_mem_list.comp Primrec.snd Primrec.fst

theorem decodePresentation_primrec : Primrec decodePresentation :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const (0, []))

def naturalRelators (p : PresentationCode) : List (FreeGroup ℕ) := p.2.map FreeGroup.mk

theorem naturalRelators_primrec : Primrec naturalRelators :=
  Primrec.list_map Primrec.snd (mk_primrec.comp Primrec.snd).to₂

def restrictGenerators (n : ℕ) : FreeGroup ℕ →* FreeGroup (Fin n) :=
  FreeGroup.lift fun i => if h : i < n then FreeGroup.of ⟨i, h⟩ else 1

def includeGenerators (n : ℕ) : FreeGroup (Fin n) →* FreeGroup ℕ :=
  FreeGroup.lift fun i => FreeGroup.of i.1

theorem restrict_mk (n : ℕ) (w : List (ℕ × Bool)) :
    restrictGenerators n (FreeGroup.mk w) = interpretWord n w := by
  rw [restrictGenerators, FreeGroup.lift_mk]
  unfold interpretWord
  congr 1
  apply List.map_congr_left
  intro letter _
  split <;> cases letter.2 <;> simp_all

theorem include_interpret (n : ℕ) (w : List (ℕ × Bool))
    (hw : ∀ letter ∈ w, letter.1 < n) :
    includeGenerators n (interpretWord n w) = FreeGroup.mk w := by
  rw [← restrict_mk]
  have hmk : (includeGenerators n).comp (restrictGenerators n) (FreeGroup.mk w) =
      (FreeGroup.lift (fun i : ℕ => FreeGroup.of i)) (FreeGroup.mk w) := by
    simp only [FreeGroup.lift_mk, restrictGenerators, MonoidHom.comp_apply,
      map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro letter hletter
    cases hb : letter.2 <;> simp [hw letter hletter, includeGenerators, hb]
  have hid : (FreeGroup.lift (fun i : ℕ => FreeGroup.of i)) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    simp
  simpa only [hid, MonoidHom.id_apply, MonoidHom.comp_apply] using hmk

theorem map_normalClosure {G H : Type*} [Group G] [Group H]
    (f : G →* H) (S : Set G) (T : Set H)
    (h : ∀ r ∈ S, f r ∈ Subgroup.normalClosure T) {x : G}
    (hx : x ∈ Subgroup.normalClosure S) : f x ∈ Subgroup.normalClosure T := by
  exact Subgroup.normalClosure_le_normal (N := (Subgroup.normalClosure T).comap f) h hx

theorem natural_word_trivial_iff (p : PresentationCode) (hp : WellFormed p)
    (w : List (ℕ × Bool)) (hw : ∀ letter ∈ w, letter.1 < p.1) :
    FreeGroup.mk w ∈ Subgroup.normalClosure {r | r ∈ naturalRelators p} ↔
      PresentedGroup.mk (relations p) (interpretWord p.1 w) = 1 := by
  rw [PresentedGroup.mk_eq_one_iff]
  constructor
  · intro h
    rw [← restrict_mk]
    apply map_normalClosure (restrictGenerators p.1) _ _ ?_ h
    intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    rw [restrict_mk]
    apply Subgroup.subset_normalClosure
    exact List.mem_map.mpr ⟨v, hv, rfl⟩
  · intro h
    rw [← include_interpret p.1 w hw]
    apply map_normalClosure (includeGenerators p.1) _ _ ?_ h
    intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    rw [include_interpret p.1 v (hp v hv)]
    apply Subgroup.subset_normalClosure
    exact List.mem_map.mpr ⟨v, hv, rfl⟩

def validInput (input : PresentationCode × List (ℕ × Bool)) : Prop :=
  WellFormed input.1 ∧ ∀ letter ∈ input.2, letter.1 < input.1.1

instance : DecidablePred validInput := fun input =>
  inferInstanceAs (Decidable ((∀ w ∈ input.1.2, ∀ l ∈ w, l.1 < input.1.1) ∧
    ∀ l ∈ input.2, l.1 < input.1.1))

theorem validInput_primrec : PrimrecPred validInput := by
  have hletter : PrimrecRel (fun letter : ℕ × Bool => fun n => letter.1 < n) :=
    Primrec.nat_lt.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (wellFormed_primrec.comp Primrec.fst).and
    (hletter.forall_mem_list.comp Primrec.snd (Primrec.fst.comp Primrec.fst))

def checkTrivial (input : PresentationCode × List (ℕ × Bool)) (certificate : ℕ) : Bool :=
  decide (validInput input) &&
    ComputableClosure.checkNat (naturalRelators input.1, FreeGroup.mk input.2) certificate

theorem checkTrivial_primrec : Primrec₂ checkTrivial :=
  Primrec.and.comp (validInput_primrec.decide.comp Primrec.fst)
    ((ComputableClosure.checkNat_primrec mul_primrec inv_primrec).comp
      (((naturalRelators_primrec.comp Primrec.fst).pair (mk_primrec.comp Primrec.snd)).comp
        Primrec.fst) Primrec.snd)

theorem checkTrivial_correct (input : PresentationCode × List (ℕ × Bool)) :
    (∃ certificate, checkTrivial input certificate = true) ↔
      validInput input ∧
        PresentedGroup.mk (relations input.1) (interpretWord input.1.1 input.2) = 1 := by
  simp only [checkTrivial, Bool.and_eq_true, decide_eq_true_eq, exists_and_left]
  rw [ComputableClosure.checkNat_correct]
  constructor
  · rintro ⟨hvalid, hw⟩
    exact ⟨hvalid, (natural_word_trivial_iff _ hvalid.1 _ hvalid.2).mp hw⟩
  · rintro ⟨hvalid, hw⟩
    exact ⟨hvalid, (natural_word_trivial_iff _ hvalid.1 _ hvalid.2).mpr hw⟩

/-- An unconditional uniform semidecision procedure, on the original presentation
and word codes, for equality to the identity in their ordinary presented group. -/
theorem ordinary_word_problem_re :
    REPred (fun input : PresentationCode × List (ℕ × Bool) =>
      validInput input ∧
        PresentedGroup.mk (relations input.1) (interpretWord input.1.1 input.2) = 1) := by
  have hp : Partrec (fun input : PresentationCode × List (ℕ × Bool) =>
      Nat.rfind (fun c => (checkTrivial input c : Part Bool))) :=
    Partrec.rfind checkTrivial_primrec.to_comp.partrec.to₂
  apply hp.dom_re.of_eq
  intro input
  rw [Nat.rfind_dom, ← checkTrivial_correct]
  simp

end Kourovka.MetabelianEnumeration.ComputablePresentations
