/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Computability.ComputableWords

/-!
# Computable Closure

A primitive-recursive bounded search for normal-closure membership.
The certificate consists only of a finite list of conjugators and a natural
depth. Its completeness is proved for the actual subgroup normal closure.
-/

namespace Kourovka.MetabelianEnumeration.ComputableClosure

variable {G : Type*} [Group G]

def expand (conjugators xs : List G) : List G :=
  xs ++ xs.map Inv.inv ++
    xs.flatMap (fun x => xs.map (fun y => x * y)) ++
    conjugators.flatMap (fun g => xs.map (fun x => g * x * g⁻¹))

def stages (rels conjugators : List G) (n : ℕ) : List G :=
  (expand conjugators)^[n] (1 :: rels)

theorem mem_expand (C xs : List G) (x : G) :
    x ∈ expand C xs ↔ x ∈ xs ∨ (∃ y ∈ xs, y⁻¹ = x) ∨
      (∃ y ∈ xs, ∃ z ∈ xs, y * z = x) ∨
      (∃ g ∈ C, ∃ y ∈ xs, g * y * g⁻¹ = x) := by
  simp only [expand, List.mem_append, List.mem_map, List.mem_flatMap, or_assoc]

theorem subset_expand (C xs : List G) : xs ⊆ expand C xs :=
  fun x hx => (mem_expand C xs x).mpr (Or.inl hx)

theorem expand_mono {C D xs ys : List G} (hCD : C ⊆ D) (hxy : xs ⊆ ys) :
    expand C xs ⊆ expand D ys := by
  intro x hx
  rcases (mem_expand C xs x).mp hx with hx | ⟨y, hy, rfl⟩ |
    ⟨y, hy, z, hz, rfl⟩ | ⟨g, hg, y, hy, rfl⟩
  · exact (mem_expand D ys x).mpr (Or.inl (hxy hx))
  · exact (mem_expand D ys _).mpr (Or.inr (Or.inl ⟨y, hxy hy, rfl⟩))
  · exact (mem_expand D ys _).mpr (Or.inr (Or.inr (Or.inl ⟨y, hxy hy, z, hxy hz, rfl⟩)))
  · exact (mem_expand D ys _).mpr (Or.inr (Or.inr (Or.inr ⟨g, hCD hg, y, hxy hy, rfl⟩)))

@[simp] theorem stages_zero (rels C : List G) : stages rels C 0 = 1 :: rels := rfl

theorem stages_succ (rels C : List G) (n : ℕ) :
    stages rels C (n + 1) = expand C (stages rels C n) :=
  Function.iterate_succ_apply' _ _ _

theorem stages_mono_conjugators (rels : List G) {C D : List G} (hCD : C ⊆ D) (n : ℕ) :
    stages rels C n ⊆ stages rels D n := by
  induction n with
  | zero => exact List.Subset.refl _
  | succ n ih => rw [stages_succ, stages_succ]; exact expand_mono hCD ih

theorem stages_mono_depth (rels C : List G) {n m : ℕ} (hnm : n ≤ m) :
    stages rels C n ⊆ stages rels C m := by
  induction hnm with
  | refl => exact List.Subset.refl _
  | @step m hm ih =>
    rw [stages_succ]
    exact ih.trans (subset_expand _ _)

theorem stages_sound (rels C : List G) (n : ℕ) {x : G}
    (hx : x ∈ stages rels C n) : x ∈ Subgroup.normalClosure {r | r ∈ rels} := by
  induction n generalizing x with
  | zero =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_normalClosure hx
  | succ n ih =>
    rw [stages_succ] at hx
    rcases (mem_expand _ _ _).mp hx with hx | ⟨y, hy, rfl⟩ |
      ⟨y, hy, z, hz, rfl⟩ | ⟨g, _, y, hy, rfl⟩
    · exact ih hx
    · exact Subgroup.inv_mem _ (ih hy)
    · exact Subgroup.mul_mem _ (ih hy) (ih hz)
    · exact Subgroup.Normal.conj_mem inferInstance _ (ih hy) _

def reachable (rels : List G) : Subgroup G where
  carrier := {x | ∃ C n, x ∈ stages rels C n}
  one_mem' := ⟨[], 0, by simp⟩
  inv_mem' := by
    rintro x ⟨C, n, hx⟩
    refine ⟨C, n + 1, ?_⟩
    rw [stages_succ]
    exact (mem_expand _ _ _).mpr (Or.inr (Or.inl ⟨x, hx, rfl⟩))
  mul_mem' := by
    rintro x y ⟨C, n, hx⟩ ⟨D, m, hy⟩
    have hx' : x ∈ stages rels (C ++ D) (max n m) :=
      stages_mono_depth _ _ (le_max_left n m)
        (stages_mono_conjugators rels (by intro _ h; exact List.mem_append_left _ h) n hx)
    have hy' : y ∈ stages rels (C ++ D) (max n m) :=
      stages_mono_depth _ _ (le_max_right n m)
        (stages_mono_conjugators rels (by intro _ h; exact List.mem_append_right _ h) m hy)
    refine ⟨C ++ D, max n m + 1, ?_⟩
    rw [stages_succ]
    exact (mem_expand _ _ _).mpr (Or.inr (Or.inr (Or.inl ⟨x, hx', y, hy', rfl⟩)))

instance reachable_normal (rels : List G) : (reachable rels).Normal where
  conj_mem := by
    rintro x ⟨C, n, hx⟩ g
    have hx' : x ∈ stages rels (g :: C) n :=
      stages_mono_conjugators rels (by intro _ h; exact List.mem_cons_of_mem _ h) n hx
    refine ⟨g :: C, n + 1, ?_⟩
    rw [stages_succ]
    exact (mem_expand _ _ _).mpr (Or.inr (Or.inr (Or.inr ⟨g, by simp, x, hx', rfl⟩)))

theorem mem_normalClosure_iff (rels : List G) (x : G) :
    x ∈ Subgroup.normalClosure {r | r ∈ rels} ↔ ∃ C n, x ∈ stages rels C n := by
  constructor
  · apply Subgroup.normalClosure_le_normal (N := reachable rels)
    intro r hr
    exact ⟨[], 0, List.mem_cons_of_mem _ hr⟩
  · rintro ⟨C, n, hx⟩
    exact stages_sound rels C n hx

section Computability

variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))

include hmul hinv

omit [DecidableEq G] in
theorem expand_primrec : Primrec₂ (@expand G _) := by
  have hi : Primrec (fun p : List G × List G => p.2.map Inv.inv) :=
    Primrec.list_map Primrec.snd (hinv.comp Primrec.snd).to₂
  have hm : Primrec (fun p : List G × List G =>
      p.2.flatMap fun x => p.2.map fun y => x * y) :=
    Primrec.list_flatMap Primrec.snd
      (Primrec.list_map (Primrec.snd.comp Primrec.fst)
        (hmul.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  have hc : Primrec (fun p : List G × List G =>
      p.1.flatMap fun g => p.2.map fun x => g * x * g⁻¹) :=
    Primrec.list_flatMap Primrec.fst
      (Primrec.list_map (Primrec.snd.comp Primrec.fst)
        (hmul.comp (hmul.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
          (hinv.comp (Primrec.snd.comp Primrec.fst))).to₂).to₂
  exact Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.list_append.comp Primrec.snd hi) hm) hc

omit [DecidableEq G] in
theorem stages_primrec : Primrec (fun p : (List G × List G) × ℕ => stages p.1.1 p.1.2 p.2) :=
  Primrec.nat_iterate Primrec.snd
    (Primrec.list_cons.comp (Primrec.const 1) (Primrec.fst.comp Primrec.fst))
    ((expand_primrec hmul hinv).comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂

def check (input : List G × G) (certificate : List G × ℕ) : Bool :=
  decide (input.2 ∈ stages input.1 certificate.1 certificate.2)

theorem check_primrec : Primrec₂ (@check G _ _) := by
  have hm : PrimrecRel (fun xs : List G => fun x => x ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun p => by simp)
  exact hm.decide.comp
    ((stages_primrec hmul hinv).comp
      (((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd))) (Primrec.snd.comp Primrec.fst)

omit hmul hinv [Primcodable G] in
theorem check_correct (input : List G × G) :
    (∃ certificate, check input certificate = true) ↔
      input.2 ∈ Subgroup.normalClosure {r | r ∈ input.1} := by
  simp only [check, decide_eq_true_eq, Prod.exists]
  exact (mem_normalClosure_iff _ _).symm

def checkNat (input : List G × G) (certificate : ℕ) : Bool :=
  check input ((Encodable.decode (α := List G × ℕ) certificate).getD ([], 0))

theorem checkNat_primrec : Primrec₂ (@checkNat G _ _ _) :=
  (check_primrec hmul hinv).comp Primrec.fst
    (Primrec.option_getD.comp (Primrec.decode.comp Primrec.snd) (Primrec.const ([], 0)))

omit hmul hinv in
theorem checkNat_correct (input : List G × G) :
    (∃ certificate, checkNat input certificate = true) ↔
      input.2 ∈ Subgroup.normalClosure {r | r ∈ input.1} := by
  rw [← check_correct]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨_, hn⟩
  · rintro ⟨certificate, hc⟩
    refine ⟨Encodable.encode certificate, ?_⟩
    simpa [checkNat] using hc

theorem normalClosure_re :
    REPred (fun input : List G × G => input.2 ∈ Subgroup.normalClosure {r | r ∈ input.1}) := by
  have hp : Partrec (fun input : List G × G =>
      Nat.rfind (fun c => (checkNat input c : Part Bool))) :=
    Partrec.rfind (checkNat_primrec hmul hinv).to_comp.partrec.to₂
  apply hp.dom_re.of_eq
  intro input
  rw [Nat.rfind_dom, ← checkNat_correct]
  simp

end Computability

/-- Uniform recursive enumerability of trivial words in finite presentations.
Neither the presentation nor the word is fixed in this predicate. -/
theorem presented_word_problem_re {α : Type*} [Primcodable α] [DecidableEq α] :
    REPred (fun input : List (FreeGroup α) × FreeGroup α =>
      PresentedGroup.mk {r | r ∈ input.1} input.2 = 1) := by
  apply (normalClosure_re ComputableWords.mul_primrec ComputableWords.inv_primrec).of_eq
  intro input
  exact PresentedGroup.mk_eq_one_iff.symm

end Kourovka.MetabelianEnumeration.ComputableClosure
