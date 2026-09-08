/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Certificates.WordCertificates

/-!
# Computable Words

Primitive-recursive free reduction, with the actual Mathlib encoding.
This is a computability theorem, not merely an executable implementation.
-/

namespace Kourovka.MetabelianEnumeration.ComputableWords

variable {α : Type*} [Primcodable α] [DecidableEq α]

def reduceStep (letter : α × Bool) (word : List (α × Bool)) : List (α × Bool) :=
  List.casesOn word [letter] fun head tail =>
    if letter.1 = head.1 ∧ letter.2 = !head.2 then tail else letter :: head :: tail

theorem reduceStep_primrec : Primrec₂ (@reduceStep α _) := by
  let hnil : Primrec (fun p : (α × Bool) × List (α × Bool) => [p.1]) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.const [])
  have hcond : PrimrecPred (fun p : ((α × Bool) × List (α × Bool)) ×
      ((α × Bool) × List (α × Bool)) =>
      p.1.1.1 = p.2.1.1 ∧ p.1.1.2 = !p.2.1.2) :=
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).and
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.not.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  have hbody : Primrec₂ (fun p : (α × Bool) × List (α × Bool) =>
      fun q : (α × Bool) × List (α × Bool) =>
      if p.1.1 = q.1.1 ∧ p.1.2 = !q.1.2 then q.2 else p.1 :: q.1 :: q.2) :=
    (Primrec.ite hcond (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd)))).to₂
  exact Primrec.list_casesOn Primrec.snd hnil hbody

omit [Primcodable α] in
theorem reduce_eq_foldr (word : List (α × Bool)) :
    FreeGroup.reduce word = word.foldr reduceStep [] := by
  induction word with
  | nil => rfl
  | cons letter word ih => rw [FreeGroup.reduce.cons, List.foldr_cons, ← ih]; rfl

theorem reduce_primrec : Primrec (@FreeGroup.reduce α _) := by
  have h := Primrec.list_foldr (Primrec.id (α := List (α × Bool))) (Primrec.const [])
    ((reduceStep_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq (fun w => (reduce_eq_foldr w).symm)

def wordEq (left right : List (α × Bool)) : Bool :=
  decide (FreeGroup.reduce left = FreeGroup.reduce right)

theorem wordEq_primrec : Primrec₂ (@wordEq α _) :=
  Primrec.eq.decide.comp (reduce_primrec.comp Primrec.fst) (reduce_primrec.comp Primrec.snd)

omit [Primcodable α] in
theorem wordEq_correct (left right : List (α × Bool)) :
    wordEq left right = true ↔ FreeGroup.mk left = FreeGroup.mk right := by
  simp only [wordEq, decide_eq_true_eq]
  constructor
  · intro h
    have h' := congrArg FreeGroup.mk h
    simpa only [FreeGroup.reduce.self] using h'
  · intro h
    have h' := congrArg FreeGroup.toWord h
    simpa only [FreeGroup.toWord_mk] using h'

/-- The encoding keeps exactly the freely reduced lists. -/
abbrev ReducedWord (α : Type*) [DecidableEq α] :=
  {w : List (α × Bool) // FreeGroup.reduce w = w}

theorem reduced_primrec : PrimrecPred (fun w : List (α × Bool) => FreeGroup.reduce w = w) :=
  Primrec.eq.comp reduce_primrec Primrec.id

instance reducedWordPrimcodable : Primcodable (ReducedWord α) :=
  Primcodable.subtype reduced_primrec

def reducedWordEquiv : FreeGroup α ≃ ReducedWord α where
  toFun g := ⟨g.toWord, FreeGroup.reduce_toWord g⟩
  invFun w := FreeGroup.mk w.1
  left_inv _ := FreeGroup.mk_toWord
  right_inv w := Subtype.ext (by exact w.2)

instance freeGroupPrimcodable : Primcodable (FreeGroup α) :=
  Primcodable.ofEquiv (ReducedWord α) reducedWordEquiv

theorem toWord_primrec : Primrec (@FreeGroup.toWord α _) :=
  Primrec.subtype_val.comp (Primrec.of_equiv (e := reducedWordEquiv))

theorem freeGroup_primrec_iff {β : Type*} [Primcodable β] {f : β → FreeGroup α} :
    Primrec f ↔ Primrec (fun b => (f b).toWord) := by
  rw [← Primrec.of_equiv_iff reducedWordEquiv, ← Primrec.subtype_val_iff]
  rfl

theorem mk_primrec : Primrec (@FreeGroup.mk α) :=
  freeGroup_primrec_iff.mpr reduce_primrec

theorem mul_primrec : Primrec₂ (fun x y : FreeGroup α => x * y) :=
  freeGroup_primrec_iff.mpr <|
    (reduce_primrec.comp (Primrec.list_append.comp
      (toWord_primrec.comp Primrec.fst) (toWord_primrec.comp Primrec.snd))).of_eq
        (fun p => (FreeGroup.toWord_mul p.1 p.2).symm)

omit [DecidableEq α] in
theorem invRev_primrec : Primrec (@FreeGroup.invRev α) :=
  Primrec.list_reverse.comp <|
    Primrec.list_map Primrec.id
      ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.not.comp (Primrec.snd.comp Primrec.snd))).to₂

theorem inv_primrec : Primrec (fun x : FreeGroup α => x⁻¹) :=
  freeGroup_primrec_iff.mpr <|
    (invRev_primrec.comp toWord_primrec).of_eq (fun g => (FreeGroup.toWord_inv g).symm)

theorem conjugate_primrec : Primrec₂ (fun g x : FreeGroup α => g * x * g⁻¹) :=
  mul_primrec.comp (mul_primrec.comp Primrec.fst Primrec.snd)
    (inv_primrec.comp Primrec.fst)

end Kourovka.MetabelianEnumeration.ComputableWords
