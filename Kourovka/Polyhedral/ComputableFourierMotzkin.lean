/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Computability.ComputableIntegers
import Kourovka.Polyhedral.FourierMotzkin

/-!
# Computable Fourier Motzkin

Uniform list encoding of integer Fourier–Motzkin elimination. Dimensions
are natural inputs, so no dependent finite-vector encoding is required.
-/

namespace Kourovka.MetabelianEnumeration.ComputableFourierMotzkin

open ComputableIntegers

abbrev RowCode := List ℤ × ℤ

def coeff (r : RowCode) (i : ℕ) : ℤ := r.1.getD i 0

def head (r : RowCode) : ℤ := coeff r 0

def tail (r : RowCode) : RowCode := (r.1.tail, r.2)

def combineCoeff (p : RowCode × RowCode) (i : ℕ) : ℤ :=
  head p.2 * coeff p.1 i - head p.1 * coeff p.2 i

def combine (p : RowCode × RowCode) : RowCode :=
  ((List.range (max p.1.1.length p.2.1.length)).map fun i => combineCoeff p (i + 1),
    head p.2 * p.1.2 - head p.1 * p.2.2)

def eliminate (rows : List RowCode) : List RowCode :=
  (rows.filter (fun r => head r = 0)).map tail ++
    (rows.filter (fun r => head r < 0)).flatMap fun l =>
      (rows.filter (fun r => 0 < head r)).map fun u => combine (l, u)

def check (n : ℕ) (rows : List RowCode) : Bool :=
  ((eliminate^[n]) rows).all fun r => r.2 ≤ 0

def decodeRow (n : ℕ) (r : RowCode) : FourierMotzkin.Row n :=
  ⟨fun i => (coeff r i : ℚ), r.2⟩

theorem coeff_primrec : Primrec₂ coeff :=
  (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd

theorem head_primrec : Primrec head := coeff_primrec.comp Primrec.id (Primrec.const 0)

theorem tail_primrec : Primrec tail := (Primrec.list_tail.comp Primrec.fst).pair Primrec.snd

theorem combineCoeff_primrec : Primrec₂ combineCoeff :=
  sub_primrec.comp
    (mul_primrec.comp (head_primrec.comp (Primrec.snd.comp Primrec.fst))
      (coeff_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))
    (mul_primrec.comp (head_primrec.comp (Primrec.fst.comp Primrec.fst))
      (coeff_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))

theorem combine_primrec : Primrec combine :=
  (Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_max.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))))
    (combineCoeff_primrec.comp Primrec.fst (Primrec.succ.comp Primrec.snd)).to₂).pair
    (sub_primrec.comp
      (mul_primrec.comp (head_primrec.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (mul_primrec.comp (head_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))

theorem eliminate_primrec : Primrec eliminate := by
  have hz : Primrec (fun rows : List RowCode => rows.filter fun r => head r = 0) :=
    Primrec.listFilter (Primrec.eq.comp head_primrec (Primrec.const 0))
  have hn : Primrec (fun rows : List RowCode => rows.filter fun r => head r < 0) :=
    Primrec.listFilter (lt_primrec.comp head_primrec (Primrec.const 0))
  have hp : Primrec (fun rows : List RowCode => rows.filter fun r => 0 < head r) :=
    Primrec.listFilter (lt_primrec.comp (Primrec.const 0) head_primrec)
  exact Primrec.list_append.comp
    (Primrec.list_map hz (tail_primrec.comp Primrec.snd).to₂)
    (Primrec.list_flatMap hn
      (Primrec.list_map (hp.comp Primrec.fst)
        (combine_primrec.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂)

theorem check_primrec : Primrec₂ check := by
  have hi : Primrec (fun p : ℕ × List RowCode => (eliminate^[p.1]) p.2) :=
    Primrec.nat_iterate Primrec.fst Primrec.snd (eliminate_primrec.comp Primrec.snd).to₂
  have hall : Primrec (fun rows : List RowCode => rows.all fun r => r.2 ≤ 0) := by
    exact ((le_primrec.comp Primrec.snd (Primrec.const 0)).forall_mem_list.decide).of_eq
      (fun rows => by rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq, List.all_eq_true])
  exact hall.comp hi

theorem decode_head (n : ℕ) (r : RowCode) : (decodeRow (n + 1) r).head = (head r : ℚ) := rfl

theorem decode_tail (n : ℕ) (r : RowCode) :
    decodeRow n (tail r) = (decodeRow (n + 1) r).tail := by
  apply congrArg₂ (FourierMotzkin.Row.mk (n := n))
  · ext i
    simp [decodeRow, tail, coeff, List.getD_eq_getElem?_getD]
  · rfl

theorem combine_coeff (p : RowCode × RowCode) (i : ℕ) :
    coeff (combine p) i = combineCoeff p (i + 1) := by
  by_cases hi : i < max p.1.1.length p.2.1.length
  · simp [coeff, combine, List.getD_eq_getElem?_getD, hi]
  · have hleft : p.1.1.length ≤ i + 1 := by omega
    have hright : p.2.1.length ≤ i + 1 := by omega
    simp [coeff, combine, combineCoeff, List.getD_eq_getElem?_getD, hi,
      List.getElem?_eq_none hleft, List.getElem?_eq_none hright]

theorem decode_combine (n : ℕ) (p : RowCode × RowCode) :
    decodeRow n (combine p) = (decodeRow (n + 1) p.1).combine (decodeRow (n + 1) p.2) := by
  apply congrArg₂ (FourierMotzkin.Row.mk (n := n))
  · ext i
    simp [decodeRow, combine_coeff, combineCoeff,
      FourierMotzkin.Row.head, head]
  · simp [decodeRow, combine, FourierMotzkin.Row.head, head]

theorem map_filter_eq {α β : Type*} (f : α → β) (p : α → Bool) (q : β → Bool)
    (h : ∀ x, q (f x) = p x) (l : List α) :
    (l.filter p).map f = (l.map f).filter q := by
  induction l with
  | nil => rfl
  | cons x l ih => cases hpx : p x <;> simp [h, hpx, ih]

theorem decode_eliminate (n : ℕ) (rows : List RowCode) :
    (eliminate rows).map (decodeRow n) =
      FourierMotzkin.eliminate (rows.map (decodeRow (n + 1))) := by
  have hz : ((rows.filter fun r => head r = 0).map (decodeRow (n + 1))) =
      (rows.map (decodeRow (n + 1))).filter (fun r => r.head = 0) := by
    apply map_filter_eq
    intro r; simp [decode_head]
  have hn : ((rows.filter fun r => head r < 0).map (decodeRow (n + 1))) =
      FourierMotzkin.negatives (rows.map (decodeRow (n + 1))) := by
    apply map_filter_eq
    intro r; simp [decode_head]
  have hp : ((rows.filter fun r => 0 < head r).map (decodeRow (n + 1))) =
      FourierMotzkin.positives (rows.map (decodeRow (n + 1))) := by
    apply map_filter_eq
    intro r; simp [decode_head]
  simp only [eliminate, List.map_append, List.map_map, List.map_flatMap,
    FourierMotzkin.eliminate, ← hz, ← hn, ← hp, List.map_map, List.flatMap_map]
  simp only [Function.comp_def, decode_tail, decode_combine]

theorem check_eq (n : ℕ) (rows : List RowCode) :
    check n rows = FourierMotzkin.check n (rows.map (decodeRow n)) := by
  induction n generalizing rows with
  | zero =>
    rw [Bool.eq_iff_iff]
    simp [check, FourierMotzkin.check, decodeRow, List.all_map, Function.comp_def]
  | succ n ih =>
    rw [check, Function.iterate_succ_apply]
    change check n (eliminate rows) = _
    rw [ih, decode_eliminate, FourierMotzkin.check]

end Kourovka.MetabelianEnumeration.ComputableFourierMotzkin
