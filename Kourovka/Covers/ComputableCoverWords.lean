/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Covers.ComputableLatticeBall
import Kourovka.Presentations.RelatorCodes

/-!
# Computable Cover Words

Primitive recursive generation of cover relators on the natural alphabet.
-/

namespace Kourovka.MetabelianEnumeration.ComputableCoverWords

open ComputableCoverData

abbrev WordGroup := FreeGroup ℕ

def ordered (k : ℕ) (v : List ℤ) : WordGroup :=
  ((List.range k).map fun i => FreeGroup.of i ^ v.getD i 0).prod

def polynomial (k : ℕ) (x : WordGroup) (p : PolynomialCode) : WordGroup :=
  (p.2.map fun term => FiniteCover.conjugate (x ^ term.2)
    (bif p.1 then ordered k term.1 else (ordered k term.1)⁻¹)).prod

def designated (data : DatumCode) (i j : ℕ) : ℕ :=
  ((data.2.1.getD i []).getD j 0) % alphabet data

def tRelators (data : DatumCode) : List WordGroup :=
  (List.range (dimension data)).flatMap fun i =>
    ((List.range (dimension data)).filter fun j => i < j).map fun j =>
      FiniteCover.rightComm (FreeGroup.of i) (FreeGroup.of j) *
        (FreeGroup.of (dimension data + designated data i j))⁻¹

def shortRelators (data : DatumCode) (R : ℕ) : List WordGroup :=
  (List.range (alphabet data)).flatMap fun i =>
    (List.range (alphabet data)).flatMap fun j =>
      (ComputableLatticeBall.ball (dimension data) R).map fun v =>
        FiniteCover.rightComm (FreeGroup.of (dimension data + i))
          (FiniteCover.conjugate (FreeGroup.of (dimension data + j)) (ordered (dimension data) v))

def polynomialRelators (data : DatumCode) : List WordGroup :=
  (List.range (alphabet data)).flatMap fun i => data.2.2.map fun p =>
    (FreeGroup.of (dimension data + i))⁻¹ *
      polynomial (dimension data) (FreeGroup.of (dimension data + i)) p

def relators (data : DatumCode) (R : ℕ) : List WordGroup :=
  tRelators data ++ shortRelators data R ++ polynomialRelators data

def presentation (data : DatumCode) (R : ℕ) : PresentationCode :=
  (dimension data + alphabet data, (relators data R).map FreeGroup.toWord)

theorem of_primrec : Primrec (FreeGroup.of : ℕ → WordGroup) :=
  ComputableWords.mk_primrec.comp (Primrec.list_cons.comp
    (Primrec.id.pair (Primrec.const true)) (Primrec.const []))

theorem pow_primrec : Primrec₂ (fun x : WordGroup => fun n : ℕ => x ^ n) := by
  have h := Primrec.nat_rec (Primrec.const (1 : WordGroup))
    (ComputableWords.mul_primrec.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂
  apply h.of_eq
  intro x n
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih, pow_succ]

theorem zpow_primrec : Primrec₂ (fun x : WordGroup => fun z : ℤ => x ^ z) := by
  apply (ComputableIntegers.casesOn_primrec Primrec.snd
    (pow_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
    (ComputableWords.inv_primrec.comp (pow_primrec.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.succ.comp Primrec.snd))).to₂).of_eq
  rintro ⟨x, z⟩
  cases z with
  | ofNat n => exact (zpow_natCast x n).symm
  | negSucc n => simp only [zpow_negSucc]

theorem prod_primrec : Primrec (List.prod : List WordGroup → WordGroup) :=
  (Primrec.list_foldr Primrec.id (Primrec.const 1)
    (ComputableWords.mul_primrec.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    (fun l => by induction l <;> simp_all)

theorem rightComm_primrec : Primrec₂ (FiniteCover.rightComm : WordGroup → WordGroup → WordGroup) :=
  ComputableWords.mul_primrec.comp
    (ComputableWords.mul_primrec.comp
      (ComputableWords.mul_primrec.comp (ComputableWords.inv_primrec.comp Primrec.fst)
        (ComputableWords.inv_primrec.comp Primrec.snd)) Primrec.fst) Primrec.snd

theorem conjugate_primrec : Primrec₂ (FiniteCover.conjugate : WordGroup → WordGroup → WordGroup) :=
  ComputableWords.mul_primrec.comp
    (ComputableWords.mul_primrec.comp (ComputableWords.inv_primrec.comp Primrec.snd) Primrec.fst)
    Primrec.snd

theorem ordered_primrec : Primrec₂ ordered :=
  prod_primrec.comp (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (zpow_primrec.comp (of_primrec.comp Primrec.snd)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂)

theorem polynomial_primrec : Primrec (fun p : (ℕ × WordGroup) × PolynomialCode =>
    polynomial p.1.1 p.1.2 p.2) :=
  prod_primrec.comp (Primrec.list_map (Primrec.snd.comp Primrec.snd)
    (conjugate_primrec.comp
      (zpow_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.cond (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (ordered_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd))
        (ComputableWords.inv_primrec.comp
          (ordered_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd))))).to₂)

theorem designated_primrec : Primrec (fun p : DatumCode × (ℕ × ℕ) => designated p.1 p.2.1 p.2.2) :=
  Primrec.nat_mod.comp
    ((Primrec.list_getD 0).comp
      ((Primrec.list_getD []).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd))
    (alphabet_primrec.comp Primrec.fst)

def tRelator (p : DatumCode × (ℕ × ℕ)) : WordGroup :=
  FiniteCover.rightComm (FreeGroup.of p.2.1) (FreeGroup.of p.2.2) *
    (FreeGroup.of (dimension p.1 + designated p.1 p.2.1 p.2.2))⁻¹

theorem tRelator_primrec : Primrec tRelator :=
  ComputableWords.mul_primrec.comp
    (rightComm_primrec.comp (of_primrec.comp (Primrec.fst.comp Primrec.snd))
      (of_primrec.comp (Primrec.snd.comp Primrec.snd)))
    (ComputableWords.inv_primrec.comp (of_primrec.comp
      (Primrec.nat_add.comp (dimension_primrec.comp Primrec.fst) designated_primrec)))

theorem tRelators_primrec : Primrec tRelators := by
  have hlt : PrimrecRel (fun j i : ℕ => i < j) :=
    Primrec.nat_lt.comp Primrec.snd Primrec.fst
  have hjs : Primrec (fun p : DatumCode × ℕ =>
      (List.range (dimension p.1)).filter fun j => p.2 < j) :=
    hlt.listFilter.comp
      (Primrec.list_range.comp (dimension_primrec.comp Primrec.fst)) Primrec.snd
  exact Primrec.list_flatMap (Primrec.list_range.comp dimension_primrec)
    (Primrec.list_map hjs
      (tRelator_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂).to₂

def shortRelator (p : DatumCode × ((ℕ × ℕ) × List ℤ)) : WordGroup :=
  FiniteCover.rightComm (FreeGroup.of (dimension p.1 + p.2.1.1))
    (FiniteCover.conjugate (FreeGroup.of (dimension p.1 + p.2.1.2))
      (ordered (dimension p.1) p.2.2))

theorem shortRelator_primrec : Primrec shortRelator :=
  rightComm_primrec.comp
    (of_primrec.comp (Primrec.nat_add.comp (dimension_primrec.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))
    (conjugate_primrec.comp
      (of_primrec.comp (Primrec.nat_add.comp (dimension_primrec.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (ordered_primrec.comp (dimension_primrec.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))

theorem shortRelators_primrec : Primrec₂ shortRelators := by
  let Base := DatumCode × ℕ
  have hball : Primrec (fun p : (Base × ℕ) × ℕ =>
      ComputableLatticeBall.ball (dimension p.1.1.1) p.1.1.2) :=
    ComputableLatticeBall.ball_primrec.comp
      (dimension_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hrow : Primrec (fun p : ((Base × ℕ) × ℕ) × List ℤ =>
      shortRelator (p.1.1.1.1, ((p.1.1.2, p.1.2), p.2))) :=
    shortRelator_primrec.comp
      ((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
        (((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  have hv := Primrec.list_map hball hrow.to₂
  have hj := Primrec.list_flatMap
    (Primrec.list_range.comp (alphabet_primrec.comp (Primrec.fst.comp Primrec.fst))) hv.to₂
  exact Primrec.list_flatMap (Primrec.list_range.comp (alphabet_primrec.comp Primrec.fst)) hj.to₂

def polynomialRelator (p : (DatumCode × ℕ) × PolynomialCode) : WordGroup :=
  (FreeGroup.of (dimension p.1.1 + p.1.2))⁻¹ *
    polynomial (dimension p.1.1) (FreeGroup.of (dimension p.1.1 + p.1.2)) p.2

set_option maxHeartbeats 1000000 in
theorem polynomialRelator_primrec : Primrec polynomialRelator := by
  have hx : Primrec (fun p : (DatumCode × ℕ) × PolynomialCode =>
      (FreeGroup.of (dimension p.1.1 + p.1.2) : WordGroup)) :=
    of_primrec.comp (Primrec.nat_add.comp
      (dimension_primrec.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
  exact ComputableWords.mul_primrec.comp (ComputableWords.inv_primrec.comp hx)
    (polynomial_primrec.comp
      (((dimension_primrec.comp (Primrec.fst.comp Primrec.fst)).pair hx).pair Primrec.snd))

theorem polynomialRelators_primrec : Primrec polynomialRelators :=
  Primrec.list_flatMap (Primrec.list_range.comp alphabet_primrec)
    (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) polynomialRelator_primrec.to₂).to₂

theorem relators_primrec : Primrec₂ relators :=
  Primrec.list_append.comp
    (Primrec.list_append.comp (tRelators_primrec.comp Primrec.fst) shortRelators_primrec)
    (polynomialRelators_primrec.comp Primrec.fst)

theorem presentation_primrec : Primrec₂ presentation :=
  (Primrec.nat_add.comp (dimension_primrec.comp Primrec.fst) (alphabet_primrec.comp Primrec.fst)).pair
    (Primrec.list_map relators_primrec (ComputableWords.toWord_primrec.comp Primrec.snd).to₂)

end Kourovka.MetabelianEnumeration.ComputableCoverWords
