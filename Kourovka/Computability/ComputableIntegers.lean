/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Computability.ComputablePresentations

/-!
# Computable Integers

Primitive recursive signed integer arithmetic using an explicit sum
encoding. All external certificate data remains natural numbers and lists.
-/

namespace Kourovka.MetabelianEnumeration.ComputableIntegers

instance integerPrimcodable : Primcodable ℤ :=
  Primcodable.ofEquiv (ℕ ⊕ ℕ) Equiv.intEquivNatSumNat

theorem ofNat_primrec : Primrec (fun n : ℕ => (n : ℤ)) :=
  (Primrec.of_equiv_symm (e := Equiv.intEquivNatSumNat)).comp Primrec.sumInl

theorem negSucc_primrec : Primrec Int.negSucc :=
  (Primrec.of_equiv_symm (e := Equiv.intEquivNatSumNat)).comp Primrec.sumInr

theorem casesOn_primrec {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → ℤ} {g h : α → ℕ → β}
    (hf : Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) :
    Primrec (fun a => Int.casesOn (motive := fun _ => β) (f a) (g a) (h a)) :=
  (Primrec.sumCasesOn ((Primrec.of_equiv (e := Equiv.intEquivNatSumNat)).comp hf) hg hh).of_eq
    (fun a => by cases f a <;> rfl)

theorem toNat_primrec : Primrec Int.toNat := by
  exact (casesOn_primrec Primrec.id Primrec.snd.to₂ (Primrec.const 0).to₂).of_eq
    (fun z => by cases z <;> rfl)

theorem natAbs_primrec : Primrec Int.natAbs := by
  exact (casesOn_primrec Primrec.id Primrec.snd.to₂ (Primrec.succ.comp Primrec.snd).to₂).of_eq
    (fun z => by cases z <;> rfl)

def subNat (m n : ℕ) : ℤ :=
  if n ≤ m then ((m - n : ℕ) : ℤ) else Int.negSucc (n - m - 1)

theorem subNat_eq (m n : ℕ) : subNat m n = (m : ℤ) - n := by
  unfold subNat
  split <;> omega

theorem subNat_primrec : Primrec₂ subNat :=
  Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
    (ofNat_primrec.comp Primrec.nat_sub)
    (negSucc_primrec.comp (Primrec.nat_sub.comp
      (Primrec.nat_sub.comp Primrec.snd Primrec.fst) (Primrec.const 1)))

theorem neg_primrec : Primrec (fun z : ℤ => -z) := by
  apply (casesOn_primrec Primrec.id
    (subNat_primrec.comp (Primrec.const 0) Primrec.snd).to₂
    (ofNat_primrec.comp (Primrec.succ.comp Primrec.snd)).to₂).of_eq
  intro z
  cases z with
  | ofNat n => change subNat 0 n = -(n : ℤ); simp [subNat_eq]
  | negSucc n => rfl

theorem add_primrec : Primrec₂ (fun x y : ℤ => x + y) := by
  have hp : Primrec₂ (fun x y : ℤ => x.toNat + y.toNat) :=
    Primrec.nat_add.comp (toNat_primrec.comp Primrec.fst) (toNat_primrec.comp Primrec.snd)
  have hn : Primrec₂ (fun x y : ℤ => (-x).toNat + (-y).toNat) :=
    Primrec.nat_add.comp (toNat_primrec.comp (neg_primrec.comp Primrec.fst))
      (toNat_primrec.comp (neg_primrec.comp Primrec.snd))
  apply (subNat_primrec.comp hp hn).of_eq
  intro z
  rw [subNat_eq]
  rcases z with ⟨x, y⟩
  cases x <;> cases y <;> simp [Int.negSucc_eq] <;> omega

theorem sub_primrec : Primrec₂ (fun x y : ℤ => x - y) :=
  (add_primrec.comp Primrec.fst (neg_primrec.comp Primrec.snd)).of_eq (fun _ => rfl)

theorem le_primrec : PrimrecRel (fun x y : ℤ => x ≤ y) := by
  apply (Primrec.nat_le.comp
    (Primrec.nat_add.comp (toNat_primrec.comp Primrec.fst)
      (toNat_primrec.comp (neg_primrec.comp Primrec.snd)))
    (Primrec.nat_add.comp (toNat_primrec.comp Primrec.snd)
      (toNat_primrec.comp (neg_primrec.comp Primrec.fst)))).of_eq
  intro z
  rcases z with ⟨x, y⟩
  cases x <;> cases y <;> simp [Int.negSucc_eq] <;> omega

theorem lt_primrec : PrimrecRel (fun x y : ℤ => x < y) :=
  (le_primrec.comp Primrec.snd Primrec.fst).not.of_eq (fun _ => by omega)

theorem abs_primrec : Primrec (fun z : ℤ => |z|) :=
  (ofNat_primrec.comp natAbs_primrec).of_eq (fun z => Int.natCast_natAbs z)

theorem mul_primrec : Primrec₂ (fun x y : ℤ => x * y) := by
  have hprod : Primrec₂ (fun x y : ℤ => ((x.natAbs * y.natAbs : ℕ) : ℤ)) :=
    ofNat_primrec.comp (Primrec.nat_mul.comp
      (natAbs_primrec.comp Primrec.fst) (natAbs_primrec.comp Primrec.snd))
  have hsign : PrimrecPred (fun p : ℤ × ℤ => (p.1 < 0) ↔ (p.2 < 0)) :=
    (Primrec.eq.comp (lt_primrec.comp Primrec.fst (Primrec.const 0)).decide
      (lt_primrec.comp Primrec.snd (Primrec.const 0)).decide).of_eq (fun p => by simp)
  apply (Primrec.ite hsign hprod (neg_primrec.comp hprod)).of_eq
  rintro ⟨x, y⟩
  simp only [Nat.cast_mul, Int.natCast_natAbs]
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  · simp [hx, hy, abs_of_neg hx, abs_of_neg hy]
  · simp [hx, hy, abs_of_neg hx, abs_of_nonneg (le_of_not_gt hy)]
  · simp [hx, hy, abs_of_nonneg (le_of_not_gt hx), abs_of_neg hy]
  · simp [hx, hy, abs_of_nonneg (le_of_not_gt hx), abs_of_nonneg (le_of_not_gt hy)]

theorem nat_pow_primrec : Primrec₂ (fun a n : ℕ => a ^ n) := by
  have h := Primrec.nat_rec (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂
  apply h.of_eq
  intro a n
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, ih]

end Kourovka.MetabelianEnumeration.ComputableIntegers
