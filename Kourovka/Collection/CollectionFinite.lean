/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Collection.Collection

/-!
# Collection Finite

Finite-budget collection. A block may be traversed whenever both
endpoints belong to a coordinatewise solid lattice set.
-/

namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection

variable {G : Type*} [Group G]

def shift {k : ℕ} (v : Lattice k) (i : Fin k) (m : ℤ) : Lattice k :=
  Function.update v i (v i + m)

@[simp] theorem shift_zero {k : ℕ} (v : Lattice k) (i : Fin k) : shift v i 0 = v := by
  simp [shift]

@[simp] theorem raise_shift {k : ℕ} (v : Lattice k) (i : Fin k) (m : ℤ) :
    raise (shift v i m) i = shift v i (m + 1) := by
  simp [raise, shift, add_assoc]

@[simp] theorem lower_shift {k : ℕ} (v : Lattice k) (i : Fin k) (m : ℤ) :
    lower (shift v i m) i = shift v i (m - 1) := by
  simp [lower, shift, sub_eq_add_neg, add_assoc]

theorem shift_mem_interval {k : ℕ} {B : Set (Lattice k)} (hB : Solid B)
    (v : Lattice k) (i : Fin k) (m r : ℤ) (hv : v ∈ B) (hm : shift v i m ∈ B)
    (hr : min 0 m ≤ r) (hr' : r ≤ max 0 m) : shift v i r ∈ B := by
  have habs : |v i + r| ≤ max |v i| |v i + m| := by
    apply abs_le.mpr
    have h0 := le_max_left |v i| |v i + m|
    have h1 := le_max_right |v i| |v i + m|
    have h2 := le_abs_self (v i)
    have h3 := neg_abs_le (v i)
    have h4 := le_abs_self (v i + m)
    have h5 := neg_abs_le (v i + m)
    by_cases h : 0 ≤ m
    · simp only [min_eq_left h, max_eq_right h] at hr hr'
      constructor <;> omega
    · have h : m ≤ 0 := by omega
      simp only [min_eq_right h, max_eq_left h] at hr hr'
      constructor <;> omega
  by_cases h : |v i + m| ≤ |v i|
  · apply hB _ _ hv
    intro j
    by_cases hj : j = i
    · subst j
      simpa [shift, max_eq_left h] using habs
    · simp [shift, hj]
  · have h : |v i| ≤ |v i + m| := by omega
    apply hB _ _ hm
    intro j
    by_cases hj : j = i
    · subst j
      simpa [shift, max_eq_right h] using habs
    · simp [shift, hj]

section Blocks

variable {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
  (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
  (hB : Solid B)
  (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
  (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))

include hB ht hs

theorem ordered_append_pow (p : Fin a) (v : Lattice k) (i : Fin k) (n : ℕ)
    (h : ∀ r : ℕ, r ≤ n → shift v i r ∈ B) :
    conjugate (A p) (orderedWord t v * t i ^ n) =
      conjugate (A p) (orderedWord t (shift v i n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun r hr => h r (hr.trans (Nat.le_succ n)))
    calc
      conjugate (A p) (orderedWord t v * t i ^ (n + 1)) =
          conjugate (conjugate (A p) (orderedWord t v * t i ^ n)) (t i) := by
        rw [pow_succ, ← mul_assoc, conjugate_mul]
      _ = conjugate (A p) (orderedWord t (shift v i n) * t i) := by
        rw [hn, conjugate_mul]
      _ = conjugate (A p) (orderedWord t (shift v i (n + 1 : ℕ))) := by
        have hi := ordered_insert A t designated B hB ht hs p (shift v i n) i
          (h n (Nat.le_succ n)) (by simpa using h (n + 1) le_rfl)
        simpa using hi

theorem ordered_append_inv_pow (p : Fin a) (v : Lattice k) (i : Fin k) (n : ℕ)
    (h : ∀ r : ℕ, r ≤ n → shift v i (-(r : ℤ)) ∈ B) :
    conjugate (A p) (orderedWord t v * (t i)⁻¹ ^ n) =
      conjugate (A p) (orderedWord t (shift v i (-(n : ℤ)))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun r hr => h r (hr.trans (Nat.le_succ n)))
    calc
      conjugate (A p) (orderedWord t v * (t i)⁻¹ ^ (n + 1)) =
          conjugate (conjugate (A p) (orderedWord t v * (t i)⁻¹ ^ n)) (t i)⁻¹ := by
        rw [pow_succ, ← mul_assoc, conjugate_mul]
      _ = conjugate (A p) (orderedWord t (shift v i (-(n : ℤ))) * (t i)⁻¹) := by
        rw [hn, conjugate_mul]
      _ = conjugate (A p) (orderedWord t (shift v i (-((n + 1 : ℕ) : ℤ)))) := by
        have hi := ordered_insert_inv A t designated B hB ht hs p (shift v i (-(n : ℤ))) i
          (h n (Nat.le_succ n)) (by simpa [sub_eq_add_neg, neg_add, add_comm] using h (n + 1) le_rfl)
        simpa [sub_eq_add_neg, neg_add, add_comm] using hi

/-- Arbitrarily long positive or negative powers can be inserted if the
two endpoints remain within the budget. -/
theorem ordered_append_zpow (p : Fin a) (v : Lattice k) (i : Fin k) (m : ℤ)
    (hv : v ∈ B) (hm : shift v i m ∈ B) :
    conjugate (A p) (orderedWord t v * t i ^ m) =
      conjugate (A p) (orderedWord t (shift v i m)) := by
  cases m with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, zpow_natCast]
    apply ordered_append_pow A t designated B hB ht hs
    intro r hr
    apply shift_mem_interval hB v i (n : ℤ) r hv hm
    · simp
    · simpa using (show (r : ℤ) ≤ n by exact_mod_cast hr)
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    apply ordered_append_inv_pow A t designated B hB ht hs
    intro r hr
    have hm' : shift v i (-((n + 1 : ℕ) : ℤ)) ∈ B := by simpa [Int.negSucc_eq] using hm
    apply shift_mem_interval hB v i (-((n + 1 : ℕ) : ℤ)) (-(r : ℤ)) hv hm'
    · have hr' : (r : ℤ) ≤ n + 1 := by exact_mod_cast hr
      simp only [Nat.cast_add, Nat.cast_one]
      omega
    · simp

end Blocks

def blockWord {k : ℕ} (t : Fin k → G) (w : Lattice k) (l : List (Fin k)) : G :=
  (l.map fun i => t i ^ w i).prod

def shiftList {k : ℕ} (v w : Lattice k) (l : List (Fin k)) : Lattice k :=
  fun i => v i + if i ∈ l then w i else 0

@[simp] theorem shiftList_nil {k : ℕ} (v w : Lattice k) : shiftList v w [] = v := by
  ext i; simp [shiftList]

theorem shiftList_cons {k : ℕ} (v w : Lattice k) (i : Fin k) (l : List (Fin k))
    (hi : i ∉ l) : shiftList (shift v i (w i)) w l = shiftList v w (i :: l) := by
  ext j
  by_cases hj : j = i
  · subst j; simp [shiftList, shift, hi]
  · simp [shiftList, shift, hj]

@[simp] theorem blockWord_finRange {k : ℕ} (t : Fin k → G) (w : Lattice k) :
    blockWord t w (List.finRange k) = orderedWord t w := by
  simp [blockWord, orderedWord, List.ofFn_eq_map]

@[simp] theorem shiftList_finRange {k : ℕ} (v w : Lattice k) :
    shiftList v w (List.finRange k) = v + w := by
  ext i; simp [shiftList]

/-- Collect any semi-ordered block sequence whose entire coordinate box
lies in the budget. The block order is arbitrary. -/
theorem collect_blocks {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p : Fin a) (v w : Lattice k) (l : List (Fin k)) (hl : l.Nodup)
    (d : Lattice k) (hd : d ∈ B)
    (hv : ∀ i, |v i| ≤ |d i|) (hend : ∀ i, |shiftList v w l i| ≤ |d i|) :
    conjugate (A p) (orderedWord t v * blockWord t w l) =
      conjugate (A p) (orderedWord t (shiftList v w l)) := by
  induction l generalizing v with
  | nil => simp [blockWord]
  | cons i l ih =>
    have hi : i ∉ l := (List.nodup_cons.mp hl).1
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    have hmid : ∀ j, |shift v i (w i) j| ≤ |d j| := by
      intro j
      by_cases hj : j = i
      · subst j
        simpa [shift, shiftList] using hend i
      · simpa [shift, hj] using hv j
    have hstartB := hB v d hd hv
    have hmidB := hB (shift v i (w i)) d hd hmid
    have htail := ih (shift v i (w i)) hl' hmid (by simpa [shiftList_cons v w i l hi] using hend)
    calc
      conjugate (A p) (orderedWord t v * blockWord t w (i :: l)) =
          conjugate (conjugate (A p) (orderedWord t v * t i ^ w i)) (blockWord t w l) := by
        simp only [blockWord, List.map_cons, List.prod_cons]
        rw [← mul_assoc, conjugate_mul]
      _ = conjugate (conjugate (A p) (orderedWord t (shift v i (w i)))) (blockWord t w l) := by
        rw [ordered_append_zpow A t designated B hB ht hs p v i (w i) hstartB hmidB]
      _ = conjugate (A p) (orderedWord t (shiftList (shift v i (w i)) w l)) := by
        rw [← conjugate_mul]
        exact htail
      _ = conjugate (A p) (orderedWord t (shiftList v w (i :: l))) := by
        rw [shiftList_cons v w i l hi]

theorem collect_ordered_box {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p : Fin a) (v w d : Lattice k) (hd : d ∈ B)
    (hv : ∀ i, |v i| ≤ |d i|) (hend : ∀ i, |v i + w i| ≤ |d i|) :
    conjugate (A p) (orderedWord t v * orderedWord t w) =
      conjugate (A p) (orderedWord t (v + w)) := by
  simpa using collect_blocks A t designated B hB ht hs p v w (List.finRange k)
    (List.nodup_finRange k) d hd hv (by simpa using hend)

@[simp] theorem orderedWord_zero {k : ℕ} (t : Fin k → G) : orderedWord t (0 : Lattice k) = 1 := by
  simp [orderedWord]

theorem blockWord_inverse {k : ℕ} (t : Fin k → G) (w : Lattice k) (l : List (Fin k)) :
    (blockWord t w l)⁻¹ = blockWord t (-w) l.reverse := by
  simp [blockWord, List.prod_inv_reverse, List.map_reverse, List.map_map, Function.comp_def]

theorem collect_ordered_inverse_box {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p : Fin a) (v w d : Lattice k) (hd : d ∈ B)
    (hv : ∀ i, |v i| ≤ |d i|) (hend : ∀ i, |v i - w i| ≤ |d i|) :
    conjugate (A p) (orderedWord t v * (orderedWord t w)⁻¹) =
      conjugate (A p) (orderedWord t (v - w)) := by
  have he : shiftList v (-w) (List.finRange k).reverse = v - w := by
    ext i
    simp [shiftList, sub_eq_add_neg]
  have hw : blockWord t (-w) (List.finRange k).reverse = (orderedWord t w)⁻¹ := by
    rw [← blockWord_inverse, blockWord_finRange]
  have h := collect_blocks A t designated B hB ht hs p v (-w) (List.finRange k).reverse
    (by simpa using List.nodup_finRange k) d hd hv (by simpa [he] using hend)
  simpa [he, hw] using h

theorem commute_conjugate_iff (a b w : G) :
    Commute a (conjugate b w) ↔ Commute (conjugate a w⁻¹) b := by
  constructor
  · intro h
    simpa [conjugate, MulAut.conj_apply, mul_assoc] using h.map (MulAut.conj w).toMonoidHom
  · intro h
    simpa [conjugate, MulAut.conj_apply, mul_assoc] using h.map (MulAut.conj w⁻¹).toMonoidHom

/-- Collection inside a commutator when both exponent vectors and their
sum lie within the budget. The proof moves shrinking coordinates first. -/
theorem collection_three_points {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hs : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p q : Fin a) (x y : Lattice k) (hx : x ∈ B) (hy : y ∈ B) (hxy : x + y ∈ B) :
    Commute (A p) (conjugate (A q) (orderedWord t x * orderedWord t y)) := by
  let c : Lattice k := fun i => if |x i + y i| ≤ |x i| then y i else 0
  let d := y - c
  have hcd : c + d = y := by dsimp [d]; abel
  have hcabs : ∀ i, |c i| ≤ |y i| := by
    intro i; dsimp [c]; split <;> simp
  have hdabs : ∀ i, |d i| ≤ |y i| := by
    intro i; dsimp [d, c]; split <;> simp
  have hxc : ∀ i, |x i + c i| ≤ |x i| := by
    intro i; dsimp [c]; split <;> rename_i h <;> simp [h]
  have hxcend : ∀ i, |x i + c i| ≤ |x i + y i| := by
    intro i; dsimp [c]; split <;> simp
    omega
  have hsum : x + c + d = x + y := by rw [add_assoc, hcd]
  have hneg : -d - c = -y := by rw [sub_eq_add_neg, ← neg_add, add_comm d c, hcd]
  have hfirst := collect_ordered_box A t designated B hB ht hs q x c x hx (fun _ => le_rfl) hxc
  have hsecond := collect_ordered_box A t designated B hB ht hs q (x + c) d (x + y) hxy
    hxcend (by intro i; simpa only [← Pi.add_apply, hsum] using (le_refl |(x + y) i|))
  have hcollect : conjugate (A q) (orderedWord t x * (orderedWord t c * orderedWord t d)) =
      conjugate (A q) (orderedWord t (x + y)) := by
    rw [← mul_assoc, conjugate_mul, hfirst, ← conjugate_mul, hsecond, hsum]
  have hay := collect_ordered_inverse_box A t designated B hB ht hs p 0 y y hy
    (by intro i; simp) (by intro i; simp)
  have had := collect_ordered_inverse_box A t designated B hB ht hs p 0 d y hy
    (by intro i; simp) (by simpa using hdabs)
  have hac := collect_ordered_inverse_box A t designated B hB ht hs p (-d) c y hy
    (by simpa using hdabs) (by
      intro i
      change |(-d - c) i| ≤ |y i|
      rw [hneg]
      simp)
  simp only [orderedWord_zero, one_mul, zero_sub] at hay had
  have haw : conjugate (A p) (orderedWord t c * orderedWord t d)⁻¹ =
      conjugate (A p) (orderedWord t (-y)) := by
    rw [mul_inv_rev, conjugate_mul, had, ← conjugate_mul, hac, hneg]
  have hcomm := hs p q (x + y) hxy
  rw [← hcollect, conjugate_mul] at hcomm
  have hpair := (commute_conjugate_iff (A p) (conjugate (A q) (orderedWord t x))
    (orderedWord t c * orderedWord t d)).mp hcomm
  rw [haw, ← hay] at hpair
  rw [conjugate_mul]
  exact (commute_conjugate_iff _ _ _).mpr hpair

end Kourovka.MetabelianEnumeration.FiniteCover.Collection
