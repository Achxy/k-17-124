/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Covers.FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Collection

Collection identities for the Bieri–Strebel finite presentations.
The local reordering argument retains the literal order of every conjugating
word; commutation is used only at lattice points within the specified budget.
-/

namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection

variable {G : Type*} [Group G]

@[simp] theorem conjugate_one (x : G) : conjugate x 1 = x := by simp [conjugate]

theorem conjugate_mul (x u v : G) :
    conjugate x (u * v) = conjugate (conjugate x u) v := by
  simp [conjugate, mul_assoc]

theorem conjugate_eq_self {x c : G} (h : Commute c x) : conjugate x c = x := by
  rw [conjugate, mul_assoc, ← h.eq, inv_mul_cancel_left]

theorem rightComm_eq_one_iff (x y : G) : rightComm x y = 1 ↔ Commute x y := by
  constructor
  · intro h
    change x * y = y * x
    have hh := congrArg (fun z => y * x * z) h
    simpa [rightComm, mul_assoc] using hh
  · intro h
    change x⁻¹ * y⁻¹ * x * y = 1
    rw [mul_assoc, mul_assoc, h.eq]
    group

theorem conjugate_pow_mul (x t c : G) (n : ℕ)
    (h : ∀ r : ℕ, r ≤ n → Commute c (conjugate x (t ^ r))) :
    conjugate x ((t * c) ^ n) = conjugate x (t ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun r hr => h r (hr.trans (Nat.le_succ n)))
    calc
      conjugate x ((t * c) ^ (n + 1)) =
          conjugate (conjugate x (t ^ n)) (t * c) := by
        rw [pow_succ, conjugate_mul, hn]
      _ = conjugate (conjugate x (t ^ (n + 1))) c := by
        simp only [pow_succ, conjugate_mul]
      _ = conjugate x (t ^ (n + 1)) := conjugate_eq_self (h (n + 1) le_rfl)

theorem conjugate_inv_pow_mul (x t c : G) (n : ℕ)
    (h : ∀ r : ℕ, r ≤ n → Commute c (conjugate x (t⁻¹ ^ r))) :
    conjugate x ((t * c)⁻¹ ^ n) = conjugate x (t⁻¹ ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun r hr => h r (hr.trans (Nat.le_succ n)))
    calc
      conjugate x ((t * c)⁻¹ ^ (n + 1)) =
          conjugate (conjugate x (t⁻¹ ^ n)) (c⁻¹ * t⁻¹) := by
        rw [pow_succ, conjugate_mul, hn, mul_inv_rev]
      _ = conjugate (conjugate x (t⁻¹ ^ n)) t⁻¹ := by
        rw [conjugate_mul, conjugate_eq_self (h n (Nat.le_succ n)).inv_left]
      _ = conjugate x (t⁻¹ ^ (n + 1)) := by rw [pow_succ, conjugate_mul]

theorem conjugate_zpow_mul (x t c : G) (m : ℤ)
    (h : ∀ r : ℤ, |r| ≤ |m| → Commute c (conjugate x (t ^ r))) :
    conjugate x ((t * c) ^ m) = conjugate x (t ^ m) := by
  cases m with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe, zpow_natCast]
    apply conjugate_pow_mul
    intro r hr
    simpa using h (r : ℤ) (by simpa using (show (r : ℤ) ≤ n by exact_mod_cast hr))
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    apply conjugate_inv_pow_mul
    intro r hr
    have hb : |-(r : ℤ)| ≤ |Int.negSucc n| := by
      simpa only [abs_neg, Int.abs_natCast, Int.negSucc_eq, abs_neg] using
        (show (r : ℤ) ≤ n + 1 by exact_mod_cast hr)
    simpa only [zpow_neg, zpow_natCast, inv_pow] using h (-(r : ℤ)) hb

theorem orderedWord_snoc {k : ℕ} (t : Fin (k + 1) → G) (v : Lattice (k + 1)) :
    orderedWord t v = orderedWord (fun i => t i.castSucc) (fun i => v i.castSucc) *
      t (Fin.last k) ^ v (Fin.last k) := by
  simp only [orderedWord, List.ofFn_succ', List.prod_concat]

def raise {k : ℕ} (v : Lattice k) (i : Fin k) : Lattice k :=
  Function.update v i (v i + 1)

@[simp] theorem raise_snoc_castSucc {k : ℕ} (v : Lattice k) (m : ℤ) (i : Fin k) :
    raise (Fin.snoc v m) i.castSucc = Fin.snoc (raise v i) m := by
  simp only [raise, Fin.snoc_castSucc, Fin.snoc_update]

@[simp] theorem raise_snoc_last {k : ℕ} (v : Lattice k) (m : ℤ) :
    raise (Fin.snoc v m) (Fin.last k) = Fin.snoc v (m + 1) := by
  simp only [raise, Fin.snoc_last, Fin.update_snoc_last]

/-- Euclidean balls and the entire lattice are solid in this sense. -/
def Solid {k : ℕ} (B : Set (Lattice k)) : Prop :=
  ∀ v w, w ∈ B → (∀ i, |v i| ≤ |w i|) → v ∈ B

def prefixBudget {k : ℕ} (B : Set (Lattice (k + 1))) : Set (Lattice k) :=
  {v | Fin.snoc v 0 ∈ B}

theorem prefixBudget_solid {k : ℕ} {B : Set (Lattice (k + 1))} (hB : Solid B) :
    Solid (prefixBudget B) := by
  intro v w hw h
  apply hB _ _ hw
  intro i
  cases i using Fin.lastCases <;> simp [h]

theorem prefix_mem {k : ℕ} {B : Set (Lattice (k + 1))} (hB : Solid B)
    {v : Lattice k} {m : ℤ} (hv : Fin.snoc v m ∈ B) : v ∈ prefixBudget B := by
  apply hB _ _ hv
  intro i
  cases i using Fin.lastCases <;> simp

theorem snoc_mem_of_abs_le {k : ℕ} {B : Set (Lattice (k + 1))} (hB : Solid B)
    {v : Lattice k} {m r : ℤ} (hv : Fin.snoc v m ∈ B) (hr : |r| ≤ |m|) :
    Fin.snoc v r ∈ B := by
  apply hB _ _ hv
  intro i
  cases i using Fin.lastCases <;> simp [hr]

/-- Insert one positive generator into an ordered conjugating word. Only
the original and final lattice points and their coordinatewise sub-boxes
are used by the proof. -/
theorem ordered_insert {a : ℕ} (A : Fin a → G) :
    ∀ {k : ℕ} (t : Fin k → G) (designated : Fin k → Fin k → Fin a)
      (B : Set (Lattice k)),
      Solid B →
      (∀ i j, i < j → rightComm (t i) (t j) = A (designated i j)) →
      (∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v))) →
      ∀ p v i, v ∈ B → raise v i ∈ B →
        conjugate (A p) (orderedWord t v * t i) =
          conjugate (A p) (orderedWord t (raise v i)) := by
  intro k
  induction k with
  | zero =>
    intro t designated B hB ht hshort p v i
    exact Fin.elim0 i
  | succ k ih =>
    intro t designated B hB ht hshort p v i hv hvi
    obtain ⟨⟨m, w⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (k + 1) => ℤ)).surjective v
    change Fin.snoc w m ∈ B at hv
    change raise (Fin.snoc w m) i ∈ B at hvi
    change conjugate (A p) (orderedWord t (Fin.snoc w m) * t i) =
      conjugate (A p) (orderedWord t (raise (Fin.snoc w m) i))
    revert hvi
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hvi
      simp only [raise_snoc_last, orderedWord_snoc, Fin.snoc_castSucc, Fin.snoc_last]
      rw [mul_assoc, ← zpow_add_one]
    · intro hvi
      rw [raise_snoc_castSucc] at hvi ⊢
      let t' : Fin k → G := fun j => t j.castSucc
      let d' : Fin k → Fin k → Fin a := fun j l => designated j.castSucc l.castSucc
      have ht' : ∀ j l, j < l → rightComm (t' j) (t' l) = A (d' j l) := by
        intro j l hjl
        exact ht j.castSucc l.castSucc hjl
      have hs' : ∀ b c v, v ∈ prefixBudget B →
          Commute (A b) (conjugate (A c) (orderedWord t' v)) := by
        intro b c v hv
        simpa [orderedWord_snoc, t'] using hshort b c (Fin.snoc v 0) hv
      have hi := ih t' d' (prefixBudget B) (prefixBudget_solid hB) ht' hs' p w i
        (prefix_mem hB hv) (prefix_mem hB hvi)
      let s := t i.castSucc
      let b := t (Fin.last k)
      let c := A (designated i.castSucc (Fin.last k))
      have hc : rightComm s b = c := ht i.castSucc (Fin.last k) i.castSucc_lt_last
      have hbc : b * c⁻¹ = s⁻¹ * b * s := by
        rw [← hc, rightComm]
        group
      have hp : b ^ m * s = s * (b * c⁻¹) ^ m := by
        rw [hbc]
        have hz : (s⁻¹ * b * s) ^ m = s⁻¹ * b ^ m * s := by
          simpa using (conj_zpow (a := s⁻¹) (b := b) (i := m))
        rw [hz]
        group
      have horbit : ∀ r : ℤ, |r| ≤ |m| →
          Commute c⁻¹ (conjugate (conjugate (A p) (orderedWord t' (raise w i))) (b ^ r)) := by
        intro r hr
        have hs := hshort (designated i.castSucc (Fin.last k)) p
          (Fin.snoc (raise w i) r) (snoc_mem_of_abs_le hB hvi hr)
        simpa only [orderedWord_snoc, Fin.snoc_castSucc, Fin.snoc_last,
          conjugate_mul] using hs.inv_left
      simp only [orderedWord_snoc, Fin.snoc_castSucc, Fin.snoc_last]
      change conjugate (A p) ((orderedWord t' w * b ^ m) * s) =
        conjugate (A p) (orderedWord t' (raise w i) * b ^ m)
      rw [mul_assoc, hp, ← mul_assoc, conjugate_mul, hi]
      rw [conjugate_zpow_mul _ b c⁻¹ m horbit, conjugate_mul]

def lower {k : ℕ} (v : Lattice k) (i : Fin k) : Lattice k :=
  Function.update v i (v i - 1)

@[simp] theorem raise_lower {k : ℕ} (v : Lattice k) (i : Fin k) :
    raise (lower v i) i = v := by
  ext j
  by_cases h : j = i
  · subst j; simp [raise, lower]
  · simp [raise, lower, h]

theorem ordered_insert_inv {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a) (B : Set (Lattice k))
    (hB : Solid B)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hshort : ∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v)))
    (p : Fin a) (v : Lattice k) (i : Fin k) (hv : v ∈ B) (hvi : lower v i ∈ B) :
    conjugate (A p) (orderedWord t v * (t i)⁻¹) =
      conjugate (A p) (orderedWord t (lower v i)) := by
  have hi := ordered_insert A t designated B hB ht hshort p (lower v i) i hvi
    (by simpa using hv)
  rw [raise_lower] at hi
  calc
    conjugate (A p) (orderedWord t v * (t i)⁻¹) =
        conjugate (conjugate (A p) (orderedWord t v)) (t i)⁻¹ := conjugate_mul _ _ _
    _ = conjugate (conjugate (A p) (orderedWord t (lower v i) * t i)) (t i)⁻¹ := by
      rw [hi]
    _ = conjugate (A p) (orderedWord t (lower v i)) := by
      rw [← conjugate_mul]
      simp

def OrderedOrbit {a k : ℕ} (A : Fin a → G) (t : Fin k → G) : Set G :=
  {x | ∃ p v, x = conjugate (A p) (orderedWord t v)}

theorem conjugate_closure_mem (S : Set G) (g : G)
    (h : ∀ x ∈ S, conjugate x g ∈ Subgroup.closure S) :
    ∀ x ∈ Subgroup.closure S, conjugate x g ∈ Subgroup.closure S := by
  have hle : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g⁻¹).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    simpa [Subgroup.mem_comap, MulAut.conj_apply, conjugate] using h x hx
  intro x hx
  simpa [Subgroup.mem_comap, MulAut.conj_apply, conjugate] using hle hx

theorem mem_normalizer_of_conjugate {H : Subgroup G} {g : G}
    (hg : ∀ x ∈ H, conjugate x g ∈ H)
    (hi : ∀ x ∈ H, conjugate x g⁻¹ ∈ H) : g ∈ H.normalizer := by
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  constructor
  · exact hg x
  · intro hx
    have hh := hi (conjugate x g) hx
    simpa [conjugate, mul_assoc] using hh

/-- Infinite-radius collection: ordered commutation at every lattice
point suffices to make the full normal closure of the A-generators abelian. -/
theorem normalClosure_abelian {a k : ℕ} (A : Fin a → G) (t : Fin k → G)
    (designated : Fin k → Fin k → Fin a)
    (ht : ∀ i j, i < j → rightComm (t i) (t j) = A (designated i j))
    (hshort : ∀ p q v, Commute (A p) (conjugate (A q) (orderedWord t v)))
    (hgen : Subgroup.closure (Set.range t ∪ Set.range A) = ⊤) :
    ∀ x ∈ Subgroup.normalClosure (Set.range A),
      ∀ y ∈ Subgroup.normalClosure (Set.range A), Commute x y := by
  let S := OrderedOrbit A t
  let H := Subgroup.closure S
  have hsolid : Solid (Set.univ : Set (Lattice k)) := fun _ _ _ _ => trivial
  have hs : ∀ p q v, v ∈ (Set.univ : Set (Lattice k)) →
      Commute (A p) (conjugate (A q) (orderedWord t v)) := fun p q v _ => hshort p q v
  have hT : ∀ i, t i ∈ H.normalizer := by
    intro i
    apply mem_normalizer_of_conjugate
    · apply conjugate_closure_mem
      rintro x ⟨p, v, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨p, raise v i, ?_⟩
      rw [← conjugate_mul]
      exact ordered_insert A t designated Set.univ hsolid ht hs p v i trivial trivial
    · apply conjugate_closure_mem
      rintro x ⟨p, v, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨p, lower v i, ?_⟩
      rw [← conjugate_mul]
      exact ordered_insert_inv A t designated Set.univ hsolid ht hs p v i trivial trivial
  have hAN : ∀ p, A p ∈ H.normalizer := by
    intro p
    apply mem_normalizer_of_conjugate
    · apply conjugate_closure_mem
      rintro x ⟨q, v, rfl⟩
      rw [conjugate_eq_self (hshort p q v)]
      exact Subgroup.subset_closure ⟨q, v, rfl⟩
    · apply conjugate_closure_mem
      rintro x ⟨q, v, rfl⟩
      rw [conjugate_eq_self (hshort p q v).inv_left]
      exact Subgroup.subset_closure ⟨q, v, rfl⟩
  have hn : H.normalizer = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply (Subgroup.closure_le _).mpr
    rintro x (⟨i, rfl⟩ | ⟨p, rfl⟩)
    · exact hT i
    · exact hAN p
  letI : H.Normal := Subgroup.normalizer_eq_top_iff.mp hn
  have hA : Set.range A ⊆ H := by
    rintro x ⟨p, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨p, 0, ?_⟩
    simp [orderedWord]
  have hNH : Subgroup.normalClosure (Set.range A) ≤ H :=
    Subgroup.normalClosure_le_normal hA
  have hHC : H ≤ Subgroup.centralizer (Set.range A) := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨q, v, rfl⟩ p ⟨p, rfl⟩
    exact (hshort p q v).eq
  have hAC : Set.range A ⊆ Subgroup.centralizer (H : Set G) := by
    rintro x ⟨p, rfl⟩ y hy
    exact (hHC hy (A p) ⟨p, rfl⟩).symm
  have hNC : Subgroup.normalClosure (Set.range A) ≤ Subgroup.centralizer (H : Set G) :=
    Subgroup.normalClosure_le_normal hAC
  intro x hx y hy
  exact (hNC hx y (hNH hy)).symm

end Kourovka.MetabelianEnumeration.FiniteCover.Collection
