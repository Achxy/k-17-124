/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Covers.ComputableCoverData

/-!
# Computable Lattice Ball

Primitive recursive enumeration of finite integer lattice balls.
-/

namespace Kourovka.MetabelianEnumeration.ComputableLatticeBall

open ComputableIntegers ComputableCoverData

def interval (R : ℕ) : List ℤ :=
  (List.range (2 * R + 1)).map fun (i : ℕ) => (i : ℤ) - R

theorem mem_interval (R : ℕ) (z : ℤ) : z ∈ interval R ↔ |z| ≤ (R : ℤ) := by
  simp only [interval, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    apply abs_le.mpr
    constructor <;> omega
  · intro hz
    obtain ⟨hz₁, hz₂⟩ := abs_le.mp hz
    refine ⟨(z + R).toNat, ?_, ?_⟩ <;> omega

def cube (R : ℕ) : ℕ → List (List ℤ)
  | 0 => [[]]
  | k + 1 => (interval R).flatMap fun z => (cube R k).map fun v => z :: v

theorem mem_cube (R k : ℕ) (v : List ℤ) : v ∈ cube R k ↔
    ∃ w : Fin k → ℤ, List.ofFn w = v ∧ ∀ i, |w i| ≤ (R : ℤ) := by
  induction k generalizing v with
  | zero =>
    constructor
    · intro h
      have hv : v = [] := by simpa [cube] using h
      subst v
      exact ⟨Fin.elim0, by simp, fun i => Fin.elim0 i⟩
    · rintro ⟨w, rfl, _⟩
      simp [cube]
  | succ k ih =>
    constructor
    · intro hv
      obtain ⟨z, hz, hmap⟩ := List.mem_flatMap.mp hv
      obtain ⟨tail, hmem, rfl⟩ := List.mem_map.mp hmap
      obtain ⟨w, hw, hbound⟩ := (ih tail).mp hmem
      refine ⟨Fin.cons z w, ?_, ?_⟩
      · simp [List.ofFn_succ, hw]
      · intro i
        cases i using Fin.cases with
        | zero => simpa using (mem_interval R z).mp hz
        | succ i => simpa using hbound i
    · rintro ⟨w, rfl, hbound⟩
      rw [List.ofFn_succ]
      apply List.mem_flatMap.mpr
      refine ⟨w 0, (mem_interval R _).mpr (hbound 0), List.mem_map.mpr ?_⟩
      refine ⟨List.ofFn (fun i => w i.succ), (ih _).mpr ⟨fun i => w i.succ, rfl, ?_⟩, rfl⟩
      exact fun i => hbound i.succ

def normSq (v : List ℤ) : ℕ := (v.map fun z => z.natAbs ^ 2).sum

theorem normSq_ofFn {k : ℕ} (v : Fin k → ℤ) :
    (normSq (List.ofFn v) : ℤ) = ∑ i, v i ^ 2 := by
  simp [normSq, List.map_ofFn, List.sum_ofFn, sq_abs]

def ball (k R : ℕ) : List (List ℤ) :=
  (cube R k).filter fun v => normSq v < R ^ 2

theorem mem_ball (k R : ℕ) (v : List ℤ) : v ∈ ball k R ↔
    ∃ w : Fin k → ℤ, List.ofFn w = v ∧ (∑ i, w i ^ 2) < (R : ℤ) ^ 2 := by
  rw [ball, List.mem_filter]
  constructor
  · rintro ⟨hv, hnorm⟩
    obtain ⟨w, rfl, _⟩ := (mem_cube R k v).mp hv
    refine ⟨w, rfl, ?_⟩
    have h := of_decide_eq_true hnorm
    have h' : (normSq (List.ofFn w) : ℤ) < (R : ℤ) ^ 2 := by exact_mod_cast h
    simpa only [normSq_ofFn] using h'
  · rintro ⟨w, rfl, hnorm⟩
    refine ⟨(mem_cube R k _).mpr ⟨w, rfl, ?_⟩, ?_⟩
    · intro i
      have hi : w i ^ 2 ≤ ∑ j, w j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)
      have hR : (0 : ℤ) ≤ R := Int.natCast_nonneg R
      apply abs_le.mpr
      constructor <;> nlinarith
    · apply decide_eq_true
      have h' : (normSq (List.ofFn w) : ℤ) < (R : ℤ) ^ 2 := by rwa [normSq_ofFn]
      exact_mod_cast h'

theorem mem_ball_ofFn {k R : ℕ} (v : Fin k → ℤ) :
    List.ofFn v ∈ ball k R ↔ (∑ i, v i ^ 2) < (R : ℤ) ^ 2 := by
  rw [mem_ball]
  constructor
  · rintro ⟨w, hw, h⟩
    have he := List.ofFn_injective hw
    simpa only [he] using h
  · intro h
    exact ⟨v, rfl, h⟩

theorem interval_primrec : Primrec interval := by
  have hf : Primrec (fun p : ℕ × ℕ => (p.2 : ℤ) - (p.1 : ℤ)) :=
    ComputableIntegers.sub_primrec.comp (ofNat_primrec.comp Primrec.snd)
      (ofNat_primrec.comp Primrec.fst)
  exact Primrec.list_map (Primrec.list_range.comp
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))) hf.to₂

theorem cube_primrec : Primrec₂ cube := by
  have hstep : Primrec (fun p : ℕ × (ℕ × List (List ℤ)) =>
      (interval p.1).flatMap fun z => p.2.2.map fun v => z :: v) :=
    Primrec.list_flatMap (interval_primrec.comp Primrec.fst)
      (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  have h := Primrec.nat_rec (Primrec.const [[]]) hstep.to₂
  apply h.of_eq
  intro R k
  induction k with
  | zero => rfl
  | succ k ih => simp only [cube, ih]

theorem normSq_primrec : Primrec normSq :=
  nat_sum_primrec.comp (Primrec.list_map Primrec.id
    (nat_pow_primrec.comp (natAbs_primrec.comp Primrec.snd) (Primrec.const 2)).to₂)

theorem ball_primrec : Primrec₂ ball := by
  have hp : PrimrecRel (fun v : List ℤ => fun R : ℕ => normSq v < R ^ 2) :=
    Primrec.nat_lt.comp (normSq_primrec.comp Primrec.fst)
      (nat_pow_primrec.comp Primrec.snd (Primrec.const 2))
  exact hp.listFilter.comp (cube_primrec.comp Primrec.snd Primrec.fst) Primrec.snd

end Kourovka.MetabelianEnumeration.ComputableLatticeBall
