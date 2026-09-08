/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Polyhedral.ComputableCone
import Kourovka.Covers.CertifiedCover

/-!
# Computable Cover Data

Uniform natural/list encoding of finite cover data and its explicit
integer radius. Both dimensions are encoded one below their positive value.
-/

namespace Kourovka.MetabelianEnumeration.ComputableCoverData

open ComputableIntegers FiniteCover

abbrev PolynomialCode := Bool × List (List ℤ × ℤ)
abbrev DatumCode := (ℕ × ℕ) × (List (List ℕ) × List PolynomialCode)

def dimension (data : DatumCode) : ℕ := data.1.1 + 1

def alphabet (data : DatumCode) : ℕ := data.1.2 + 1

def decodePolynomial (k : ℕ) (p : PolynomialCode) : FiniteCover.Polynomial k :=
  (p.1, p.2.map fun term => ((fun i : Fin k => term.1.getD i 0), term.2))

def decode (data : DatumCode) : FiniteCover.Datum (dimension data) (alphabet data) where
  designated i j := ⟨((data.2.1.getD i []).getD j 0) % alphabet data, Nat.mod_lt _ (Nat.succ_pos _)⟩
  polynomials := data.2.2.map (decodePolynomial (dimension data))

def encode {k a : ℕ} (data : FiniteCover.Datum (k + 1) (a + 1)) : DatumCode :=
  ((k, a), ((List.ofFn fun i => List.ofFn fun j => (data.designated i j).val),
    data.polynomials.map fun p => (p.1, p.2.map fun term => (List.ofFn term.1, term.2))))

theorem getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) (i : Fin n) :
    (List.ofFn f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD]

theorem decode_encode {k a : ℕ} (data : FiniteCover.Datum (k + 1) (a + 1)) :
    decode (encode data) = data := by
  cases data with
  | mk designated polynomials =>
    apply congrArg₂ FiniteCover.Datum.mk
    · funext i j
      apply Fin.ext
      change ((List.ofFn fun i => List.ofFn fun j => (designated i j).val).getD i []).getD j 0 %
        (a + 1) = (designated i j).val
      rw [getD_ofFn, getD_ofFn, Nat.mod_eq_of_lt (designated i j).isLt]
    · simp only [encode, dimension, decodePolynomial, List.map_map, Function.comp_def]
      have ht : ∀ term : FiniteCover.Lattice (k + 1) × ℤ,
          ((fun i : Fin (k + 1) => (List.ofFn term.1).getD i 0), term.2) = term := by
        intro term
        apply Prod.ext
        · ext i; exact getD_ofFn term.1 0 i
        · rfl
      simp only [ht]
      change List.map (fun p => (p.1, List.map id p.2)) polynomials = polynomials
      simp only [List.map_id]
      change List.map id polynomials = polynomials
      exact List.map_id _

def supports (data : DatumCode) : ComputableCone.SupportsCode :=
  data.2.2.map fun p => p.2.map Prod.fst

theorem decode_supports (data : DatumCode) :
    ComputableCone.decodeSupports (dimension data) (supports data) =
      (decode data).polynomials.map TamenessCompactness.polynomialSupport := by
  simp only [ComputableCone.decodeSupports, supports, decode,
    TamenessCompactness.polynomialSupport, decodePolynomial, List.map_map, Function.comp_def]
  rfl

def vectorLength (k : ℕ) (v : List ℤ) : ℕ :=
  ((List.range k).map fun i => (v.getD i 0).natAbs).sum

def lengthBound (data : DatumCode) : ℕ :=
  1 + (data.2.2.flatMap fun p => p.2.map fun term => vectorLength (dimension data) term.1).sum

theorem vectorLength_eq (k : ℕ) (v : List ℤ) :
    (vectorLength k v : ℚ) = supportLength (fun i : Fin k => v.getD i 0) := by
  rw [vectorLength, ← List.map_coe_finRange k]
  simp only [List.map_map, Function.comp_def, Nat.cast_list_sum, List.map_map, supportLength]
  simp [← List.ofFn_eq_map, List.sum_ofFn]

theorem lengthBound_eq (data : DatumCode) :
    (lengthBound data : ℚ) = supportBound (decode data) := by
  simp only [lengthBound, supportBound, supportLengths, decode, decodePolynomial,
    Nat.cast_add, Nat.cast_one, Nat.cast_list_sum, List.map_flatMap, List.map_map,
    List.flatMap_map, Function.comp_def, vectorLength_eq]

def radius (data : DatumCode) (r : ℕ) : ℕ :=
  1 + 2 * dimension data * (1 + lengthBound data +
    lengthBound data ^ 2 * dimension data * 2 ^ r)

theorem marginConstant_eq {k : ℕ} (hk : 1 ≤ k) (r : ℕ) :
    marginConstant k r = (1 / 2 : ℚ) ^ r / k := by
  have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℚ) < k := by linarith
  apply min_eq_left
  apply (div_le_one hk0).mpr
  exact (pow_le_one₀ (by norm_num) (by norm_num) : (1 / 2 : ℚ) ^ r ≤ 1).trans hk1

theorem coneRadius_formula {k a : ℕ} (data : FiniteCover.Datum k a) (hk : 1 ≤ k)
    (r D : ℕ) (hD : supportBound data = (D : ℚ)) :
    coneRadius data r = 1 + 2 * k * (1 + D + D ^ 2 * k * 2 ^ r) := by
  rw [coneRadius, certifiedRadius, marginConstant_eq hk r, hD]
  have he : 2 * (k : ℚ) * (1 + D + (D : ℚ) ^ 2 / ((1 / 2 : ℚ) ^ r / k)) =
      ((2 * k * (1 + D + D ^ 2 * k * 2 ^ r) : ℕ) : ℚ) := by
    push_cast
    simp only [div_eq_mul_inv, one_mul, mul_inv_rev, inv_pow, inv_inv]
    ring
  rw [he, Nat.ceil_natCast]

theorem radius_eq (data : DatumCode) (r : ℕ) : radius data r = coneRadius (decode data) r := by
  rw [coneRadius_formula (decode data) (by simp [dimension]) r (lengthBound data) (lengthBound_eq data).symm]
  rfl

theorem dimension_primrec : Primrec dimension :=
  Primrec.succ.comp (Primrec.fst.comp Primrec.fst)

theorem alphabet_primrec : Primrec alphabet :=
  Primrec.succ.comp (Primrec.snd.comp Primrec.fst)

theorem supports_primrec : Primrec supports :=
  Primrec.list_map (Primrec.snd.comp Primrec.snd)
    (Primrec.list_map (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd).to₂).to₂

theorem nat_sum_primrec : Primrec (List.sum : List ℕ → ℕ) :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    (fun l => by induction l <;> simp_all)

theorem vectorLength_primrec : Primrec₂ vectorLength :=
  nat_sum_primrec.comp (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (natAbs_primrec.comp ((Primrec.list_getD 0).comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂)

theorem lengthBound_primrec : Primrec lengthBound :=
  Primrec.nat_add.comp (Primrec.const 1) (nat_sum_primrec.comp
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      (Primrec.list_map (Primrec.snd.comp Primrec.snd)
        (vectorLength_primrec.comp (dimension_primrec.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)).to₂).to₂))

theorem radius_primrec : Primrec₂ radius :=
  Primrec.nat_add.comp (Primrec.const 1) (Primrec.nat_mul.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (dimension_primrec.comp Primrec.fst))
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 1) (lengthBound_primrec.comp Primrec.fst))
      (Primrec.nat_mul.comp
        (Primrec.nat_mul.comp
          (nat_pow_primrec.comp (lengthBound_primrec.comp Primrec.fst) (Primrec.const 2))
          (dimension_primrec.comp Primrec.fst))
        (nat_pow_primrec.comp (Primrec.const 2) Primrec.snd))))

def check (data : DatumCode) (r : ℕ) : Bool :=
  ComputableCone.checkMargin (dimension data, r) (supports data)

theorem check_primrec : Primrec₂ check :=
  ComputableCone.checkMargin_primrec.comp ((dimension_primrec.comp Primrec.fst).pair Primrec.snd)
    (supports_primrec.comp Primrec.fst)

theorem check_sound (data : DatumCode) (r : ℕ) (h : check data r = true) :
    Metabelian (FiniteCover.GroupOf (decode data) (radius data r)) := by
  rw [radius_eq]
  apply checked_cover_metabelian (decode data) (by simp [dimension]) r
  simpa only [check, ComputableCone.checkMargin_eq, decode_supports] using h

end Kourovka.MetabelianEnumeration.ComputableCoverData
