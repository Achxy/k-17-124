/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Polyhedral.ComputableFourierMotzkin
import Kourovka.Polyhedral.ConeVerifier

/-!
# Computable Cone

Natural/list computation of the dyadic cone-margin test, uniformly in
the dimension. Scaling by 2^r keeps the elimination arithmetic integral.
-/

namespace Kourovka.MetabelianEnumeration.ComputableCone

open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

abbrev VectorCode := List ℤ
abbrev SupportsCode := List (List VectorCode)

def decodeVector (n : ℕ) (v : VectorCode) : ConeVerifier.Vec n :=
  fun i => (v.getD i 0 : ℚ)

def decodeSupports (n : ℕ) (supports : SupportsCode) : ConeVerifier.Supports n :=
  supports.map fun s => s.map (decodeVector n)

def supportRow (r : ℕ) (v : VectorCode) : RowCode :=
  (v.map fun z => (2 ^ r : ℤ) * z, -1)

def coordinate (n i : ℕ) (a b : ℤ) : RowCode :=
  ((List.range n).map fun j => if j = i then a else 0, b)

def cubeRows (n : ℕ) : List RowCode :=
  (List.range n).flatMap fun i => [coordinate n i 1 (-1), coordinate n i (-1) (-1)]

def faceRows (n i : ℕ) (sign : ℤ) : List RowCode :=
  [coordinate n i 1 (-sign), coordinate n i (-1) sign] ++ cubeRows n

def choices (r : ℕ) : SupportsCode → List (List RowCode)
  | [] => [[]]
  | support :: rest => support.flatMap fun u => (choices r rest).map fun rows => supportRow r u :: rows

def badDirection (nr : ℕ × ℕ) (supports : SupportsCode) : Bool :=
  (List.range nr.1).any fun i => ([-1, 1] : List ℤ).any fun sign =>
    (choices nr.2 supports).any fun rows =>
      ComputableFourierMotzkin.check nr.1 (rows ++ faceRows nr.1 i sign)

def checkMargin (nr : ℕ × ℕ) (supports : SupportsCode) : Bool := !badDirection nr supports

theorem supportRow_coeff (n r : ℕ) (v : VectorCode) (i : Fin n) :
    (decodeRow n (supportRow r v)).coeff i = (2 ^ r : ℚ) * decodeVector n v i := by
  change (((v.map fun z => (2 ^ r : ℤ) * z).getD i 0 : ℤ) : ℚ) = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hv : v[(i : ℕ)]? <;> simp [hv, decodeVector, List.getD_eq_getElem?_getD]

theorem supportRow_iff (n r : ℕ) (v : VectorCode) (x : Fin n → ℝ) :
    (decodeRow n (supportRow r v)).eval x ≤ 0 ↔
      ConeVerifier.dot (decodeVector n v) x ≤ (1 / 2 : ℝ) ^ r := by
  have he : (decodeRow n (supportRow r v)).eval x =
      (2 ^ r : ℝ) * ConeVerifier.dot (decodeVector n v) x - 1 := by
    simp only [FourierMotzkin.Row.eval, supportRow_coeff, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
    simp only [decodeRow, supportRow, Int.cast_neg, Int.cast_one]
    simp only [ConeVerifier.dot, Finset.mul_sum, mul_assoc]
    ring
  rw [he]
  have hp : (0 : ℝ) < 2 ^ r := by positivity
  rw [one_div_pow]
  constructor
  · intro h
    apply (le_div_iff₀ hp).mpr
    nlinarith
  · intro h
    have h' := (le_div_iff₀ hp).mp h
    nlinarith

theorem decode_coordinate (n : ℕ) (i : Fin n) (a b : ℤ) :
    decodeRow n (coordinate n i a b) = ConeVerifier.coordinate i (a : ℚ) (b : ℚ) := by
  apply congrArg₂ (FourierMotzkin.Row.mk (n := n))
  · ext j
    simp [coordinate, ComputableFourierMotzkin.coeff,
      List.getD_eq_getElem?_getD, j.isLt, Fin.ext_iff]
  · rfl

theorem decode_cubeRows (n : ℕ) :
    (cubeRows n).map (decodeRow n) = ConeVerifier.cubeRows n := by
  rw [cubeRows, ← List.map_coe_finRange n]
  simp only [List.flatMap_map, List.map_flatMap, List.map_cons, List.map_nil,
    decode_coordinate, Int.cast_one, Int.cast_neg]
  rfl

theorem decode_faceRows (n : ℕ) (i : Fin n) (sign : ℤ) :
    (faceRows n i sign).map (decodeRow n) = ConeVerifier.faceRows i (sign : ℚ) := by
  simp only [faceRows, List.map_append, List.map_cons, List.map_nil, decode_coordinate,
    decode_cubeRows, Int.cast_one, Int.cast_neg, ConeVerifier.faceRows]

def Satisfies (n : ℕ) (rows : List RowCode) (x : Fin n → ℝ) : Prop :=
  ∀ row ∈ rows, (decodeRow n row).eval x ≤ 0

theorem satisfies_decode (n : ℕ) (rows : List RowCode) (x : Fin n → ℝ) :
    FourierMotzkin.Satisfies (rows.map (decodeRow n)) x ↔ Satisfies n rows x := by
  simp only [FourierMotzkin.Satisfies, Satisfies, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]

theorem choices_correct (n r : ℕ) (supports : SupportsCode) (x : Fin n → ℝ) :
    (∃ rows ∈ choices r supports, Satisfies n rows x) ↔
      ∀ support ∈ supports, ∃ u ∈ support,
        ConeVerifier.dot (decodeVector n u) x ≤ (1 / 2 : ℝ) ^ r := by
  induction supports with
  | nil => simp [choices, Satisfies]
  | cons support rest ih =>
    rw [List.forall_mem_cons]
    constructor
    · rintro ⟨rows, hrows, hsat⟩
      obtain ⟨u, hu, hrows⟩ := List.mem_flatMap.mp hrows
      obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp hrows
      refine ⟨⟨u, hu, (supportRow_iff n r u x).mp (hsat _ List.mem_cons_self)⟩, ?_⟩
      apply ih.mp
      exact ⟨tail, htail, fun row hrow => hsat row (List.mem_cons_of_mem _ hrow)⟩
    · rintro ⟨⟨u, hu, hux⟩, hrest⟩
      obtain ⟨rows, hrows, hsat⟩ := ih.mpr hrest
      refine ⟨supportRow r u :: rows,
        List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨rows, hrows, rfl⟩⟩, ?_⟩
      intro row hrow
      rcases List.mem_cons.mp hrow with rfl | hrow
      · exact (supportRow_iff n r u x).mpr hux
      · exact hsat row hrow

theorem check_face_correct (n r : ℕ) (supports : SupportsCode) (i : Fin n) (sign : ℤ) :
    ((choices r supports).any fun rows =>
      ComputableFourierMotzkin.check n (rows ++ faceRows n i sign)) = true ↔
    ∃ x : Fin n → ℝ, (x i = (sign : ℝ) ∧ ∀ j, -1 ≤ x j ∧ x j ≤ 1) ∧
      ∀ support ∈ supports, ∃ u ∈ support,
        ConeVerifier.dot (decodeVector n u) x ≤ (1 / 2 : ℝ) ^ r := by
  simp only [List.any_eq_true, ComputableFourierMotzkin.check_eq,
    FourierMotzkin.check_correct n _ ℝ, FourierMotzkin.Feasible]
  constructor
  · rintro ⟨rows, hrows, x, hx⟩
    have hface : FourierMotzkin.Satisfies (ConeVerifier.faceRows i (sign : ℚ)) x := by
      rw [← decode_faceRows]
      intro row hrow
      exact hx row (by simpa only [List.map_append, List.mem_append] using Or.inr hrow)
    have hsat : Satisfies n rows x := by
      apply (satisfies_decode _ _ _).mp
      intro row hrow
      exact hx row (by simpa only [List.map_append, List.mem_append] using Or.inl hrow)
    refine ⟨x, ?_, (choices_correct n r supports x).mp ⟨rows, hrows, hsat⟩⟩
    simpa using (ConeVerifier.faceRows_iff i (sign : ℚ) x).mp hface
  · rintro ⟨x, hface, hs⟩
    obtain ⟨rows, hrows, hsat⟩ := (choices_correct n r supports x).mpr hs
    refine ⟨rows, hrows, x, ?_⟩
    have hf : FourierMotzkin.Satisfies (ConeVerifier.faceRows i (sign : ℚ)) x :=
      (ConeVerifier.faceRows_iff i (sign : ℚ) x).mpr (by simpa using hface)
    intro row hrow
    rw [List.map_append, List.mem_append] at hrow
    rcases hrow with hrow | hrow
    · exact (satisfies_decode _ _ _).mpr hsat row hrow
    · rw [decode_faceRows] at hrow
      exact hf row hrow

theorem badDirection_eq (nr : ℕ × ℕ) (supports : SupportsCode) :
    badDirection nr supports =
      ConeVerifier.badDirection (decodeSupports nr.1 supports) ((1 / 2 : ℚ) ^ nr.2) := by
  rw [Bool.eq_iff_iff, ConeVerifier.badDirection_correct]
  simp only [badDirection, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, sign, hsign, h⟩
    obtain ⟨x, hface, hs⟩ := (check_face_correct nr.1 nr.2 supports ⟨i, hi⟩ sign).mp (List.any_eq_true.mpr h)
    refine ⟨x, ⟨hface.2, ⟨i, hi⟩, ?_⟩, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hsign
      rcases hsign with rfl | rfl <;> simp_all
    · intro support hsupport
      obtain ⟨s, hsmem, rfl⟩ := List.mem_map.mp hsupport
      obtain ⟨u, hu, hux⟩ := hs s hsmem
      exact ⟨decodeVector nr.1 u, List.mem_map.mpr ⟨u, hu, rfl⟩, by simpa using hux⟩
  · rintro ⟨x, ⟨hcube, i, hi⟩, hs⟩
    have hs' : ∀ support ∈ supports, ∃ u ∈ support,
        ConeVerifier.dot (decodeVector nr.1 u) x ≤ (1 / 2 : ℝ) ^ nr.2 := by
      intro support hsupport
      obtain ⟨u, hu, hux⟩ := hs (support.map (decodeVector nr.1))
        (List.mem_map.mpr ⟨support, hsupport, rfl⟩)
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
      exact ⟨v, hv, by simpa using hux⟩
    rcases hi with hi | hi
    · refine ⟨i, i.isLt, -1, by simp, ?_⟩
      exact List.any_eq_true.mp ((check_face_correct _ _ _ i (-1)).mpr ⟨x, ⟨by simpa using hi, hcube⟩, hs'⟩)
    · refine ⟨i, i.isLt, 1, by simp, ?_⟩
      exact List.any_eq_true.mp ((check_face_correct _ _ _ i 1).mpr ⟨x, ⟨by simpa using hi, hcube⟩, hs'⟩)

theorem checkMargin_eq (nr : ℕ × ℕ) (supports : SupportsCode) :
    checkMargin nr supports =
      ConeVerifier.checkMargin (decodeSupports nr.1 supports) ((1 / 2 : ℚ) ^ nr.2) := by
  rw [checkMargin, ConeVerifier.checkMargin, badDirection_eq]

theorem any_primrec {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).any (p a)) := by
  have h := Primrec.list_foldr hf (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b l ih => simp [List.foldr_cons, List.any_cons, ih]

theorem powTwo_primrec : Primrec (fun r : ℕ => (2 ^ r : ℤ)) :=
  (ofNat_primrec.comp (nat_pow_primrec.comp (Primrec.const 2) Primrec.id)).of_eq (fun r => by simp)

theorem supportRow_primrec : Primrec₂ supportRow :=
  (Primrec.list_map Primrec.snd
    (mul_primrec.comp (powTwo_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂).pair
    (Primrec.const (-1))

theorem coordinate_primrec : Primrec (fun p : (ℕ × ℕ) × (ℤ × ℤ) =>
    coordinate p.1.1 p.1.2 p.2.1 p.2.2) :=
  (Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 0)).to₂).pair
    (Primrec.snd.comp Primrec.snd)

theorem cubeRows_primrec : Primrec cubeRows :=
  Primrec.list_flatMap Primrec.list_range
    (Primrec.list_cons.comp (coordinate_primrec.comp
      (Primrec.id.pair ((Primrec.const 1).pair (Primrec.const (-1)))))
      (Primrec.list_cons.comp (coordinate_primrec.comp
        (Primrec.id.pair ((Primrec.const (-1)).pair (Primrec.const (-1)))))
        (Primrec.const []))).to₂

theorem faceRows_primrec : Primrec (fun p : (ℕ × ℕ) × ℤ => faceRows p.1.1 p.1.2 p.2) :=
  Primrec.list_append.comp
    (Primrec.list_cons.comp (coordinate_primrec.comp
      (Primrec.fst.pair ((Primrec.const 1).pair (neg_primrec.comp Primrec.snd))))
      (Primrec.list_cons.comp (coordinate_primrec.comp
        (Primrec.fst.pair ((Primrec.const (-1)).pair Primrec.snd))) (Primrec.const [])))
    (cubeRows_primrec.comp (Primrec.fst.comp Primrec.fst))

def prependChoices (p : ℕ × List VectorCode) (states : List (List RowCode)) : List (List RowCode) :=
  p.2.flatMap fun u => states.map fun rows => supportRow p.1 u :: rows

theorem prependChoices_primrec : Primrec₂ prependChoices :=
  Primrec.list_flatMap (Primrec.snd.comp Primrec.fst)
    (Primrec.list_map (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp
        (supportRow_primrec.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂).to₂

theorem choices_primrec : Primrec₂ choices := by
  have h := Primrec.list_foldr Primrec.snd (Primrec.const [[]])
    (prependChoices_primrec.comp
      ((Primrec.fst.comp Primrec.fst).pair (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  intro p
  induction p.2 with
  | nil => rfl
  | cons s rest ih => simp only [List.foldr_cons, choices, ← ih]; rfl

set_option maxHeartbeats 2000000 in
theorem badDirection_primrec : Primrec₂ badDirection := by
  let Base := (ℕ × ℕ) × SupportsCode
  let Face := (Base × ℕ) × ℤ
  have hn : Primrec (fun p : Face => p.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hi : Primrec (fun p : Face => p.1.2) := Primrec.snd.comp Primrec.fst
  have hf : Primrec (fun p : Face => faceRows p.1.1.1.1 p.1.2 p.2) :=
    faceRows_primrec.comp ((hn.pair hi).pair Primrec.snd)
  have hc : Primrec (fun p : Face × List RowCode =>
      ComputableFourierMotzkin.check p.1.1.1.1.1 (p.2 ++ faceRows p.1.1.1.1.1 p.1.1.2 p.1.2)) :=
    ComputableFourierMotzkin.check_primrec.comp (hn.comp Primrec.fst)
      (Primrec.list_append.comp Primrec.snd (hf.comp Primrec.fst))
  have hs : Primrec (fun p : Face => choices p.1.1.1.2 p.1.1.2) :=
    choices_primrec.comp
      (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hrows : Primrec (fun p : Face => (choices p.1.1.1.2 p.1.1.2).any fun rows =>
      ComputableFourierMotzkin.check p.1.1.1.1 (rows ++ faceRows p.1.1.1.1 p.1.2 p.2)) :=
    any_primrec hs hc.to₂
  have hsign : Primrec (fun p : Base × ℕ => ([-1, 1] : List ℤ).any fun sign =>
      (choices p.1.1.2 p.1.2).any fun rows =>
        ComputableFourierMotzkin.check p.1.1.1 (rows ++ faceRows p.1.1.1 p.2 sign)) :=
    any_primrec (Primrec.const [-1, 1]) hrows.to₂
  exact any_primrec (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)) hsign.to₂

theorem checkMargin_primrec : Primrec₂ checkMargin := Primrec.not.comp badDirection_primrec

end Kourovka.MetabelianEnumeration.ComputableCone
