/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Modules.SignedTameness

/-!
# Module Realization

Conversion of signed Laurent-module identities to the exact ordinary
group relators. Negative tags retain the literal inverse ordered word.
-/

noncomputable section

namespace Kourovka.MetabelianEnumeration.ModuleRealization

open FiniteCover ValuationModule SignedTameness TamenessCompactness

variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]

def encodeSigned (p : SignedPolynomial k) : Polynomial k :=
  (p.1, p.2.support.toList.map fun u => (if p.1 then u else -u, p.2 u))

theorem polynomialSupport_encode (p : SignedPolynomial k) :
    polynomialSupport (encodeSigned p) = signedSupport p := by
  simp only [polynomialSupport, encodeSigned, signedSupport, List.map_map]
  apply List.map_congr_left
  intro u _
  funext i
  cases p.1 <;> simp

def ActionCompatible (j : Multiplicative M →* G) (t : Fin k → G) : Prop :=
  ∀ u m, j (Multiplicative.ofAdd ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)) =
    conjugate (j (Multiplicative.ofAdd m)) (orderedWord t u)

theorem map_sum (j : Multiplicative M →* G) (xs : List M) :
    j (Multiplicative.ofAdd xs.sum) = (xs.map fun m => j (Multiplicative.ofAdd m)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih => simpa using congrArg (fun g => j (Multiplicative.ofAdd x) * g) ih

theorem single_smul (u : Lattice k) (c : ℤ) (m : M) :
    (AddMonoidAlgebra.single u c : GroupRing (Lattice k)) • m =
      c • ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m) := by
  have h : (AddMonoidAlgebra.single u c : GroupRing (Lattice k)) =
      c • (AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) := by simp
  rw [h, smul_assoc]

theorem smul_as_sum (p : GroupRing (Lattice k)) (m : M) :
    p • m = (p.support.toList.map fun u => p u •
      ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)).sum := by
  rw [Finset.sum_map_toList]
  conv_lhs => rw [← AddMonoidAlgebra.sum_single p]
  change (∑ u ∈ p.support, AddMonoidAlgebra.single u (p u)) • m = _
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro u _
  exact single_smul u (p u) m

theorem compatible_inverse (j : Multiplicative M →* G) (t : Fin k → G)
    (h : ActionCompatible j t) (u : Lattice k) (m : M) :
    conjugate (j (Multiplicative.ofAdd m)) ((orderedWord t (-u))⁻¹) =
      j (Multiplicative.ofAdd ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)) := by
  have hh := h (-u) ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)
  have hs : (AddMonoidAlgebra.single (-u) 1 : GroupRing (Lattice k)) •
      ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m) = m := by
    rw [← mul_smul, AddMonoidAlgebra.single_mul_single]
    simp [← AddMonoidAlgebra.one_def]
  rw [hs] at hh
  rw [hh]
  simp [conjugate, mul_assoc]

theorem conjugate_zpow (x w : G) (c : ℤ) : conjugate (x ^ c) w = (conjugate x w) ^ c := by
  simpa [conjugate, MulAut.conj_apply] using (map_zpow ((MulAut.conj w⁻¹).toMonoidHom) x c)

/-- A positive or negative tagged polynomial evaluates to its original module
action. For negative tags, exponent negation and the literal inverse cancel. -/
theorem polynomialWord_encode (j : Multiplicative M →* G) (t : Fin k → G)
    (h : ActionCompatible j t) (p : SignedPolynomial k) (m : M) :
    polynomialWord t (j (Multiplicative.ofAdd m)) (encodeSigned p) =
      j (Multiplicative.ofAdd (p.2 • m)) := by
  rw [smul_as_sum, map_sum]
  simp only [polynomialWord, encodeSigned, List.map_map]
  congr 1
  apply List.map_congr_left
  intro u _
  simp only [Function.comp_apply, conjugate_zpow, ofAdd_zsmul, map_zpow]
  cases hb : p.1
  · simpa only [hb, Bool.false_eq_true, if_false] using
      congrArg (fun x : G => x ^ p.2 u) (compatible_inverse j t h u m)
  · simpa only [hb, if_true] using
      congrArg (fun x : G => x ^ p.2 u) (h u m).symm

/-- Actual tameness of the Laurent module gives finite group polynomial
relations and the exact real cone-cover condition needed by the finite cover. -/
theorem finite_realizing_polynomials [Module.Finite (GroupRing (Lattice k)) M]
    (j : Multiplicative M →* G) (t : Fin k → G) (h : ActionCompatible j t)
    (ht : Tame (k := k) M) :
    ∃ ps : List (Polynomial k),
      (∀ p ∈ ps, ∀ m : M, j (Multiplicative.ofAdd m) =
        polynomialWord t (j (Multiplicative.ofAdd m)) p) ∧
      ConeVerifier.ConeCover (ps.map polynomialSupport) := by
  obtain ⟨ps, hact, hcover⟩ := finite_signed_centralizers ht
  refine ⟨ps.map encodeSigned, ?_, ?_⟩
  · intro p hp m
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [polynomialWord_encode j t h, hact q hq m]
  · simpa only [List.map_map, Function.comp_def, polynomialSupport_encode] using hcover

end Kourovka.MetabelianEnumeration.ModuleRealization
