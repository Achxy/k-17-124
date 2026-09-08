/-
Adapted from ProCGroups by n-yamaguchi-0729, commit
6933dfe3f376833421ce10e782108b95ac84bda5, under Apache License 2.0.
See ../../third_party/ProCGroups-LICENSE and ProCGroups-PROVENANCE.md.
Local changes: module and namespace prefixes; compatibility with Lean 4.24.
-/
import Mathlib.GroupTheory.PresentedGroup
import Kourovka.Schreier.RelatorCongruence
import Kourovka.Schreier.RelatorOperations

set_option autoImplicit false


/-!
# Reidemeister Schreier / Discrete / Reidemeister Schreier / Rewriting

This module defines abstract right Schreier representatives, their associated
symbols and generators, and the rewriting maps that turn kernel words into
words on Schreier symbols.
-/

namespace Kourovka.Schreier.Discrete

open Kourovka.Schreier.Discrete.Presentations

variable {X : Type*}

/--
A normalized representative function for right cosets of \(L\) in a free group. The condition
\(g(\operatorname{rep}(g))^{-1}\in L\) says that \(\operatorname{rep}(g)\) represents the same
right coset as \(g\).
-/
structure RightSchreierRepresentative (L : Subgroup (FreeGroup X)) where
  /-- The chosen representative of the right coset of each free-group element. -/
  representative : FreeGroup X → FreeGroup X
  /-- Every element and its chosen representative belong to the same right coset of \(L\). -/
  sameRightCoset : ∀ g, g * (representative g)⁻¹ ∈ L
  /-- Elements in the same right coset receive the same representative. -/
  representative_eq_of_sameRightCoset :
    ∀ {g h}, g * h⁻¹ ∈ L → representative g = representative h
  /-- The identity coset is represented by the identity. -/
  representative_one : representative 1 = 1

namespace RightSchreierRepresentative

variable {L : Subgroup (FreeGroup X)} (S : RightSchreierRepresentative L)

/-- A representative differs from the original element by an element of the subgroup. -/
theorem representative_mul_inv_mem (g : FreeGroup X) :
    S.representative g * g⁻¹ ∈ L := by
  simpa using L.inv_mem (S.sameRightCoset g)

/-- The right Schreier representative is the identity exactly in the subgroup-membership case. -/
theorem representative_eq_one_of_mem {g : FreeGroup X} (hg : g ∈ L) :
    S.representative g = 1 := by
  have h : S.representative g = S.representative (1 : FreeGroup X) := by
    apply S.representative_eq_of_sameRightCoset
    simpa using hg
  simpa [S.representative_one] using h

/--
Replacing a word by its chosen right Schreier representative does not change the representative
selected after multiplying by a generator.
-/
theorem representative_mul_generator_eq (p : FreeGroup X) (x : X) :
    S.representative (S.representative p * FreeGroup.of x) =
      S.representative (p * FreeGroup.of x) := by
  apply S.representative_eq_of_sameRightCoset
  have h := S.representative_mul_inv_mem p
  convert h using 1
  group

/--
After moving backward by a generator, replacing the resulting word by its representative and
then moving forward selects the original word's representative.
-/
theorem representative_inv_generator_mul_generator_eq (p : FreeGroup X) (x : X) :
    S.representative (S.representative (p * (FreeGroup.of x)⁻¹) * FreeGroup.of x) =
      S.representative p := by
  apply S.representative_eq_of_sameRightCoset
  have h := S.representative_mul_inv_mem (p * (FreeGroup.of x)⁻¹)
  convert h using 1
  group

end RightSchreierRepresentative

/--
Labels for Schreier generators. A label \((t,x)\) represents the generator \(t x\overline{t
x}^{-1}\).
-/
abbrev SchreierSymbol (X : Type*) := FreeGroup X × X

namespace SchreierRewriting

variable {L : Subgroup (FreeGroup X)} (S : RightSchreierRepresentative L)

/--
The Schreier generator is the correction term \(t x \overline{t x}^{-1}\) attached to a
representative and a generator.
-/
def schreierGenerator (t : FreeGroup X) (x : X) : FreeGroup X :=
  t * FreeGroup.of x * (S.representative (t * FreeGroup.of x))⁻¹

/-- Evaluation of one Schreier symbol as its Schreier generator in the free group. -/
def symbolEval (z : SchreierSymbol X) : FreeGroup X :=
  schreierGenerator S z.1 z.2

/-- Each evaluated Schreier symbol lies in the subgroup being rewritten. -/
theorem symbolEval_mem (z : SchreierSymbol X) :
    symbolEval S z ∈ L := by
  rcases z with ⟨t, x⟩
  exact S.sameRightCoset (t * FreeGroup.of x)

/-- The homomorphism extending Schreier-symbol evaluation to the free group on Schreier symbols. -/
def symbolEvalHom : FreeGroup (SchreierSymbol X) →* FreeGroup X :=
  FreeGroup.lift (symbolEval S)

/-- The evaluation homomorphism sends a Schreier-symbol generator to its symbol evaluation. -/
@[simp]
theorem symbolEvalHom_of (z : SchreierSymbol X) :
    symbolEvalHom S (FreeGroup.of z) = symbolEval S z := by
  simp only [symbolEvalHom, FreeGroup.lift_apply_of]

/--
The image of the Schreier-symbol evaluation homomorphism lies in the subgroup being rewritten.
-/
theorem symbolEvalHom_mem (q : FreeGroup (SchreierSymbol X)) :
    symbolEvalHom S q ∈ L := by
  have hle : (symbolEvalHom S).range ≤ L := by
    rw [symbolEvalHom, FreeGroup.range_lift_eq_closure]
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact symbolEval_mem (S := S) z
  exact hle ⟨q, rfl⟩

/-- Evaluation as a homomorphism into the subgroup being rewritten. -/
def symbolEvalSubgroupHom : FreeGroup (SchreierSymbol X) →* L where
  toFun q := ⟨symbolEvalHom S q, symbolEvalHom_mem (S := S) q⟩
  map_one' := Subtype.ext (symbolEvalHom S).map_one
  map_mul' q r := Subtype.ext ((symbolEvalHom S).map_mul q r)

/--
Forgetting the subgroup target of \(\mathrm{symbolEvalSubgroupHom}\) gives the ordinary
evaluation homomorphism.
-/
@[simp]
theorem symbolEvalSubgroupHom_apply (q : FreeGroup (SchreierSymbol X)) :
    (symbolEvalSubgroupHom S q : FreeGroup X) = symbolEvalHom S q :=
  rfl

/--
Evaluation of the Schreier symbol starting at a chosen representative has the expected
positive-letter formula.
-/
@[simp]
theorem symbolEval_representative_mul_generator (p : FreeGroup X) (x : X) :
    symbolEval S (S.representative p, x) =
      S.representative p * FreeGroup.of x * (S.representative (p * FreeGroup.of x))⁻¹ := by
  simp only [symbolEval, schreierGenerator,
      RightSchreierRepresentative.representative_mul_generator_eq]

/--
Evaluation of the Schreier symbol for an inverse-letter step has the expected representative
formula.
-/
@[simp]
theorem symbolEval_representative_inv_generator (p : FreeGroup X) (x : X) :
    symbolEval S (S.representative (p * (FreeGroup.of x)⁻¹), x) =
      S.representative (p * (FreeGroup.of x)⁻¹) *
        FreeGroup.of x * (S.representative p)⁻¹ := by
  simp only [symbolEval, schreierGenerator,
  RightSchreierRepresentative.representative_inv_generator_mul_generator_eq]

/--
A word list beginning with a positive letter represents that generator multiplied by the word
represented by the tail.
-/
@[simp]
theorem mk_cons_true (x : X) (xs : List (X × Bool)) :
    FreeGroup.mk ((x, true) :: xs) =
      FreeGroup.of x * FreeGroup.mk xs := by
  change FreeGroup.mk ((x, true) :: xs) =
    FreeGroup.mk [(x, true)] * FreeGroup.mk xs
  rw [FreeGroup.mul_mk]
  rfl

/--
A word list beginning with a negative letter represents the inverse generator multiplied by the
word represented by the tail.
-/
@[simp]
theorem mk_cons_false (x : X) (xs : List (X × Bool)) :
    FreeGroup.mk ((x, false) :: xs) =
      (FreeGroup.of x)⁻¹ * FreeGroup.mk xs := by
  change FreeGroup.mk ((x, false) :: xs) =
    (FreeGroup.mk [(x, true)])⁻¹ * FreeGroup.mk xs
  rw [FreeGroup.inv_mk, FreeGroup.mul_mk]
  rfl

/-- Schreier rewriting of a raw word list, starting from prefix \(p\). -/
def tauList : FreeGroup X → List (X × Bool) → FreeGroup (SchreierSymbol X)
  | _p, [] => 1
  | p, (x, true) :: xs =>
      FreeGroup.of (S.representative p, x) *
        tauList (p * FreeGroup.of x) xs
  | p, (x, false) :: xs =>
      (FreeGroup.of (S.representative (p * (FreeGroup.of x)⁻¹), x))⁻¹ *
        tauList (p * (FreeGroup.of x)⁻¹) xs

/-- Evaluating a \(\tau\)-list gives the quotient-section conjugate of the represented word. -/
@[simp]
theorem symbolEvalHom_tauList
    (p : FreeGroup X) (xs : List (X × Bool)) :
    symbolEvalHom S (tauList S p xs) =
      S.representative p * FreeGroup.mk xs *
        (S.representative (p * FreeGroup.mk xs))⁻¹ := by
  induction xs generalizing p with
  | nil =>
      simp only [tauList, map_one]
      change 1 = S.representative p * 1 * (S.representative (p * 1))⁻¹
      simp only [mul_one, mul_inv_cancel]
  | cons hd xs ih =>
      rcases hd with ⟨x, eps⟩
      cases eps
      · simp only [tauList, map_mul, map_inv, symbolEvalHom_of,
          symbolEval_representative_mul_generator, mul_assoc,
  inv_mul_cancel, mul_one, mul_inv_rev, inv_inv, ih, inv_mul_cancel_left, mk_cons_false]
      · simp only [tauList, map_mul, symbolEvalHom_of, symbolEval_representative_mul_generator,
          mul_assoc, ih,
  inv_mul_cancel_left, mk_cons_true]

/--
The \(\tau\)-list rewrite of a concatenated word splits as the product of the first rewrite and
the rewrite of the second word from the updated quotient element.
-/
theorem tauList_append
    (p : FreeGroup X) (xs ys : List (X × Bool)) :
    tauList S p (xs ++ ys) =
      tauList S p xs * tauList S (p * FreeGroup.mk xs) ys := by
  induction xs generalizing p with
  | nil =>
      simp only [List.nil_append, tauList, one_mul]
      change tauList S p ys = tauList S (p * 1) ys
      simp only [mul_one]
  | cons hd xs ih =>
      rcases hd with ⟨x, eps⟩
      cases eps
      · simp only [List.cons_append, tauList, ih, mul_assoc, mk_cons_false]
      · simp only [List.cons_append, tauList, ih, mul_assoc, mk_cons_true]

/-- The symbol evaluation of the \(\tau\)-rewrite lies in the Schreier subgroup kernel. -/
theorem symbolEvalHom_tauList_mem
    (p : FreeGroup X) (xs : List (X × Bool)) :
    symbolEvalHom S (tauList S p xs) ∈ L := by
  rw [symbolEvalHom_tauList]
  have hleft := S.representative_mul_inv_mem p
  have hright := S.sameRightCoset (p * FreeGroup.mk xs)
  have hproduct := L.mul_mem hleft hright
  convert hproduct using 1
  group

variable [DecidableEq X]

/-- Explicit Schreier rewriting of a free group word. -/
def tau (t w : FreeGroup X) : FreeGroup (SchreierSymbol X) :=
  tauList S t w.toWord

/-- Evaluating a \(\tau\)-word gives the quotient-section conjugate of the rewritten word. -/
theorem symbolEvalHom_tau
    (t w : FreeGroup X) :
    symbolEvalHom S (tau S t w) =
      S.representative t * w * (S.representative (t * w))⁻¹ := by
  simp only [tau, symbolEvalHom_tauList, FreeGroup.mk_toWord]

/-- The symbol evaluation of the \(\tau\)-rewrite lies in the Schreier subgroup kernel. -/
theorem symbolEvalHom_tau_mem
    (t w : FreeGroup X) :
    symbolEvalHom S (tau S t w) ∈ L := by
  simpa [tau] using symbolEvalHom_tauList_mem (S := S) t w.toWord

/--
When the starting word is already the chosen representative, evaluating \(\tau\) gives that
representative times the word and the inverse of the next representative.
-/
theorem symbolEvalHom_tau_of_representative
    {t w : FreeGroup X} (ht : S.representative t = t) :
    symbolEvalHom S (tau S t w) =
      t * w * (S.representative (t * w))⁻¹ := by
  simpa [ht] using symbolEvalHom_tau (S := S) t w

/--
For a word in the Schreier subgroup, evaluating its \(\tau\)-rewrite from the identity
representative recovers that word.
-/
theorem symbolEvalHom_tau_one_of_mem
    {w : FreeGroup X} (hw : w ∈ L) :
    symbolEvalHom S (tau S 1 w) = w := by
  have hwrep : S.representative w = 1 := S.representative_eq_one_of_mem hw
  simpa [RightSchreierRepresentative.representative_one, hwrep] using
    symbolEvalHom_tau (S := S) (t := 1) (w := w)

/-- The set of representatives selected by a normalized Schreier representative function. -/
def representativeSet : Set (FreeGroup X) :=
  Set.range S.representative

/--
The Schreier relators attached to a relator set \(R\) and an explicit transversal \(T\): all
rewrites \(\tau(t,r)\) with \(t \in T\).
-/
def schreierRelatorsOn
    (T : Set (FreeGroup X)) (R : Set (FreeGroup X)) :
    Set (FreeGroup (SchreierSymbol X)) :=
  { q | ∃ t ∈ T, ∃ r ∈ R, q = tau S t r }

/--
The default Schreier relator set is formed by rewriting relators with the range of the
representative function as the transversal.
-/
def schreierRelators (R : Set (FreeGroup X)) :
    Set (FreeGroup (SchreierSymbol X)) :=
  schreierRelatorsOn S (representativeSet S) R

/--
Degenerate Schreier generators \(s(t,x)\) whose evaluation is already \(1\). These are the
Tietze-removable generators in the raw Reidemeister--Schreier presentation.
-/
def degenerateSchreierRelatorsOn
    (T : Set (FreeGroup X)) :
    Set (FreeGroup (SchreierSymbol X)) :=
  { q | ∃ t ∈ T, ∃ x : X,
      S.representative (t * FreeGroup.of x) = t * FreeGroup.of x ∧
        q = FreeGroup.of (t, x) }

/-- The set of degenerate Schreier relators for the default representative set. -/
def degenerateSchreierRelators :
    Set (FreeGroup (SchreierSymbol X)) :=
  degenerateSchreierRelatorsOn S (representativeSet S)

/--
The raw relator set for the Reidemeister--Schreier presentation: rewritten original relators
plus degenerate Schreier generators.
-/
def presentationRelatorsOn
    (T : Set (FreeGroup X)) (R : Set (FreeGroup X)) :
    Set (FreeGroup (SchreierSymbol X)) :=
  schreierRelatorsOn S T R ∪ degenerateSchreierRelatorsOn S T

/--
The Reidemeister--Schreier presentation relators are the Schreier relators together with the
degenerate Schreier-generator relators.
-/
def presentationRelators
    (R : Set (FreeGroup X)) :
    Set (FreeGroup (SchreierSymbol X)) :=
  presentationRelatorsOn S (representativeSet S) R

/--
The \(\tau\)-rewrite of an original relator at a chosen representative belongs to the Schreier
relator set on that representative set.
-/
theorem tau_mem_schreierRelatorsOn
    {T R : Set (FreeGroup X)} {t : FreeGroup X} (ht : t ∈ T)
    {r : FreeGroup X} (hr : r ∈ R) :
    tau S t r ∈ schreierRelatorsOn S T R :=
  ⟨t, ht, r, hr, rfl⟩

/--
The \(\tau\)-rewrite at the canonical representative of an original relator belongs to the
default Schreier relator set.
-/
theorem tau_representative_mem_schreierRelators
    {R : Set (FreeGroup X)} (t : FreeGroup X) {r : FreeGroup X} (hr : r ∈ R) :
    tau S (S.representative t) r ∈ schreierRelators S R :=
  tau_mem_schreierRelatorsOn (S := S) (T := representativeSet S)
    ⟨t, rfl⟩ hr

omit [DecidableEq X] in
/--
Every degenerate Schreier relator evaluates to the identity under the Schreier evaluation map.
-/
theorem degenerateSchreierRelator_eval_eq_one
    {T : Set (FreeGroup X)}
    {q : FreeGroup (SchreierSymbol X)}
    (hq : q ∈ degenerateSchreierRelatorsOn S T) :
    symbolEvalHom S q = 1 := by
  rcases hq with ⟨t, _ht, x, hrepresentative, rfl⟩
  simp only [symbolEvalHom_of, symbolEval, schreierGenerator, hrepresentative, mul_inv_rev]
  group

omit [DecidableEq X] in
/--
The evaluation of a degenerate Schreier relator lies in the normal closure of the defining
source relators.
-/
theorem eval_degenerateSchreierRelator_mem_normalClosure
    {T R : Set (FreeGroup X)}
    {q : FreeGroup (SchreierSymbol X)}
    (hq : q ∈ degenerateSchreierRelatorsOn S T) :
    symbolEvalHom S q ∈ Subgroup.normalClosure R := by
  simp only [degenerateSchreierRelator_eval_eq_one (S := S) hq, one_mem]

omit [DecidableEq X] in
/--
Multiplying a chosen representative by an original relator does not change the chosen
representative when the relators lie in the subgroup.
-/
theorem representative_mul_relator_eq
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (t : FreeGroup X) {r : FreeGroup X} (hr : r ∈ R) :
    S.representative (t * r) = S.representative t := by
  apply S.representative_eq_of_sameRightCoset
  exact hR (by
    simpa [mul_assoc] using
      conjugate_mem_normalClosure_of_mem (R := R) hr t)

/--
The symbol evaluation of the \(\tau\)-rewrite of a defining relator lies in the normal closure
of the original relators.
-/
theorem symbolEvalHom_tau_relator_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (t : FreeGroup X) {r : FreeGroup X} (hr : r ∈ R) :
    symbolEvalHom S (tau S t r) ∈ Subgroup.normalClosure R := by
  have hrep := representative_mul_relator_eq (S := S) hR t hr
  have hconj :
      S.representative t * r * (S.representative t)⁻¹ ∈
        Subgroup.normalClosure R :=
    conjugate_mem_normalClosure_of_mem (R := R) hr (S.representative t)
  simpa [symbolEvalHom_tau, hrep, mul_assoc] using hconj

/--
Evaluating a Schreier relator on a specified representative set gives an element of the normal
closure of the original relators.
-/
theorem eval_schreierRelatorOn_mem_normalClosure
    {T R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (SchreierSymbol X)}
    (hq : q ∈ schreierRelatorsOn S T R) :
    symbolEvalHom S q ∈ Subgroup.normalClosure R := by
  rcases hq with ⟨t, _ht, r, hr, rfl⟩
  exact symbolEvalHom_tau_relator_mem_normalClosure (S := S) hR t hr

/--
Evaluating a default Schreier relator gives an element of the normal closure of the original
relators.
-/
theorem eval_schreierRelator_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (SchreierSymbol X)}
    (hq : q ∈ schreierRelators S R) :
    symbolEvalHom S q ∈ Subgroup.normalClosure R :=
  eval_schreierRelatorOn_mem_normalClosure (S := S) hR hq

/--
Membership in the source relator normal closure is preserved by the Reidemeister--Schreier
evaluation map.
-/
theorem eval_mem_normalClosure_of_mem_normalClosure_schreierRelatorsOn
    {T R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (SchreierSymbol X)}
    (hq : q ∈ Subgroup.normalClosure (schreierRelatorsOn S T R)) :
    symbolEvalHom S q ∈ Subgroup.normalClosure R :=
  map_mem_normalClosure_of_relators (symbolEvalHom S)
    (fun _ hr => eval_schreierRelatorOn_mem_normalClosure (S := S) hR hr) hq

/--
Membership in the source relator normal closure is preserved by the Reidemeister--Schreier
evaluation map.
-/
theorem eval_mem_normalClosure_of_mem_normalClosure_schreierRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (SchreierSymbol X)}
    (hq : q ∈ Subgroup.normalClosure (schreierRelators S R)) :
    symbolEvalHom S q ∈ Subgroup.normalClosure R :=
  eval_mem_normalClosure_of_mem_normalClosure_schreierRelatorsOn (S := S) hR hq

/--
Evaluating a presentation relator on a specified representative set gives an element of the
normal closure of the original relators.
-/
theorem eval_presentationRelatorOn_mem_normalClosure
    {T R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (SchreierSymbol X)}
    (hq : q ∈ presentationRelatorsOn S T R) :
    symbolEvalHom S q ∈ Subgroup.normalClosure R := by
  rcases hq with hq | hq
  · exact eval_schreierRelatorOn_mem_normalClosure (S := S) hR hq
  · exact eval_degenerateSchreierRelator_mem_normalClosure (S := S) hq

/--
Membership in the source relator normal closure is preserved by the Reidemeister--Schreier
evaluation map.
-/
theorem eval_mem_normalClosure_of_mem_normalClosure_presentationRelatorsOn
    {T R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (SchreierSymbol X)}
    (hq : q ∈ Subgroup.normalClosure (presentationRelatorsOn S T R)) :
    symbolEvalHom S q ∈ Subgroup.normalClosure R :=
  map_mem_normalClosure_of_relators (symbolEvalHom S)
    (fun _ hr => eval_presentationRelatorOn_mem_normalClosure (S := S) hR hr) hq

/--
Membership in the source relator normal closure is preserved by the Reidemeister--Schreier
evaluation map.
-/
theorem eval_mem_normalClosure_of_mem_normalClosure_presentationRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (SchreierSymbol X)}
    (hq : q ∈ Subgroup.normalClosure (presentationRelators S R)) :
    symbolEvalHom S q ∈ Subgroup.normalClosure R :=
  eval_mem_normalClosure_of_mem_normalClosure_presentationRelatorsOn (S := S) hR hq

/-- The subgroup of \(L\) induced by the ambient normal closure of the original relators. -/
def relatorSubgroup
    (R : Set (FreeGroup X)) :
    Subgroup L where
  carrier := {g | (g : FreeGroup X) ∈ Subgroup.normalClosure R}
  one_mem' := by
    simp only [Set.mem_setOf_eq, OneMemClass.coe_one, one_mem]
  mul_mem' := by
    intro a b ha hb
    exact Subgroup.mul_mem (Subgroup.normalClosure R) ha hb
  inv_mem' := by
    intro a ha
    exact Subgroup.inv_mem (Subgroup.normalClosure R) ha

/-- The subgroup generated by the relators of the presented group is normal. -/
instance relatorSubgroup_normal
    (R : Set (FreeGroup X)) :
    (relatorSubgroup (L := L) R).Normal where
  conj_mem n hn g := by
    change ((g : FreeGroup X) * (n : FreeGroup X) * (g : FreeGroup X)⁻¹) ∈
      Subgroup.normalClosure R
    simpa [mul_assoc] using
      (Subgroup.normalClosure_normal.conj_mem
        (n : FreeGroup X) hn (g : FreeGroup X))

/--
The symbol-evaluation subgroup homomorphism sends the indicated normal-closure element into the
relator subgroup.
-/
theorem symbolEvalSubgroupHom_mem_relatorSubgroup_of_mem_normalClosure_schreierRelatorsOn
    {T R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (SchreierSymbol X)}
    (hq : q ∈ Subgroup.normalClosure (schreierRelatorsOn S T R)) :
    symbolEvalSubgroupHom S q ∈ relatorSubgroup (L := L) R :=
  eval_mem_normalClosure_of_mem_normalClosure_schreierRelatorsOn (S := S) hR hq

/--
The canonical map from the raw Schreier-relator quotient to the subgroup quotient \(L/(L \cap
\langle\!\langle R \rangle\!\rangle)\).
-/
noncomputable def symbolEvalQuotientHomOn
    {T R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L) :
    FreeGroup (SchreierSymbol X) ⧸
        Subgroup.normalClosure (schreierRelatorsOn S T R) →*
      L ⧸ relatorSubgroup (L := L) R :=
  QuotientGroup.lift
    (Subgroup.normalClosure (schreierRelatorsOn S T R))
    ((QuotientGroup.mk' (relatorSubgroup (L := L) R)).comp
      (symbolEvalSubgroupHom S))
    (by
      intro q hq
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff
        (N := relatorSubgroup (L := L) R)
        (symbolEvalSubgroupHom S q)).2
        (symbolEvalSubgroupHom_mem_relatorSubgroup_of_mem_normalClosure_schreierRelatorsOn
          (S := S) hR hq))

/--
The canonical evaluation map from the Schreier-relator quotient to the relator-subgroup quotient
of the subgroup.
-/
noncomputable def symbolEvalQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L) :
    FreeGroup (SchreierSymbol X) ⧸
        Subgroup.normalClosure (schreierRelators S R) →*
      L ⧸ relatorSubgroup (L := L) R :=
  symbolEvalQuotientHomOn (S := S) hR

/--
The evaluation map from a raw presentation quotient with a specified transversal set to the
relator-subgroup quotient.
-/
noncomputable def symbolEvalPresentationQuotientHomOn
    {T R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L) :
    FreeGroup (SchreierSymbol X) ⧸
        Subgroup.normalClosure (presentationRelatorsOn S T R) →*
      L ⧸ relatorSubgroup (L := L) R :=
  QuotientGroup.lift
    (Subgroup.normalClosure (presentationRelatorsOn S T R))
    ((QuotientGroup.mk' (relatorSubgroup (L := L) R)).comp
      (symbolEvalSubgroupHom S))
    (by
      intro q hq
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff
        (N := relatorSubgroup (L := L) R)
        (symbolEvalSubgroupHom S q)).2
        (eval_mem_normalClosure_of_mem_normalClosure_presentationRelatorsOn
          (S := S) hR hq))

/--
The evaluation map from the raw Schreier presentation quotient to the relator-subgroup quotient.
-/
noncomputable def symbolEvalPresentationQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L) :
    FreeGroup (SchreierSymbol X) ⧸
        Subgroup.normalClosure (presentationRelators S R) →*
      L ⧸ relatorSubgroup (L := L) R :=
  symbolEvalPresentationQuotientHomOn (S := S) hR

/-- The specified-transversal presentation evaluation quotient map is surjective. -/
theorem symbolEvalPresentationQuotientHomOn_surjective
    {T R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L) :
    Function.Surjective (symbolEvalPresentationQuotientHomOn (S := S) (T := T) hR) := by
  intro y
  rcases QuotientGroup.mk'_surjective (relatorSubgroup (L := L) R) y with ⟨l, rfl⟩
  refine ⟨QuotientGroup.mk'
      (Subgroup.normalClosure (presentationRelatorsOn S T R))
      (tau S 1 (l : FreeGroup X)), ?_⟩
  simp only [symbolEvalPresentationQuotientHomOn, QuotientGroup.mk'_apply, QuotientGroup.lift_mk,
  MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply]
  have hsub :
      symbolEvalSubgroupHom S (tau S 1 (l : FreeGroup X)) = l :=
    Subtype.ext (symbolEvalHom_tau_one_of_mem (S := S) l.property)
  simpa using congrArg (QuotientGroup.mk' (relatorSubgroup (L := L) R)) hsub

/-- The raw Schreier presentation evaluation quotient map is surjective. -/
theorem symbolEvalPresentationQuotientHom_surjective
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L) :
    Function.Surjective (symbolEvalPresentationQuotientHom (S := S) hR) :=
  symbolEvalPresentationQuotientHomOn_surjective (S := S) hR

/--
The kernel relator case: if an original relator lies in the subgroup being rewritten, its
rewrite from the identity evaluates back to that relator.
-/
theorem eval_tau_one_relator_mem_normalClosure
    {R : Set (FreeGroup X)}
    {r : FreeGroup X} (hr : r ∈ R) (hrL : r ∈ L) :
    symbolEvalHom S (tau S 1 r) ∈ Subgroup.normalClosure R := by
  simpa [symbolEvalHom_tau_one_of_mem (S := S) hrL] using
    (Subgroup.subset_normalClosure hr :
      r ∈ Subgroup.normalClosure R)

/-- Schreier generator labels indexed by the chosen representative set. -/
abbrev RepresentativeSchreierSymbol :=
  representativeSet S × X

/--
The representative Schreier generator is the correction term determined by a representative and
an original generator.
-/
def representativeSchreierGenerator
    (z : RepresentativeSchreierSymbol S) : FreeGroup X :=
  (z.1 : FreeGroup X) * FreeGroup.of z.2 *
    (S.representative ((z.1 : FreeGroup X) * FreeGroup.of z.2))⁻¹

/-- Evaluation of one representative-indexed Schreier symbol as its Schreier generator. -/
def representativeSymbolEval
    (z : RepresentativeSchreierSymbol S) : FreeGroup X :=
  representativeSchreierGenerator S z

omit [DecidableEq X] in
/-- Each evaluated representative-indexed Schreier symbol lies in the subgroup being rewritten. -/
theorem representativeSymbolEval_mem
    (z : RepresentativeSchreierSymbol S) :
    representativeSymbolEval S z ∈ L := by
  rcases z with ⟨t, x⟩
  exact S.sameRightCoset ((t : FreeGroup X) * FreeGroup.of x)

/-- The homomorphism extending representative-indexed Schreier-symbol evaluation. -/
def representativeSymbolEvalHom :
    FreeGroup (RepresentativeSchreierSymbol S) →* FreeGroup X :=
  FreeGroup.lift (representativeSymbolEval S)

omit [DecidableEq X] in
/--
The representative evaluation homomorphism sends a generator to its representative symbol
evaluation.
-/
@[simp]
theorem representativeSymbolEvalHom_of
    (z : RepresentativeSchreierSymbol S) :
    representativeSymbolEvalHom S (FreeGroup.of z) =
      representativeSymbolEval S z := by
  simp only [representativeSymbolEvalHom, FreeGroup.lift_apply_of]

omit [DecidableEq X] in
/-- The image of the representative evaluation homomorphism lies in the subgroup being rewritten. -/
theorem representativeSymbolEvalHom_mem
    (q : FreeGroup (RepresentativeSchreierSymbol S)) :
    representativeSymbolEvalHom S q ∈ L := by
  have hle : (representativeSymbolEvalHom S).range ≤ L := by
    rw [representativeSymbolEvalHom, FreeGroup.range_lift_eq_closure]
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact representativeSymbolEval_mem (S := S) z
  exact hle ⟨q, rfl⟩

/--
Representative-indexed Schreier-symbol evaluation bundled as a homomorphism into the subgroup
being rewritten.
-/
def representativeSymbolEvalSubgroupHom :
    FreeGroup (RepresentativeSchreierSymbol S) →* L where
  toFun q := ⟨representativeSymbolEvalHom S q,
    representativeSymbolEvalHom_mem (S := S) q⟩
  map_one' := Subtype.ext (representativeSymbolEvalHom S).map_one
  map_mul' q r := Subtype.ext ((representativeSymbolEvalHom S).map_mul q r)

omit [DecidableEq X] in
/--
Forgetting the subgroup target of the representative evaluation homomorphism gives the ordinary
representative evaluation homomorphism.
-/
@[simp]
theorem representativeSymbolEvalSubgroupHom_apply
    (q : FreeGroup (RepresentativeSchreierSymbol S)) :
    (representativeSymbolEvalSubgroupHom S q : FreeGroup X) =
      representativeSymbolEvalHom S q :=
  rfl

/-- The representative label records the chosen representative attached to a free-group word. -/
def representativeLabel (p : FreeGroup X) (x : X) :
    RepresentativeSchreierSymbol S :=
  (⟨S.representative p, ⟨p, rfl⟩⟩, x)

/-- Restricted Schreier rewriting of a raw word list. -/
def representativeTauList :
    FreeGroup X → List (X × Bool) → FreeGroup (RepresentativeSchreierSymbol S)
  | _p, [] => 1
  | p, (x, true) :: xs =>
      FreeGroup.of (representativeLabel S p x) *
        representativeTauList (p * FreeGroup.of x) xs
  | p, (x, false) :: xs =>
      (FreeGroup.of
        (representativeLabel S (p * (FreeGroup.of x)⁻¹) x))⁻¹ *
        representativeTauList (p * (FreeGroup.of x)⁻¹) xs

omit [DecidableEq X] in
/-- The representative \(\tau\)-list rewrite is unchanged when adjacent inverse letters cancel. -/
@[simp]
theorem representativeTauList_cons_true_false
    (p : FreeGroup X) (x : X) (xs : List (X × Bool)) :
    representativeTauList S p ((x, true) :: (x, false) :: xs) =
      representativeTauList S p xs := by
  simp only [representativeTauList, representativeLabel, mul_inv_cancel_right, mul_inv_cancel_left]

omit [DecidableEq X] in
/-- The representative \(\tau\)-list rewrite is unchanged when adjacent inverse letters cancel. -/
@[simp]
theorem representativeTauList_cons_false_true
    (p : FreeGroup X) (x : X) (xs : List (X × Bool)) :
    representativeTauList S p ((x, false) :: (x, true) :: xs) =
      representativeTauList S p xs := by
  simp only [representativeTauList, representativeLabel, inv_mul_cancel_right, inv_mul_cancel_left]

omit [DecidableEq X] in
/-- The representative \(\tau\)-list rewrite is unchanged when adjacent inverse letters cancel. -/
@[simp]
theorem representativeTauList_cons_cancel
    (p : FreeGroup X) (x : X) (b : Bool) (xs : List (X × Bool)) :
    representativeTauList S p ((x, b) :: (x, !b) :: xs) =
      representativeTauList S p xs := by
  cases b
  · exact representativeTauList_cons_false_true (S := S) p x xs
  · exact representativeTauList_cons_true_false (S := S) p x xs

omit [DecidableEq X] in
/--
The representative \(\tau\)-list rewrite of a concatenated word splits as the product of the
first rewrite and the rewrite of the second word from the updated quotient element.
-/
theorem representativeTauList_append
    (p : FreeGroup X) (xs ys : List (X × Bool)) :
    representativeTauList S p (xs ++ ys) =
      representativeTauList S p xs *
        representativeTauList S (p * FreeGroup.mk xs) ys := by
  induction xs generalizing p with
  | nil =>
      rw [← FreeGroup.one_eq_mk]
      simp only [List.nil_append, representativeTauList, mul_one, one_mul]
  | cons hd xs ih =>
      rcases hd with ⟨x, eps⟩
      cases eps
      · simp only [List.cons_append, representativeTauList, ih, mul_assoc, mk_cons_false]
      · simp only [List.cons_append, representativeTauList, ih, mul_assoc, mk_cons_true]

omit [DecidableEq X] in
/-- Representative \(\tau\)-list rewrites agree for starting words in the same right coset. -/
theorem representativeTauList_eq_of_sameRightCoset
    {p q : FreeGroup X} (hpq : p * q⁻¹ ∈ L)
    (xs : List (X × Bool)) :
    representativeTauList S p xs = representativeTauList S q xs := by
  induction xs generalizing p q with
  | nil =>
      simp only [representativeTauList]
  | cons hd xs ih =>
      rcases hd with ⟨x, eps⟩
      cases eps
      · have hstep :
            (p * (FreeGroup.of x)⁻¹) *
                (q * (FreeGroup.of x)⁻¹)⁻¹ ∈ L := by
          convert hpq using 1
          group
        have hlabel :
            representativeLabel S (p * (FreeGroup.of x)⁻¹) x =
              representativeLabel S (q * (FreeGroup.of x)⁻¹) x := by
          simp only [representativeLabel, S.representative_eq_of_sameRightCoset hstep]
        simp only [representativeTauList, hlabel, ih hstep]
      · have hstep :
            (p * FreeGroup.of x) * (q * FreeGroup.of x)⁻¹ ∈ L := by
          convert hpq using 1
          group
        have hlabel :
            representativeLabel S p x = representativeLabel S q x := by
          simp only [representativeLabel, S.representative_eq_of_sameRightCoset hpq]
        simp only [representativeTauList, hlabel, ih hstep]

omit [DecidableEq X] in
/-- A single free-group reduction step does not change the representative \(\tau\)-list rewrite. -/
theorem representativeTauList_redStep
    (p : FreeGroup X) {xs ys : List (X × Bool)}
    (h : FreeGroup.Red.Step xs ys) :
    representativeTauList S p xs = representativeTauList S p ys := by
  cases h with
  | not =>
      rw [representativeTauList_append, representativeTauList_append]
      simp only [representativeTauList_cons_cancel]

omit [DecidableEq X] in
/-- Free-group reduction does not change the representative \(\tau\)-list rewrite. -/
theorem representativeTauList_red
    (p : FreeGroup X) {xs ys : List (X × Bool)}
    (h : FreeGroup.Red xs ys) :
    representativeTauList S p xs = representativeTauList S p ys := by
  induction h with
  | refl =>
      rfl
  | tail _ hstep ih =>
      exact ih.trans (representativeTauList_redStep (S := S) p hstep)

omit [DecidableEq X] in
/--
Equal free-group words have equal the representative \(\tau\)-list rewrites from the same
starting quotient element.
-/
theorem representativeTauList_eq_of_mk_eq
    (p : FreeGroup X) {xs ys : List (X × Bool)}
    (h : FreeGroup.mk xs = FreeGroup.mk ys) :
    representativeTauList S p xs = representativeTauList S p ys := by
  rcases FreeGroup.Red.exact.1 h with ⟨zs, hxs, hys⟩
  exact (representativeTauList_red (S := S) p hxs).trans
    (representativeTauList_red (S := S) p hys).symm

omit [DecidableEq X] in
/-- Evaluating a \(\tau\)-list gives the quotient-section conjugate of the represented word. -/
@[simp 900]
theorem representativeSymbolEvalHom_representativeTauList
    (p : FreeGroup X) (xs : List (X × Bool)) :
    representativeSymbolEvalHom S (representativeTauList S p xs) =
      S.representative p * FreeGroup.mk xs *
        (S.representative (p * FreeGroup.mk xs))⁻¹ := by
  induction xs generalizing p with
  | nil =>
      simp only [representativeTauList, map_one]
      change 1 = S.representative p * 1 * (S.representative (p * 1))⁻¹
      simp only [mul_one, mul_inv_cancel]
  | cons hd xs ih =>
      rcases hd with ⟨x, eps⟩
      cases eps
      · simp only [representativeTauList, representativeLabel, map_mul, map_inv,
          representativeSymbolEvalHom_of,
  representativeSymbolEval, representativeSchreierGenerator,
  RightSchreierRepresentative.representative_inv_generator_mul_generator_eq, mul_assoc,
      mul_inv_rev, inv_inv, ih,
  inv_mul_cancel_left, mk_cons_false]
      · simp only [representativeTauList, representativeLabel, map_mul,
          representativeSymbolEvalHom_of,
  representativeSymbolEval, representativeSchreierGenerator,
  RightSchreierRepresentative.representative_mul_generator_eq, mul_assoc, ih,
      inv_mul_cancel_left, mk_cons_true]

/--
The representative \(\tau\)-map applies the explicit Schreier rewriting procedure to free-group
elements.
-/
def representativeTau (t w : FreeGroup X) :
    FreeGroup (RepresentativeSchreierSymbol S) :=
  representativeTauList S t w.toWord

/-- Rewriting the identity word by the representative \(\tau\)-map gives the identity. -/
@[simp]
theorem representativeTau_one (t : FreeGroup X) :
    representativeTau S t 1 = 1 := by
  simp only [representativeTau, FreeGroup.toWord_one, representativeTauList]

/--
The representative \(\tau\)-rewrite of \(\mathrm{FreeGroup.mk}(xs)\) agrees with rewriting the
list \(xs\).
-/
theorem representativeTau_mk
    (t : FreeGroup X) (xs : List (X × Bool)) :
    representativeTau S t (FreeGroup.mk xs) =
      representativeTauList S t xs := by
  rw [representativeTau, FreeGroup.toWord_mk]
  exact (representativeTauList_red (S := S) t FreeGroup.reduce.red).symm

/-- Evaluating a \(\tau\)-word gives the quotient-section conjugate of the rewritten word. -/
theorem representativeSymbolEvalHom_tau
    (t w : FreeGroup X) :
    representativeSymbolEvalHom S (representativeTau S t w) =
      S.representative t * w * (S.representative (t * w))⁻¹ := by
  simp only [representativeTau, representativeSymbolEvalHom_representativeTauList,
      FreeGroup.mk_toWord]

/--
The representative \(\tau\)-rewrite of a product factors into the rewrite of the first word and
the rewrite of the second word from the updated quotient element.
-/
theorem representativeTau_mul
    (t u v : FreeGroup X) :
    representativeTau S t (u * v) =
      representativeTau S t u * representativeTau S (t * u) v := by
  calc
    representativeTau S t (u * v) =
        representativeTau S t (FreeGroup.mk (u.toWord ++ v.toWord)) := by
          rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
    _ = representativeTauList S t (u.toWord ++ v.toWord) :=
        representativeTau_mk (S := S) t (u.toWord ++ v.toWord)
    _ =
        representativeTauList S t u.toWord *
          representativeTauList S (t * FreeGroup.mk u.toWord) v.toWord := by
          rw [representativeTauList_append]
    _ = representativeTau S t u * representativeTau S (t * u) v := by
          simp only [FreeGroup.mk_toWord, representativeTau]

/-- Representative \(\tau\)-words agree for group elements in the same right coset. -/
theorem representativeTau_eq_of_sameRightCoset
    {p q : FreeGroup X} (hpq : p * q⁻¹ ∈ L)
    (w : FreeGroup X) :
    representativeTau S p w = representativeTau S q w :=
  representativeTauList_eq_of_sameRightCoset (S := S) hpq w.toWord

/--
If the initial word lies in the Schreier subgroup, its representative \(\tau\)-rewrite agrees
with the rewrite starting at the identity.
-/
theorem representativeTau_eq_one_start_of_mem
    {p : FreeGroup X} (hp : p ∈ L) (w : FreeGroup X) :
    representativeTau S p w = representativeTau S 1 w := by
  exact representativeTau_eq_of_sameRightCoset (S := S) (by simpa using hp) w

/--
For a kernel word, the representative \(\tau\)-rewriting preserves products from the identity
quotient element.
-/
theorem representativeTau_mul_of_mem
    {u v : FreeGroup X} (hu : u ∈ L) :
    representativeTau S 1 (u * v) =
      representativeTau S 1 u * representativeTau S 1 v := by
  rw [representativeTau_mul]
  have hstart :
      representativeTau S (1 * u) v = representativeTau S 1 v := by
    simpa using representativeTau_eq_one_start_of_mem (S := S) hu v
  rw [hstart]

/--
The representative \(\tau\)-rewrite of an inverse is the inverse of the \(\tau\)-rewrite from
the updated quotient element.
-/
theorem representativeTau_inv (t u : FreeGroup X) :
    representativeTau S (t * u) u⁻¹ =
      (representativeTau S t u)⁻¹ := by
  have hmul :
      representativeTau S t u * representativeTau S (t * u) u⁻¹ = 1 := by
    simpa using (representativeTau_mul (S := S) t u u⁻¹).symm
  calc
    representativeTau S (t * u) u⁻¹ =
        1 * representativeTau S (t * u) u⁻¹ := by simp only [one_mul]
    _ =
        ((representativeTau S t u)⁻¹ * representativeTau S t u) *
          representativeTau S (t * u) u⁻¹ := by simp only [one_mul, inv_mul_cancel]
    _ =
        (representativeTau S t u)⁻¹ *
          (representativeTau S t u *
            representativeTau S (t * u) u⁻¹) := by group
    _ = (representativeTau S t u)⁻¹ := by
          rw [hmul]
          simp only [mul_one]

/--
For a kernel word, the representative \(\tau\)-rewriting commutes with inversion from the
identity quotient element.
-/
theorem representativeTau_inv_of_mem
    {u : FreeGroup X} (hu : u ∈ L) :
    representativeTau S 1 u⁻¹ = (representativeTau S 1 u)⁻¹ := by
  rw [← representativeTau_eq_one_start_of_mem (S := S) hu u⁻¹]
  simpa using representativeTau_inv (S := S) 1 u

/--
For a word in the Schreier subgroup, evaluating its representative \(\tau\)-rewrite from the
identity recovers that word.
-/
theorem representativeSymbolEvalHom_tau_one_of_mem
    {w : FreeGroup X} (hw : w ∈ L) :
    representativeSymbolEvalHom S (representativeTau S 1 w) = w := by
  have hwrep : S.representative w = 1 := S.representative_eq_one_of_mem hw
  simpa [RightSchreierRepresentative.representative_one, hwrep] using
    representativeSymbolEvalHom_tau (S := S) (t := 1) (w := w)

omit [DecidableEq X] in
/-- Applying the representative-selection map twice gives the same representative. -/
theorem representative_representative (g : FreeGroup X) :
    S.representative (S.representative g) = S.representative g := by
  apply S.representative_eq_of_sameRightCoset
  exact S.representative_mul_inv_mem g

omit [DecidableEq X] in
/-- An element of the representative set is fixed by the representative-selection map. -/
theorem representative_eq_self_of_mem_representativeSet
    {t : FreeGroup X} (ht : t ∈ representativeSet S) :
    S.representative t = t := by
  rcases ht with ⟨g, rfl⟩
  exact representative_representative (S := S) g

/-- The representative \(\tau\) of a chosen representative is trivial in the Schreier rewriting. -/
theorem representativeTau_of_representative
    (t : representativeSet S) (x : X) :
    representativeTau S (t : FreeGroup X) (FreeGroup.of x) =
      FreeGroup.of (t, x) := by
  have ht : S.representative (t : FreeGroup X) = (t : FreeGroup X) :=
    representative_eq_self_of_mem_representativeSet (S := S) t.property
  simp only [representativeTau, FreeGroup.toWord_of, representativeTauList, representativeLabel, ht,
  Subtype.coe_eta, mul_one]

/--
The representative Schreier relators are the rewrites of the original relators over the chosen
representative transversal.
-/
def representativeSchreierRelators
    (R : Set (FreeGroup X)) :
    Set (FreeGroup (RepresentativeSchreierSymbol S)) :=
  { q | ∃ t : representativeSet S, ∃ r ∈ R,
      q = representativeTau S (t : FreeGroup X) r }

/--
The representative degenerate Schreier relators are the section relators forced by the
representative transversal.
-/
def representativeDegenerateSchreierRelators :
    Set (FreeGroup (RepresentativeSchreierSymbol S)) :=
  { q | ∃ t : representativeSet S, ∃ x : X,
      S.representative ((t : FreeGroup X) * FreeGroup.of x) =
        (t : FreeGroup X) * FreeGroup.of x ∧
      q = FreeGroup.of (t, x) }

/--
The representative presentation relators are the rewritten original relators together with
degenerate Schreier-generator relators.
-/
def representativePresentationRelators
    (R : Set (FreeGroup X)) :
    Set (FreeGroup (RepresentativeSchreierSymbol S)) :=
  representativeSchreierRelators S R ∪
    representativeDegenerateSchreierRelators S

/--
These extra relators kill the rewrites of the chosen representatives. They are redundant for
prefix-closed Schreier systems, but are needed for an arbitrary normalized representative
function.
-/
def representativeSectionRelators :
    Set (FreeGroup (RepresentativeSchreierSymbol S)) :=
  { q | ∃ t : representativeSet S,
      q = representativeTau S 1 (t : FreeGroup X) }

/--
The augmented representative presentation relators consist of the representative presentation
relators together with the section relators.
-/
def representativeAugmentedPresentationRelators
    (R : Set (FreeGroup X)) :
    Set (FreeGroup (RepresentativeSchreierSymbol S)) :=
  representativePresentationRelators S R ∪ representativeSectionRelators S

/--
Prefix-closedness along a concrete representative word. Positive letters say the next prefix is
itself a representative; negative letters say the current prefix is obtained from the previous
representative by appending the positive letter.
-/
def representativePrefixClosedAlongList (S : RightSchreierRepresentative L) :
    FreeGroup X → List (X × Bool) → Prop
  | _p, [] => True
  | p, (x, true) :: xs =>
      S.representative (S.representative p * FreeGroup.of x) =
        S.representative p * FreeGroup.of x ∧
      representativePrefixClosedAlongList S (p * FreeGroup.of x) xs
  | p, (x, false) :: xs =>
      S.representative p =
        S.representative (p * (FreeGroup.of x)⁻¹) * FreeGroup.of x ∧
      representativePrefixClosedAlongList S (p * (FreeGroup.of x)⁻¹) xs

/-- The representative system is prefix closed on its own representative words. -/
def IsPrefixClosedRepresentativeSystem : Prop :=
  ∀ t : representativeSet S,
    representativePrefixClosedAlongList S 1 (t : FreeGroup X).toWord

/--
The representative \(\tau\)-rewrite of an original relator belongs to the representative
Schreier relator set.
-/
theorem representativeTau_mem_schreierRelators
    {R : Set (FreeGroup X)}
    (t : representativeSet S) {r : FreeGroup X} (hr : r ∈ R) :
    representativeTau S (t : FreeGroup X) r ∈
      representativeSchreierRelators S R :=
  ⟨t, r, hr, rfl⟩

/--
The representative \(\tau\)-rewrite of a quotient-section word belongs to the representative
section-relator set.
-/
theorem representativeTau_mem_sectionRelators
    (t : representativeSet S) :
    representativeTau S 1 (t : FreeGroup X) ∈
      representativeSectionRelators S :=
  ⟨t, rfl⟩

/--
Every representative presentation relator is an augmented representative presentation relator.
-/
theorem representativePresentationRelators_subset_augmented
    (R : Set (FreeGroup X)) :
    representativePresentationRelators S R ⊆
      representativeAugmentedPresentationRelators S R :=
  fun _ hq => Or.inl hq

/--
Every representative section relator is included among the augmented representative presentation
relators.
-/
theorem representativeSectionRelators_subset_augmented
    (R : Set (FreeGroup X)) :
    representativeSectionRelators S ⊆
      representativeAugmentedPresentationRelators S R :=
  fun _ hq => Or.inr hq

omit [DecidableEq X] in
/--
A list following the prefix-closed representative system rewrites into the normal closure of the
degenerate representative Schreier relators.
-/
theorem representativeTauList_mem_normalClosure_degenerate_of_prefixClosedAlongList
    {p : FreeGroup X} {xs : List (X × Bool)}
    (hprefix : representativePrefixClosedAlongList S p xs) :
    representativeTauList S p xs ∈
      Subgroup.normalClosure (representativeDegenerateSchreierRelators S) := by
  induction xs generalizing p with
  | nil =>
      simp only [representativeTauList, one_mem]
  | cons hd xs ih =>
      rcases hd with ⟨x, eps⟩
      cases eps
      · rcases hprefix with ⟨hstep, htail⟩
        have hgenerator :
            FreeGroup.of
                (representativeLabel S (p * (FreeGroup.of x)⁻¹) x) ∈
              representativeDegenerateSchreierRelators S := by
          refine ⟨⟨S.representative (p * (FreeGroup.of x)⁻¹),
              ⟨p * (FreeGroup.of x)⁻¹, rfl⟩⟩, x, ?_, rfl⟩
          rw [← hstep]
          exact representative_representative (S := S) p
        exact Subgroup.mul_mem
          (Subgroup.normalClosure (representativeDegenerateSchreierRelators S))
          (Subgroup.inv_mem _
            (Subgroup.subset_normalClosure hgenerator))
          (ih htail)
      · rcases hprefix with ⟨hstep, htail⟩
        have hgenerator :
            FreeGroup.of (representativeLabel S p x) ∈
              representativeDegenerateSchreierRelators S :=
          ⟨⟨S.representative p, ⟨p, rfl⟩⟩, x, hstep, rfl⟩
        exact Subgroup.mul_mem
          (Subgroup.normalClosure (representativeDegenerateSchreierRelators S))
          (Subgroup.subset_normalClosure hgenerator)
          (ih htail)

/--
The \(\tau\)-rewrite of the indicated relator or section word belongs to the appropriate
Reidemeister--Schreier normal closure.
-/
theorem representativeTau_section_mem_normalClosure_degenerate_of_isPrefixClosed
    (hprefix : IsPrefixClosedRepresentativeSystem S)
    (t : representativeSet S) :
    representativeTau S 1 (t : FreeGroup X) ∈
      Subgroup.normalClosure (representativeDegenerateSchreierRelators S) := by
  simpa [representativeTau] using
    representativeTauList_mem_normalClosure_degenerate_of_prefixClosedAlongList
      (S := S) (hprefix t)

/--
The \(\tau\)-rewrite of the indicated relator or section word belongs to the appropriate
Reidemeister--Schreier normal closure.
-/
theorem representativeTau_section_mem_normalClosure_presentation_of_isPrefixClosed
    (R : Set (FreeGroup X))
    (hprefix : IsPrefixClosedRepresentativeSystem S)
    (t : representativeSet S) :
    representativeTau S 1 (t : FreeGroup X) ∈
      Subgroup.normalClosure (representativePresentationRelators S R) :=
  Subgroup.normalClosure_mono
    (fun _ hq => Or.inr hq)
    (representativeTau_section_mem_normalClosure_degenerate_of_isPrefixClosed
      (S := S) hprefix t)

/--
Evaluating the representative \(\tau\)-rewrite of an original relator gives an element of the
normal closure of the original relators.
-/
theorem representativeSymbolEvalHom_tau_relator_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (t : representativeSet S) {r : FreeGroup X} (hr : r ∈ R) :
    representativeSymbolEvalHom S
        (representativeTau S (t : FreeGroup X) r) ∈
      Subgroup.normalClosure R := by
  have ht : S.representative (t : FreeGroup X) = (t : FreeGroup X) :=
    representative_eq_self_of_mem_representativeSet (S := S) t.property
  have hrep :
      S.representative ((t : FreeGroup X) * r) = (t : FreeGroup X) := by
    simpa [ht] using
      representative_mul_relator_eq (S := S) hR (t : FreeGroup X) hr
  have hconj :
      (t : FreeGroup X) * r * (t : FreeGroup X)⁻¹ ∈
        Subgroup.normalClosure R :=
    conjugate_mem_normalClosure_of_mem (R := R) hr (t : FreeGroup X)
  simpa [representativeSymbolEvalHom_tau, ht, hrep, mul_assoc] using hconj

/--
Evaluating a representative Schreier relator gives an element of the normal closure of the
original relators.
-/
theorem representativeEval_schreierRelator_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (RepresentativeSchreierSymbol S)}
    (hq : q ∈ representativeSchreierRelators S R) :
    representativeSymbolEvalHom S q ∈ Subgroup.normalClosure R := by
  rcases hq with ⟨t, r, hr, rfl⟩
  exact representativeSymbolEvalHom_tau_relator_mem_normalClosure
    (S := S) hR t hr

omit [DecidableEq X] in
/-- The evaluation of a representative degenerate Schreier relator is the identity. -/
theorem representativeDegenerateRelator_eval_eq_one
    {q : FreeGroup (RepresentativeSchreierSymbol S)}
    (hq : q ∈ representativeDegenerateSchreierRelators S) :
    representativeSymbolEvalHom S q = 1 := by
  rcases hq with ⟨t, x, htx, rfl⟩
  simp only [representativeSymbolEvalHom_of, representativeSymbolEval,
      representativeSchreierGenerator, htx,
  mul_inv_rev]
  group

omit [DecidableEq X] in
/--
The indicated evaluated relator belongs to the normal closure supplied by the
Reidemeister--Schreier relator comparison.
-/
theorem representativeEval_degenerateRelator_mem_normalClosure
    {R : Set (FreeGroup X)}
    {q : FreeGroup (RepresentativeSchreierSymbol S)}
    (hq : q ∈ representativeDegenerateSchreierRelators S) :
    representativeSymbolEvalHom S q ∈ Subgroup.normalClosure R := by
  simp only [representativeDegenerateRelator_eval_eq_one (S := S) hq, one_mem]

/-- The evaluation of a representative section relator is the identity. -/
theorem representativeSectionRelator_eval_eq_one
    {q : FreeGroup (RepresentativeSchreierSymbol S)}
    (hq : q ∈ representativeSectionRelators S) :
    representativeSymbolEvalHom S q = 1 := by
  rcases hq with ⟨t, rfl⟩
  have ht : S.representative (t : FreeGroup X) = (t : FreeGroup X) :=
    representative_eq_self_of_mem_representativeSet (S := S) t.property
  simpa [RightSchreierRepresentative.representative_one, ht] using
    representativeSymbolEvalHom_tau
      (S := S) (t := 1) (w := (t : FreeGroup X))

/--
The indicated evaluated relator belongs to the normal closure supplied by the
Reidemeister--Schreier relator comparison.
-/
theorem representativeEval_sectionRelator_mem_normalClosure
    {R : Set (FreeGroup X)}
    {q : FreeGroup (RepresentativeSchreierSymbol S)}
    (hq : q ∈ representativeSectionRelators S) :
    representativeSymbolEvalHom S q ∈ Subgroup.normalClosure R := by
  simp only [representativeSectionRelator_eval_eq_one (S := S) hq, one_mem]

/--
Evaluating a representative presentation relator gives an element of the normal closure of the
original relators.
-/
theorem representativeEval_presentationRelator_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (RepresentativeSchreierSymbol S)}
    (hq : q ∈ representativePresentationRelators S R) :
    representativeSymbolEvalHom S q ∈ Subgroup.normalClosure R := by
  rcases hq with hq | hq
  · exact representativeEval_schreierRelator_mem_normalClosure (S := S) hR hq
  · exact representativeEval_degenerateRelator_mem_normalClosure (S := S) hq

/--
The indicated evaluated relator belongs to the normal closure supplied by the
Reidemeister--Schreier relator comparison.
-/
theorem representativeEval_augmentedRelator_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (RepresentativeSchreierSymbol S)}
    (hq : q ∈ representativeAugmentedPresentationRelators S R) :
    representativeSymbolEvalHom S q ∈ Subgroup.normalClosure R := by
  rcases hq with hq | hq
  · exact representativeEval_presentationRelator_mem_normalClosure (S := S) hR hq
  · exact representativeEval_sectionRelator_mem_normalClosure (S := S) hq

/--
Evaluation sends the normal closure of the augmented representative presentation relators into
the normal closure of the original relators.
-/
theorem representativeEval_mem_normalClosure_of_mem_normalClosure_augmentedRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (RepresentativeSchreierSymbol S)}
    (hq : q ∈
      Subgroup.normalClosure (representativeAugmentedPresentationRelators S R)) :
    representativeSymbolEvalHom S q ∈ Subgroup.normalClosure R :=
  map_mem_normalClosure_of_relators (representativeSymbolEvalHom S)
    (fun _ hr =>
      representativeEval_augmentedRelator_mem_normalClosure (S := S) hR hr) hq

/--
The subgroup-valued evaluation map sends the normal closure of the augmented representative
presentation relators into the relator subgroup.
-/
theorem representativeSymbolEvalSubgroupHom_mem_relatorSubgroup_of_mem_normalClosure_augmented
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {q : FreeGroup (RepresentativeSchreierSymbol S)}
    (hq : q ∈
      Subgroup.normalClosure (representativeAugmentedPresentationRelators S R)) :
    representativeSymbolEvalSubgroupHom S q ∈ relatorSubgroup (L := L) R := by
  change representativeSymbolEvalHom S q ∈ Subgroup.normalClosure R
  exact representativeEval_mem_normalClosure_of_mem_normalClosure_augmentedRelators
    (S := S) hR hq

/--
The evaluation map from the representative augmented presentation quotient to the
relator-subgroup quotient of the subgroup.
-/
noncomputable def representativeSymbolEvalAugmentedPresentationQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L) :
    FreeGroup (RepresentativeSchreierSymbol S) ⧸
        Subgroup.normalClosure (representativeAugmentedPresentationRelators S R) →*
      L ⧸ relatorSubgroup (L := L) R :=
  QuotientGroup.lift
    (Subgroup.normalClosure (representativeAugmentedPresentationRelators S R))
    ((QuotientGroup.mk' (relatorSubgroup (L := L) R)).comp
      (representativeSymbolEvalSubgroupHom S))
    (by
      intro q hq
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff
        (N := relatorSubgroup (L := L) R)
        (representativeSymbolEvalSubgroupHom S q)).2
        (representativeSymbolEvalSubgroupHom_mem_relatorSubgroup_of_mem_normalClosure_augmented
          (S := S) hR hq))

/--
The \(\tau\)-rewrite of the indicated relator or section word belongs to the appropriate
Reidemeister--Schreier normal closure.
-/
theorem representativeTau_conjugate_relator_mem_normalClosure_schreierRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (g : FreeGroup X) {r : FreeGroup X} (hr : r ∈ R) :
    representativeTau S 1 (g * r * g⁻¹) ∈
      Subgroup.normalClosure (representativeSchreierRelators S R) := by
  let t : representativeSet S := ⟨S.representative g, ⟨g, rfl⟩⟩
  have hgrL :
      (g * r) * g⁻¹ ∈ L := by
    exact hR (by
      simpa [mul_assoc] using
        conjugate_mem_normalClosure_of_mem (R := R) hr g)
  have hstate :
      representativeTau S (g * r) g⁻¹ =
        representativeTau S g g⁻¹ :=
    representativeTau_eq_of_sameRightCoset (S := S) hgrL g⁻¹
  have hinv :
      representativeTau S g g⁻¹ =
        (representativeTau S 1 g)⁻¹ := by
    simpa using representativeTau_inv (S := S) 1 g
  have hstart :
      representativeTau S g r =
        representativeTau S (S.representative g) r :=
    representativeTau_eq_of_sameRightCoset (S := S) (S.sameRightCoset g) r
  have hrel :
      representativeTau S (S.representative g) r ∈
        Subgroup.normalClosure (representativeSchreierRelators S R) :=
    Subgroup.subset_normalClosure
      (representativeTau_mem_schreierRelators (S := S) t hr)
  have hrelg :
      representativeTau S g r ∈
        Subgroup.normalClosure (representativeSchreierRelators S R) := by
    simpa [hstart] using hrel
  have hdecomp :
      representativeTau S 1 (g * r * g⁻¹) =
        representativeTau S 1 g * representativeTau S g r *
          (representativeTau S 1 g)⁻¹ := by
    calc
      representativeTau S 1 (g * r * g⁻¹) =
          representativeTau S 1 (g * (r * g⁻¹)) := by
            rw [mul_assoc]
      _ =
          representativeTau S 1 g *
            representativeTau S (1 * g) (r * g⁻¹) := by
            rw [representativeTau_mul]
      _ =
          representativeTau S 1 g *
            (representativeTau S g r *
              representativeTau S (g * r) g⁻¹) := by
            simp only [one_mul, representativeTau_mul]
      _ =
          representativeTau S 1 g *
            (representativeTau S g r *
              (representativeTau S 1 g)⁻¹) := by
            rw [hstate, hinv]
      _ =
          representativeTau S 1 g * representativeTau S g r *
            (representativeTau S 1 g)⁻¹ := by
            group
  have hconj :
      representativeTau S 1 g * representativeTau S g r *
          (representativeTau S 1 g)⁻¹ ∈
        Subgroup.normalClosure (representativeSchreierRelators S R) :=
    conjugate_mem_normalClosure
      (R := representativeSchreierRelators S R) hrelg
      (representativeTau S 1 g)
  rw [hdecomp]
  exact hconj

/--
The \(\tau\)-rewrite of the indicated relator or section word belongs to the appropriate
Reidemeister--Schreier normal closure.
-/
theorem representativeTau_conjugate_relator_mem_normalClosure_presentationRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (g : FreeGroup X) {r : FreeGroup X} (hr : r ∈ R) :
    representativeTau S 1 (g * r * g⁻¹) ∈
      Subgroup.normalClosure (representativePresentationRelators S R) :=
  Subgroup.normalClosure_mono
    (fun _ hq => Or.inl hq)
    (representativeTau_conjugate_relator_mem_normalClosure_schreierRelators
      (S := S) hR g hr)

/--
The \(\tau\)-rewrite of the indicated relator or section word belongs to the appropriate
Reidemeister--Schreier normal closure.
-/
theorem representativeTau_conjugate_relator_mem_normalClosure_augmentedRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (g : FreeGroup X) {r : FreeGroup X} (hr : r ∈ R) :
    representativeTau S 1 (g * r * g⁻¹) ∈
      Subgroup.normalClosure (representativeAugmentedPresentationRelators S R) :=
  Subgroup.normalClosure_mono
    (representativePresentationRelators_subset_augmented (S := S) R)
    (representativeTau_conjugate_relator_mem_normalClosure_presentationRelators
      (S := S) hR g hr)

/--
The representative \(\tau\)-homomorphism from the kernel to the augmented presentation quotient
is defined by Reidemeister--Schreier rewriting.
-/
noncomputable def representativeTauKernelAugmentedPresentationQuotientHom
    (R : Set (FreeGroup X)) :
    L →* FreeGroup (RepresentativeSchreierSymbol S) ⧸
      Subgroup.normalClosure (representativeAugmentedPresentationRelators S R) where
  toFun k :=
    QuotientGroup.mk'
      (Subgroup.normalClosure (representativeAugmentedPresentationRelators S R))
      (representativeTau S 1 (k : FreeGroup X))
  map_one' := by
    simp only [OneMemClass.coe_one, representativeTau_one, QuotientGroup.mk'_apply,
        QuotientGroup.mk_one]
  map_mul' k l := by
    change
      QuotientGroup.mk'
          (Subgroup.normalClosure (representativeAugmentedPresentationRelators S R))
          (representativeTau S 1 ((k : FreeGroup X) * (l : FreeGroup X))) =
        QuotientGroup.mk'
          (Subgroup.normalClosure (representativeAugmentedPresentationRelators S R))
          (representativeTau S 1 (k : FreeGroup X)) *
        QuotientGroup.mk'
          (Subgroup.normalClosure (representativeAugmentedPresentationRelators S R))
          (representativeTau S 1 (l : FreeGroup X))
    rw [representativeTau_mul_of_mem (S := S) k.property]
    rfl

/--
The representative \(\tau\)-homomorphism to the augmented-presentation quotient kills every
element of the normal closure of the original relators.
-/
theorem representativeTauKernelAugmentedPresentationQuotientHom_eq_one_of_mem_normalClosure
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    {n : FreeGroup X} (hn : n ∈ Subgroup.normalClosure R) :
    representativeTauKernelAugmentedPresentationQuotientHom (S := S) R
      ⟨n, hR hn⟩ = 1 := by
  let killedSubgroup : Subgroup (FreeGroup X) :=
    { carrier :=
        {n | ∃ hnL : n ∈ L,
          representativeTauKernelAugmentedPresentationQuotientHom (S := S) R
            ⟨n, hnL⟩ = 1}
      one_mem' := by
        refine ⟨L.one_mem, ?_⟩
        change
          representativeTauKernelAugmentedPresentationQuotientHom (S := S) R
            (1 : L) = 1
        exact (representativeTauKernelAugmentedPresentationQuotientHom
          (S := S) R).map_one
      mul_mem' := by
        intro a b ha hb
        rcases ha with ⟨haL, haone⟩
        rcases hb with ⟨hbL, hbone⟩
        refine ⟨L.mul_mem haL hbL, ?_⟩
        have hmul :=
          (representativeTauKernelAugmentedPresentationQuotientHom
            (S := S) R).map_mul ⟨a, haL⟩ ⟨b, hbL⟩
        simpa [haone, hbone] using hmul
      inv_mem' := by
        intro a ha
        rcases ha with ⟨haL, haone⟩
        refine ⟨L.inv_mem haL, ?_⟩
        change
          representativeTauKernelAugmentedPresentationQuotientHom (S := S) R
              (⟨a, haL⟩ : L)⁻¹ = 1
        rw [(representativeTauKernelAugmentedPresentationQuotientHom
          (S := S) R).map_inv, haone]
        simp only [inv_one]}
  have hclosure : Subgroup.normalClosure R ≤ killedSubgroup := by
    rw [Subgroup.normalClosure]
    rw [Subgroup.closure_le]
    intro x hx
    have hxN : x ∈ Subgroup.normalClosure R :=
      Subgroup.conjugatesOfSet_subset_normalClosure hx
    refine ⟨hR hxN, ?_⟩
    change
      QuotientGroup.mk'
          (Subgroup.normalClosure
            (representativeAugmentedPresentationRelators S R))
          (representativeTau S 1 x) = 1
    rcases Group.mem_conjugatesOfSet_iff.1 hx with ⟨r, hr, hconj⟩
    rcases isConj_iff.1 hconj with ⟨g, rfl⟩
    exact (QuotientGroup.eq_one_iff
      (N := Subgroup.normalClosure
        (representativeAugmentedPresentationRelators S R))
      (representativeTau S 1 (g * r * g⁻¹))).2
      (representativeTau_conjugate_relator_mem_normalClosure_augmentedRelators
        (S := S) hR g hr)
  rcases hclosure hn with ⟨hnL, hone⟩
  simpa using hone

/--
The quotient homomorphism induced by \(\tau\)-rewriting maps the relator subgroup quotient to
the augmented Schreier-presentation quotient.
-/
noncomputable def representativeTauRelatorSubgroupAugmentedPresentationQuotientHom
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L) :
    L ⧸ relatorSubgroup (L := L) R →*
      FreeGroup (RepresentativeSchreierSymbol S) ⧸
        Subgroup.normalClosure (representativeAugmentedPresentationRelators S R) :=
  QuotientGroup.lift
    (relatorSubgroup (L := L) R)
    (representativeTauKernelAugmentedPresentationQuotientHom (S := S) R)
    (by
      intro k hk
      rw [MonoidHom.mem_ker]
      change
        representativeTauKernelAugmentedPresentationQuotientHom (S := S) R k = 1
      have hk' : (k : FreeGroup X) ∈ Subgroup.normalClosure R := hk
      simpa using
        (representativeTauKernelAugmentedPresentationQuotientHom_eq_one_of_mem_normalClosure
          (S := S) hR hk'))

/--
A representative section relator is relator-equivalent to the identity modulo the augmented
presentation relators.
-/
theorem representativeSectionRelator_relatorEquivalent_one
    (R : Set (FreeGroup X)) (t : representativeSet S) :
    RelatorEquivalent (representativeAugmentedPresentationRelators S R)
      (representativeTau S 1 (t : FreeGroup X)) 1 :=
  RelatorEquivalent.of_mem
    (representativeSectionRelators_subset_augmented (S := S) R
      (representativeTau_mem_sectionRelators (S := S) t))

/--
The \(\tau\)-word and its symbol evaluation are relator-equivalent modulo the augmented
presentation relators.
-/
theorem representativeTau_symbolEval_relatorEquivalent_augmented
    (R : Set (FreeGroup X)) (z : RepresentativeSchreierSymbol S) :
    RelatorEquivalent (representativeAugmentedPresentationRelators S R)
      (representativeTau S 1 (representativeSymbolEval S z))
      (FreeGroup.of z) := by
  rcases z with ⟨t, x⟩
  let A : Set (FreeGroup (RepresentativeSchreierSymbol S)) :=
    representativeAugmentedPresentationRelators S R
  let txRepresentative : representativeSet S :=
    ⟨S.representative ((t : FreeGroup X) * FreeGroup.of x),
      ⟨(t : FreeGroup X) * FreeGroup.of x, rfl⟩⟩
  have ht : S.representative (t : FreeGroup X) = (t : FreeGroup X) :=
    representative_eq_self_of_mem_representativeSet (S := S) t.property
  have htailStart :
      representativeTau S ((t : FreeGroup X) * FreeGroup.of x)
          (S.representative ((t : FreeGroup X) * FreeGroup.of x))⁻¹ =
        representativeTau S
          (S.representative ((t : FreeGroup X) * FreeGroup.of x))
          (S.representative ((t : FreeGroup X) * FreeGroup.of x))⁻¹ :=
    representativeTau_eq_of_sameRightCoset
      (S := S) (S.sameRightCoset ((t : FreeGroup X) * FreeGroup.of x))
      (S.representative ((t : FreeGroup X) * FreeGroup.of x))⁻¹
  have htail :
      representativeTau S
          (S.representative ((t : FreeGroup X) * FreeGroup.of x))
          (S.representative ((t : FreeGroup X) * FreeGroup.of x))⁻¹ =
        (representativeTau S 1
          (S.representative ((t : FreeGroup X) * FreeGroup.of x)))⁻¹ := by
    simpa using
      representativeTau_inv
        (S := S) 1
        (S.representative ((t : FreeGroup X) * FreeGroup.of x))
  have hof :
      representativeTau S (t : FreeGroup X) (FreeGroup.of x) =
        FreeGroup.of (t, x) :=
    representativeTau_of_representative (S := S) t x
  have hdecomp :
      representativeTau S 1 (representativeSymbolEval S (t, x)) =
        representativeTau S 1 (t : FreeGroup X) * FreeGroup.of (t, x) *
          (representativeTau S 1
            (S.representative ((t : FreeGroup X) * FreeGroup.of x)))⁻¹ := by
    calc
      representativeTau S 1 (representativeSymbolEval S (t, x)) =
          representativeTau S 1
            ((t : FreeGroup X) *
              (FreeGroup.of x *
                (S.representative
                  ((t : FreeGroup X) * FreeGroup.of x))⁻¹)) := by
            simp only [representativeSymbolEval, representativeSchreierGenerator, mul_assoc]
      _ =
          representativeTau S 1 (t : FreeGroup X) *
            representativeTau S (1 * (t : FreeGroup X))
              (FreeGroup.of x *
                (S.representative
                  ((t : FreeGroup X) * FreeGroup.of x))⁻¹) := by
            rw [representativeTau_mul]
      _ =
          representativeTau S 1 (t : FreeGroup X) *
            representativeTau S (t : FreeGroup X)
              (FreeGroup.of x *
                (S.representative
                  ((t : FreeGroup X) * FreeGroup.of x))⁻¹) := by
            simp only [one_mul]
      _ =
          representativeTau S 1 (t : FreeGroup X) *
            (representativeTau S (t : FreeGroup X) (FreeGroup.of x) *
              representativeTau S
                ((t : FreeGroup X) * FreeGroup.of x)
                (S.representative
                  ((t : FreeGroup X) * FreeGroup.of x))⁻¹) := by
            rw [representativeTau_mul]
      _ =
          representativeTau S 1 (t : FreeGroup X) *
            (FreeGroup.of (t, x) *
              (representativeTau S 1
                (S.representative
                  ((t : FreeGroup X) * FreeGroup.of x)))⁻¹) := by
            rw [hof, htailStart, htail]
      _ =
          representativeTau S 1 (t : FreeGroup X) * FreeGroup.of (t, x) *
            (representativeTau S 1
              (S.representative
                ((t : FreeGroup X) * FreeGroup.of x)))⁻¹ := by
            group
  have hleft :
      RelatorEquivalent A
        (representativeTau S 1 (t : FreeGroup X)) 1 :=
    representativeSectionRelator_relatorEquivalent_one (S := S) R t
  have hright :
      RelatorEquivalent A
        ((representativeTau S 1
          (S.representative ((t : FreeGroup X) * FreeGroup.of x)))⁻¹) 1 := by
    simpa using
      RelatorEquivalent.inv
        (representativeSectionRelator_relatorEquivalent_one
          (S := S) R txRepresentative)
  have hmiddle :
      RelatorEquivalent A (FreeGroup.of (t, x)) (FreeGroup.of (t, x)) :=
    RelatorEquivalent.refl A (FreeGroup.of (t, x))
  have hprod :=
    RelatorEquivalent.mul (RelatorEquivalent.mul hleft hmiddle) hright
  rw [hdecomp]
  simpa [A, mul_assoc] using hprod

/--
The \(\tau\)-word and its symbol evaluation are relator-equivalent modulo the augmented
presentation relators.
-/
theorem representativeTau_symbolEvalHom_relatorEquivalent_augmented
    (R : Set (FreeGroup X))
    (z : FreeGroup (RepresentativeSchreierSymbol S)) :
    RelatorEquivalent (representativeAugmentedPresentationRelators S R)
      (representativeTau S 1 (representativeSymbolEvalHom S z)) z := by
  refine FreeGroup.induction_on z ?one ?of ?inv ?mul
  · exact RelatorEquivalent.refl
      (representativeAugmentedPresentationRelators S R) 1
  · intro y
    simpa using
      representativeTau_symbolEval_relatorEquivalent_augmented (S := S) R y
  · intro y hy
    have hyL : representativeSymbolEval S y ∈ L :=
      representativeSymbolEval_mem (S := S) y
    have hinv :
        representativeTau S 1 (representativeSymbolEval S y)⁻¹ =
          (representativeTau S 1 (representativeSymbolEval S y))⁻¹ :=
      representativeTau_inv_of_mem (S := S) hyL
    simpa [map_inv, hinv] using RelatorEquivalent.inv hy
  · intro y z hy hz
    have hyL : representativeSymbolEvalHom S y ∈ L :=
      representativeSymbolEvalHom_mem (S := S) y
    have hmul :
        representativeTau S 1
            (representativeSymbolEvalHom S (y * z)) =
          representativeTau S 1 (representativeSymbolEvalHom S y) *
            representativeTau S 1 (representativeSymbolEvalHom S z) := by
      simpa [map_mul] using
        representativeTau_mul_of_mem
          (S := S) (v := representativeSymbolEvalHom S z) hyL
    rw [hmul]
    exact RelatorEquivalent.mul hy hz

/-- The \(\tau\)-map sends kernel elements into the augmented Schreier presentation quotient. -/
theorem representativeSymbolEvalAugmentedPresentationQuotientHom_tauKernel
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (k : L) :
    representativeSymbolEvalAugmentedPresentationQuotientHom (S := S) hR
        (representativeTauKernelAugmentedPresentationQuotientHom (S := S) R k) =
      QuotientGroup.mk' (relatorSubgroup (L := L) R) k := by
  change representativeSymbolEvalAugmentedPresentationQuotientHom (S := S) hR
      (QuotientGroup.mk'
        (Subgroup.normalClosure (representativeAugmentedPresentationRelators S R))
        (representativeTau S 1 (k : FreeGroup X))) =
    QuotientGroup.mk' (relatorSubgroup (L := L) R) k
  simp only [representativeSymbolEvalAugmentedPresentationQuotientHom, QuotientGroup.mk'_apply,
  QuotientGroup.lift_mk, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply]
  have hsub :
      representativeSymbolEvalSubgroupHom S
          (representativeTau S 1 (k : FreeGroup X)) = k :=
    Subtype.ext (representativeSymbolEvalHom_tau_one_of_mem (S := S) k.property)
  simpa using congrArg (QuotientGroup.mk' (relatorSubgroup (L := L) R)) hsub

/--
The \(\tau\)-map descends from the relator-subgroup quotient to the augmented Schreier
presentation quotient.
-/
theorem representativeSymbolEvalAugmentedPresentationQuotientHom_tauRelatorSubgroup
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (y : L ⧸ relatorSubgroup (L := L) R) :
    representativeSymbolEvalAugmentedPresentationQuotientHom (S := S) hR
        (representativeTauRelatorSubgroupAugmentedPresentationQuotientHom
          (S := S) hR y) = y := by
  rcases QuotientGroup.mk'_surjective (relatorSubgroup (L := L) R) y with
    ⟨k, rfl⟩
  simpa [representativeTauRelatorSubgroupAugmentedPresentationQuotientHom] using
    representativeSymbolEvalAugmentedPresentationQuotientHom_tauKernel
      (S := S) hR k

/--
\(\tau\)-rewriting followed by symbol evaluation is the identity on the augmented
Schreier-presentation quotient.
-/
theorem representativeTauRelatorSubgroupAugmentedPresentationQuotientHom_symbolEval
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (y : FreeGroup (RepresentativeSchreierSymbol S) ⧸
        Subgroup.normalClosure (representativeAugmentedPresentationRelators S R)) :
    representativeTauRelatorSubgroupAugmentedPresentationQuotientHom
        (S := S) hR
        (representativeSymbolEvalAugmentedPresentationQuotientHom
          (S := S) hR y) = y := by
  rcases QuotientGroup.mk'_surjective
      (Subgroup.normalClosure (representativeAugmentedPresentationRelators S R)) y with
    ⟨z, rfl⟩
  change representativeTauRelatorSubgroupAugmentedPresentationQuotientHom
      (S := S) hR
      (QuotientGroup.mk' (relatorSubgroup (L := L) R)
        (representativeSymbolEvalSubgroupHom S z)) =
    QuotientGroup.mk'
      (Subgroup.normalClosure (representativeAugmentedPresentationRelators S R)) z
  simp only [representativeTauRelatorSubgroupAugmentedPresentationQuotientHom,
      QuotientGroup.mk'_apply,
  QuotientGroup.lift_mk]
  exact relatorEquivalent_iff_eq_in_presentedQuotient.1
    (representativeTau_symbolEvalHom_relatorEquivalent_augmented
      (S := S) R z)

/--
The augmented representative presentation quotient is equivalent to the relator quotient of the
subgroup.
-/
noncomputable def representativeAugmentedPresentationQuotientEquiv
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L) :
    FreeGroup (RepresentativeSchreierSymbol S) ⧸
        Subgroup.normalClosure (representativeAugmentedPresentationRelators S R) ≃*
      L ⧸ relatorSubgroup (L := L) R where
  toFun := representativeSymbolEvalAugmentedPresentationQuotientHom (S := S) hR
  invFun :=
    representativeTauRelatorSubgroupAugmentedPresentationQuotientHom
      (S := S) hR
  left_inv :=
    representativeTauRelatorSubgroupAugmentedPresentationQuotientHom_symbolEval
      (S := S) hR
  right_inv :=
    representativeSymbolEvalAugmentedPresentationQuotientHom_tauRelatorSubgroup
      (S := S) hR
  map_mul' x y :=
    (representativeSymbolEvalAugmentedPresentationQuotientHom
      (S := S) hR).map_mul x y

/--
The presented group for the augmented representative presentation is equivalent to the relator
quotient of the subgroup.
-/
noncomputable def representativeAugmentedPresentedGroupEquiv
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L) :
    PresentedGroup (representativeAugmentedPresentationRelators S R) ≃*
      L ⧸ relatorSubgroup (L := L) R :=
  representativeAugmentedPresentationQuotientEquiv (S := S) hR

/--
The augmented-presentation relator normal closure equals the normal closure generated by the
corresponding Reidemeister--Schreier relators.
-/
theorem normalClosure_representativeAugmentedPresentationRelators_eq
    {R : Set (FreeGroup X)}
    (hsection :
      ∀ t : representativeSet S,
        representativeTau S 1 (t : FreeGroup X) ∈
          Subgroup.normalClosure (representativePresentationRelators S R)) :
    Subgroup.normalClosure (representativeAugmentedPresentationRelators S R) =
      Subgroup.normalClosure (representativePresentationRelators S R) := by
  apply normalClosure_eq_of_subset_normalClosure
  · intro q hq
    rcases hq with hq | hq
    · exact Subgroup.subset_normalClosure hq
    · rcases hq with ⟨t, rfl⟩
      exact hsection t
  · intro q hq
    exact Subgroup.subset_normalClosure (Or.inl hq)

/--
The augmented-presentation relator normal closure equals the normal closure generated by the
corresponding Reidemeister--Schreier relators.
-/
theorem normalClosure_representativeAugmentedPresentationRelators_eq_of_isPrefixClosed
    {R : Set (FreeGroup X)}
    (hprefix : IsPrefixClosedRepresentativeSystem S) :
    Subgroup.normalClosure (representativeAugmentedPresentationRelators S R) =
      Subgroup.normalClosure (representativePresentationRelators S R) :=
  normalClosure_representativeAugmentedPresentationRelators_eq
    (S := S)
    (fun t =>
      representativeTau_section_mem_normalClosure_presentation_of_isPrefixClosed
        (S := S) R hprefix t)

/--
After adding the section relators, the representative presentation quotient is equivalent to the
subgroup relator quotient.
-/
noncomputable def representativePresentationQuotientEquivOfSectionRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (hsection :
      ∀ t : representativeSet S,
        representativeTau S 1 (t : FreeGroup X) ∈
          Subgroup.normalClosure (representativePresentationRelators S R)) :
    FreeGroup (RepresentativeSchreierSymbol S) ⧸
        Subgroup.normalClosure (representativePresentationRelators S R) ≃*
      L ⧸ relatorSubgroup (L := L) R :=
  (QuotientGroup.congr
    (Subgroup.normalClosure (representativePresentationRelators S R))
    (Subgroup.normalClosure (representativeAugmentedPresentationRelators S R))
    (MulEquiv.refl (FreeGroup (RepresentativeSchreierSymbol S)))
    (by
      simpa using
        (normalClosure_representativeAugmentedPresentationRelators_eq
          (S := S) hsection).symm)).trans
    (representativeAugmentedPresentationQuotientEquiv (S := S) hR)

/--
After adding the section relators, the representative presented group is equivalent to the
subgroup quotient.
-/
noncomputable def representativePresentedGroupEquivOfSectionRelators
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (hsection :
      ∀ t : representativeSet S,
        representativeTau S 1 (t : FreeGroup X) ∈
          Subgroup.normalClosure (representativePresentationRelators S R)) :
    PresentedGroup (representativePresentationRelators S R) ≃*
      L ⧸ relatorSubgroup (L := L) R :=
  representativePresentationQuotientEquivOfSectionRelators
    (S := S) hR hsection

/--
For a prefix-closed representative set, the representative presentation quotient is equivalent
to the subgroup relator quotient.
-/
noncomputable def representativePresentationQuotientEquivOfIsPrefixClosed
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (hprefix : IsPrefixClosedRepresentativeSystem S) :
    FreeGroup (RepresentativeSchreierSymbol S) ⧸
        Subgroup.normalClosure (representativePresentationRelators S R) ≃*
      L ⧸ relatorSubgroup (L := L) R :=
  representativePresentationQuotientEquivOfSectionRelators
    (S := S) hR
    (fun t =>
      representativeTau_section_mem_normalClosure_presentation_of_isPrefixClosed
        (S := S) R hprefix t)

/--
For a prefix-closed representative set, the representative presented group is equivalent to the
subgroup quotient.
-/
noncomputable def representativePresentedGroupEquivOfIsPrefixClosed
    {R : Set (FreeGroup X)}
    (hR : Subgroup.normalClosure R ≤ L)
    (hprefix : IsPrefixClosedRepresentativeSystem S) :
    PresentedGroup (representativePresentationRelators S R) ≃*
      L ⧸ relatorSubgroup (L := L) R :=
  representativePresentationQuotientEquivOfIsPrefixClosed
    (S := S) hR hprefix

end SchreierRewriting

end Kourovka.Schreier.Discrete
