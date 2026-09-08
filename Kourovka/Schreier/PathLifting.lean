/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Schreier.Transversal

/-!
# Lifting words through the coset graph

Edge labels may take values in any group. Reading a negative letter traverses
its positive edge backwards. Adjacent inverse letters cancel, so path lifting
descends from lists to the free group. Concatenation gives the cocycle identity.
-/

namespace Kourovka.Schreier.Transversal

variable {X : Type*} {L : Subgroup (FreeGroup X)} (S : Transversal L)
variable {H : Type*} [Group H]

/-- Read a signed word from a specified initial coset and multiply its edge labels. -/
def walk (f : S.Edge → H) : FreeGroup X → List (X × Bool) → H
  | _, [] => 1
  | p, (x, true) :: xs => f (S.edge p x) * walk f (p * FreeGroup.of x) xs
  | p, (x, false) :: xs =>
      (f (S.edge (p * (FreeGroup.of x)⁻¹) x))⁻¹ * walk f (p * (FreeGroup.of x)⁻¹) xs

theorem mk_cons_true (x : X) (xs : List (X × Bool)) :
    FreeGroup.mk ((x, true) :: xs) = FreeGroup.of x * FreeGroup.mk xs := rfl

theorem mk_cons_false (x : X) (xs : List (X × Bool)) :
    FreeGroup.mk ((x, false) :: xs) = (FreeGroup.of x)⁻¹ * FreeGroup.mk xs := rfl

/-- Lifting a concatenation follows the first path before starting the second. -/
theorem walk_append (f : S.Edge → H) (p : FreeGroup X) (xs ys : List (X × Bool)) :
    S.walk f p (xs ++ ys) = S.walk f p xs * S.walk f (p * FreeGroup.mk xs) ys := by
  induction xs generalizing p with
  | nil => simp [walk, ← FreeGroup.one_eq_mk]
  | cons z xs ih => cases z with
    | mk x b => cases b <;> simp [walk, ih, mk_cons_true, mk_cons_false, mul_assoc]

/-- A free-reduction step does not change the lifted label. -/
theorem walk_cancel (f : S.Edge → H) (p : FreeGroup X) {xs ys : List (X × Bool)}
    (h : FreeGroup.Red.Step xs ys) : S.walk f p xs = S.walk f p ys := by
  cases h with
  | @not before after x b =>
    rw [walk_append, walk_append]
    cases b <;> simp [walk, mul_assoc]

/-- The group-valued lift of a free-group element from an arbitrary initial coset. -/
def lift (f : S.Edge → H) (p : FreeGroup X) : FreeGroup X → H :=
  Quot.lift (S.walk f p) (fun _ _ h => S.walk_cancel f p h)

@[simp] theorem lift_mk (f : S.Edge → H) (p : FreeGroup X) (xs : List (X × Bool)) :
    S.lift f p (FreeGroup.mk xs) = S.walk f p xs := rfl

@[simp] theorem lift_one (f : S.Edge → H) (p : FreeGroup X) : S.lift f p 1 = 1 := rfl

@[simp] theorem lift_of (f : S.Edge → H) (p : FreeGroup X) (x : X) :
    S.lift f p (FreeGroup.of x) = f (S.edge p x) := by
  change f (S.edge p x) * 1 = f (S.edge p x)
  exact mul_one _

/-- The cocycle identity for path lifting. -/
theorem lift_mul (f : S.Edge → H) (p u v : FreeGroup X) :
    S.lift f p (u * v) = S.lift f p u * S.lift f (p * u) v := by
  rcases u with ⟨xs⟩
  rcases v with ⟨ys⟩
  exact S.walk_append f p xs ys

/-- Only the initial coset, rather than its chosen word, affects a lift. -/
theorem walk_start_eq (f : S.Edge → H) {p q : FreeGroup X}
    (h : S.rep p = S.rep q) (xs : List (X × Bool)) : S.walk f p xs = S.walk f q xs := by
  induction xs generalizing p q with
  | nil => rfl
  | cons z xs ih => cases z with
    | mk x b =>
      cases b
      · simp only [walk, S.edge_eq (S.rep_right_eq h (FreeGroup.of x)⁻¹) x,
          ih (S.rep_right_eq h (FreeGroup.of x)⁻¹)]
      · simp only [walk, S.edge_eq h x, ih (S.rep_right_eq h (FreeGroup.of x))]

theorem lift_start_eq (f : S.Edge → H) {p q : FreeGroup X}
    (h : S.rep p = S.rep q) (w : FreeGroup X) : S.lift f p w = S.lift f q w := by
  rcases w with ⟨xs⟩
  exact S.walk_start_eq f h xs

/-- Closed lifts at the identity coset form a homomorphism on the subgroup. -/
def subgroupLift (f : S.Edge → H) : L →* H where
  toFun u := S.lift f 1 u.val
  map_one' := rfl
  map_mul' u v := by
    change S.lift f 1 (u.val * v.val) = S.lift f 1 u.val * S.lift f 1 v.val
    rw [lift_mul]
    congr 1
    exact S.lift_start_eq f (by simpa only [one_mul, S.rep_one] using S.rep_eq_one u.property) v.val


/-- Reversing a path inverts its lifted label. -/
theorem lift_inv (f : S.Edge → H) (p w : FreeGroup X) :
    S.lift f (p * w) w⁻¹ = (S.lift f p w)⁻¹ := by
  apply mul_left_cancel (a := S.lift f p w)
  calc
    _ = 1 := by simpa only [mul_inv_cancel, lift_one] using (S.lift_mul f p w w⁻¹).symm
    _ = _ := (mul_inv_cancel _).symm

/-- Applying a homomorphism to edge labels commutes with path lifting. -/
theorem lift_map {K : Type*} [Group K] (φ : H →* K) (f : S.Edge → H)
    (p w : FreeGroup X) : φ (S.lift f p w) = S.lift (fun z => φ (f z)) p w := by
  rcases w with ⟨xs⟩
  change φ (S.walk f p xs) = S.walk (fun z => φ (f z)) p xs
  induction xs generalizing p with
  | nil => exact φ.map_one
  | cons z xs ih => cases z with
    | mk x b => cases b <;> simp only [walk, map_mul, map_inv, ih]

/-- Schreier rewriting is the universal lift, with formal edges as labels. -/
def rewrite (p w : FreeGroup X) : FreeGroup S.Edge := S.lift FreeGroup.of p w

/-- List form of the same rewriting, used to control the vertices visited by a path. -/
def rewriteWord (p : FreeGroup X) (xs : List (X × Bool)) : FreeGroup S.Edge :=
  S.walk FreeGroup.of p xs

@[simp] theorem rewrite_mk (p : FreeGroup X) (xs : List (X × Bool)) :
    S.rewrite p (FreeGroup.mk xs) = S.rewriteWord p xs := rfl

theorem rewrite_eq_word [DecidableEq X] (p w : FreeGroup X) :
    S.rewrite p w = S.rewriteWord p w.toWord := by
  rw [← rewrite_mk, FreeGroup.mk_toWord]

/-- Evaluating lifted edges telescopes to the initial section, word, and final section. -/
theorem lift_edgeValue (p w : FreeGroup X) :
    S.lift S.edgeValue p w = S.rep p * w * (S.rep (p * w))⁻¹ := by
  rcases w with ⟨xs⟩
  change S.walk S.edgeValue p xs = _
  induction xs generalizing p with
  | nil => simp [walk, ← FreeGroup.one_eq_mk]
  | cons z xs ih => cases z with
    | mk x b =>
      cases b <;>
        simp [walk, edgeValue, edge, S.rep_mul, ih, mk_cons_true, mk_cons_false, mul_assoc]

/-- Evaluation of rewritten words recovers their subgroup correction. -/
theorem evaluate_rewrite (p w : FreeGroup X) :
    (S.evaluate (S.rewrite p w)).val = S.rep p * w * (S.rep (p * w))⁻¹ := by
  have h := S.lift_map (L.subtype.comp S.evaluate) FreeGroup.of p w
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, evaluate_of,
    rewrite, lift_edgeValue] using h

end Kourovka.Schreier.Transversal
