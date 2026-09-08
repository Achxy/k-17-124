/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Halfspaces.HalfspaceSplitting

/-!
# Halfspace Geometry

Reordering lattice steps inside a thick strip. This supplies the path
connectivity used in the Bieri–Strebel halfspace argument.
-/

namespace Kourovka.MetabelianEnumeration.HalfspaceGeometry

variable {X : Type*}

/-- A predicate holds at every successive path vertex, including both ends. -/
def PathIn (f : X → ℝ) (P : ℝ → Prop) (p : ℝ) : List X → Prop
  | [] => P p
  | x :: xs => P p ∧ PathIn f P (p + f x) xs

/-- The height increment of a signed free-group letter. -/
def letterHeight {Y : Type*} (h : Y → ℝ) (z : Y × Bool) : ℝ :=
  if z.2 then h z.1 else -h z.1

theorem PathIn.mono {f : X → ℝ} {P Q : ℝ → Prop} {p : ℝ} {xs : List X}
    (h : PathIn f P p xs) (hpq : ∀ x, P x → Q x) : PathIn f Q p xs := by
  induction xs generalizing p with
  | nil => exact hpq p h
  | cons x xs ih => exact ⟨hpq p h.1, ih h.2⟩

theorem PathIn.endpoint {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs : List X}
    (h : PathIn f P p xs) : P (p + (xs.map f).sum) := by
  induction xs generalizing p with
  | nil => simpa [PathIn] using h
  | cons x xs ih => simpa only [List.map_cons, List.sum_cons, add_assoc] using ih h.2

theorem PathIn.append {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs ys : List X}
    (hx : PathIn f P p xs) (hy : PathIn f P (p + (xs.map f).sum) ys) :
    PathIn f P p (xs ++ ys) := by
  induction xs generalizing p with
  | nil => simpa using hy
  | cons x xs ih =>
    exact ⟨hx.1, ih hx.2 (by simpa only [List.map_cons, List.sum_cons, add_assoc] using hy)⟩

theorem pathIn_append_iff {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs ys : List X} :
    PathIn f P p (xs ++ ys) ↔
      PathIn f P p xs ∧ PathIn f P (p + (xs.map f).sum) ys := by
  induction xs generalizing p with
  | nil =>
    simp only [List.nil_append, List.map_nil, List.sum_nil, add_zero, PathIn]
    constructor
    · intro h
      have hstart : P p := by
        cases ys with
        | nil => exact h
        | cons y ys => exact h.1
      exact ⟨hstart, h⟩
    · exact And.right
  | cons x xs ih =>
    simp only [List.cons_append, PathIn, List.map_cons, List.sum_cons, ih, and_assoc,
      add_assoc]

theorem PathIn.start {f : X → ℝ} {P : ℝ → Prop} {p : ℝ} {xs : List X}
    (h : PathIn f P p xs) : P p := by
  cases xs with
  | nil => exact h
  | cons x xs => exact h.1

theorem PathIn.redStep {h : X → ℝ} {P : ℝ → Prop} {p : ℝ}
    {xs ys : List (X × Bool)} (hx : PathIn (letterHeight h) P p xs)
    (hr : FreeGroup.Red.Step xs ys) : PathIn (letterHeight h) P p ys := by
  cases hr with
  | @not as bs x b =>
    rw [pathIn_append_iff] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have hh := hx.2.2.2
    cases b <;> simpa [letterHeight, add_assoc] using hh

theorem PathIn.red {h : X → ℝ} {P : ℝ → Prop} {p : ℝ}
    {xs ys : List (X × Bool)} (hx : PathIn (letterHeight h) P p xs)
    (hr : FreeGroup.Red xs ys) : PathIn (letterHeight h) P p ys := by
  induction hr with
  | refl => exact hx
  | tail _ hstep ih => exact ih.redStep hstep

theorem PathIn.toWord_mk [DecidableEq X] {h : X → ℝ} {P : ℝ → Prop} {p : ℝ}
    {xs : List (X × Bool)} (hx : PathIn (letterHeight h) P p xs) :
    PathIn (letterHeight h) P p (FreeGroup.mk xs).toWord := by
  rw [FreeGroup.toWord_mk]
  exact hx.red FreeGroup.reduce.red

/-- Every vertex of the step path remains in the given real interval. -/
def Within (f : X → ℝ) (l u p : ℝ) : List X → Prop
  | [] => l ≤ p ∧ p ≤ u
  | x :: xs => (l ≤ p ∧ p ≤ u) ∧ Within f l u (p + f x) xs

theorem Within.pathIn {f : X → ℝ} {l u p : ℝ} {xs : List X}
    (h : Within f l u p xs) : PathIn f (fun x => l ≤ x ∧ x ≤ u) p xs := by
  induction xs generalizing p with
  | nil => exact h
  | cons x xs ih => exact ⟨h.1, ih h.2⟩

/-- At least one remaining step stays in a strip whose width is at least twice
the maximum step size, provided that both the present and final vertices lie
inside the strip. -/
theorem exists_safe_step (f : X → ℝ) (D l u p : ℝ) (xs : List X)
    (hne : xs ≠ []) (hD : ∀ x ∈ xs, |f x| ≤ D)
    (hwidth : 2 * D ≤ u - l) (hp : l ≤ p ∧ p ≤ u)
    (hend : l ≤ p + (xs.map f).sum ∧ p + (xs.map f).sum ≤ u) :
    ∃ x ∈ xs, l ≤ p + f x ∧ p + f x ≤ u := by
  by_contra! h
  obtain ⟨a, ys, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hbound : ∀ x ∈ a :: ys, -D ≤ f x ∧ f x ≤ D :=
    fun x hx => abs_le.mp (hD x hx)
  by_cases hnear : p - l ≤ D
  · have hneg : ∀ x ∈ a :: ys, p + f x < l := by
      intro x hx
      by_contra! hxlo
      have hxhi : p + f x ≤ u := by have := (hbound x hx).2; linarith
      exact (not_lt_of_ge hxhi) (h x hx hxlo)
    have htail : (ys.map f).sum ≤ 0 := by
      have hterm : ∀ x ∈ ys, f x ≤ 0 := by
        intro x hx
        have := hneg x (List.mem_cons_of_mem _ hx)
        linarith [hp.1]
      clear hneg hbound hD h hend hne
      induction ys with
      | nil => simp
      | cons z zs ih =>
        simp only [List.map_cons, List.sum_cons]
        have hz := hterm z List.mem_cons_self
        have hs := ih (fun x hx => hterm x (List.mem_cons_of_mem _ hx))
        linarith
    have := hneg a (List.mem_cons_self)
    simp only [List.map_cons, List.sum_cons] at hend
    linarith [hend.1]
  · have hpos : ∀ x ∈ a :: ys, u < p + f x := by
      intro x hx
      apply h x hx
      have := (hbound x hx).1
      linarith
    have htail : 0 ≤ (ys.map f).sum := List.sum_nonneg fun z hz => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
      have := hpos x (List.mem_cons_of_mem _ hx)
      linarith [hp.2]
    have := hpos a (List.mem_cons_self)
    simp only [List.map_cons, List.sum_cons] at hend
    linarith [hend.2]

/-- Any finite list of bounded steps can be reordered to stay in a sufficiently
thick interval containing its initial and final vertices. -/
theorem reorder_within (f : X → ℝ) (D l u p : ℝ) (xs : List X)
    (hD : ∀ x ∈ xs, |f x| ≤ D) (hwidth : 2 * D ≤ u - l)
    (hp : l ≤ p ∧ p ≤ u)
    (hend : l ≤ p + (xs.map f).sum ∧ p + (xs.map f).sum ≤ u) :
    ∃ ys : List X, ys.Perm xs ∧ Within f l u p ys := by
  classical
  by_cases hn : xs = []
  · subst xs
    exact ⟨[], List.Perm.refl _, hp⟩
  obtain ⟨a, ha, hsafe⟩ := exists_safe_step f D l u p xs hn hD hwidth hp hend
  have hperm : xs.Perm (a :: xs.erase a) := List.perm_cons_erase ha
  have hsum : (xs.map f).sum = f a + ((xs.erase a).map f).sum := by
    simpa only [List.map_cons, List.sum_cons] using (hperm.map f).sum_eq
  obtain ⟨ys, hys, hy⟩ := reorder_within f D l u (p + f a) (xs.erase a)
    (fun x hx => hD x (List.mem_of_mem_erase hx)) hwidth hsafe (by
      rw [add_assoc, ← hsum]
      exact hend)
  exact ⟨a :: ys, (hys.cons a).trans hperm.symm, hp, hy⟩
termination_by xs.length
 decreasing_by
  have hlen := hperm.length_eq
  simp only [List.length_cons] at hlen
  omega

/-- The interval common to the two halfspaces can be respected simultaneously;
outside it the path stays in the halfspace containing its endpoint. -/
theorem reorder_halfspaces (f : X → ℝ) (D μ : ℝ) (xs : List X)
    (hD : ∀ x ∈ xs, |f x| ≤ D) (hD0 : 0 ≤ D) (hμ : 2 * D ≤ μ) :
    ∃ ys : List X, ys.Perm xs ∧
      Within f (min 0 (xs.map f).sum) (max μ (xs.map f).sum) 0 ys := by
  apply reorder_within f D _ _ 0 xs hD
  · have hl : min 0 (xs.map f).sum ≤ 0 := min_le_left _ _
    have hu : μ ≤ max μ (xs.map f).sum := le_max_left _ _
    linarith
  · constructor
    · exact min_le_left _ _
    · exact (by linarith : 0 ≤ μ).trans (le_max_left _ _)
  · simpa only [zero_add] using
      And.intro (min_le_right 0 (xs.map f).sum) (le_max_right μ (xs.map f).sum)

end Kourovka.MetabelianEnumeration.HalfspaceGeometry
