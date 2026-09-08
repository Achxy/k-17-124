/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Tactic

/-!
# Coset transversals and Schreier edges

A transversal chooses one word in each right coset of a subgroup of a free
group. Its edges are labelled by pairs `(chosen representative, generator)`.
The correction word attached to an edge lies in the subgroup.
-/

namespace Kourovka.Schreier

variable {X : Type*}

/-- A normalized section of the right-coset projection. -/
structure Transversal (L : Subgroup (FreeGroup X)) where
  rep : FreeGroup X → FreeGroup X
  sameCoset : ∀ w, w * (rep w)⁻¹ ∈ L
  constantOnCosets : ∀ {u v}, u * v⁻¹ ∈ L → rep u = rep v
  rep_one : rep 1 = 1

namespace Transversal

variable {L : Subgroup (FreeGroup X)} (S : Transversal L)

/-- Replacing the initial vertex by its representative preserves the endpoint coset. -/
theorem rep_mul (u v : FreeGroup X) : S.rep (S.rep u * v) = S.rep (u * v) := by
  apply S.constantOnCosets
  have h := L.inv_mem (S.sameCoset u)
  convert h using 1
  group

@[simp] theorem rep_rep (u : FreeGroup X) : S.rep (S.rep u) = S.rep u := by
  simpa using S.rep_mul u 1

theorem rep_right_eq {u v : FreeGroup X} (h : S.rep u = S.rep v) (w : FreeGroup X) :
    S.rep (u * w) = S.rep (v * w) := by
  rw [← S.rep_mul u w, ← S.rep_mul v w, h]

theorem rep_eq_one {u : FreeGroup X} (h : u ∈ L) : S.rep u = 1 := by
  rw [← S.rep_one]
  exact S.constantOnCosets (by simpa using h)

/-- The chosen representatives, regarded as vertices of the coset graph. -/
def vertices : Set (FreeGroup X) := Set.range S.rep

@[simp] theorem rep_vertex (v : S.vertices) : S.rep v.val = v.val := by
  obtain ⟨w, hw⟩ := v.property
  rw [← hw, S.rep_rep]

/-- An oriented edge is a representative together with a positive generator. -/
abbrev Edge := S.vertices × X

/-- The edge with initial coset represented by `p` and label `x`. -/
def edge (p : FreeGroup X) (x : X) : S.Edge := (⟨S.rep p, ⟨p, rfl⟩⟩, x)

theorem edge_eq {p q : FreeGroup X} (h : S.rep p = S.rep q) (x : X) :
    S.edge p x = S.edge q x := by
  apply Prod.ext
  · exact Subtype.ext h
  · rfl

@[simp] theorem edge_vertex (z : S.Edge) : S.edge z.1.val z.2 = z := by
  apply Prod.ext
  · exact Subtype.ext (S.rep_vertex z.1)
  · rfl

/-- The subgroup element obtained by following an edge and returning along the section. -/
def edgeValue (z : S.Edge) : FreeGroup X :=
  z.1.val * FreeGroup.of z.2 * (S.rep (z.1.val * FreeGroup.of z.2))⁻¹

theorem edgeValue_mem (z : S.Edge) : S.edgeValue z ∈ L :=
  S.sameCoset (z.1.val * FreeGroup.of z.2)

/-- Schreier-edge evaluation as a homomorphism into the subgroup. -/
def evaluate : FreeGroup S.Edge →* L :=
  FreeGroup.lift (fun z => ⟨S.edgeValue z, S.edgeValue_mem z⟩)

@[simp] theorem evaluate_of (z : S.Edge) : (S.evaluate (FreeGroup.of z)).val = S.edgeValue z := by
  simp [evaluate]

end Transversal
end Kourovka.Schreier
