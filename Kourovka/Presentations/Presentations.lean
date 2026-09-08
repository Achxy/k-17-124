/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Computability.Enumeration
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Ordinary finite presentations and the metabelian identity

`PresentationCode` stores a finite alphabet and a list of words. `GroupOf` is the
quotient of the free group by the normal closure of those relators.
`DefinesMetabelian` includes the alphabet check; decoding alone does not establish it.
-/

namespace Kourovka.MetabelianEnumeration

/-- An ordinary finite presentation: a generator count and a finite list of finite words. -/
abbrev PresentationCode := ℕ × List (List (ℕ × Bool))

/-- Every generator index occurring in a relator lies in the declared alphabet. -/
def WellFormed (p : PresentationCode) : Prop :=
  ∀ w ∈ p.2, ∀ letter ∈ w, letter.1 < p.1

/-- Interpret a signed word in the free group on `n` generators.
Out-of-range letters evaluate to the identity; `WellFormed` excludes them from valid inputs. -/
def interpretWord (n : ℕ) (w : List (ℕ × Bool)) : FreeGroup (Fin n) :=
  (w.map fun letter => if h : letter.1 < n then
    if letter.2 then FreeGroup.of ⟨letter.1, h⟩ else (FreeGroup.of ⟨letter.1, h⟩)⁻¹
    else 1).prod

/-- The finite set of relators, interpreted as elements of the free group. -/
def relations (p : PresentationCode) : Set (FreeGroup (Fin p.1)) :=
  {r | r ∈ p.2.map (interpretWord p.1)}

/-- The ordinary presented group: the free group modulo the relator normal closure. -/
def GroupOf (p : PresentationCode) := PresentedGroup (relations p)

instance (p : PresentationCode) : Group (GroupOf p) :=
  inferInstanceAs (Group (PresentedGroup (relations p)))

theorem relations_finite (p : PresentationCode) : (relations p).Finite :=
  List.finite_toSet _

/-- The metabelian identity, quantified over all group elements. -/
def Metabelian (G : Type*) [Group G] : Prop :=
  ∀ a b c d : G, Commute ⁅a, b⁆ ⁅c, d⁆

/-- A surjective homomorphic image of a metabelian group is metabelian. -/
theorem metabelian_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (hG : Metabelian G) : Metabelian H := by
  intro a b c d
  obtain ⟨a, rfl⟩ := hf a
  obtain ⟨b, rfl⟩ := hf b
  obtain ⟨c, rfl⟩ := hf c
  obtain ⟨d, rfl⟩ := hf d
  simpa only [map_commutatorElement] using (hG a b c d).map f

/-- Total decoding of a natural number. An unsuccessful decode gives the empty presentation. -/
def decodePresentation (n : ℕ) : PresentationCode :=
  (Encodable.decode (α := PresentationCode) n).getD (0, [])

theorem decode_encode_presentation (p : PresentationCode) :
    decodePresentation (Encodable.encode p) = p := by simp [decodePresentation]

/-- The decoded input is well formed and its ordinary presented group is metabelian. -/
def DefinesMetabelian (n : ℕ) : Prop :=
  WellFormed (decodePresentation n) ∧ Metabelian (GroupOf (decodePresentation n))

/-- The recursive-enumerability statement for ordinary finite presentations. -/
def MainClaim : Prop := REPred DefinesMetabelian

theorem completion_of_certificates
    (check : ℕ → ℕ → Bool) (hc : Computable₂ check)
    (correct : ∀ p, DefinesMetabelian p ↔ ∃ c, check p c = true) : MainClaim :=
  recursively_enumerable_of_certificates check hc DefinesMetabelian correct

end Kourovka.MetabelianEnumeration
