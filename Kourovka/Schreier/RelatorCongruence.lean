/-
Adapted from ProCGroups by n-yamaguchi-0729, commit
6933dfe3f376833421ce10e782108b95ac84bda5, under Apache License 2.0.
See ../../third_party/ProCGroups-LICENSE and ProCGroups-PROVENANCE.md.
Local changes: module and namespace prefixes; compatibility with Lean 4.24.
-/
import Kourovka.Schreier.RelatorBasic

set_option autoImplicit false

/-!
# Relator maps and normal-closure congruence

This module transports normal-closure membership and relator equivalence
through inclusions, homomorphisms, and indexed unions of relator families.
-/

namespace Kourovka.Schreier.Discrete.Presentations

variable {G H : Type*} [Group G] [Group H]

section NormalClosure

variable {R S : Set G} {r a b : G}

/-- Membership in a normal closure is preserved when the relator set is enlarged. -/
theorem mem_normalClosure_of_subset
    (hR_to_S : R ⊆ S) {x : G}
    (hx : x ∈ Subgroup.normalClosure R) :
    x ∈ Subgroup.normalClosure S :=
  Subgroup.normalClosure_mono hR_to_S hx

/-- Membership in the left normal closure implies membership in the normal closure of the union. -/
theorem mem_normalClosure_union_left
    {x : G} (hx : x ∈ Subgroup.normalClosure R) :
    x ∈ Subgroup.normalClosure (R ∪ S) :=
  mem_normalClosure_of_subset (R := R) (S := R ∪ S)
    (Set.subset_union_left) hx

/-- Membership in the right normal closure implies membership in the normal closure of the union. -/
theorem mem_normalClosure_union_right
    {x : G} (hx : x ∈ Subgroup.normalClosure S) :
    x ∈ Subgroup.normalClosure (R ∪ S) :=
  mem_normalClosure_of_subset (R := S) (S := R ∪ S)
    (Set.subset_union_right) hx

/--
Membership in one indexed normal closure implies membership in the normal closure of the indexed
union.
-/
theorem mem_normalClosure_iUnion
    {ι : Sort*} (R : ι → Set G) (i : ι)
    {x : G} (hx : x ∈ Subgroup.normalClosure (R i)) :
    x ∈ Subgroup.normalClosure (Set.iUnion R) :=
  mem_normalClosure_of_subset (R := R i) (S := Set.iUnion R)
    (fun _ hy => Set.mem_iUnion.2 ⟨i, hy⟩) hx

/--
Membership in one doubly indexed normal closure implies membership in the normal closure of the
doubly indexed union.
-/
theorem mem_normalClosure_iUnion₂
    {ι : Sort*} {κ : ι → Sort*}
    (R : ∀ i : ι, κ i → Set G) (i : ι) (j : κ i)
    {x : G} (hx : x ∈ Subgroup.normalClosure (R i j)) :
    x ∈ Subgroup.normalClosure
        (Set.iUnion fun i : ι => Set.iUnion (R i)) :=
  mem_normalClosure_of_subset
    (R := R i j)
    (S := Set.iUnion fun i : ι => Set.iUnion (R i))
    (fun _ hy => Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, hy⟩⟩) hx

/--
An explicit pair of indices gives membership in the normal closure of the doubly indexed union.
-/
theorem mem_normalClosure_iUnion₂_of_exists
    {ι : Sort*} {κ : ι → Sort*}
    (R : ∀ i : ι, κ i → Set G)
    {x : G} (hx : ∃ i : ι, ∃ j : κ i,
      x ∈ Subgroup.normalClosure (R i j)) :
    x ∈ Subgroup.normalClosure
        (Set.iUnion fun i : ι => Set.iUnion (R i)) := by
  rcases hx with ⟨i, j, hij⟩
  exact mem_normalClosure_iUnion₂ (R := R) i j hij

/--
Maps that preserve each indexed relator family send the union of the source relators into the
target normal closure.
-/
theorem maps_iUnion_relators_mem_normalClosure
    {ι : Sort*} (f : G →* H) {R : ι → Set G} {S : Set H}
    (hR : ∀ i : ι, ∀ r ∈ R i, f r ∈ Subgroup.normalClosure S) :
    ∀ r ∈ Set.iUnion R, f r ∈ Subgroup.normalClosure S := by
  intro r hr
  rcases Set.mem_iUnion.1 hr with ⟨i, hi⟩
  exact hR i r hi

/--
Maps that preserve each doubly indexed relator family send the union of the source relators into
the target normal closure.
-/
theorem maps_iUnion₂_relators_mem_normalClosure
    {ι : Sort*} {κ : ι → Sort*}
    (f : G →* H) {R : ∀ i : ι, κ i → Set G} {S : Set H}
    (hR : ∀ i : ι, ∀ j : κ i, ∀ r ∈ R i j,
      f r ∈ Subgroup.normalClosure S) :
    ∀ r ∈ Set.iUnion (fun i : ι => Set.iUnion (R i)),
      f r ∈ Subgroup.normalClosure S := by
  intro r hr
  rcases Set.mem_iUnion.1 hr with ⟨i, hi⟩
  rcases Set.mem_iUnion.1 hi with ⟨j, hj⟩
  exact hR i j r hj

/-- A relator-preserving map sends relators into the normal closure of the target relator set. -/
theorem map_mem_normalClosure_of_relators
    (f : G →* H) {R : Set G} {S : Set H}
    (hR : ∀ r ∈ R, f r ∈ Subgroup.normalClosure S)
    {x : G} (hx : x ∈ Subgroup.normalClosure R) :
    f x ∈ Subgroup.normalClosure S := by
  let N : Subgroup G := Subgroup.comap f (Subgroup.normalClosure S)
  have hle : Subgroup.normalClosure R ≤ N := by
    refine Subgroup.normalClosure_le_normal ?_
    intro r hr
    exact hR r hr
  exact hle hx

/--
A homomorphism preserves relator equivalence when each source relator maps into the target
normal closure.
-/
theorem hom_relatorEquivalent_of_maps_relators
    (f : G →* H) {R : Set G} {S : Set H}
    (hR : ∀ r ∈ R, f r ∈ Subgroup.normalClosure S)
    {u v : G} (h : RelatorEquivalent R u v) :
    RelatorEquivalent S (f u) (f v) := by
  have hx :
      f (u * v⁻¹) ∈ Subgroup.normalClosure S :=
    map_mem_normalClosure_of_relators f hR (by simpa [RelatorEquivalent] using h)
  simpa [RelatorEquivalent, map_mul] using hx

/--
A homomorphism preserves relator equivalence when each source relator maps to a
target-relator-equivalent trivial word.
-/
theorem hom_relatorEquivalent_of_maps_relators_relatorEquivalent
    (f : G →* H) {R : Set G} {S : Set H}
    (hR : ∀ r ∈ R, RelatorEquivalent S (f r) 1)
    {u v : G} (h : RelatorEquivalent R u v) :
    RelatorEquivalent S (f u) (f v) :=
  hom_relatorEquivalent_of_maps_relators f
    (fun r hr => RelatorEquivalent.mem_normalClosure_of_eq_one (hR r hr)) h

/--
A mapped relator from an indexed family lies in the normal closure of the union of the mapped
relator families.
-/
theorem map_mem_normalClosure_iUnion_of_relators
    {ι : Sort*} (f : G →* H) {R : ι → Set G} {S : Set H}
    (hR : ∀ i : ι, ∀ r ∈ R i, f r ∈ Subgroup.normalClosure S)
    {x : G} (hx : x ∈ Subgroup.normalClosure (Set.iUnion R)) :
    f x ∈ Subgroup.normalClosure S :=
  map_mem_normalClosure_of_relators f
    (maps_iUnion_relators_mem_normalClosure f hR) hx

/--
A mapped relator from a doubly indexed family lies in the normal closure of the union of the
mapped relator families.
-/
theorem map_mem_normalClosure_iUnion₂_of_relators
    {ι : Sort*} {κ : ι → Sort*}
    (f : G →* H) {R : ∀ i : ι, κ i → Set G} {S : Set H}
    (hR : ∀ i : ι, ∀ j : κ i, ∀ r ∈ R i j,
      f r ∈ Subgroup.normalClosure S)
    {x : G}
    (hx : x ∈ Subgroup.normalClosure
      (Set.iUnion fun i : ι => Set.iUnion (R i))) :
    f x ∈ Subgroup.normalClosure S :=
  map_mem_normalClosure_of_relators f
    (maps_iUnion₂_relators_mem_normalClosure f hR) hx

/--
A homomorphism preserves relator equivalence for an indexed union of relators when every source
relator maps into the target normal closure.
-/
theorem hom_relatorEquivalent_of_maps_iUnion_relators
    {ι : Sort*} (f : G →* H) {R : ι → Set G} {S : Set H}
    (hR : ∀ i : ι, ∀ r ∈ R i, f r ∈ Subgroup.normalClosure S)
    {u v : G} (h : RelatorEquivalent (Set.iUnion R) u v) :
    RelatorEquivalent S (f u) (f v) :=
  hom_relatorEquivalent_of_maps_relators f
    (maps_iUnion_relators_mem_normalClosure f hR) h

/--
A homomorphism preserves relator equivalence for an indexed union of relators when every source
relator maps to a target-relator-equivalent trivial word.
-/
theorem hom_relatorEquivalent_of_maps_iUnion_relators_relatorEquivalent
    {ι : Sort*} (f : G →* H) {R : ι → Set G} {S : Set H}
    (hR : ∀ i : ι, ∀ r ∈ R i, RelatorEquivalent S (f r) 1)
    {u v : G} (h : RelatorEquivalent (Set.iUnion R) u v) :
    RelatorEquivalent S (f u) (f v) :=
  hom_relatorEquivalent_of_maps_iUnion_relators f
    (fun i r hr => RelatorEquivalent.mem_normalClosure_of_eq_one (hR i r hr)) h

/--
A homomorphism preserves relator equivalence for a doubly indexed union of relators when every
source relator maps into the target normal closure.
-/
theorem hom_relatorEquivalent_of_maps_iUnion₂_relators
    {ι : Sort*} {κ : ι → Sort*}
    (f : G →* H) {R : ∀ i : ι, κ i → Set G} {S : Set H}
    (hR : ∀ i : ι, ∀ j : κ i, ∀ r ∈ R i j,
      f r ∈ Subgroup.normalClosure S)
    {u v : G}
    (h : RelatorEquivalent
      (Set.iUnion fun i : ι => Set.iUnion (R i)) u v) :
    RelatorEquivalent S (f u) (f v) :=
  hom_relatorEquivalent_of_maps_relators f
    (maps_iUnion₂_relators_mem_normalClosure f hR) h

/--
A homomorphism preserves relator equivalence for a doubly indexed union of relators when every
source relator maps to a target-relator-equivalent trivial word.
-/
theorem hom_relatorEquivalent_of_maps_iUnion₂_relators_relatorEquivalent
    {ι : Sort*} {κ : ι → Sort*}
    (f : G →* H) {R : ∀ i : ι, κ i → Set G} {S : Set H}
    (hR : ∀ i : ι, ∀ j : κ i, ∀ r ∈ R i j,
      RelatorEquivalent S (f r) 1)
    {u v : G}
    (h : RelatorEquivalent
      (Set.iUnion fun i : ι => Set.iUnion (R i)) u v) :
    RelatorEquivalent S (f u) (f v) :=
  hom_relatorEquivalent_of_maps_iUnion₂_relators f
    (fun i j r hr => RelatorEquivalent.mem_normalClosure_of_eq_one (hR i j r hr)) h

end NormalClosure

end Kourovka.Schreier.Discrete.Presentations
