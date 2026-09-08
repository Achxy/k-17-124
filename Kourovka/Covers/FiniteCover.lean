/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Polyhedral.ConeMargin
import Kourovka.Presentations.FiniteQuotient
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Lex

/-!
# Finite Cover

The actual finite ordinary presentation appearing in (17.124.1)–(17.124.4).
The signed-polynomial relation retains the literal inverse ordered word.
-/

namespace Kourovka.MetabelianEnumeration.FiniteCover

/-- The exponent lattice `ℤ^k`. -/
abbrev Lattice (k : ℕ) := Fin k → ℤ
/-- An ordered list of Laurent terms with a sign tag. `true` uses the
ordered conjugating word; `false` uses its literal inverse. -/
abbrev Polynomial (k : ℕ) := Bool × List (Lattice k × ℤ)

/-- Finite algebraic data defining a cover on `k` quotient generators
and `a` kernel generators. -/
structure Datum (k a : ℕ) where
  /-- The kernel generator assigned to a quotient-generator commutator. -/
  designated : Fin k → Fin k → Fin a
  /-- Ordered signed Laurent relations, imposed at every kernel generator. -/
  polynomials : List (Polynomial k)

/-- Integer lattice vectors with squared Euclidean norm strictly below `radius²`. -/
def latticeBall (k radius : ℕ) : Finset (Lattice k) :=
  (Fintype.piFinset fun _ : Fin k => Finset.Icc (-(radius : ℤ)) radius).filter
    fun v => (∑ i, v i ^ 2) < (radius : ℤ) ^ 2

theorem mem_latticeBall {k radius : ℕ} (v : Lattice k) :
    v ∈ latticeBall k radius ↔ (∑ i, v i ^ 2) < (radius : ℤ) ^ 2 := by
  rw [latticeBall, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    have hi : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    have hr : (0 : ℤ) ≤ radius := Int.natCast_nonneg radius
    apply Finset.mem_Icc.mpr
    constructor <;> nlinarith

/-- Sorting makes enumeration executable instead of selecting an arbitrary ordering. -/
def latticeBallList (k radius : ℕ) : List (Lattice k) :=
  let order : LinearOrder (Lattice k) := LinearOrder.lift' List.ofFn List.ofFn_injective
  letI : LinearOrder (Lattice k) := order
  (latticeBall k radius).sort order.le

theorem mem_latticeBallList {k radius : ℕ} (v : Lattice k) :
    v ∈ latticeBallList k radius ↔ (∑ i, v i ^ 2) < (radius : ℤ) ^ 2 := by
  rw [latticeBallList, Finset.mem_sort, mem_latticeBall]

/-- Right commutator: `x⁻¹ * y⁻¹ * x * y`. -/
def rightComm {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

/-- Right conjugation: `w⁻¹ * x * w`. -/
def conjugate {G : Type*} [Group G] (x w : G) : G := w⁻¹ * x * w

/-- The fixed-order product `t₁^v₁ ⋯ tₖ^vₖ`. -/
def orderedWord {k : ℕ} {G : Type*} [Group G] (t : Fin k → G) (v : Lattice k) : G :=
  (List.ofFn fun i => t i ^ v i).prod

/-- Evaluate the ordered polynomial relation as a product of conjugates.
Order is retained because the ambient group has not yet been proved metabelian. -/
def polynomialWord {k : ℕ} {G : Type*} [Group G] (t : Fin k → G)
    (x : G) (p : Polynomial k) : G :=
  (p.2.map fun term => conjugate (x ^ term.2)
    (if p.1 then orderedWord t term.1 else (orderedWord t term.1)⁻¹)).prod

theorem map_rightComm {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G) :
    f (rightComm x y) = rightComm (f x) (f y) := by simp [rightComm]

theorem map_conjugate {G H : Type*} [Group G] [Group H] (f : G →* H) (x w : G) :
    f (conjugate x w) = conjugate (f x) (f w) := by simp [conjugate]

theorem map_orderedWord {k : ℕ} {G H : Type*} [Group G] [Group H] (f : G →* H)
    (t : Fin k → G) (v : Lattice k) :
    f (orderedWord t v) = orderedWord (fun i => f (t i)) v := by
  simp [orderedWord, map_list_prod, List.map_ofFn, Function.comp_def]

theorem map_polynomialWord {k : ℕ} {G H : Type*} [Group G] [Group H] (f : G →* H)
    (t : Fin k → G) (x : G) (p : Polynomial k) :
    f (polynomialWord t x p) = polynomialWord (fun i => f (t i)) (f x) p := by
  simp only [polynomialWord, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro term _
  simp only [Function.comp_apply, map_conjugate, map_zpow]
  split <;> simp only [map_orderedWord, map_inv]

def tGenerator (k a : ℕ) (i : Fin k) : FreeGroup (Fin (k + a)) :=
  FreeGroup.of (Fin.castAdd a i)

def aGenerator (k a : ℕ) (i : Fin a) : FreeGroup (Fin (k + a)) :=
  FreeGroup.of (Fin.natAdd k i)

/-- Relations identifying each quotient-generator commutator with a kernel generator. -/
def tRelations {k a : ℕ} (data : Datum k a) : List (FreeGroup (Fin (k + a))) :=
  (List.finRange k).flatMap fun i => ((List.finRange k).filter fun j => i < j).map fun j =>
    rightComm (tGenerator k a i) (tGenerator k a j) *
      (aGenerator k a (data.designated i j))⁻¹

/-- Commutation relations for kernel generators at lattice displacements below the radius. -/
def shortRelations (k a radius : ℕ) : List (FreeGroup (Fin (k + a))) :=
  (List.finRange a).flatMap fun i => (List.finRange a).flatMap fun j =>
    (latticeBallList k radius).map fun v =>
      rightComm (aGenerator k a i) (conjugate (aGenerator k a j)
        (orderedWord (tGenerator k a) v))

/-- The signed Laurent relations for each kernel generator. -/
def polynomialRelations {k a : ℕ} (data : Datum k a) : List (FreeGroup (Fin (k + a))) :=
  (List.finRange a).flatMap fun i => data.polynomials.map fun p =>
    (aGenerator k a i)⁻¹ * polynomialWord (tGenerator k a) (aGenerator k a i) p

/-- Ordinary finite group relators, with no relative-variety presentation involved. -/
def relators {k a : ℕ} (data : Datum k a) (radius : ℕ) :
    List (FreeGroup (Fin (k + a))) :=
  tRelations data ++ shortRelations k a radius ++ polynomialRelations data

/-- The ordinary group defined by the three finite relator families. -/
def GroupOf {k a : ℕ} (data : Datum k a) (radius : ℕ) :=
  PresentedGroup (WordCertificates.relSet (relators data radius))

instance {k a : ℕ} (data : Datum k a) (radius : ℕ) : Group (GroupOf data radius) :=
  inferInstanceAs (Group (PresentedGroup (WordCertificates.relSet (relators data radius))))

theorem relators_finite {k a : ℕ} (data : Datum k a) (radius : ℕ) :
    (WordCertificates.relSet (relators data radius)).Finite := List.finite_toSet _

def generatorAssignment {k a : ℕ} {G : Type*} (t : Fin k → G) (A : Fin a → G) :
    Fin (k + a) → G := Fin.addCases t A

theorem lift_tGenerator {k a : ℕ} {G : Type*} [Group G] (t : Fin k → G)
    (A : Fin a → G) (i : Fin k) :
    FreeGroup.lift (generatorAssignment t A) (tGenerator k a i) = t i := by
  simp [generatorAssignment, tGenerator]

theorem lift_aGenerator {k a : ℕ} {G : Type*} [Group G] (t : Fin k → G)
    (A : Fin a → G) (i : Fin a) :
    FreeGroup.lift (generatorAssignment t A) (aGenerator k a i) = A i := by
  simp [generatorAssignment, aGenerator]

/-- A realization spells out the three defining relation families in a target group. -/
structure Realizes {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G) : Prop where
  /-- Quotient-generator commutators have their designated kernel values. -/
  t_comm : ∀ i j, i < j → rightComm (t i) (t j) = A (data.designated i j)
  /-- Kernel generators commute at all displacements inside the finite radius. -/
  short_comm : ∀ i j v, (∑ s, v s ^ 2) < (radius : ℤ) ^ 2 →
    rightComm (A i) (conjugate (A j) (orderedWord t v)) = 1
  /-- The signed Laurent identities hold for each kernel generator. -/
  polynomial : ∀ i p, p ∈ data.polynomials → A i = polynomialWord t (A i) p

theorem realization_relators {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G)
    (h : Realizes data radius t A) (r : FreeGroup (Fin (k + a)))
    (hr : r ∈ relators data radius) : FreeGroup.lift (generatorAssignment t A) r = 1 := by
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨i, _, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have hij : i < j := of_decide_eq_true (List.mem_filter.mp hj).2
      simp only [map_mul, map_inv, map_rightComm, lift_tGenerator, lift_aGenerator]
      rw [h.t_comm i j hij]
      exact mul_inv_cancel _
    · obtain ⟨i, _, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨j, _, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
      simp only [map_rightComm, map_conjugate, map_orderedWord,
        lift_tGenerator, lift_aGenerator]
      exact h.short_comm i j v ((mem_latticeBallList v).mp hv)
  · obtain ⟨i, _, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    simp only [map_mul, map_inv, map_polynomialWord, lift_tGenerator, lift_aGenerator]
    rw [← h.polynomial i p hp]
    exact inv_mul_cancel _

/-- The homomorphism induced by generators satisfying the cover relations. -/
def realizationHom {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G)
    (h : Realizes data radius t A) : GroupOf data radius →* G :=
  PresentedGroup.toGroup (f := generatorAssignment t A) (realization_relators data radius t A h)

theorem realizationHom_generator {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G)
    (h : Realizes data radius t A) (i : Fin (k + a)) :
    realizationHom data radius t A h (PresentedGroup.of i) = generatorAssignment t A i :=
  PresentedGroup.toGroup.of _

/-- The induced homomorphism is surjective when the chosen images generate the target. -/
theorem realizationHom_surjective {k a : ℕ} (data : Datum k a) (radius : ℕ)
    {G : Type*} [Group G] (t : Fin k → G) (A : Fin a → G)
    (h : Realizes data radius t A)
    (hgen : Subgroup.closure (Set.range t ∪ Set.range A) = ⊤) :
    Function.Surjective (realizationHom data radius t A h) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  rw [Subgroup.closure_le]
  rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact ⟨PresentedGroup.of (Fin.castAdd a i), by
      simp [realizationHom_generator, generatorAssignment]⟩
  · exact ⟨PresentedGroup.of (Fin.natAdd k i), by
      simp [realizationHom_generator, generatorAssignment]⟩

end Kourovka.MetabelianEnumeration.FiniteCover
