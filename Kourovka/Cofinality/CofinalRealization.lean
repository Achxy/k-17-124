/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Cofinality.LatticePullback
import Kourovka.Modules.ModuleRealization
import Kourovka.Covers.CertifiedCover
import Kourovka.Modules.FiniteModuleGenerators

/-!
# Cofinal Realization

A tame finite Laurent module with its actual group extension gives the
finite ordinary covers in the enumeration.
-/

noncomputable section

set_option maxHeartbeats 50000
set_option autoImplicit false

namespace Kourovka.MetabelianEnumeration.CofinalCover

open FiniteCover CommutatorModule ModuleRealization ValuationModule SignedTameness
open TamenessCompactness

variable {k : ℕ} {E : Type} [Group E]
variable (π : E →* Multiplicative (Lattice k))

def kernelInclusion : Multiplicative (Additive π.ker) →* E where
  toFun m := m.toAdd.toMul.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projection_orderedWord (t : Fin k → E)
    (ht : ∀ i, π (t i) = Multiplicative.ofAdd (Pi.single i 1)) (v : Lattice k) :
    π (orderedWord t v) = Multiplicative.ofAdd v := by
  rw [map_orderedWord]
  apply Multiplicative.toAdd.injective
  simp only [orderedWord, toAdd_list_sum, List.map_ofFn, ht,
    List.sum_ofFn, toAdd_zpow, toAdd_ofAdd, Function.comp_apply]
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem orderedWord_mem (t : Fin k → E) (K : Subgroup E) (ht : ∀ i, t i ∈ K)
    (v : Lattice k) : orderedWord t v ∈ K := by
  apply K.list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact K.zpow_mem (ht i) _

variable [IsMulCommutative π.ker]

theorem rightComm_eq_one_of_commute {G : Type} [Group G] (x y : G) (h : Commute x y) :
    rightComm x y = 1 := by
  have hh := commutatorElement_eq_one_iff_mul_comm.mpr h.inv_left.inv_right.eq
  simpa only [commutatorElement_def, inv_inv, rightComm] using hh

theorem laurent_action_compatible (hπ : Function.Surjective π) (t : Fin k → E)
    (ht : ∀ i, π (t i) = Multiplicative.ofAdd (Pi.single i 1)) :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
    ActionCompatible (kernelInclusion π) t := by
  letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
  intro u m
  exact laurent_single_image π hπ (MonoidHom.id _) u (orderedWord t u)
    (projection_orderedWord π t ht u).symm m

section CompatibleAction

variable [Module (GroupRing (Lattice k)) (Additive π.ker)]

/-- Finite module generators together with lifts of a lattice basis generate
the actual extension group. -/
theorem closure_module_generators {a : ℕ} (t : Fin k → E)
    (ht : ∀ i, π (t i) = Multiplicative.ofAdd (Pi.single i 1))
    (hact : ActionCompatible (kernelInclusion π) t) (A : Fin a → Additive π.ker)
    (hA : Submodule.span (GroupRing (Lattice k)) (Set.range A) = ⊤) :
    Subgroup.closure (Set.range t ∪ Set.range (fun i => (A i).toMul.val)) = ⊤ := by
  let K := Subgroup.closure (Set.range t ∪ Set.range (fun i => (A i).toMul.val))
  have htK (i : Fin k) : t i ∈ K := Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  let B : AddSubgroup (Additive π.ker) := (K.comap π.ker.subtype).toAddSubgroup
  have hsmul (r : GroupRing (Lattice k)) (m : Additive π.ker) (hm : m ∈ B) :
      r • m ∈ B := by
    rw [smul_as_sum]
    apply B.list_sum_mem
    intro n hn
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hn
    apply B.zsmul_mem
    change (kernelInclusion π) (Multiplicative.ofAdd
      ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)) ∈ K
    rw [hact]
    exact K.mul_mem (K.mul_mem (K.inv_mem (orderedWord_mem t K htK u)) hm)
      (orderedWord_mem t K htK u)
  let V : Submodule (GroupRing (Lattice k)) (Additive π.ker) := {
    carrier := B
    zero_mem' := B.zero_mem
    add_mem' := B.add_mem
    smul_mem' := hsmul }
  have hspan : Submodule.span (GroupRing (Lattice k)) (Set.range A) ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hker : π.ker ≤ K := by
    intro n hn
    exact hspan (by rw [hA]; exact Submodule.mem_top (x := Additive.ofMul ⟨n, hn⟩))
  apply top_unique
  intro g _
  let w := orderedWord t (π g).toAdd
  have hw : w ∈ K := orderedWord_mem t K htK _
  have hn : g * w⁻¹ ∈ π.ker := by
    change π (g * w⁻¹) = 1
    rw [map_mul, map_inv, projection_orderedWord π t ht]
    simp
  have h := K.mul_mem (hker hn) hw
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

/-- A tame actual Laurent action produces finite cover data, including an
identity kernel generator so the kernel alphabet is always nonempty. The
same realization works at every radius. -/
theorem exists_cover_data_of_tame (t : Fin k → E)
    (ht : ∀ i, π (t i) = Multiplicative.ofAdd (Pi.single i 1))
    (hact : ActionCompatible (kernelInclusion π) t)
    [Module.Finite (GroupRing (Lattice k)) (Additive π.ker)]
    (htame : Tame (k := k) (Additive π.ker)) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ data : Datum k a,
      ConeVerifier.ConeCover (data.polynomials.map polynomialSupport) ∧
      ∀ radius : ℕ, ∃ f : FiniteCover.GroupOf data radius →* E, Function.Surjective f := by
  classical
  let c : Fin k × Fin k → Additive π.ker := fun ij => Additive.ofMul
    ⟨rightComm (t ij.1) (t ij.2), by
      change π (rightComm (t ij.1) (t ij.2)) = 1
      simp [rightComm, mul_comm, mul_assoc]⟩
  obtain ⟨a, ha, A, designated, hspan, hAd⟩ := finite_generators_with_designated c
  obtain ⟨ps, hps, hcone⟩ := finite_realizing_polynomials (kernelInclusion π) t hact htame
  let data : Datum k a := ⟨designated, ps⟩
  refine ⟨a, ha, data, hcone, ?_⟩
  intro radius
  have hr : Realizes data radius t (fun i => (A i).toMul.val) := {
    t_comm := by
      intro i j _
      rw [show data.designated i j = designated i j from rfl, hAd]
      rfl
    short_comm := by
      intro i j v _
      let n : π.ker := ⟨conjugate (A j).toMul.val (orderedWord t v), by
        change π (conjugate (A j).toMul.val (orderedWord t v)) = 1
        have hj : π (A j).toMul.val = 1 := (A j).toMul.property
        simp [conjugate, hj]⟩
      have h : rightComm (A i).toMul n = 1 :=
        rightComm_eq_one_of_commute _ _ (mul_comm _ _)
      exact congrArg Subtype.val h
    polynomial := by
      intro i p hp
      exact hps p hp (A i) }
  exact ⟨realizationHom data radius t (fun i => (A i).toMul.val) hr,
    realizationHom_surjective data radius t (fun i => (A i).toMul.val) hr
      (closure_module_generators π t ht hact A hspan)⟩

end CompatibleAction

theorem exists_tame_cover_data (hπ : Function.Surjective π) :
    letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
    Module.Finite (GroupRing (Lattice k)) (Additive π.ker) →
    Tame (k := k) (Additive π.ker) →
    ∃ a : ℕ, 1 ≤ a ∧ ∃ data : Datum k a,
      ConeVerifier.ConeCover (data.polynomials.map polynomialSupport) ∧
      ∀ radius : ℕ, ∃ f : FiniteCover.GroupOf data radius →* E, Function.Surjective f := by
  classical
  letI := laurentModule π hπ (MonoidHom.id (Multiplicative (Lattice k)))
  intro hfinite htame
  letI := hfinite
  choose t ht using (fun i : Fin k => hπ (Multiplicative.ofAdd (Pi.single i 1)))
  exact exists_cover_data_of_tame π t ht (laurent_action_compatible π hπ t ht) htame

end Kourovka.MetabelianEnumeration.CofinalCover
