/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Certificates.WordCertificates

/-!
# Presentation Isomorphism

A finite isomorphism-certificate alternative to enumerating Tietze moves.
The checker uses explicit words for both generator maps and finite derivations
for their relators and inverse identities.
-/

namespace Kourovka.MetabelianEnumeration.WordCertificates

def relSet {n : ℕ} (rels : List (FreeGroup (Fin n))) : Set (FreeGroup (Fin n)) :=
  {r | r ∈ rels}

structure MapsCertificate {n m : ℕ}
    (source : List (FreeGroup (Fin n))) (target : List (FreeGroup (Fin m))) where
  forward : Fin n → Word m
  backward : Fin m → Word n
  sourceProof : Fin source.length → Derivation m
  targetProof : Fin target.length → Derivation n
  sourceInverse : Fin n → Derivation n
  targetInverse : Fin m → Derivation m

def MapsCertificate.forwardMap {n m : ℕ} {source : List (FreeGroup (Fin n))}
    {target : List (FreeGroup (Fin m))} (cert : MapsCertificate source target) :=
  FreeGroup.lift (fun i => FreeGroup.mk (cert.forward i))

def MapsCertificate.backwardMap {n m : ℕ} {source : List (FreeGroup (Fin n))}
    {target : List (FreeGroup (Fin m))} (cert : MapsCertificate source target) :=
  FreeGroup.lift (fun i => FreeGroup.mk (cert.backward i))

def MapsCertificate.check {n m : ℕ} {source : List (FreeGroup (Fin n))}
    {target : List (FreeGroup (Fin m))} (cert : MapsCertificate source target) : Bool :=
  decide (
    (∀ i : Fin source.length,
      (cert.sourceProof i).eval target = cert.forwardMap source[i]) ∧
    (∀ i : Fin target.length,
      (cert.targetProof i).eval source = cert.backwardMap target[i]) ∧
    (∀ i : Fin n, (cert.sourceInverse i).eval source =
      cert.backwardMap (FreeGroup.mk (cert.forward i)) * (FreeGroup.of i)⁻¹) ∧
    (∀ i : Fin m, (cert.targetInverse i).eval target =
      cert.forwardMap (FreeGroup.mk (cert.backward i)) * (FreeGroup.of i)⁻¹))

theorem lift_mapped_mk {n m : ℕ} (target : List (FreeGroup (Fin m)))
    (f : Fin n → FreeGroup (Fin m)) (w : FreeGroup (Fin n)) :
    FreeGroup.lift (fun i => PresentedGroup.mk (relSet target) (f i)) w =
      PresentedGroup.mk (relSet target) (FreeGroup.lift f w) := by
  exact (FreeGroup.lift_unique ((PresentedGroup.mk (relSet target)).comp (FreeGroup.lift f))
    (by intro i; simp)).symm

def descend {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (h : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target)) :
    PresentedGroup (relSet source) →* PresentedGroup (relSet target) :=
  PresentedGroup.toGroup (f := fun i => PresentedGroup.mk (relSet target) (f i))
    (by
      intro r hr
      rw [lift_mapped_mk]
      exact PresentedGroup.mk_eq_one_iff.mpr (h r hr))

theorem descend_of {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (h : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (i : Fin n) : descend source target f h (PresentedGroup.of i) =
      PresentedGroup.mk (relSet target) (f i) := by
  exact PresentedGroup.toGroup.of _

theorem descend_mk {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (h : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (w : FreeGroup (Fin n)) :
    descend source target f h (PresentedGroup.mk (relSet source) w) =
      PresentedGroup.mk (relSet target) (FreeGroup.lift f w) := by
  change FreeGroup.lift (fun i => PresentedGroup.mk (relSet target) (f i)) w = _
  exact lift_mapped_mk target f w

theorem exists_iso_of_maps {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) (f : Fin n → FreeGroup (Fin m))
    (g : Fin m → FreeGroup (Fin n))
    (hf : ∀ r ∈ source, FreeGroup.lift f r ∈ Subgroup.normalClosure (relSet target))
    (hg : ∀ r ∈ target, FreeGroup.lift g r ∈ Subgroup.normalClosure (relSet source))
    (hgf : ∀ i, FreeGroup.lift g (f i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet source))
    (hfg : ∀ i, FreeGroup.lift f (g i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet target)) :
    Nonempty (PresentedGroup (relSet source) ≃* PresentedGroup (relSet target)) := by
  let F := descend source target f hf
  let G := descend target source g hg
  have hGF : G.comp F = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro i
    change G (F (PresentedGroup.of i)) = PresentedGroup.of i
    rw [descend_of, descend_mk]
    have h := PresentedGroup.mk_eq_one_iff.mpr (hgf i)
    simpa only [map_mul, map_inv, mul_inv_eq_one] using h
  have hFG : F.comp G = MonoidHom.id _ := by
    apply PresentedGroup.ext
    intro i
    change F (G (PresentedGroup.of i)) = PresentedGroup.of i
    rw [descend_of, descend_mk]
    have h := PresentedGroup.mk_eq_one_iff.mpr (hfg i)
    simpa only [map_mul, map_inv, mul_inv_eq_one] using h
  exact ⟨F.toMulEquiv G hGF hFG⟩

theorem MapsCertificate.sound {n m : ℕ} {source : List (FreeGroup (Fin n))}
    {target : List (FreeGroup (Fin m))} (cert : MapsCertificate source target)
    (h : cert.check = true) :
    Nonempty (PresentedGroup (relSet source) ≃* PresentedGroup (relSet target)) := by
  have hc := of_decide_eq_true h
  obtain ⟨hs, ht, hsi, hti⟩ := hc
  apply exists_iso_of_maps source target (fun i => FreeGroup.mk (cert.forward i))
    (fun i => FreeGroup.mk (cert.backward i))
  · intro r hr
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hr
    simpa only [MapsCertificate.forwardMap, hs, List.get_eq_getElem] using
      (cert.sourceProof i).eval_mem target
  · intro r hr
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hr
    simpa only [MapsCertificate.backwardMap, ht, List.get_eq_getElem] using
      (cert.targetProof i).eval_mem source
  · intro i
    simpa only [hsi, MapsCertificate.backwardMap] using (cert.sourceInverse i).eval_mem source
  · intro i
    simpa only [hti, MapsCertificate.forwardMap] using (cert.targetInverse i).eval_mem target

theorem mk_lift_of_generator_images {n m : ℕ}
    (source : List (FreeGroup (Fin n))) (target : List (FreeGroup (Fin m)))
    (e : PresentedGroup (relSet source) →* PresentedGroup (relSet target))
    (f : Fin n → FreeGroup (Fin m))
    (hf : ∀ i, PresentedGroup.mk (relSet target) (f i) = e (PresentedGroup.of i))
    (w : FreeGroup (Fin n)) :
    PresentedGroup.mk (relSet target) (FreeGroup.lift f w) =
      e (PresentedGroup.mk (relSet source) w) := by
  have h : (PresentedGroup.mk (relSet target)).comp (FreeGroup.lift f) =
      e.comp (PresentedGroup.mk (relSet source)) := by
    apply FreeGroup.ext_hom
    intro i
    simpa only [MonoidHom.comp_apply, FreeGroup.lift_apply_of] using hf i
  exact DFunLike.congr_fun h w

/-- Every actual isomorphism has a certificate made exclusively of finite words
and finite normal-closure derivations. No semantic isomorphism is stored in the data. -/
theorem MapsCertificate.complete {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m)))
    (e : PresentedGroup (relSet source) ≃* PresentedGroup (relSet target)) :
    ∃ cert : MapsCertificate source target, cert.check = true := by
  classical
  choose f hf using fun i : Fin n =>
    PresentedGroup.mk_surjective (relSet target) (e (PresentedGroup.of i))
  choose g hg using fun i : Fin m =>
    PresentedGroup.mk_surjective (relSet source) (e.symm (PresentedGroup.of i))
  have hF := mk_lift_of_generator_images source target e.toMonoidHom f hf
  have hG := mk_lift_of_generator_images target source e.symm.toMonoidHom g hg
  have hs : ∀ i : Fin source.length,
      FreeGroup.lift f source[i] ∈ Subgroup.normalClosure (relSet target) := by
    intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [hF, PresentedGroup.one_of_mem (by simp [relSet])]
    exact e.map_one
  have ht : ∀ i : Fin target.length,
      FreeGroup.lift g target[i] ∈ Subgroup.normalClosure (relSet source) := by
    intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [hG, PresentedGroup.one_of_mem (by simp [relSet])]
    exact e.symm.map_one
  have hi : ∀ i : Fin n, FreeGroup.lift g (f i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet source) := by
    intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [map_mul, map_inv, hG, hf]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, PresentedGroup.of,
      mul_inv_cancel]
  have hj : ∀ i : Fin m, FreeGroup.lift f (g i) * (FreeGroup.of i)⁻¹ ∈
      Subgroup.normalClosure (relSet target) := by
    intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [map_mul, map_inv, hF, hg]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, PresentedGroup.of,
      mul_inv_cancel]
  choose ds hds using fun i => (hasDerivation_iff target _).mpr (hs i)
  choose dt hdt using fun i => (hasDerivation_iff source _).mpr (ht i)
  choose di hdi using fun i => (hasDerivation_iff source _).mpr (hi i)
  choose dj hdj using fun i => (hasDerivation_iff target _).mpr (hj i)
  refine ⟨⟨fun i => (f i).toWord, fun i => (g i).toWord, ds, dt, di, dj⟩, ?_⟩
  simp only [MapsCertificate.check, MapsCertificate.forwardMap, MapsCertificate.backwardMap,
    FreeGroup.mk_toWord, decide_eq_true_eq]
  exact ⟨hds, hdt, hdi, hdj⟩

theorem isomorphism_certificate_iff {n m : ℕ} (source : List (FreeGroup (Fin n)))
    (target : List (FreeGroup (Fin m))) :
    (∃ cert : MapsCertificate source target, cert.check = true) ↔
      Nonempty (PresentedGroup (relSet source) ≃* PresentedGroup (relSet target)) := by
  constructor
  · rintro ⟨cert, hcert⟩
    exact cert.sound hcert
  · rintro ⟨e⟩
    exact MapsCertificate.complete source target e

end Kourovka.MetabelianEnumeration.WordCertificates
