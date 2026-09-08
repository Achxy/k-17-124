/-
Authors: Achyuth Jayadevan
Released under CC0 1.0 Universal; see LICENSE.
-/
import Kourovka.Certificates.ComputableIsomorphism

/-!
# Isomorphism Semantics

Soundness and completeness of the natural-alphabet isomorphism equations.
-/

namespace Kourovka.MetabelianEnumeration.ComputableIsomorphism

open NaturalWordSubstitution NaturalWordCertificates ComputablePresentations

def GoodMaps (pq : PresentationCode × PresentationCode) (fg : Maps) : Prop :=
  (∀ w ∈ pq.1.2, Good (pq.2, substitute fg.1 w)) ∧
    (∀ w ∈ pq.2.2, Good (pq.1, substitute fg.2 w)) ∧
      (∀ i < pq.1.1, Good (pq.1, substitute fg.2 (fg.1.getD i []) ++ [(i, false)])) ∧
        (∀ i < pq.2.1, Good (pq.2, substitute fg.1 (fg.2.getD i []) ++ [(i, false)]))

theorem good_obligations (pq : PresentationCode × PresentationCode) (fg : Maps) :
    (∀ input ∈ obligations (pq, fg), Good input) ↔ GoodMaps pq fg := by
  simp only [obligations, List.forall_mem_append, relatorChecks, inverseChecks,
    List.forall_mem_map, List.mem_range, GoodMaps, and_assoc]

theorem goodMaps_sound (pq : PresentationCode × PresentationCode) (fg : Maps)
    (hv : validMaps (pq, fg)) (hg : GoodMaps pq fg) :
    Nonempty (GroupOf pq.1 ≃* GroupOf pq.2) := by
  rcases hv with ⟨hp, hq, _, _, hfvalid, hgvalid⟩
  rcases hg with ⟨hforward, hback, hgf, hfg⟩
  apply WordCertificates.exists_iso_of_maps
    (pq.1.2.map (interpretWord pq.1.1)) (pq.2.2.map (interpretWord pq.2.1))
    (fun i => interpretWord pq.2.1 (fg.1.getD i.val []))
    (fun i => interpretWord pq.1.1 (fg.2.getD i.val []))
  · intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_substitute pq.1.1 pq.2.1 fg.1 w (hp w hw)]
    exact (hforward w hw).2
  · intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_substitute pq.2.1 pq.1.1 fg.2 w (hq w hw)]
    exact (hback w hw).2
  · intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_inverseCheck pq.1.1 pq.2.1 fg.1 fg.2 hfvalid i.val i.isLt]
    exact (hgf i.val i.isLt).2
  · intro i
    apply PresentedGroup.mk_eq_one_iff.mp
    rw [← interpret_inverseCheck pq.2.1 pq.1.1 fg.2 fg.1 hgvalid i.val i.isLt]
    exact (hfg i.val i.isLt).2

/-- Substitution evaluates to the given homomorphism whenever its finitely
many generator images do. -/
theorem eval_substitute (p q : PresentationCode) (e : GroupOf p →* GroupOf q)
    (f : Images)
    (hf : ∀ i : Fin p.1, PresentedGroup.mk (relations q)
      (interpretWord q.1 (f.getD i.val [])) = e (PresentedGroup.of i))
    (w : Word) (hw : ValidWord p.1 w) :
    PresentedGroup.mk (relations q) (interpretWord q.1 (substitute f w)) =
      e (PresentedGroup.mk (relations p) (interpretWord p.1 w)) := by
  rw [interpret_substitute p.1 q.1 f w hw]
  have h : (PresentedGroup.mk (relations q)).comp
      (FreeGroup.lift (fun i : Fin p.1 => interpretWord q.1 (f.getD i.val []))) =
      e.comp (PresentedGroup.mk (relations p)) := by
    apply FreeGroup.ext_hom
    intro i
    simpa only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, PresentedGroup.of] using hf i
  exact DFunLike.congr_fun h _

def encodeImages {n m : ℕ} (f : Fin n → FreeGroup (Fin m)) : Images :=
  List.ofFn fun i => WordCertificates.encodeWord (f i).toWord

@[simp] theorem encodeImages_length {n m : ℕ} (f : Fin n → FreeGroup (Fin m)) :
    (encodeImages f).length = n := by simp [encodeImages]

theorem encodeImages_wellFormed {n m : ℕ} (f : Fin n → FreeGroup (Fin m)) :
    WellFormed (m, encodeImages f) := by
  intro w hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
  exact valid_encode _

@[simp] theorem interpret_encodeImages_getD {n m : ℕ} (f : Fin n → FreeGroup (Fin m))
    (i : Fin n) : interpretWord m ((encodeImages f).getD i.val []) = f i := by
  rw [List.getD_eq_getElem _ _ (by simp [encodeImages])]
  simp [encodeImages, WordCertificates.interpret_encodeWord, FreeGroup.mk_toWord]

/-- Every actual ordinary-presentation isomorphism admits finite natural
words satisfying all relator and inverse-generator equations. -/
theorem goodMaps_complete (p q : PresentationCode) (hp : WellFormed p) (hq : WellFormed q)
    (e : GroupOf p ≃* GroupOf q) :
    ∃ fg : Maps, validMaps ((p, q), fg) ∧ GoodMaps (p, q) fg := by
  classical
  choose f hf using fun i : Fin p.1 => PresentedGroup.mk_surjective (relations q) (e (PresentedGroup.of i))
  choose g hg using fun i : Fin q.1 => PresentedGroup.mk_surjective (relations p) (e.symm (PresentedGroup.of i))
  let F := encodeImages f
  let G := encodeImages g
  have hF : WellFormed (q.1, F) := encodeImages_wellFormed f
  have hG : WellFormed (p.1, G) := encodeImages_wellFormed g
  have hf' : ∀ i : Fin p.1, PresentedGroup.mk (relations q)
      (interpretWord q.1 (F.getD i.val [])) = e (PresentedGroup.of i) := by
    intro i; simpa only [F, interpret_encodeImages_getD] using hf i
  have hg' : ∀ i : Fin q.1, PresentedGroup.mk (relations p)
      (interpretWord p.1 (G.getD i.val [])) = e.symm (PresentedGroup.of i) := by
    intro i; simpa only [G, interpret_encodeImages_getD] using hg i
  refine ⟨(F, G), ⟨hp, hq, encodeImages_length f, encodeImages_length g, hF, hG⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    refine ⟨⟨hq, valid_substitute q.1 F hF w⟩, ?_⟩
    rw [eval_substitute p q e.toMonoidHom F hf' w (hp w hw)]
    rw [PresentedGroup.one_of_mem (List.mem_map.mpr ⟨w, hw, rfl⟩), map_one]
  · intro w hw
    refine ⟨⟨hp, valid_substitute p.1 G hG w⟩, ?_⟩
    rw [eval_substitute q p e.symm.toMonoidHom G hg' w (hq w hw)]
    rw [PresentedGroup.one_of_mem (List.mem_map.mpr ⟨w, hw, rfl⟩), map_one]
  · intro i hi
    have hvi : ValidWord p.1 [(i, false)] := by intro z hz; simpa using List.mem_singleton.mp hz ▸ hi
    refine ⟨⟨hp, valid_append (valid_substitute p.1 G hG _) hvi⟩, ?_⟩
    rw [interpret_append, map_mul, interpret_singleton_false p.1 i hi, map_inv,
      eval_substitute q p e.symm.toMonoidHom G hg' _ (valid_getD q.1 F hF i),
      hf' ⟨i, hi⟩]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, PresentedGroup.of, mul_inv_cancel]
  · intro i hi
    have hvi : ValidWord q.1 [(i, false)] := by intro z hz; simpa using List.mem_singleton.mp hz ▸ hi
    refine ⟨⟨hq, valid_append (valid_substitute q.1 F hF _) hvi⟩, ?_⟩
    rw [interpret_append, map_mul, interpret_singleton_false q.1 i hi, map_inv,
      eval_substitute p q e.toMonoidHom F hf' _ (valid_getD p.1 G hG i),
      hg' ⟨i, hi⟩]
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, PresentedGroup.of, mul_inv_cancel]

theorem checkIso_correct (pq : PresentationCode × PresentationCode) :
    (∃ n, checkIso pq n = true) ↔
      WellFormed pq.1 ∧ WellFormed pq.2 ∧ Nonempty (GroupOf pq.1 ≃* GroupOf pq.2) := by
  constructor
  · rintro ⟨n, hn⟩
    let c := decodeCertificate n
    have hd : checkData pq c = true := hn
    have h := (checkData_correct pq c.1).mp ⟨c.2, hd⟩
    exact ⟨h.1.1, h.1.2.1, goodMaps_sound pq c.1 h.1 ((good_obligations pq c.1).mp h.2)⟩
  · rintro ⟨hp, hq, ⟨e⟩⟩
    obtain ⟨fg, hv, hg⟩ := goodMaps_complete pq.1 pq.2 hp hq e
    obtain ⟨cs, hcs⟩ := (checkData_correct pq fg).mpr ⟨hv, (good_obligations pq fg).mpr hg⟩
    refine ⟨Encodable.encode (fg, cs), ?_⟩
    simpa only [checkIso, decodeCertificate, Encodable.encodek, Option.getD_some] using hcs

end Kourovka.MetabelianEnumeration.ComputableIsomorphism
