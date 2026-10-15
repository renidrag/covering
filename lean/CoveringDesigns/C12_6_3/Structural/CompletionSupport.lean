import CoveringDesigns.C12_6_3.Structural.Templates
import CoveringDesigns.C12_6_3.Structural.CompletionEncoding
import CoveringDesigns.Foundations.StandardAxioms

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace CoveringDesigns.GPPTStructural.CompletionVerification
open Finset

theorem pairEq_sound {p q : Pair} (h : pairEq p q = true) : pairSet p = pairSet q := by
  simp only [pairEq, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · simp [pairSet, h₁, h₂]
  · simp [pairSet, h₁, h₂, pair_comm]

theorem image_pairSet (f : Fin 12 → Fin 12) (p : Pair) :
    (pairSet p).image f = pairSet (mapPair f p) := by
  simp [pairSet, mapPair]

structure GoodAut (p : Fin 12 → Fin 12) (f : Fin 3 → Fin 3) : Prop where
  point_injective : Function.Injective p
  fibre_injective : Function.Injective f
  core_image : core.image (fun B => B.image p) = core
  spine_image : ∀ i, (spine i).image p = spine (f i)

theorem goodAut_id : GoodAut id id := by
  constructor
  · exact Function.injective_id
  · exact Function.injective_id
  · simp
  · intro i; simp

theorem GoodAut.comp {p q : Fin 12 → Fin 12} {f g : Fin 3 → Fin 3}
    (hq : GoodAut q g) (hp : GoodAut p f) : GoodAut (q ∘ p) (g ∘ f) := by
  refine ⟨hq.point_injective.comp hp.point_injective,
    hq.fibre_injective.comp hp.fibre_injective, ?_, ?_⟩
  · calc
      core.image (fun B => B.image (q ∘ p)) =
          (core.image (fun B => B.image p)).image (fun B => B.image q) := by
        simp only [image_image, Function.comp_def]
      _ = core := by rw [hp.core_image, hq.core_image]
  · intro i
    rw [← image_image, hp.spine_image, hq.spine_image]
    rfl

theorem injective_of_finRange_nodup {n : Nat} {f : Fin n → Fin n}
    (h : ((List.finRange n).map f).Nodup) : Function.Injective f := by
  intro x y hxy
  exact List.inj_on_of_nodup_map h (by simp) (by simp) hxy

def decodeCore (x : BitVec 144) : Family (Fin 12) :=
  univ.image (fun r : Fin 12 => univ.filter (fun q : Fin 12 => x.getLsbD (12*q.val+r.val)))

theorem decodeCore_image_of_bits (x y : BitVec 144)
    (π ρ : Fin 12 → Fin 12)
    (hp : Function.Injective π) (hr : Function.Surjective ρ)
    (hbits : ∀ r q, x.getLsbD (12*q.val+r.val) =
      y.getLsbD (12*(π q).val+(ρ r).val)) :
    (decodeCore x).image (fun B => B.image π) = decodeCore y := by
  have hps : Function.Surjective π := Finite.injective_iff_surjective.mp hp
  have row_eq (r : Fin 12) :
      (univ.filter (fun q : Fin 12 => x.getLsbD (12*q.val+r.val))).image π =
        univ.filter (fun q : Fin 12 => y.getLsbD (12*q.val+(ρ r).val)) := by
    ext p
    obtain ⟨q, rfl⟩ := hps p
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨q', hq', he⟩
      have heq := hp he
      subst q'
      simpa only [hbits] using hq'
    · intro hq
      exact ⟨q, by simpa only [hbits] using hq, rfl⟩
  unfold decodeCore
  rw [image_image]
  ext B
  simp only [mem_image, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨ρ r, (row_eq r).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨r, rfl⟩ := hr t
    exact ⟨r, row_eq r⟩

theorem spine_image_of_quarters (p : Fin 12 → Fin 12) (f : Fin 3 → Fin 3)
    (hp : Function.Injective p) (hf : Function.Injective f)
    (hquarters : ∀ q, (p q).val / 4 = (f ⟨q.val / 4, by omega⟩).val) :
    ∀ i, (spine i).image p = spine (f i) := by
  intro i
  ext z
  constructor
  · intro hz
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
    have hqi : (⟨q.val / 4, by omega⟩ : Fin 3) = i := by
      apply Fin.ext
      have hh : q ∈ univ.filter (fun x : Fin 12 => x.val / 4 = i.val) := by
        simpa only [← spine_eq_filter] using hq
      exact (mem_filter.mp hh).2
    rw [spine_eq_filter]
    apply mem_filter.mpr
    exact ⟨mem_univ _, by rw [hquarters, hqi]⟩
  · intro hz
    obtain ⟨q, rfl⟩ := Finite.surjective_of_injective hp z
    have he : f (⟨q.val / 4, by omega⟩ : Fin 3) = f i := by
      apply Fin.ext
      rw [← hquarters]
      have hh : p q ∈ univ.filter (fun x : Fin 12 => x.val / 4 = (f i).val) := by
        simpa only [← spine_eq_filter] using hz
      exact (mem_filter.mp hh).2
    have hqi := congrArg Fin.val (hf he)
    apply mem_image.mpr
    refine ⟨q, ?_, rfl⟩
    rw [spine_eq_filter]
    exact mem_filter.mpr ⟨mem_univ _, hqi⟩

theorem decodeCore_coreCode : decodeCore coreCode = core := by decide +kernel

theorem autCheck_sound {a : AutCert} (h : autCheck a = true) :
    GoodAut (pointMap a.1) (fibreMap a.2.2) := by
  simp only [autCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨hp, hr⟩, hf⟩, hq⟩, hb⟩
  have hp' := injective_of_finRange_nodup hp
  have hr' := injective_of_finRange_nodup hr
  have hf' := injective_of_finRange_nodup hf
  refine ⟨hp', hf', ?_, ?_⟩
  · rw [← decodeCore_coreCode]
    apply decodeCore_image_of_bits _ _ _ _ hp' (Finite.surjective_of_injective hr')
    intro r q
    exact beq_iff_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp hb r (by simp)) q (by simp))
  · apply spine_image_of_quarters _ _ hp' hf'
    intro q
    exact of_decide_eq_true (List.all_eq_true.mp hq q (by simp))

theorem image_template {p : Fin 12 → Fin 12} {f : Fin 3 → Fin 3}
    (h : GoodAut p f) (R S : Fin 3 → Finset (Fin 12))
    (hR : ∀ i, (R i).image p = S (f i)) :
    (templateBlocks R).image (fun B => B.image p) = templateBlocks S := by
  unfold templateBlocks
  rw [image_union, h.core_image, image_image]
  congr 1
  ext B
  simp only [mem_image, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨f i, by rw [image_union, h.spine_image, hR]⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ := Finite.surjective_of_injective h.fibre_injective j
    exact ⟨i, by rw [image_union, h.spine_image, hR]⟩

def transportedAdditions (p : Fin 12 → Fin 12) (f : Equiv.Perm (Fin 3))
    (R : Fin 3 → Finset (Fin 12)) : Fin 3 → Finset (Fin 12) :=
  fun i => (R (f.symm i)).image p

theorem valid_transported {p : Fin 12 → Fin 12} {f : Equiv.Perm (Fin 3)}
    (h : GoodAut p f) {R : Fin 3 → Finset (Fin 12)} (hR : ValidAdditions R) :
    ValidAdditions (transportedAdditions p f R) := by
  intro i
  constructor
  · intro z hz
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hz
    refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
    intro hq'
    have hm : p q ∈ (spine (f.symm i)).image p := by
      simpa only [h.spine_image, Equiv.apply_symm_apply] using hq'
    obtain ⟨q', hq's, he⟩ := mem_image.mp hm
    have heq := h.point_injective he
    subst q'
    exact (mem_sdiff.mp ((hR _).1 hq)).2 hq's
  · dsimp [transportedAdditions]
    rw [card_image_of_injective _ h.point_injective]
    exact (hR _).2

theorem template_isomorphic_transported {p : Fin 12 → Fin 12} {f : Equiv.Perm (Fin 3)}
    (h : GoodAut p f) (R : Fin 3 → Finset (Fin 12)) :
    Isomorphic (templateBlocks R) (templateBlocks (transportedAdditions p f R)) := by
  apply isomorphic_of_image p h.point_injective
  apply image_template h
  intro i
  simp only [transportedAdditions, Equiv.symm_apply_apply]

#guard_standard_axioms pairEq_sound image_pairSet GoodAut.comp decodeCore_image_of_bits autCheck_sound
  spine_image_of_quarters image_template valid_transported template_isomorphic_transported

end CoveringDesigns.GPPTStructural.CompletionVerification
