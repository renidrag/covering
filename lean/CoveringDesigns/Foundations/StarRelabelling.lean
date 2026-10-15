import CoveringDesigns.Foundations.Links
import CoveringDesigns.Foundations.Relabelling
import CoveringDesigns.Foundations.Stars

/-! Relabelling and deletion identities used by the minimum-star catalogue.
These statements concern arbitrary finite families, independently of the
finite catalogue and of its computational checks. -/

namespace CoveringDesigns

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def complementEquiv (e : α ≃ β) (p : α) :
    {q : α // q ≠ p} ≃ {q : β // q ≠ e p} where
  toFun q := ⟨e q.val, fun h => q.property (e.injective h)⟩
  invFun q := ⟨e.symm q.val, fun h => q.property (by simpa [h] using (e.apply_symm_apply q.val).symm)⟩
  left_inv q := by ext; simp
  right_inv q := by ext; simp

@[simp] theorem complementEquiv_apply (e : α ≃ β) (p : α)
    (q : {q : α // q ≠ p}) : (complementEquiv e p q).val = e q.val := rfl

@[simp] theorem relabel_refl (C : Family α) : relabel (Equiv.refl α) C = C := by
  ext B
  simp [relabel]

@[simp] theorem relabel_symm_relabel (e : α ≃ β) (C : Family α) :
    relabel e.symm (relabel e C) = C := by
  rw [relabel_trans]
  simpa using relabel_refl C

theorem relabel_injective (e : α ≃ β) : Function.Injective (relabel e) := by
  intro C D h
  simpa using congrArg (relabel e.symm) h

theorem subtype_map_complement (e : α ≃ β) (p : α) (B : Finset α) :
    (B.map e.toEmbedding).subtype (· ≠ e p) =
      (B.subtype (· ≠ p)).map (complementEquiv e p).toEmbedding := by
  ext q
  simp only [mem_subtype, mem_map]
  constructor
  · rintro ⟨a, ha, he⟩
    have hp : a ≠ p := by intro h; subst a; exact q.property he.symm
    refine ⟨⟨a, hp⟩, ?_, ?_⟩
    · simpa using ha
    · exact Subtype.ext he
  · rintro ⟨a, ha, he⟩
    exact ⟨a.val, by simpa using ha, congrArg Subtype.val he⟩

theorem outside_relabel (e : α ≃ β) (C : Family α) (p : α) :
    outside (relabel e C) (e p) = relabel e (outside C p) := by
  unfold outside relabel
  rw [filter_map]
  congr 1
  ext B
  simp [Function.comp_def]

/-- The blocks avoiding a point, regarded on its complement. -/
def puncturedOutside (C : Family α) (p : α) : Family {q : α // q ≠ p} :=
  (outside C p).image (Finset.subtype (· ≠ p))

theorem image_subtype_relabel (e : α ≃ β) (C : Family α) (p : α) :
    (relabel e C).image (Finset.subtype (· ≠ e p)) =
      relabel (complementEquiv e p) (C.image (Finset.subtype (· ≠ p))) := by
  ext B
  simp only [relabel, mem_image, mem_map]
  constructor
  · rintro ⟨D, ⟨A, ha, rfl⟩, rfl⟩
    refine ⟨A.subtype (· ≠ p), ⟨A, ha, rfl⟩, ?_⟩
    exact (subtype_map_complement e p A).symm
  · rintro ⟨D, ⟨A, ha, rfl⟩, rfl⟩
    exact ⟨A.map e.toEmbedding, ⟨A, ha, rfl⟩, subtype_map_complement e p A⟩

theorem link_relabel (e : α ≃ β) (C : Family α) (p : α) :
    link (relabel e C) (e p) = relabel (complementEquiv e p) (link C p) := by
  unfold link
  rw [star_relabel, image_subtype_relabel]

theorem puncturedOutside_relabel (e : α ≃ β) (C : Family α) (p : α) :
    puncturedOutside (relabel e C) (e p) =
      relabel (complementEquiv e p) (puncturedOutside C p) := by
  unfold puncturedOutside
  rw [outside_relabel, image_subtype_relabel]

def forgetComplement (p : α) (D : Family {q : α // q ≠ p}) : Family α :=
  D.image (fun B => B.map (Function.Embedding.subtype _))

def adjoinComplement (p : α) (D : Family {q : α // q ≠ p}) : Family α :=
  (forgetComplement p D).image (insert p)

theorem map_subtype_of_notMem (p : α) (B : Finset α) (hp : p ∉ B) :
    (B.subtype (· ≠ p)).map (Function.Embedding.subtype _) = B := by
  ext q
  simp only [mem_map]
  constructor
  · rintro ⟨r, hr, rfl⟩
    simpa using hr
  · intro hq
    refine ⟨⟨q, ?_⟩, ?_, rfl⟩
    · intro h; subst q; exact hp hq
    · simpa using hq

theorem forgetComplement_puncturedOutside (C : Family α) (p : α) :
    forgetComplement p (puncturedOutside C p) = outside C p := by
  unfold forgetComplement puncturedOutside
  rw [image_image]
  ext B
  simp only [mem_image]
  constructor
  · rintro ⟨D, hD, h⟩
    rw [Function.comp_apply, map_subtype_of_notMem p D (mem_filter.mp hD).2] at h
    simpa [← h] using hD
  · intro hB
    exact ⟨B, hB, map_subtype_of_notMem p B (mem_filter.mp hB).2⟩

theorem adjoinComplement_puncturedOutside (C : Family α) (p : α) :
    adjoinComplement p (puncturedOutside C p) = (outside C p).image (insert p) := by
  unfold adjoinComplement
  rw [forgetComplement_puncturedOutside]

/-- Change canonical coordinates through an isomorphism, then return to the
original family's canonical coordinates. -/
theorem relabel_transport {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (e : α ≃ β) (k : α ≃ γ) (l : β ≃ δ) (C : Family α) :
    relabel (l.symm.trans (e.symm.trans k)) (relabel l (relabel e C)) =
      relabel k C := by
  rw [← relabel_trans, relabel_symm_relabel, ← relabel_trans, relabel_symm_relabel]

def canonicalTransport {γ δ : Type*} (e : α ≃ β) (p : α)
    (k : {q : α // q ≠ p} ≃ γ) (l : {q : β // q ≠ e p} ≃ δ) : δ ≃ γ :=
  l.symm.trans ((complementEquiv e p).symm.trans k)

theorem canonicalTransport_link {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (e : α ≃ β) (p : α) (k : {q : α // q ≠ p} ≃ γ)
    (l : {q : β // q ≠ e p} ≃ δ) (C : Family α) :
    relabel (canonicalTransport e p k l) (relabel l (link (relabel e C) (e p))) =
      relabel k (link C p) := by
  rw [link_relabel]
  exact relabel_transport (complementEquiv e p) k l (link C p)

theorem canonicalTransport_outside {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (e : α ≃ β) (p : α) (k : {q : α // q ≠ p} ≃ γ)
    (l : {q : β // q ≠ e p} ≃ δ) (C : Family α) :
    relabel (canonicalTransport e p k l)
        (relabel l (puncturedOutside (relabel e C) (e p))) =
      relabel k (puncturedOutside C p) := by
  rw [puncturedOutside_relabel]
  exact relabel_transport (complementEquiv e p) k l (puncturedOutside C p)

end CoveringDesigns
