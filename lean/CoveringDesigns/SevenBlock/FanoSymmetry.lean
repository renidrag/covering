import CoveringDesigns.SevenBlock.Fano
import CoveringDesigns.Foundations.Relabelling

/-! Normalising exceptional supports inside the fixed Fano plane. These
finite incidence checks concern only the seven-position plane and its binary
linear coordinate maps. They do not enumerate coverings or bound a parameter.
The universal counting and recognition arguments are in separate modules. -/
namespace CoveringDesigns.SevenBlock
open Finset

private def third (p q : Fin 7) : Fin 7 :=
  Fin.ofNat 7 ((Nat.xor (p.val+1) (q.val+1))-1)

private def basis (p q r : Fin 7) : Prop :=
  p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ third p q ≠ r

private def frameMap (p q r : Fin 7) : Fin 7 → Fin 7 :=
  ![p,q,third p q,r,third p r,third q r,third (third p q) r]

section FixedPlane
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

private instance (p q r : Fin 7) : Decidable (basis p q r) := inferInstanceAs
  (Decidable (p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ third p q ≠ r))

private theorem frame_injective : ∀ p q r, basis p q r → Function.Injective (frameMap p q r) := by
  unfold Function.Injective
  decide +kernel

private theorem frame_lines : ∀ p q r, basis p q r → ∀ l,
    ∃ m, (line l).image (frameMap p q r) = line m := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 10000 in
private theorem exceptional_normalisation :
    ∀ H ∈ (univ : Finset (Fin 7)).powersetCard 4,
    ∀ G ∈ (univ : Finset (Fin 7)).powersetCard 4,
      (∀ l, (H ∩ line l).Nonempty ∧ (G ∩ line l).Nonempty) →
      (∀ l, Even ((H ∩ line l).card + (G ∩ line l).card)) →
      ((H ∩ G).card = 2 ∨ (H ∩ G).card = 4) →
      ∃ p q r : Fin 7, basis p q r ∧
        ((H.image (frameMap p q r) = highSupport ((H ∩ G).card == 4) false ∧
          G.image (frameMap p q r) = highSupport ((H ∩ G).card == 4) true) ∨
         (H.image (frameMap p q r) = highSupport ((H ∩ G).card == 4) true ∧
          G.image (frameMap p q r) = highSupport ((H ∩ G).card == 4) false)) := by
  decide +kernel

end FixedPlane

/-- The two exceptional supports are normalised by a Fano automorphism.
The parity premise is supplied by the integer incidence inverse. -/
theorem exceptional_support_normal_form (H G : Finset (Fin 7))
    (hH : H.card = 4) (hG : G.card = 4)
    (hm : ∀ l, (H ∩ line l).Nonempty ∧ (G ∩ line l).Nonempty)
    (heven : ∀ l, Even ((H ∩ line l).card + (G ∩ line l).card))
    (hinter : (H ∩ G).card = 2 ∨ (H ∩ G).card = 4) :
    ∃ (e : Equiv.Perm (Fin 7)) (tag swap : Bool),
      relabel e (univ.image line) = univ.image line ∧
      H.map e.toEmbedding = highSupport tag swap ∧
      G.map e.toEmbedding = highSupport tag (!swap) := by
  classical
  obtain ⟨p,q,r,hb,hn⟩ := exceptional_normalisation H (mem_powersetCard_univ.mpr hH)
    G (mem_powersetCard_univ.mpr hG) hm heven hinter
  let e := Equiv.ofBijective (frameMap p q r)
    ⟨frame_injective p q r hb,Finite.surjective_of_injective (frame_injective p q r hb)⟩
  have he : relabel e (univ.image line) = univ.image line := by
    apply eq_of_subset_of_card_le
    · intro L hL
      obtain ⟨M,hM,rfl⟩ := mem_map.mp hL
      obtain ⟨l,_,rfl⟩ := mem_image.mp hM
      obtain ⟨m,hm⟩ := frame_lines p q r hb l
      apply mem_image.mpr
      refine ⟨m,mem_univ _,?_⟩
      change line m = (line l).map e.toEmbedding
      rw [map_eq_image]
      change line m = (line l).image (frameMap p q r)
      exact hm.symm
    · rw [relabel_card]
  rcases hn with hn | hn
  · exact ⟨e,((H ∩ G).card == 4),false,he,
      by rw [map_eq_image]; exact hn.1,
      by rw [map_eq_image]; exact hn.2⟩
  · exact ⟨e,((H ∩ G).card == 4),true,he,
      by rw [map_eq_image]; exact hn.1,
      by rw [map_eq_image]; exact hn.2⟩

#guard_standard_axioms exceptional_support_normal_form

end CoveringDesigns.SevenBlock
