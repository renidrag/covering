import CoveringDesigns.PairConsequences.Primitive
import CoveringDesigns.PairConsequences.Intervals

namespace CoveringDesigns.PairConsequences
open Finset

def replicatedFamily {X : Type*} [DecidableEq X] (C : Family X) (m : ℕ) :
    Family (X × Fin m) := C.image (fun A => A ×ˢ univ)

theorem replication_injective {X : Type*} [DecidableEq X] {m : ℕ} (hm : 0 < m) :
    Function.Injective (fun A : Finset X => A ×ˢ (univ : Finset (Fin m))) := by
  intro A B he
  ext x
  have h := congrArg (fun S => (x,⟨0,hm⟩) ∈ S) he
  simpa using h

/-- Actual positive-fibre replication, retaining the original block images. -/
theorem primitive_replication {X : Type*} [Fintype X] [DecidableEq X]
    {q m : ℕ} {C : Family X} (hq : 2 ≤ q) (hm : 0 < m)
    (hv : Fintype.card X = q*(q+1)) (hC : IsCover C (q+1) 2)
    (hc : C.card = q*(q+1)) :
    Fintype.card (X × Fin m) = q*((q+1)*m) ∧
      IsCover (replicatedFamily C m) ((q+1)*m) 2 ∧
      (replicatedFamily C m).card = q*(q+1) ∧
      ∀ A ∈ C, ∀ p : X × Fin m, p ∈ A ×ˢ (univ : Finset (Fin m)) ↔ p.1 ∈ A := by
  refine ⟨by simp [hv,Nat.mul_assoc],⟨?_,?_⟩,?_,?_⟩
  · intro B hB
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hB
    simp [hC.1 A hA]
  · intro S hS
    obtain ⟨A,hA,hSA⟩ := AffineConstructions.covers_subset_of_card_le hC.2
      (by rw [hv]; nlinarith : 2 ≤ Fintype.card X) (S.image Prod.fst)
      (card_image_le.trans_eq hS)
    refine ⟨A ×ˢ univ,mem_image.mpr ⟨A,hA,rfl⟩,?_⟩
    intro p hp
    exact mem_product.mpr ⟨hSA (mem_image.mpr ⟨p,hp,rfl⟩),mem_univ _⟩
  · rw [replicatedFamily,card_image_of_injective _ (replication_injective hm),hc]
  · intro A hA p
    simp

/-- An actual primitive witness gives exact replicated coverings on arbitrary
labels. No assertion of primitive existence is made. -/
theorem replication_exact {X Y : Type*} [Fintype X] [Fintype Y]
    {q m : ℕ} {C : Family X} (hq : 2 ≤ q) (hm : 0 < m)
    (hv : Fintype.card X = q*(q+1)) (hC : IsCover C (q+1) 2)
    (hc : C.card = q*(q+1)) (hy : Fintype.card Y = q*((q+1)*m)) :
    (∃ D : Family Y, IsCover D ((q+1)*m) 2 ∧ D.card = q*(q+1)) ∧
      (∀ D : Family Y, IsCover D ((q+1)*m) 2 → q*(q+1) ≤ D.card) := by
  classical
  obtain ⟨hp,hD,hd,_⟩ := primitive_replication hq hm hv hC hc
  let e : X × Fin m ≃ Y := Fintype.equivOfCardEq (hp.trans hy.symm)
  refine ⟨⟨relabel e (replicatedFamily C m),relabel_isCover e hD,?_⟩,?_⟩
  · rw [relabel_card]
    exact hd
  · intro D hD
    simpa using indexed_pair_floor hq (show q ≤ (q+1)*m by nlinarith) hy
      ((Multicover.ofFamily_isCover_one D ((q+1)*m) 2).mpr hD)

end CoveringDesigns.PairConsequences
