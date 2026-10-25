import CoveringDesigns.SevenBlock.Degrees
import CoveringDesigns.SevenBlock.SupportShadow

/-! Full low-support pair shadow, including the a=2 zero-shadow boundary. -/
namespace CoveringDesigns.SevenBlock
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem low_support_shadow {a : ℕ} (ha : 2 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1)
    (hi : Fintype.card I = 7) (p q : V) (hpq : p ≠ q)
    (hp : indexedDegree B p = 4) (hq : indexedDegree B q = 4)
    (hr : ∀ x, x ≠ p → x ≠ q → indexedDegree B x = 3)
    (P : Finset I) (hP : P.card = 2) :
    0 < indexedSubsetDegree (remainingSupports B {p,q}) P := by
  let S := remainingSupports B {p,q}
  have hs : ∀ x, (S x).card = 3 := by
    intro x
    exact hr x.val (fun hx => x.property (by simp [hx])) (fun hx => x.property (by simp [hx]))
  have hm : ∀ x y, x ≠ y → (S x ∩ S y).Nonempty := by
    intro x y hxy
    exact pointSupports_meet h x.val y.val (fun he => hxy (Subtype.ext he))
  have hc : Fintype.card {x : V // x ∉ ({p,q} : Finset V)} = 7*a+2 := by
    rw [Multicover.subset_complement_card,card_pair hpq,hv]
    omega
  have hdiv : Fintype.card {x : V // x ∉ ({p,q} : Finset V)} * Nat.choose 3 2 =
      (Fintype.card I).choose 2 * a + 6 := by
    rw [hc,hi]
    norm_num [show Nat.choose 7 2 = 21 by decide,show Nat.choose 3 2 = 3 by decide]
    omega
  have hz : indexedSubsetDegree B {p,q} ≤ 4 := by
    rw [← pointSupport_pair]
    exact (card_le_card inter_subset_left).trans_eq hp
  have hb : partialOverlap S 3 + 2 * supportImbalance S a 6 ≤ 6 := by
    have hh := covering_slack hv h.1 hi p q hpq hp hq
    change partialOverlap S 3 + 2 * supportImbalance S a 6 = _ at hh
    omega
  exact shadow_positive S ha hi hs hm hdiv hb P hP

#guard_standard_axioms low_support_shadow

end CoveringDesigns.SevenBlock
