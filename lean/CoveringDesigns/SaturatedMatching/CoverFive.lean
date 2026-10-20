import CoveringDesigns.SaturatedMatching.CoverFour

/-! The five-pair excess obstruction in an ordinary covering.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset TwoKMinusTwo C20_11_3
variable {α M : Type*} [Fintype α] [DecidableEq α] [Fintype M] [DecidableEq M]
variable {C : Family α}

namespace Split
variable {p q : α} (s : Split C p q 31)
theorem orient_cross {x y : α} (hx : x ≠ p ∧ x ≠ q) (hy : y ≠ p ∧ y ≠ q)
    (hsep : x ∈ s.left ↔ y ∉ s.left) :
    ∃ z ∈ s.X ×ˢ s.Y, ({z.1,z.2} : Finset α) = {x,y} := by
  rcases s.residual_of_separated hx hy hsep with h | h
  · exact ⟨(x,y),mem_product.mpr h,rfl⟩
  · exact ⟨(y,x),mem_product.mpr ⟨h.2,h.1⟩,pair_comm _ _⟩

/-- Two distinct actual residual pairs of multiplicity four already exceed
the entire five-edge budget. -/
theorem excess_two {z w : α × α} (hz : z ∈ s.X ×ˢ s.Y) (hw : w ∈ s.X ×ˢ s.Y)
    (hzw : z ≠ w) (hz4 : degree (star C z.1) z.2 = 4)
    (hw4 : degree (star C w.1) w.2 = 4) : 2 ≤ s.excess := by
  have hh := sum_le_sum_of_subset_of_nonneg
    (f := fun z : α × α => degree (star C z.1) z.2 - 3)
    (s := {z,w}) (t := s.X ×ˢ s.Y)
    (by simpa only [insert_subset_iff,singleton_subset_iff] using And.intro hz hw)
    (fun _ _ _ => Nat.zero_le _)
  rw [sum_pair hzw,hz4,hw4] at hh
  exact hh
end Split

namespace CoverMatching
variable (T : CoverMatching (M := M) C)
include T

theorem not_five (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) (hM : Fintype.card M = 5) : False := by
  let P := T.pattern hv hC hb
  obtain ⟨f,_,g,_,hfg⟩ := one_lt_card.mp
    (show 1 < (univ : Finset M).card by simpa [hM])
  obtain ⟨e,hef,heg,b,c,h1,h2,hs1,hs2⟩ :=
    five_pair_excess P hM (T.endpoint_degree hv hC hb)
      (fun f g hfg b c => T.pair_floor hv hC hb _ g c
        (T.point_ne hfg b c) (T.point_ne hfg b (!c))) f g hfg
  obtain ⟨z,hz,hze⟩ := (T.split e).orient_cross
    ⟨T.point_ne hef.symm b true,T.point_ne hef.symm b false⟩
    ⟨T.point_ne heg.symm c true,T.point_ne heg.symm c false⟩ (hs1 true)
  obtain ⟨w,hw,hwe⟩ := (T.split e).orient_cross
    ⟨T.point_ne hef.symm (!b) true,T.point_ne hef.symm (!b) false⟩
    ⟨T.point_ne heg.symm (!c) true,T.point_ne heg.symm (!c) false⟩ (hs2 true)
  have hzw : z ≠ w := by
    intro he
    have hpairs : ({T.point (f,b),T.point (g,c)} : Finset α) =
        {T.point (f,!b),T.point (g,!c)} := hze.symm.trans (he ▸ hwe)
    have hm : T.point (f,b) ∈ ({T.point (f,!b),T.point (g,!c)} : Finset α) := by
      rw [← hpairs]; simp
    rcases mem_insert.mp hm with hh | hh
    · have heq := congrArg Prod.snd (T.injective hh)
      cases b <;> simp at heq
    · exact T.point_ne hfg b (!c) (mem_singleton.mp hh)
  have hz4 : degree (star C z.1) z.2 = 4 := by
    rw [← family_pair C,hze]
    exact h1
  have hw4 : degree (star C w.1) w.2 = 4 := by
    rw [← family_pair C,hwe]
    exact h2
  have hlarge := (T.split e).excess_two hz hw hzw hz4 hw4
  have hsmall := (T.split e).small_budget hv hC hb
  omega

end CoverMatching
end CoveringDesigns.SaturatedMatching
