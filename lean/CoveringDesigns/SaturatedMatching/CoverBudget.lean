import CoveringDesigns.SaturatedMatching.CompleteMatching

/-! Exact zero-loss and excess consequences for complete actual matchings.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset TwoKMinusTwo C20_11_3
variable {α M : Type*} [Fintype α] [DecidableEq α] [Fintype M] [DecidableEq M]
variable {C : Family α}

namespace CoverMatching
variable (T : CoverMatching (M := M) C)

/-- Completeness identifies every residual saturated pair with a different
matching edge. It is not inferred from an assignment coordinate. -/
theorem cross_card_bound (e : M) :
    (T.split e).crosses.card ≤ Fintype.card M - 1 := by
  classical
  let s := T.split e
  have hc (z : s.crosses) := T.complete z.val.1 z.val.2
    (s.cross_endpoints z).2.2.2.2 (mem_filter.mp z.property).2
  choose f hf using hc
  have hne (z : s.crosses) : f z ≠ e := by
    intro he
    have hm : z.val.1 ∈ ({T.point (e,true),T.point (e,false)} : Finset α) := by
      have hh := hf z
      rw [he] at hh
      rw [← hh]; simp
    exact (mem_sdiff.mp (mem_product.mp (mem_filter.mp z.property).1).1).2 hm
  let g : s.crosses → (univ.erase e : Finset M) :=
    fun z => ⟨f z,mem_erase.mpr ⟨hne z,mem_univ _⟩⟩
  have hi : Function.Injective g := by
    intro z w he
    have hfw : f z = f w := congrArg Subtype.val he
    have heq : ({z.val.1,z.val.2} : Finset α) = {w.val.1,w.val.2} :=
      (hf z).trans (hfw ▸ (hf w).symm)
    obtain ⟨hzX,hzY⟩ := mem_product.mp (mem_filter.mp z.property).1
    obtain ⟨hwX,hwY⟩ := mem_product.mp (mem_filter.mp w.property).1
    have h1 : z.val.1 = w.val.1 := by
      have hm : z.val.1 ∈ ({w.val.1,w.val.2} : Finset α) := by rw [← heq]; simp
      rcases mem_insert.mp hm with h | h
      · exact h
      · exact (disjoint_left.mp s.geometry.1 hzX (mem_singleton.mp h ▸ hwY)).elim
    have h2 : z.val.2 = w.val.2 := by
      have hm : z.val.2 ∈ ({w.val.1,w.val.2} : Finset α) := by rw [← heq]; simp
      rcases mem_insert.mp hm with h | h
      · exact (disjoint_left.mp s.geometry.1 (h ▸ hwX) hzY).elim
      · exact mem_singleton.mp h
    exact Subtype.ext (Prod.ext h1 h2)
  have hh := Fintype.card_le_of_injective g hi
  simpa only [Fintype.card_coe,card_erase_of_mem (mem_univ e),card_univ] using hh

theorem four_zero (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) (hM : Fintype.card M = 4) (e : M) :
    (T.split e).loss = 0 ∧ (T.split e).excess = 0 := by
  have hs := (T.split e).small_budget hv hC hb
  have hc := T.cross_card_bound e
  rw [hM] at hc
  omega

theorem cross_exact (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) (hM : Fintype.card M = 4)
    (e : M) {x y : α} (hx : x ∈ (T.split e).X) (hy : y ∈ (T.split e).Y)
    (hfloor : 3 ≤ degree (star C x) y) : degree (star C x) y = 3 := by
  have he := (T.four_zero hv hC hb hM e).2
  have hh := single_le_sum (s := (T.split e).X ×ˢ (T.split e).Y)
    (f := fun z : α × α => degree (star C z.1) z.2 - 3)
    (fun _ _ => Nat.zero_le _) (show (x,y) ∈ (T.split e).X ×ˢ (T.split e).Y from
      mem_product.mpr ⟨hx,hy⟩)
  change degree (star C x) y - 3 ≤ (T.split e).excess at hh
  omega

end CoverMatching

namespace Split
variable {p q : α} (s : Split C p q 31)

/-- A zero total loss makes each endpoint-only block balanced, and gives
the size-sixteen intersection separately from the abstract pattern theorem. -/
theorem balanced_intersections (hC : IsCover C 31 3) (hz : s.loss = 0)
    {A : Finset α} (hA : A ∈ C) (honly : (p ∈ A ↔ q ∉ A)) :
    (s.left ∩ A).card = 16 ∧ (s.right ∩ A).card = 16 := by
  have hi : (A ∩ {p,q}).card = 1 := by
    by_cases hp : p ∈ A
    · have hq := honly.mp hp
      have he : A ∩ {p,q} = {p} := by ext x; simp; aesop
      rw [he,card_singleton]
    · have hq : q ∈ A := by tauto
      have he : A ∩ {p,q} = {q} := by ext x; simp; aesop
      rw [he,card_singleton]
  have hcap : s.cap A = 225 := by
    by_cases hp : p ∈ A <;> have hq := honly <;>
      simp_all [cap,capacity]
  have hw := balanced_of_loss_zero C s.weight s.cap (s.capacity_bound hC) hz A hA
  rw [hcap] at hw
  change (s.X ∩ A).card * (s.Y ∩ A).card = 225 at hw
  have hs := trace_sum s.geometry.1 s.geometry.2.2.2 A
  rw [hi,hC.1 A hA] at hs
  have hbal : (s.X ∩ A).card = 15 ∧ (s.Y ∩ A).card = 15 := by
    have hs' : ((s.X ∩ A).card : ℤ) + (s.Y ∩ A).card = 30 := by omega
    have hw' : ((s.X ∩ A).card : ℤ) * (s.Y ∩ A).card = 225 := by exact_mod_cast hw
    have he : ((s.X ∩ A).card : ℤ) - 15 = 0 := by
      apply mul_self_eq_zero.mp
      nlinarith
    omega
  have count (D : Finset α) (hD : {p,q} ⊆ D) :
      (D ∩ A).card = ((D \ {p,q}) ∩ A).card + 1 := by
    have hh := card_sdiff_add_card_inter (D ∩ A) {p,q}
    have h1 : (D ∩ A) \ {p,q} = (D \ {p,q}) ∩ A := by ext x; simp; tauto
    have h2 : (D ∩ A) ∩ {p,q} = A ∩ {p,q} := by
      ext x; simp only [mem_inter]; constructor
      · tauto
      · rintro ⟨ha,hpq⟩; exact ⟨⟨hD hpq,ha⟩,hpq⟩
    rw [h1,h2,hi] at hh
    omega
  have hl := count s.left (by simpa only [insert_subset_iff,singleton_subset_iff] using s.endpoints_left)
  have hr := count s.right (by simpa only [insert_subset_iff,singleton_subset_iff] using s.endpoints_right)
  change (s.left ∩ A).card = (s.X ∩ A).card + 1 at hl
  change (s.right ∩ A).card = (s.Y ∩ A).card + 1 at hr
  omega

end Split
end CoveringDesigns.SaturatedMatching
