import CoveringDesigns.C19_9_3.BudgetTools

namespace CoveringDesigns.C19_9_3.Internal
open Finset SevenBlock
variable {X : Type*} [Fintype X] [DecidableEq X] {C : Completion X}

theorem Normalized.exclude_two_single (N : Normalized C) (hX : Fintype.card X = 11)
    (hA : (C.class 2).card = 8) (hB : (C.class 1).card = 2) (hC : (C.class 0).card = 1) : False := by
  obtain ⟨n,c,D,hcset,hcD,hD,hDL,hn,hrest,hweights⟩ := N.two_single_weights hX hB hC
  obtain ⟨x,y,hxy,hBset⟩ := card_eq_two.mp hB
  obtain ⟨l,d,b,e,hx⟩ := N.is_b x (hBset.symm ▸ (by simp))
  obtain ⟨m,t,s,f,hy⟩ := N.is_b y (hBset.symm ▸ (by simp))
  have hdn := N.extra_direction n hrest x l d b e hx
  have htn := N.extra_direction n hrest y m t s f hy
  subst d
  subst t
  have hnl : n ∉ line l := by simpa only [hx,Column.Valid] using N.valid x
  have hnm : n ∉ line m := by simpa only [hy,Column.Valid] using N.valid y
  have hbs : b ≠ s := by
    intro he
    subst s
    have hpair := N.single_pair_le x y hxy (n,b)
      (by rw [hx]; rfl) (by rw [hy]; rfl)
    change 2 ≤ N.single n b at hpair
    have hh : N.single n b = 1 := by cases b <;> simpa only [← N.single_balanced] using hn
    omega
  have hef : e ≠ f := by
    intro he
    subst f
    have hpair := N.single_row_pair_le x y hxy l m n n b s e hx hy
    have hh := C.avoiding_row e
    rw [hA] at hh
    omega
  have hpositive (k : Fin 7) : 0 < N.weight k := by
    have hk := hweights k
    have hc := card_le_card (inter_subset_right (s₁ := D) (s₂ := line k))
    rw [line_card] at hc
    split_ifs at hk <;> omega
  have nobase (k v : Fin 7) (hvk : v ∉ line k) (hvl : v ∈ line l) (hvm : v ∈ line m) :
      ∀ z ∈ C.class 1, (N.col z).base ≠ some k := by
    intro z hz heq
    rw [hBset] at hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl | rfl
    · rw [hx] at heq
      have hlk : l = k := Option.some.inj heq
      exact hvk (hlk ▸ hvl)
    · rw [hy] at heq
      have hmk : m = k := Option.some.inj heq
      exact hvk (hmk ▸ hvm)
  by_cases hlm : l = m
  · subst m
    have hw2 := N.base_pair_le x y hxy l (by rw [hx]; rfl) (by rw [hy]; rfl)
    have hmeet : (D ∩ line l).Nonempty := by
      obtain ⟨L,hL⟩ := hDL
      obtain ⟨v,hv⟩ := line_meet L l
      exact ⟨v,mem_inter.mpr ⟨hL (mem_inter.mp hv).1,(mem_inter.mp hv).2⟩⟩
    have hcard : (D ∩ line l).card = 1 := by
      have hh := hweights l
      rw [if_neg hnl] at hh
      have := card_pos.mpr hmeet
      omega
    obtain ⟨v,hv⟩ := card_eq_one.mp hcard
    have hvl : v ∈ line l := (mem_inter.mp (hv.symm ▸ mem_singleton_self v)).2
    have hnv : n ≠ v := fun he => hnl (he.symm ▸ hvl)
    have htwo := lines_avoiding_two n v hnv
    obtain ⟨k,hk⟩ := card_pos.mp (show 0 < (univ.filter fun k : Fin 7 => n ∉ line k ∧ v ∉ line k).card by omega)
    obtain ⟨_,hnk,hvk⟩ := mem_filter.mp hk
    obtain ⟨a,ha⟩ := N.a_on_line k (hpositive k) (nobase k v hvk hvl hvl)
    have hac : a ≠ c := by intro he; rw [he,hcD] at ha; cases ha
    have hax : a ≠ x := by intro he; rw [he,hx] at ha; cases ha
    have hcx : c ≠ x := by intro he; rw [he,hx] at hcD; cases hcD
    apply C.uncovered a c x hac hax hcx
    · rw [N.plane,N.plane,N.plane,ha,hcD,hx]
      apply c_b_plane_disjoint D k l n b _ hnk
      rw [hv]
      exact disjoint_singleton_right.mpr hvk
    · rw [N.avoid,N.avoid,hcD,hx]
      simp [Column.avoid]
  · obtain ⟨v,hv⟩ := card_eq_one.mp (line_inter_card l m hlm)
    have hvl : v ∈ line l := (mem_inter.mp (hv.symm ▸ mem_singleton_self v)).1
    have hvm : v ∈ line m := (mem_inter.mp (hv.symm ▸ mem_singleton_self v)).2
    obtain ⟨k,hvk⟩ := line_avoids v
    obtain ⟨a,ha⟩ := N.a_on_line k (hpositive k) (nobase k v hvk hvl hvm)
    have hax : a ≠ x := by intro he; rw [he,hx] at ha; cases ha
    have hay : a ≠ y := by intro he; rw [he,hy] at ha; cases ha
    apply C.uncovered a x y hax hay hxy
    · rw [N.plane,N.plane,N.plane,ha,hx,hy]
      apply b_plane_disjoint k l m n b s hnl hnm _ (Or.inl hbs)
      rw [hv]
      exact disjoint_singleton_right.mpr hvk
    · rw [N.avoid,N.avoid,hx,hy]
      exact disjoint_singleton.mpr hef

end CoveringDesigns.C19_9_3.Internal
