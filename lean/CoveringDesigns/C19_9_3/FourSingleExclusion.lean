import CoveringDesigns.C19_9_3.BudgetTools

namespace CoveringDesigns.C19_9_3.Internal
open Finset SevenBlock
variable {X : Type*} [Fintype X] [DecidableEq X] {C : Completion X}

private theorem cross_base_equal (N : Normalized C) (n : Fin 7)
    (hrest : ∀ d, d ≠ n → N.single d false = 0)
    (hweights : ∀ l, N.weight l = if n ∈ line l then 1 else 2)
    (hB : (C.class 1).card = 4)
    (x y : X) (l m : Fin 7) (b s e f : Bool)
    (hx : N.col x = Column.b l n b e) (hy : N.col y = Column.b m n s f) (hef : e ≠ f) : l = m := by
  have hxy : x ≠ y := by
    intro he
    rw [he,hy] at hx
    have := Column.b.inj hx
    exact hef this.2.2.2.symm
  have hxB : x ∈ C.class 1 := mem_filter.mpr ⟨mem_univ _,by rw [N.avoid,hx]; rfl⟩
  have hyB : y ∈ C.class 1 := mem_filter.mpr ⟨mem_univ _,by rw [N.avoid,hy]; rfl⟩
  have hnl : n ∉ line l := by simpa only [hx,Column.Valid] using N.valid x
  have hnm : n ∉ line m := by simpa only [hy,Column.Valid] using N.valid y
  by_contra hlm
  obtain ⟨d,hd⟩ := card_eq_one.mp (line_inter_card l m hlm)
  have hdl : d ∈ line l := (mem_inter.mp (hd.symm ▸ mem_singleton_self d)).1
  have hdm : d ∈ line m := (mem_inter.mp (hd.symm ▸ mem_singleton_self d)).2
  have hnd : n ≠ d := fun he => hnl (he.symm ▸ hdl)
  have hex : ∃ a : X, ∃ k : Fin 7, N.col a = Column.a k ∧ d ∉ line k ∧ (b ≠ s ∨ n ∉ line k) := by
    by_cases hbs : b = s
    · let S := univ.filter fun k : Fin 7 => n ∉ line k ∧ d ∉ line k
      have hSc : S.card = 2 := lines_avoiding_two n d hnd
      have hsum : (∑ k ∈ S, N.weight k) = 4 := by
        have hW (k : Fin 7) (hk : k ∈ S) : N.weight k = 2 := by
          rw [hweights,if_neg (mem_filter.mp hk).2.1]
        rw [sum_congr rfl hW,sum_const,hSc]
        decide
      have hout (z : X) (r : Fin 7) (t u : Bool) (hz : N.col z = Column.b r n t u)
          (hdr : d ∈ line r) : z ∉ N.basePoints S := by
        intro hzP
        obtain ⟨_,k,hk,hbase⟩ := mem_filter.mp hzP
        rw [hz] at hbase
        have hrk : r = k := Option.some.inj hbase
        exact (mem_filter.mp hk).2.2 (hrk ▸ hdr)
      have hxout := hout x l b e hx hdl
      have hyout := hout y m s f hy hdm
      have hsub : C.class 1 ∩ N.basePoints S ⊆ C.class 1 \ {x,y} := by
        intro z hz
        refine mem_sdiff.mpr ⟨(mem_inter.mp hz).1,?_⟩
        simp only [mem_insert,mem_singleton,not_or]
        exact ⟨fun he => hxout (he ▸ (mem_inter.mp hz).2),fun he => hyout (he ▸ (mem_inter.mp hz).2)⟩
      have hpairsub : ({x,y} : Finset X) ⊆ C.class 1 := by
        intro z hz
        simp only [mem_insert,mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      have hdiff := card_sdiff_add_card_inter (C.class 1) ({x,y} : Finset X)
      rw [inter_eq_right.mpr hpairsub,card_pair hxy,hB] at hdiff
      have hle := card_le_card hsub
      obtain ⟨a,k,hk,ha⟩ := N.exists_a_on S (by rw [hsum]; omega)
      exact ⟨a,k,ha,(mem_filter.mp hk).2.2,Or.inr (mem_filter.mp hk).2.1⟩
    · obtain ⟨k,hnk,hdk⟩ := line_separates n d hnd
      have hw : 0 < N.weight k := by rw [hweights,if_pos hnk]; decide
      obtain ⟨a,ha⟩ := N.a_on_line k hw (by
        intro z hz hbase
        obtain ⟨r,t,u,v,hzB⟩ := N.is_b z hz
        have ht := N.extra_direction n hrest z r t u v hzB
        have hnR : n ∉ line r := by simpa only [hzB,Column.Valid,ht] using N.valid z
        rw [hzB] at hbase
        have hrk : r = k := Option.some.inj hbase
        exact hnR (hrk.symm ▸ hnk))
      exact ⟨a,k,ha,hdk,Or.inl hbs⟩
  obtain ⟨a,k,ha,hdk,hside⟩ := hex
  have hax : a ≠ x := by intro he; rw [he,hx] at ha; cases ha
  have hay : a ≠ y := by intro he; rw [he,hy] at ha; cases ha
  apply C.uncovered a x y hax hay hxy
  · rw [N.plane,N.plane,N.plane,ha,hx,hy]
    apply b_plane_disjoint k l m n b s hnl hnm _ hside
    rw [hd]
    exact disjoint_singleton_right.mpr hdk
  · rw [N.avoid,N.avoid,hx,hy]
    exact disjoint_singleton.mpr hef

theorem Normalized.exclude_four_single (N : Normalized C) (hX : Fintype.card X = 11)
    (hA : (C.class 2).card = 7) (hB : (C.class 1).card = 4) (hC : (C.class 0).card = 0) : False := by
  obtain ⟨n,hn,hrest,hweights⟩ := N.four_single_weights hX hB hC
  have hrow (b : Bool) : (C.singleRow b).card = 2 := by
    have hh := C.avoiding_row b
    rw [hA] at hh
    omega
  obtain ⟨x,hxrow⟩ := card_pos.mp (show 0 < (C.singleRow false).card by rw [hrow]; decide)
  obtain ⟨y,hyrow⟩ := card_pos.mp (show 0 < (C.singleRow true).card by rw [hrow]; decide)
  obtain ⟨l,d,b,e,hx⟩ := N.is_b x (mem_filter.mp hxrow).1
  obtain ⟨m,t,s,f,hy⟩ := N.is_b y (mem_filter.mp hyrow).1
  have he : e = false := by
    have hh := (mem_filter.mp hxrow).2
    rw [N.avoid,hx] at hh
    exact (mem_singleton.mp hh).symm
  have hf : f = true := by
    have hh := (mem_filter.mp hyrow).2
    rw [N.avoid,hy] at hh
    exact (mem_singleton.mp hh).symm
  subst e
  subst f
  have hd := N.extra_direction n hrest x l d b false hx
  have ht := N.extra_direction n hrest y m t s true hy
  subst d
  subst t
  have hlm := cross_base_equal N n hrest hweights hB x y l m b s false true hx hy (by decide)
  subst m
  have hall : C.class 1 ⊆ univ.filter fun z => (N.col z).base = some l := by
    intro z hz
    obtain ⟨k,d,u,v,hzB⟩ := N.is_b z hz
    have hd := N.extra_direction n hrest z k d u v hzB
    subst d
    have hkl : k = l := by
      cases v
      · exact cross_base_equal N n hrest hweights hB z y k l u s false true hzB hy (by decide)
      · exact (cross_base_equal N n hrest hweights hB x z l k b u false true hx hzB (by decide)).symm
    exact mem_filter.mpr ⟨mem_univ _,by rw [hzB]; exact congrArg some hkl⟩
  have hle := card_le_card hall
  change (C.class 1).card ≤ N.weight l at hle
  rw [hB,hweights] at hle
  split_ifs at hle <;> omega

end CoveringDesigns.C19_9_3.Internal
