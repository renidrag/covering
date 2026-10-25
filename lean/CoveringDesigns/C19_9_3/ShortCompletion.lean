import CoveringDesigns.C19_9_3.WeakCompletion

/-! A short completion obstruction on actual points. The two structural
branches are presence or absence of a four-direction column. -/
namespace CoveringDesigns.C19_9_3.Internal.Short
open Finset SevenBlock

private theorem pair_sum_le (m : Fin 7 → ℕ) (n d : Fin 7) (hnd : n ≠ d) :
    m n + m d ≤ ∑ k, m k := by
  have hh := sum_le_sum_of_subset_of_nonneg (subset_univ ({n,d} : Finset (Fin 7)))
    (fun k _ _ => Nat.zero_le (m k))
  simpa only [sum_pair hnd] using hh

section FixedFano
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem line_separates : ∀ n d : Fin 7, n ≠ d → ∃ l, n ∈ line l ∧ d ∉ line l := by decide +kernel
theorem lines_avoiding_two : ∀ n d : Fin 7, n ≠ d →
    (univ.filter fun l : Fin 7 => n ∉ line l ∧ d ∉ line l).card = 2 := by decide +kernel

end FixedFano

theorem double_sum_even_lines (m : Fin 7 → ℕ) (hs : ∑ n, m n = 2)
    (he : ∀ l, (∑ n ∈ line l, m n) % 2 = 0) :
    ∃ n, m n = 2 ∧ ∀ d, d ≠ n → m d = 0 := by
  obtain ⟨n,_,hn⟩ := sum_pos_iff.mp (show 0 < ∑ n, m n by omega)
  have hnle := single_le_sum (fun k (_ : k ∈ (univ : Finset (Fin 7))) => Nat.zero_le (m k)) (mem_univ n)
  by_cases hn2 : m n = 2
  · refine ⟨n,hn2,?_⟩
    intro d hdn
    have hp := pair_sum_le m n d hdn.symm
    omega
  · have hn1 : m n = 1 := by omega
    have hex : ∃ d, d ≠ n ∧ 0 < m d := by
      by_contra hh
      push Not at hh
      have hd (d : Fin 7) (hdn : d ≠ n) : m d = 0 := by have := hh d hdn; omega
      have hsum : (∑ d : Fin 7, m d) = m n := sum_eq_single n (fun d _ hdn => hd d hdn) (by simp)
      omega
    obtain ⟨d,hdn,hd⟩ := hex
    have hpd := pair_sum_le m n d hdn.symm
    have hd1 : m d = 1 := by omega
    let q (k : Fin 7) := if k = n ∨ k = d then 1 else 0
    have hqle (k : Fin 7) : q k ≤ m k := by
      by_cases hkn : k = n
      · simp [q,hkn,hn1]
      by_cases hkd : k = d
      · simp [q,hkd,hd1]
      · simp [q,hkn,hkd]
    have hqsum : (∑ k : Fin 7, q k) = 2 := by
      have hq : ∀ k, q k = if k ∈ ({n,d} : Finset (Fin 7)) then 1 else 0 := by intro k; simp [q]
      simp_rw [hq]
      rw [← sum_filter,filter_mem_eq_inter,univ_inter,sum_const,Nat.nsmul_eq_mul,mul_one,card_pair hdn.symm]
    have hpoint := (sum_eq_sum_iff_of_le (fun k (_ : k ∈ (univ : Finset (Fin 7))) => hqle k)).mp
      (hqsum.trans hs.symm)
    obtain ⟨l,hnl,hdl⟩ := line_separates n d hdn.symm
    have hline : (∑ k ∈ line l, m k) = 1 := by
      have heq : (∑ k ∈ line l, m k) = ∑ k ∈ line l, q k :=
        sum_congr rfl (fun k _ => (hpoint k (mem_univ _)).symm)
      rw [heq]
      have hq (k : Fin 7) (hk : k ∈ line l) : q k = if k = n then 1 else 0 := by
        have hkd : k ≠ d := fun heq => hdl (heq ▸ hk)
        simp [q,hkd]
      rw [sum_congr rfl hq]
      simp [hnl]
    have hh := he l
    rw [hline] at hh
    contradiction

variable {X : Type*} [Fintype X] [DecidableEq X] {C : WeakCompletion X}

theorem Normalized.line_equation (N : Normalized C) (l : Fin 7) :
    2*N.weight l + (∑ m : Fin 7, N.weight m) +
      (∑ n ∈ line l, N.single n false) + (∑ n ∈ line l, N.wideCount n) = 15 := by
  have hf : 2*N.weight l + (∑ m : Fin 7, N.weight m) =
      ∑ n ∈ line l, ∑ m ∈ univ.filter (fun m => n ∈ line m), N.weight m := by
    have hh := fano_incidence_identity (fun m => (N.weight m : ℤ)) l
    simp only [sum_filter]
    exact_mod_cast hh
  have hr := sum_congr (s₁ := line l) rfl (fun n _ => N.row n false)
  simp only [sum_add_distrib,sum_const,line_card,Nat.nsmul_eq_mul] at hr
  rw [← hf] at hr
  exact hr

theorem Normalized.no_wide (N : Normalized C) (hc : (pointClass C 0).card = 0) (n : Fin 7) :
    N.wideCount n = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hm := (mem_filter.mp hx).2
  cases he : N.col x with
  | a l => simp [he,Column.wide] at hm
  | b l m b e => simp [he,Column.wide] at hm
  | c D =>
    have hxC : x ∈ pointClass C 0 := by simp [pointClass,N.avoid,he,Column.avoid]
    rw [card_eq_zero.mp hc] at hxC
    exact notMem_empty _ hxC

theorem Normalized.four_single_weights (N : Normalized C) (hX : Fintype.card X = 11)
    (hB : (pointClass C 1).card = 4) (hC : (pointClass C 0).card = 0) :
    ∃ n : Fin 7, N.single n false = 2 ∧ (∀ d, d ≠ n → N.single d false = 0) ∧
      ∀ l, N.weight l = if n ∈ line l then 1 else 2 := by
  have htot := N.single_total
  rw [hB] at htot
  have hw := N.weight_total
  rw [hX,hC,add_zero] at hw
  have hline (l : Fin 7) : 2*N.weight l + (∑ d ∈ line l, N.single d false) = 4 := by
    have hh := N.line_equation l
    simp only [hw,N.no_wide hC,sum_const_zero,add_zero] at hh
    omega
  obtain ⟨n,hn,hrest⟩ := double_sum_even_lines (fun d => N.single d false) (by omega)
    (fun l => by have := hline l; omega)
  refine ⟨n,hn,hrest,?_⟩
  intro l
  have hm : (∑ d ∈ line l, N.single d false) = if n ∈ line l then 2 else 0 := by
    have heq (d : Fin 7) : N.single d false = if d = n then 2 else 0 := by
      by_cases hd : d = n
      · simp [hd,hn]
      · simp [hd,hrest d hd]
    simp_rw [heq]
    simp
  have hh := hline l
  rw [hm] at hh
  split_ifs at hh ⊢ <;> omega

theorem Normalized.extra_direction (N : Normalized C) (n : Fin 7)
    (hz : ∀ d, d ≠ n → N.single d false = 0) (x : X) (l d : Fin 7) (b e : Bool)
    (hx : N.col x = Column.b l d b e) : d = n := by
  by_contra hdn
  have hc : N.single d b = 0 := by cases b <;> simpa only [← N.single_balanced] using hz d hdn
  have hm : x ∈ univ.filter fun x => (N.col x).extra = some (d,b) := by
    exact mem_filter.mpr ⟨mem_univ _,by rw [hx]; rfl⟩
  have he : (univ.filter fun x => (N.col x).extra = some (d,b)) = ∅ := card_eq_zero.mp hc
  rw [he] at hm
  exact notMem_empty _ hm

def Normalized.basePoints (N : Normalized C) (S : Finset (Fin 7)) : Finset X :=
  univ.filter fun x => ∃ l ∈ S, (N.col x).base = some l

theorem Normalized.basePoints_card (N : Normalized C) (S : Finset (Fin 7)) :
    (N.basePoints S).card = ∑ l ∈ S, N.weight l := by
  simp only [Normalized.basePoints,Normalized.weight,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  cases hc : (N.col x).base with
  | none => simp
  | some l => simp

theorem Normalized.basePoints_mem (N : Normalized C) (S : Finset (Fin 7)) (x : X)
    (hx : x ∈ N.basePoints S) :
    (∃ l ∈ S, N.col x = Column.a l) ∨
      ∃ l ∈ S, ∃ n b e, N.col x = Column.b l n b e := by
  obtain ⟨_,l,hl,hbase⟩ := mem_filter.mp hx
  cases hc : N.col x with
  | a k =>
    have hkl : k = l := by simpa [hc,Column.base] using hbase
    left
    exact ⟨k,hkl.symm ▸ hl,rfl⟩
  | b k n b e =>
    have hkl : k = l := by simpa [hc,Column.base] using hbase
    right
    exact ⟨k,hkl.symm ▸ hl,n,b,e,rfl⟩
  | c D => simp [hc,Column.base] at hbase

theorem Normalized.exists_a_on (N : Normalized C) (S : Finset (Fin 7))
    (hcount : (pointClass C 1 ∩ N.basePoints S).card < ∑ l ∈ S, N.weight l) :
    ∃ x : X, ∃ l ∈ S, N.col x = Column.a l := by
  by_contra hn
  have hsub : N.basePoints S ⊆ pointClass C 1 := by
    intro x hx
    rcases N.basePoints_mem S x hx with ⟨l,hl,hx⟩ | ⟨l,hl,n,b,e,hx⟩
    · exact False.elim (hn ⟨x,l,hl,hx⟩)
    · exact mem_filter.mpr ⟨mem_univ _,by rw [N.avoid,hx]; rfl⟩
  rw [inter_eq_right.mpr hsub,N.basePoints_card] at hcount
  omega

theorem Normalized.is_b (N : Normalized C) (x : X) (hx : x ∈ pointClass C 1) :
    ∃ l n b e, N.col x = Column.b l n b e := by
  have hc := (mem_filter.mp hx).2
  rw [N.avoid] at hc
  cases he : N.col x with
  | a l => simp [he,Column.avoid] at hc
  | b l n b e => exact ⟨l,n,b,e,rfl⟩
  | c D => simp [he,Column.avoid] at hc

def singleRow (C : WeakCompletion X) (b : Bool) := (pointClass C 1).filter fun x => b ∈ C.avoid x

private theorem bool_row_identity : ∀ b : Bool, ∀ E : Finset Bool,
    (if b ∈ E then 1 else 0) = (if E.card = 2 then 1 else 0) +
      (if E.card = 1 ∧ b ∈ E then 1 else 0) := by decide +kernel

theorem avoiding_row (C : WeakCompletion X) (b : Bool) :
    (pointClass C 2).card + (singleRow C b).card = 9 := by
  have ht := sum_congr (s₁ := (univ : Finset X)) rfl (fun x _ => bool_row_identity b (C.avoid x))
  rw [sum_add_distrib] at ht
  have hleft : (∑ x : X, if b ∈ C.avoid x then 1 else 0) = 9 := by
    simpa only [card_eq_sum_ones,sum_filter] using C.avoid_row b
  have hA : (∑ x : X, if (C.avoid x).card = 2 then 1 else 0) = (pointClass C 2).card := by
    simp only [pointClass,card_eq_sum_ones,sum_filter]
  have hB : (∑ x : X, if (C.avoid x).card = 1 ∧ b ∈ C.avoid x then 1 else 0) =
      (singleRow C b).card := by
    simp only [singleRow,pointClass,filter_filter,card_eq_sum_ones,sum_filter]
  rw [hleft,hA,hB] at ht
  exact ht.symm

private theorem b_plane_disjoint (k l m n : Fin 7) (b s : Bool)
    (hk : Disjoint (line k) (line l ∩ line m)) (hn : n ∉ line k) :
    Disjoint (completeDirections (line k))
      (insert (n,b) (completeDirections (line l)) ∩ insert (n,s) (completeDirections (line m))) := by
  apply disjoint_left.mpr
  rintro ⟨d,t⟩ hd hboth
  have hdK : d ∈ line k := (mem_product.mp hd).1
  have hdn : d ≠ n := fun he => hn (he ▸ hdK)
  have hdL : d ∈ line l := by
    simpa only [mem_insert,Prod.mk.injEq,hdn,false_and,false_or,
      completeDirections,mem_product,mem_univ,and_true] using (mem_inter.mp hboth).1
  have hdM : d ∈ line m := by
    simpa only [mem_insert,Prod.mk.injEq,hdn,false_and,false_or,
      completeDirections,mem_product,mem_univ,and_true] using (mem_inter.mp hboth).2
  exact disjoint_left.mp hk hdK (mem_inter.mpr ⟨hdL,hdM⟩)

theorem uncovered (C : WeakCompletion X) (a x y : X) (hax : a ≠ x) (hay : a ≠ y) (hxy : x ≠ y)
    (hp : Disjoint (C.plane a) (C.plane x ∩ C.plane y))
    (he : Disjoint (C.avoid x) (C.avoid y)) : False := by
  rcases C.triples a x y hax hay hxy with ⟨p,hpall⟩ | ⟨b,hball⟩
  · exact disjoint_left.mp hp (mem_inter.mp (mem_inter.mp hpall).1).1
      (mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hpall).1).2,(mem_inter.mp hpall).2⟩)
  · exact disjoint_left.mp he (mem_inter.mp (mem_inter.mp hball).1).2 (mem_inter.mp hball).2

/-- A missing direction in a C column forces all A bases through it to agree.
The three points used here are actual points, distinguished by their forms
or by their different bases. -/
private theorem a_through_equal (N : Normalized C) (c x y : X)
    (H : Finset (Fin 7)) (l m d : Fin 7)
    (hc : N.col c = Column.c H) (hx : N.col x = Column.a l)
    (hy : N.col y = Column.a m) (hdH : d ∉ H)
    (hdl : d ∈ line l) (hdm : d ∈ line m) : l = m := by
  by_contra hlm
  have hxc : x ≠ c := by intro he; rw [he,hc] at hx; cases hx
  have hcy : c ≠ y := by intro he; rw [he,hy] at hc; cases hc
  have hxy : x ≠ y := by
    intro he
    rw [he,hy] at hx
    exact hlm (Column.a.inj hx).symm
  obtain ⟨v,hv⟩ := card_eq_one.mp (line_inter_card l m hlm)
  have hdv : d = v := mem_singleton.mp (hv ▸ mem_inter.mpr ⟨hdl,hdm⟩)
  subst v
  apply uncovered C x c y hxc hxy hcy
  · rw [N.plane,N.plane,N.plane,hx,hc,hy]
    apply disjoint_left.mpr
    rintro ⟨n,b⟩ hn hboth
    have hnl : n ∈ line l := (mem_product.mp hn).1
    have hnH : n ∈ H := (mem_product.mp (mem_inter.mp hboth).1).1
    have hnm : n ∈ line m := (mem_product.mp (mem_inter.mp hboth).2).1
    have hnd : n = d := mem_singleton.mp (hv ▸ mem_inter.mpr ⟨hnl,hnm⟩)
    exact hdH (hnd ▸ hnH)
  · rw [N.avoid,N.avoid,hc,hy]
    simp [Column.avoid]

/-- Both positive C budgets are excluded by one capacity inequality. -/
theorem Normalized.exclude_wide (N : Normalized C) (hX : Fintype.card X = 11)
    (hbudget : (pointClass C 1).card + 2*(pointClass C 0).card = 4)
    (hC : 0 < (pointClass C 0).card) : False := by
  have hB : (pointClass C 1).card ≤ 2 := by omega
  have hC2 : (pointClass C 0).card ≤ 2 := by omega
  obtain ⟨c,hcC⟩ := card_pos.mp hC
  have hc0 := (mem_filter.mp hcC).2
  rw [N.avoid] at hc0
  obtain ⟨H,hc⟩ : ∃ H, N.col c = Column.c H := by
    cases hh : N.col c with
    | a l => simp [hh,Column.avoid] at hc0
    | b l n b e => simp [hh,Column.avoid] at hc0
    | c H => exact ⟨H,rfl⟩
  have hH : H.card = 4 := by simpa only [hc,Column.Valid] using N.valid c
  let extraDir (x : X) := ((N.col x).extra.map Prod.fst).getD 0
  let extras := (pointClass C 1).image extraDir
  have hE : extras.card ≤ (pointClass C 1).card := card_image_le
  have hsmall : (H ∪ extras).card < (univ : Finset (Fin 7)).card := by
    have hh := card_union_le H extras
    have hu : (univ : Finset (Fin 7)).card = 7 := by simp
    omega
  obtain ⟨d,_,hd⟩ := exists_mem_notMem_of_card_lt_card hsmall
  have hdH : d ∉ H := fun hh => hd (mem_union_left _ hh)
  have hdE : d ∉ extras := fun hh => hd (mem_union_right _ hh)
  have hs : N.single d false = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have he := (mem_filter.mp hx).2
    cases hh : N.col x with
    | a l => simp [hh,Column.extra] at he
    | c D => simp [hh,Column.extra] at he
    | b l n b e =>
      rw [hh] at he
      have hnb : (n,b) = (d,false) := Option.some.inj he
      have hxB : x ∈ pointClass C 1 := by simp [pointClass,N.avoid,hh,Column.avoid]
      apply hdE
      apply mem_image.mpr
      refine ⟨x,hxB,?_⟩
      simpa [extraDir,hh,Column.extra] using congrArg Prod.fst hnb
  have hw : N.wideCount d + 1 ≤ (pointClass C 0).card := by
    have hsub : (univ.filter fun x => d ∈ (N.col x).wide) ⊆ (pointClass C 0).erase c := by
      intro x hx
      have hdx := (mem_filter.mp hx).2
      have hxc : x ≠ c := by
        intro he
        rw [he,hc] at hdx
        exact hdH hdx
      apply mem_erase.mpr
      refine ⟨hxc,?_⟩
      cases hh : N.col x with
      | a l => simp [hh,Column.wide] at hdx
      | b l n b e => simp [hh,Column.wide] at hdx
      | c D => simp [pointClass,N.avoid,hh,Column.avoid]
    have hle := card_le_card hsub
    have he := card_erase_add_one hcC
    change N.wideCount d ≤ _ at hle
    omega
  let S := univ.filter fun l : Fin 7 => d ∈ line l
  have hr : (∑ l ∈ S, N.weight l) + N.wideCount d = 5 := by
    simpa only [hs,add_zero] using N.row d false
  have hweights (l : Fin 7) : 2*N.weight l ≤ 4 + (pointClass C 0).card := by
    have ht := N.weight_total
    have hl := N.line_equation l
    omega
  have hless : ((pointClass C 1) ∩ N.basePoints S).card < ∑ l ∈ S, N.weight l := by
    have hh := card_le_card (inter_subset_left (s₁ := pointClass C 1) (s₂ := N.basePoints S))
    omega
  obtain ⟨x,l,hl,hx⟩ := N.exists_a_on S hless
  have hdl : d ∈ line l := (mem_filter.mp hl).2
  have hsub : N.basePoints S ⊆ (univ.filter fun y => (N.col y).base = some l) ∪ pointClass C 1 := by
    intro y hy
    rcases N.basePoints_mem S y hy with ⟨m,hm,hy⟩ | ⟨m,_,n,b,e,hy⟩
    · have he := a_through_equal N c x y H l m d hc hx hy hdH hdl (mem_filter.mp hm).2
      apply mem_union_left
      exact mem_filter.mpr ⟨mem_univ _,by rw [hy,← he]; rfl⟩
    · apply mem_union_right
      simp [pointClass,N.avoid,hy,Column.avoid]
  have hle := (card_le_card hsub).trans (card_union_le _ _)
  rw [N.basePoints_card] at hle
  change (∑ k ∈ S, N.weight k) ≤ N.weight l + (pointClass C 1).card at hle
  have hlbound := hweights l
  omega


private theorem cross_base_equal (N : Normalized C) (n : Fin 7)
    (hweights : ∀ l, N.weight l = if n ∈ line l then 1 else 2)
    (hB : (pointClass C 1).card = 4)
    (x y : X) (l m : Fin 7) (b s e f : Bool)
    (hx : N.col x = Column.b l n b e) (hy : N.col y = Column.b m n s f) (hef : e ≠ f) : l = m := by
  have hxy : x ≠ y := by
    intro he
    rw [he,hy] at hx
    have := Column.b.inj hx
    exact hef this.2.2.2.symm
  have hxB : x ∈ pointClass C 1 := mem_filter.mpr ⟨mem_univ _,by rw [N.avoid,hx]; rfl⟩
  have hyB : y ∈ pointClass C 1 := mem_filter.mpr ⟨mem_univ _,by rw [N.avoid,hy]; rfl⟩
  have hnl : n ∉ line l := by simpa only [hx,Column.Valid] using N.valid x
  by_contra hlm
  obtain ⟨d,hd⟩ := card_eq_one.mp (line_inter_card l m hlm)
  have hdl : d ∈ line l := (mem_inter.mp (hd.symm ▸ mem_singleton_self d)).1
  have hdm : d ∈ line m := (mem_inter.mp (hd.symm ▸ mem_singleton_self d)).2
  have hnd : n ≠ d := fun he => hnl (he.symm ▸ hdl)
  have hex : ∃ a : X, ∃ k : Fin 7, N.col a = Column.a k ∧ d ∉ line k ∧ n ∉ line k := by
    let S := univ.filter fun k : Fin 7 => n ∉ line k ∧ d ∉ line k
    have hSc : S.card = 2 := lines_avoiding_two n d hnd
    have hsum : (∑ k ∈ S, N.weight k) = 4 := by
      have hW (k : Fin 7) (hk : k ∈ S) : N.weight k = 2 := by
        rw [hweights,ite_eq_right (mem_filter.mp hk).2.1]
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
    have hsub : pointClass C 1 ∩ N.basePoints S ⊆ pointClass C 1 \ {x,y} := by
      intro z hz
      refine mem_sdiff.mpr ⟨(mem_inter.mp hz).1,?_⟩
      simp only [mem_insert,mem_singleton,not_or]
      exact ⟨fun he => hxout (he ▸ (mem_inter.mp hz).2),fun he => hyout (he ▸ (mem_inter.mp hz).2)⟩
    have hpairsub : ({x,y} : Finset X) ⊆ pointClass C 1 := by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hdiff := card_sdiff_add_card_inter (pointClass C 1) ({x,y} : Finset X)
    rw [inter_eq_right.mpr hpairsub,card_pair hxy,hB] at hdiff
    have hle := card_le_card hsub
    obtain ⟨a,k,hk,ha⟩ := N.exists_a_on S (by rw [hsum]; omega)
    exact ⟨a,k,ha,(mem_filter.mp hk).2.2,(mem_filter.mp hk).2.1⟩
  obtain ⟨a,k,ha,hdk,hnk⟩ := hex
  have hax : a ≠ x := by intro he; rw [he,hx] at ha; cases ha
  have hay : a ≠ y := by intro he; rw [he,hy] at ha; cases ha
  apply uncovered C a x y hax hay hxy
  · rw [N.plane,N.plane,N.plane,ha,hx,hy]
    apply b_plane_disjoint k l m n b s _ hnk
    rw [hd]
    exact disjoint_singleton_right.mpr hdk
  · rw [N.avoid,N.avoid,hx,hy]
    exact disjoint_singleton.mpr hef

theorem Normalized.exclude_four_single (N : Normalized C) (hX : Fintype.card X = 11)
    (hA : (pointClass C 2).card = 7) (hB : (pointClass C 1).card = 4) (hC : (pointClass C 0).card = 0) : False := by
  obtain ⟨n,hn,hrest,hweights⟩ := N.four_single_weights hX hB hC
  have hrow (b : Bool) : (singleRow C b).card = 2 := by
    have hh := avoiding_row C b
    rw [hA] at hh
    omega
  obtain ⟨x,hxrow⟩ := card_pos.mp (show 0 < (singleRow C false).card by rw [hrow]; decide)
  obtain ⟨y,hyrow⟩ := card_pos.mp (show 0 < (singleRow C true).card by rw [hrow]; decide)
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
  have hlm := cross_base_equal N n hweights hB x y l m b s false true hx hy (by decide)
  subst m
  have hall : pointClass C 1 ⊆ univ.filter fun z => (N.col z).base = some l := by
    intro z hz
    obtain ⟨k,d,u,v,hzB⟩ := N.is_b z hz
    have hd := N.extra_direction n hrest z k d u v hzB
    subst d
    have hkl : k = l := by
      cases v
      · exact cross_base_equal N n hweights hB z y k l u s false true hzB hy (by decide)
      · exact (cross_base_equal N n hweights hB x z l k b u false true hx hzB (by decide)).symm
    exact mem_filter.mpr ⟨mem_univ _,by rw [hzB]; exact congrArg some hkl⟩
  have hle := card_le_card hall
  change (pointClass C 1).card ≤ N.weight l at hle
  rw [hB,hweights] at hle
  split_ifs at hle <;> omega


end CoveringDesigns.C19_9_3.Internal.Short

namespace CoveringDesigns.C19_9_3

/-- Eleven actual points cannot complete the fourteen plane positions and
 two exceptional positions in the three weak support forms. No injectivity
 of point supports or exceptional block images is assumed. -/
theorem weak_completion_impossible {X : Type*} [Fintype X] [DecidableEq X]
    (C : WeakCompletion X) (hX : Fintype.card X = 11) : False := by
  obtain ⟨N⟩ := Internal.Short.normalize C
  obtain ⟨hpoints,havoid,hbudget⟩ := Internal.Short.budgets C hX
  by_cases hC : 0 < (Internal.Short.pointClass C 0).card
  · exact N.exclude_wide hX hbudget hC
  · exact N.exclude_four_single hX (by omega) (by omega) (by omega)

#guard_standard_axioms weak_completion_impossible
end CoveringDesigns.C19_9_3
