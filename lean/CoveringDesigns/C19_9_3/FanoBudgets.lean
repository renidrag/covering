import CoveringDesigns.C19_9_3.ColumnWeights

namespace CoveringDesigns.C19_9_3.Internal
open Finset SevenBlock

private theorem pair_sum_le (m : Fin 7 → ℕ) (n d : Fin 7) (hnd : n ≠ d) :
    m n + m d ≤ ∑ k, m k := by
  have hh := sum_le_sum_of_subset_of_nonneg (subset_univ ({n,d} : Finset (Fin 7)))
    (fun k _ _ => Nat.zero_le (m k))
  simpa only [sum_pair hnd] using hh

theorem unit_sum (m : Fin 7 → ℕ) (hs : ∑ n, m n = 1) :
    ∃ n, m n = 1 ∧ ∀ d, d ≠ n → m d = 0 := by
  obtain ⟨n,_,hn⟩ := sum_pos_iff.mp (show 0 < ∑ n, m n by omega)
  have hle := single_le_sum (fun k (_ : k ∈ (univ : Finset (Fin 7))) => Nat.zero_le (m k)) (mem_univ n)
  refine ⟨n,by omega,?_⟩
  intro d hdn
  have hp := pair_sum_le m n d hdn.symm
  omega

section FixedFano
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem line_separates : ∀ n d : Fin 7, n ≠ d → ∃ l, n ∈ line l ∧ d ∉ line l := by decide +kernel
theorem line_avoids : ∀ n : Fin 7, ∃ l, n ∉ line l := by decide +kernel
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

variable {X : Type*} [Fintype X] [DecidableEq X] {C : Completion X}

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

theorem Normalized.no_wide (N : Normalized C) (hc : (C.class 0).card = 0) (n : Fin 7) :
    N.wideCount n = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hm := (mem_filter.mp hx).2
  cases he : N.col x with
  | a l => simpa [he,Column.wide] using hm
  | b l m b e => simpa [he,Column.wide] using hm
  | c D =>
    have hxC : x ∈ C.class 0 := by simp [Completion.class,N.avoid,he,Column.avoid]
    rw [card_eq_zero.mp hc] at hxC
    exact notMem_empty _ hxC

theorem Normalized.four_single_weights (N : Normalized C) (hX : Fintype.card X = 11)
    (hB : (C.class 1).card = 4) (hC : (C.class 0).card = 0) :
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

theorem Normalized.one_wide (N : Normalized C) (hc : (C.class 0).card = 1) :
    ∃ c : X, ∃ D : Finset (Fin 7), C.class 0 = {c} ∧ N.col c = Column.c D ∧
      D.card = 4 ∧ (∃ l, line l ⊆ D) ∧
      ∀ n, N.wideCount n = if n ∈ D then 1 else 0 := by
  obtain ⟨c,hcset⟩ := card_eq_one.mp hc
  have hcC : c ∈ C.class 0 := hcset.symm ▸ mem_singleton_self c
  have hzero := (mem_filter.mp hcC).2
  rw [N.avoid] at hzero
  cases hec : N.col c with
  | a l => simp [hec,Column.avoid] at hzero
  | b l n b e => simp [hec,Column.avoid] at hzero
  | c D =>
    have hD := N.valid c
    rw [hec] at hD
    refine ⟨c,D,hcset,hec,hD.1,hD.2,?_⟩
    have hother (x : X) (hxc : x ≠ c) : (N.col x).wide = ∅ := by
      cases hx : N.col x with
      | a l => rfl
      | b l n b e => rfl
      | c H =>
        have hxC : x ∈ C.class 0 := mem_filter.mpr ⟨mem_univ _,by rw [N.avoid,hx]; rfl⟩
        rw [hcset] at hxC
        exact False.elim (hxc (mem_singleton.mp hxC))
    intro n
    have hset : (univ.filter fun x => n ∈ (N.col x).wide) = if n ∈ D then {c} else ∅ := by
      ext x
      rw [mem_filter]
      simp only [mem_univ,true_and]
      by_cases hxc : x = c
      · subst x
        by_cases hn : n ∈ D <;> simp [hec,Column.wide,hn]
      · by_cases hn : n ∈ D <;> simp [hother x hxc,hn,hxc]
    change (univ.filter fun x => n ∈ (N.col x).wide).card = _
    rw [hset]
    split_ifs <;> simp

theorem Normalized.two_single_weights (N : Normalized C) (hX : Fintype.card X = 11)
    (hB : (C.class 1).card = 2) (hC : (C.class 0).card = 1) :
    ∃ n : Fin 7, ∃ c : X, ∃ D : Finset (Fin 7),
      C.class 0 = {c} ∧ N.col c = Column.c D ∧ D.card = 4 ∧ (∃ l, line l ⊆ D) ∧
      N.single n false = 1 ∧ (∀ d, d ≠ n → N.single d false = 0) ∧
      ∀ l, 2*N.weight l + (D ∩ line l).card + (if n ∈ line l then 1 else 0) = 5 := by
  have htot := N.single_total
  rw [hB] at htot
  obtain ⟨n,hn,hr⟩ := unit_sum (fun d => N.single d false) (by omega)
  obtain ⟨c,D,hcset,hcD,hD,hDL,hwide⟩ := N.one_wide hC
  refine ⟨n,c,D,hcset,hcD,hD,hDL,hn,hr,?_⟩
  have hw := N.weight_total
  rw [hX,hC] at hw
  intro l
  have hM : (∑ d ∈ line l, N.single d false) = if n ∈ line l then 1 else 0 := by
    have heq (d : Fin 7) : N.single d false = if d = n then 1 else 0 := by
      by_cases hd : d = n
      · simp [hd,hn]
      · simp [hd,hr d hd]
    simp_rw [heq]
    simp
  have hW : (∑ d ∈ line l, N.wideCount d) = (D ∩ line l).card := by
    simp_rw [hwide]
    rw [← sum_filter,sum_const,Nat.nsmul_eq_mul,mul_one,filter_mem_eq_inter,inter_comm]
  have hh := N.line_equation l
  rw [hM,hW] at hh
  omega

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
  | some l => simp [eq_comm]

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
    (hcount : (C.class 1 ∩ N.basePoints S).card < ∑ l ∈ S, N.weight l) :
    ∃ x : X, ∃ l ∈ S, N.col x = Column.a l := by
  by_contra hn
  have hsub : N.basePoints S ⊆ C.class 1 := by
    intro x hx
    rcases N.basePoints_mem S x hx with ⟨l,hl,hx⟩ | ⟨l,hl,n,b,e,hx⟩
    · exact False.elim (hn ⟨x,l,hl,hx⟩)
    · exact mem_filter.mpr ⟨mem_univ _,by rw [N.avoid,hx]; rfl⟩
  rw [inter_eq_right.mpr hsub,N.basePoints_card] at hcount
  omega

end CoveringDesigns.C19_9_3.Internal
