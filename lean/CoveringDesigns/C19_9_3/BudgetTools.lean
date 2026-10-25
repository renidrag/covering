import CoveringDesigns.C19_9_3.FanoBudgets

namespace CoveringDesigns.C19_9_3.Internal
open Finset SevenBlock
variable {X : Type*} [Fintype X] [DecidableEq X] {C : Completion X}

theorem Normalized.is_b (N : Normalized C) (x : X) (hx : x ∈ C.class 1) :
    ∃ l n b e, N.col x = Column.b l n b e := by
  have hc := (mem_filter.mp hx).2
  rw [N.avoid] at hc
  cases he : N.col x with
  | a l => simp [he,Column.avoid] at hc
  | b l n b e => exact ⟨l,n,b,e,rfl⟩
  | c D => simp [he,Column.avoid] at hc

theorem Normalized.base_pair_le (N : Normalized C) (x y : X) (hxy : x ≠ y) (l : Fin 7)
    (hx : (N.col x).base = some l) (hy : (N.col y).base = some l) : 2 ≤ N.weight l := by
  have hs : ({x,y} : Finset X) ⊆ univ.filter fun u => (N.col u).base = some l := by
    intro u hu
    simp only [mem_insert,mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact mem_filter.mpr ⟨mem_univ _,hx⟩
    · exact mem_filter.mpr ⟨mem_univ _,hy⟩
  have hh := card_le_card hs
  rwa [card_pair hxy] at hh

theorem Normalized.single_pair_le (N : Normalized C) (x y : X) (hxy : x ≠ y) (p : PlanePosition)
    (hx : (N.col x).extra = some p) (hy : (N.col y).extra = some p) : 2 ≤ N.single p.1 p.2 := by
  have hs : ({x,y} : Finset X) ⊆ univ.filter fun u => (N.col u).extra = some p := by
    intro u hu
    simp only [mem_insert,mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact mem_filter.mpr ⟨mem_univ _,hx⟩
    · exact mem_filter.mpr ⟨mem_univ _,hy⟩
  have hh := card_le_card hs
  rwa [card_pair hxy] at hh

def Completion.singleRow (C : Completion X) (b : Bool) := (C.class 1).filter fun x => b ∈ C.avoid x

private theorem bool_row_identity : ∀ b : Bool, ∀ E : Finset Bool,
    (if b ∈ E then 1 else 0) = (if E.card = 2 then 1 else 0) +
      (if E.card = 1 ∧ b ∈ E then 1 else 0) := by decide +kernel

theorem Completion.avoiding_row (C : Completion X) (b : Bool) :
    (C.class 2).card + (C.singleRow b).card = 9 := by
  have ht := sum_congr (s₁ := (univ : Finset X)) rfl (fun x _ => bool_row_identity b (C.avoid x))
  rw [sum_add_distrib] at ht
  have hleft : (∑ x : X, if b ∈ C.avoid x then 1 else 0) = 9 := by
    simpa only [card_eq_sum_ones,sum_filter] using C.avoid_row b
  have hA : (∑ x : X, if (C.avoid x).card = 2 then 1 else 0) = (C.class 2).card := by
    simp only [Completion.class,card_eq_sum_ones,sum_filter]
  have hB : (∑ x : X, if (C.avoid x).card = 1 ∧ b ∈ C.avoid x then 1 else 0) =
      (C.singleRow b).card := by
    simp only [Completion.singleRow,Completion.class,filter_filter,card_eq_sum_ones,sum_filter]
  rw [hleft,hA,hB] at ht
  exact ht.symm

theorem Normalized.single_row_pair_le (N : Normalized C) (x y : X) (hxy : x ≠ y)
    (l m n d : Fin 7) (b s e : Bool)
    (hx : N.col x = Column.b l n b e) (hy : N.col y = Column.b m d s e) :
    2 ≤ (C.singleRow e).card := by
  have hmem (z : X) (k r : Fin 7) (t : Bool) (hz : N.col z = Column.b k r t e) : z ∈ C.singleRow e := by
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,?_⟩ <;> rw [N.avoid,hz]
    · rfl
    · exact mem_singleton_self e
  have hs : ({x,y} : Finset X) ⊆ C.singleRow e := by
    intro z hz
    simp only [mem_insert,mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hmem _ l n b hx
    · exact hmem _ m d s hy
  have hh := card_le_card hs
  rwa [card_pair hxy] at hh

theorem Normalized.a_on_line (N : Normalized C) (l : Fin 7) (hw : 0 < N.weight l)
    (hn : ∀ x ∈ C.class 1, (N.col x).base ≠ some l) : ∃ x, N.col x = Column.a l := by
  have he : C.class 1 ∩ N.basePoints {l} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxB,hxP⟩ := mem_inter.mp hx
    obtain ⟨_,k,hk,hbase⟩ := mem_filter.mp hxP
    rw [mem_singleton] at hk
    exact hn x hxB (hk ▸ hbase)
  obtain ⟨x,k,hk,hx⟩ := N.exists_a_on {l} (by rw [he,card_empty,sum_singleton]; exact hw)
  exact ⟨x,(mem_singleton.mp hk) ▸ hx⟩

theorem b_plane_disjoint (k l m n : Fin 7) (b s : Bool)
    (hnl : n ∉ line l) (hnm : n ∉ line m)
    (hk : Disjoint (line k) (line l ∩ line m)) (hside : b ≠ s ∨ n ∉ line k) :
    Disjoint (completeDirections (line k))
      (insert (n,b) (completeDirections (line l)) ∩ insert (n,s) (completeDirections (line m))) := by
  apply disjoint_left.mpr
  rintro ⟨d,t⟩ hd hboth
  have hdK : d ∈ line k := (mem_product.mp hd).1
  have hL : (d = n ∧ t = b) ∨ d ∈ line l := by
    simpa only [mem_insert,Prod.mk.injEq,completeDirections,mem_product,mem_univ,and_true] using (mem_inter.mp hboth).1
  have hM : (d = n ∧ t = s) ∨ d ∈ line m := by
    simpa only [mem_insert,Prod.mk.injEq,completeDirections,mem_product,mem_univ,and_true] using (mem_inter.mp hboth).2
  rcases hL with ⟨rfl,rfl⟩ | hdL
  · rcases hM with ⟨_,hbs⟩ | hnM
    · rcases hside with hbs' | hnK
      · exact hbs' hbs
      · exact hnK hdK
    · exact hnm hnM
  · rcases hM with ⟨rfl,_⟩ | hdM
    · exact hnl hdL
    · exact disjoint_left.mp hk hdK (mem_inter.mpr ⟨hdL,hdM⟩)

theorem c_b_plane_disjoint (D : Finset (Fin 7)) (k l n : Fin 7) (b : Bool)
    (hk : Disjoint (line k) (D ∩ line l)) (hn : n ∉ line k) :
    Disjoint (completeDirections (line k))
      (completeDirections D ∩ insert (n,b) (completeDirections (line l))) := by
  apply disjoint_left.mpr
  rintro ⟨d,t⟩ hd hboth
  have hdK : d ∈ line k := (mem_product.mp hd).1
  have hdD : d ∈ D := (mem_product.mp (mem_inter.mp hboth).1).1
  have hL : (d = n ∧ t = b) ∨ d ∈ line l := by
    simpa only [mem_insert,Prod.mk.injEq,completeDirections,mem_product,mem_univ,and_true] using (mem_inter.mp hboth).2
  rcases hL with ⟨rfl,_⟩ | hdL
  · exact hn hdK
  · exact disjoint_left.mp hk hdK (mem_inter.mpr ⟨hdD,hdL⟩)

theorem Completion.uncovered (C : Completion X) (a x y : X) (hax : a ≠ x) (hay : a ≠ y) (hxy : x ≠ y)
    (hp : Disjoint (C.plane a) (C.plane x ∩ C.plane y))
    (he : Disjoint (C.avoid x) (C.avoid y)) : False := by
  rcases C.triples a x y hax hay hxy with ⟨p,hpall⟩ | ⟨b,hball⟩
  · exact disjoint_left.mp hp (mem_inter.mp (mem_inter.mp hpall).1).1
      (mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hpall).1).2,(mem_inter.mp hpall).2⟩)
  · exact disjoint_left.mp he (mem_inter.mp (mem_inter.mp hball).1).2 (mem_inter.mp hball).2

end CoveringDesigns.C19_9_3.Internal
