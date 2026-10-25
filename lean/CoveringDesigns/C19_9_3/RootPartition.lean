import CoveringDesigns.C19_9_3.LinkTraceRules

/-! Exact counts on the shared occurrence set for three ordinary roots. -/
namespace CoveringDesigns.C19_9_3
open Finset SevenBlock

/-- Three sets with the same pairwise intersection give an exact incidence
partition. This is an identity of actual supports, with no relabelling. -/
theorem three_support_count {I : Type*} [Fintype I] [DecidableEq I]
    (R₀ R₁ R₂ T S : Finset I)
    (h₀₁ : R₀ ∩ R₁ = T) (h₀₂ : R₀ ∩ R₂ = T) (h₁₂ : R₁ ∩ R₂ = T) :
    (S ∩ R₀).card + (S ∩ R₁).card + (S ∩ R₂).card +
      (S ∩ (univ \ (R₀ ∪ R₁ ∪ R₂))).card = S.card + 2 * (S ∩ T).card := by
  have hc (A : Finset I) : (S ∩ A).card = ∑ i ∈ S, if i ∈ A then 1 else 0 := by
    rw [← filter_mem_eq_inter,card_eq_sum_ones,sum_filter]
  rw [hc R₀,hc R₁,hc R₂,hc _,hc T,card_eq_sum_ones S, mul_sum]
  rw [← sum_add_distrib,← sum_add_distrib,← sum_add_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have h01 := congrArg (fun A : Finset I => i ∈ A) h₀₁
  have h02 := congrArg (fun A : Finset I => i ∈ A) h₀₂
  have h12 := congrArg (fun A : Finset I => i ∈ A) h₁₂
  simp only [mem_inter,mem_sdiff,mem_univ,true_and,mem_union] at *
  by_cases h0 : i ∈ R₀ <;> by_cases h1 : i ∈ R₁ <;> by_cases h2 : i ∈ R₂ <;>
    simp_all

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem pointSupport_triple (B : I → Finset V) (x y z : V) :
    (pointSupport B x ∩ pointSupport B y ∩ pointSupport B z).card =
      indexedSubsetDegree B {x,y,z} := by
  congr 1
  ext i
  simp only [mem_inter,mem_pointSupport,indexedSubsetDegree,mem_filter,mem_univ,
    true_and,insert_subset_iff,singleton_subset_iff]
  tauto

/-- Three mutually ordinary minimum roots of triple multiplicity three have
no fourth actual point in their common three occurrences. -/
theorem three_ordinary_roots_no_fourth {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : indexedDegree B x = 7) (hy : indexedDegree B y = 7) (hz : indexedDegree B z = 7)
    (hxy₃ : indexedSubsetDegree B {x,y} = 3)
    (hxz₃ : indexedSubsetDegree B {x,z} = 3)
    (hyz₃ : indexedSubsetDegree B {y,z} = 3)
    (ht : indexedSubsetDegree B {x,y,z} = 3)
    (w : V) (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
    ¬ pointSupport B x ∩ pointSupport B y ∩ pointSupport B z ⊆ pointSupport B w := by
  let T := pointSupport B x ∩ pointSupport B y ∩ pointSupport B z
  have hT : T.card = 3 := (pointSupport_triple B x y z).trans ht
  have h01 : pointSupport B x ∩ pointSupport B y = T := by
    symm
    apply eq_of_subset_of_card_le inter_subset_left
    rw [pointSupport_pair,hxy₃,hT]
  have h02 : pointSupport B x ∩ pointSupport B z = T := by
    symm
    apply eq_of_subset_of_card_le
      (by intro i hi; exact mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hi).1).1,(mem_inter.mp hi).2⟩)
    rw [pointSupport_pair,hxz₃,hT]
  have h12 : pointSupport B y ∩ pointSupport B z = T := by
    symm
    apply eq_of_subset_of_card_le
      (by intro i hi; exact mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hi).1).2,(mem_inter.mp hi).2⟩)
    rw [pointSupport_pair,hyz₃,hT]
  let N := (univ : Finset I) \ (pointSupport B x ∪ pointSupport B y ∪ pointSupport B z)
  have hN : N.card = 1 := by
    have hc := three_support_count (pointSupport B x) (pointSupport B y) (pointSupport B z)
      T univ h01 h02 h12
    simp only [univ_inter,pointSupport_card,hx,hy,hz,card_univ,hi,hT] at hc
    change 7 + 7 + 7 + N.card = 16 + 2*3 at hc
    omega
  intro hTw
  have hcount := three_support_count (pointSupport B x) (pointSupport B y) (pointSupport B z)
    T (pointSupport B w) h01 h02 h12
  have hsw : (pointSupport B w ∩ T).card = 3 := by rw [inter_eq_right.mpr hTw,hT]
  have hn : (pointSupport B w ∩ N).card ≤ 1 := (card_le_card inter_subset_right).trans_eq hN
  have hxp := minimum_pair_le_four hv h x w hx hwx.symm
  have hyp := minimum_pair_le_four hv h y w hy hwy.symm
  have hzp := minimum_pair_le_four hv h z w hz hwz.symm
  have hfloor := degree_floor hv h w
  rw [hsw,pointSupport_card,pointSupport_pair,pointSupport_pair,pointSupport_pair] at hcount
  simp only [pair_comm w] at hcount
  change indexedSubsetDegree B {x,w} + indexedSubsetDegree B {y,w} +
    indexedSubsetDegree B {z,w} + (pointSupport B w ∩ N).card = indexedDegree B w + 2*3 at hcount
  have hw : indexedDegree B w = 7 := by omega
  have hp : indexedSubsetDegree B {w,x} = 4 := by rw [pair_comm]; omega
  have hq : indexedSubsetDegree B {w,y} = 4 := by rw [pair_comm]; omega
  have hr : indexedSubsetDegree B {w,z} = 4 := by rw [pair_comm]; omega
  exact no_three_minimum_exceptions hv h w x y z hw hwx.symm hwy.symm hwz.symm hxy hxz hyz hp hq hr

#guard_standard_axioms three_support_count pointSupport_triple three_ordinary_roots_no_fourth

end CoveringDesigns.C19_9_3
