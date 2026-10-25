import CoveringDesigns.C19_9_3.Incidence
import CoveringDesigns.SevenBlock.Core

/-! Classification of minimum links, using their actual point and occurrence
subtypes. This component does not import the a=1 Stanton adapter. -/
namespace CoveringDesigns.C19_9_3
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

private theorem link_cover {B : I → Finset V} (h : Multicover.IsCover B 9 3 1) (x : V) :
    Multicover.IsCover (Multicover.subsetLink B {x}) 8 2 1 := by
  simpa using Multicover.subsetLink_isCover h {x} (by simp)

private theorem link_points (hv : Fintype.card V = 19) (x : V) :
    Fintype.card {y : V // y ∉ ({x} : Finset V)} = 18 := by
  rw [Multicover.subset_complement_card,card_singleton,hv]

private theorem link_occurrences (B : I → Finset V) (x : V) (hx : indexedDegree B x = 7) :
    Fintype.card {i : I // ({x} : Finset V) ⊆ B i} = 7 := by
  rw [Multicover.subsetLink_card,Multicover.subsetDegree_singleton,hx]

/-- The a=2 classification applies to every actual minimum link. Its local
occurrence equivalence has domain the original occurrences through x. -/
theorem minimum_link_classification {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x : V) (hx : indexedDegree B x = 7) :
    ∃ tag : Bool, SevenBlock.IndexedIsomorphic (Multicover.subsetLink B {x})
      (SevenBlock.templateBlock 2 tag) :=
  SevenBlock.classification_ge_two (by decide : 2 ≤ 2) (link_points hv x)
    (link_cover h x) (link_occurrences B x hx)

/-- Point degree in an actual link is the parent pair multiplicity. -/
theorem actual_link_degree (B : I → Finset V) (x : V)
    (y : {y : V // y ∉ ({x} : Finset V)}) :
    indexedDegree (Multicover.subsetLink B {x}) y = indexedSubsetDegree B {x,y.val} := by
  rw [← Multicover.subsetDegree_singleton,Multicover.subsetLink_multiplicity]
  simp

/-- Pair multiplicity in an actual link is the parent triple multiplicity. -/
theorem actual_link_codegree (B : I → Finset V) (x : V)
    (y z : {y : V // y ∉ ({x} : Finset V)}) :
    indexedSubsetDegree (Multicover.subsetLink B {x}) {y,z} =
      indexedSubsetDegree B {x,y.val,z.val} := by
  rw [Multicover.subsetLink_multiplicity]
  simp [insert_comm]

/-- Every minimum point has exactly two distinct exceptional neighbours,
and their common triple multiplicity is two or four. -/
theorem minimum_profile {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x : V) (hx : indexedDegree B x = 7) :
    ∃ p q : V, p ≠ x ∧ q ≠ x ∧ p ≠ q ∧
      indexedSubsetDegree B {x,p} = 4 ∧ indexedSubsetDegree B {x,q} = 4 ∧
      (∀ y, y ≠ x → y ≠ p → y ≠ q → indexedSubsetDegree B {x,y} = 3) ∧
      (indexedSubsetDegree B {x,p,q} = 2 ∨ indexedSubsetDegree B {x,p,q} = 4) := by
  obtain ⟨p,q,hpq,hp,hq,hr⟩ := SevenBlock.covering_degree_profile (by decide : 1 ≤ 2)
    (link_points hv x) (link_cover h x) (link_occurrences B x hx)
  have ht := SevenBlock.exceptional_codegree_dichotomy (by decide : 2 ≤ 2)
    (link_points hv x) (link_cover h x) (link_occurrences B x hx) p q hpq hp hq hr
  refine ⟨p.val,q.val,by simpa using p.property,by simpa using q.property,
    fun he => hpq (Subtype.ext he),?_,?_,?_,?_⟩
  · exact (actual_link_degree B x p).symm.trans hp
  · exact (actual_link_degree B x q).symm.trans hq
  · intro y hy hyp hyq
    let y' : {y : V // y ∉ ({x} : Finset V)} := ⟨y,by simpa using hy⟩
    exact (actual_link_degree B x y').symm.trans
      (hr y' (fun he => hyp (congrArg Subtype.val he)) (fun he => hyq (congrArg Subtype.val he)))
  · simpa only [actual_link_codegree] using ht

theorem minimum_pair_le_four {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x y : V) (hx : indexedDegree B x = 7) (hxy : x ≠ y) :
    indexedSubsetDegree B {x,y} ≤ 4 := by
  obtain ⟨p,q,_,_,_,hp,hq,hr,_⟩ := minimum_profile hv h x hx
  by_cases hyp : y = p
  · simpa [hyp,hp]
  by_cases hyq : y = q
  · simpa [hyq,hq]
  rw [hr y hxy.symm hyp hyq]
  decide

#guard_standard_axioms minimum_link_classification actual_link_degree actual_link_codegree
  minimum_profile minimum_pair_le_four

end CoveringDesigns.C19_9_3
