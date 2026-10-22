import CoveringDesigns.QuadrupleAssembly.Contracts
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite

namespace CoveringDesigns.QuadrupleAssembly
open Finset

private def graph {G A : Type*} [DecidableEq G] [DecidableEq A]
    (S : Finset G) (f : S → A) : Finset (G × A) :=
  S.attach.image (fun g => (g.val, f g))

private theorem mem_graph {G A : Type*} [DecidableEq G] [DecidableEq A]
    {S : Finset G} {f : S → A} {x : G × A} :
    x ∈ graph S f ↔ ∃ h : x.1 ∈ S, f ⟨x.1,h⟩ = x.2 := by
  constructor
  · rintro hx
    obtain ⟨g, _, hg⟩ := mem_image.mp hx
    cases x with | mk x y =>
      simp only [Prod.mk.injEq] at hg
      obtain ⟨hgx,hgy⟩ := hg
      subst x
      exact ⟨g.property, hgy⟩
  · rintro ⟨h, hx⟩
    exact mem_image.mpr ⟨⟨x.1,h⟩, mem_attach _ _, by simpa [hx]⟩

private theorem graph_card {G A : Type*} [DecidableEq G] [DecidableEq A]
    (S : Finset G) (f : S → A) : (graph S f).card = S.card := by
  rw [graph, card_image_of_injective]
  · exact card_attach
  · intro x y h
    exact Subtype.ext (congrArg Prod.fst h)

private theorem graph_transverse {G A : Type*} [DecidableEq G] [DecidableEq A]
    (S : Finset G) (f : S → A) : Transverse Prod.fst (graph S f) := by
  intro x hx y hy he
  obtain ⟨hx, ex⟩ := mem_graph.mp hx
  obtain ⟨hy, ey⟩ := mem_graph.mp hy
  apply Prod.ext he
  have hf : f ⟨x.1,hx⟩ = f ⟨y.1,hy⟩ := congrArg f (Subtype.ext he)
  exact ex.symm.trans (hf.trans ey)

/-- Count transverse t-subsets by choosing their groups and one point per group. -/
theorem transverse_card {G A : Type*} [Fintype G] [Fintype A]
    [DecidableEq G] [DecidableEq A] (t : ℕ) :
    Nat.card {T : Finset (G × A) // T.card = t ∧ Transverse Prod.fst T} =
      (Fintype.card G).choose t * (Fintype.card A)^t := by
  classical
  let Source := Σ S : {S : Finset G // S.card = t}, (S.val → A)
  let forward : Source → {T : Finset (G × A) // T.card = t ∧ Transverse Prod.fst T} :=
    fun p => ⟨graph p.1.val p.2, by rw [graph_card]; exact p.1.property,
      graph_transverse _ _⟩
  have hinj : Function.Injective forward := by
    rintro ⟨⟨S,hS⟩,f⟩ ⟨⟨U,hU⟩,g⟩ he
    have hg : graph S f = graph U g := congrArg Subtype.val he
    have hSU : S = U := by
      ext x
      constructor
      · intro hx
        have hm : (x,f ⟨x,hx⟩) ∈ graph S f := mem_graph.mpr ⟨hx,rfl⟩
        rw [hg] at hm
        exact (mem_graph.mp hm).choose
      · intro hx
        have hm : (x,g ⟨x,hx⟩) ∈ graph U g := mem_graph.mpr ⟨hx,rfl⟩
        rw [← hg] at hm
        exact (mem_graph.mp hm).choose
    subst U
    have hfg : f = g := by
      funext x
      have hm : (x.val,f x) ∈ graph S f := mem_graph.mpr ⟨x.property,rfl⟩
      rw [hg] at hm
      exact (mem_graph.mp hm).choose_spec.symm
    subst g
    rfl
  have hsurj : Function.Surjective forward := by
    rintro ⟨T,hT,ht⟩
    let S := T.image Prod.fst
    have hs : S.card = t := (card_image_iff.mpr ht).trans hT
    have choice : ∀ g : S, ∃ a : A, (g.val,a) ∈ T := by
      intro g
      obtain ⟨x,hx,he⟩ := mem_image.mp g.property
      exact ⟨x.2, by rw [← he]; exact hx⟩
    choose f hf using choice
    refine ⟨⟨⟨S,hs⟩,f⟩, Subtype.ext ?_⟩
    change graph S f = T
    ext x
    constructor
    · intro hx
      obtain ⟨hx,he⟩ := mem_graph.mp hx
      simpa [he] using hf ⟨x.1,hx⟩
    · intro hx
      have hsx : x.1 ∈ S := mem_image.mpr ⟨x,hx,rfl⟩
      refine mem_graph.mpr ⟨hsx, ?_⟩
      have he := ht (hf ⟨x.1,hsx⟩) hx rfl
      exact congrArg Prod.snd he
  rw [Nat.card_congr (Equiv.ofBijective forward ⟨hinj,hsurj⟩).symm,
    Nat.card_eq_fintype_card]
  change Fintype.card Source = _
  simp only [Source, Fintype.card_sigma, Fintype.card_fun, Fintype.card_coe]
  calc
    _ = ∑ _x : {S : Finset G // S.card = t}, (Fintype.card A)^t := by
      apply sum_congr rfl
      intro x _
      rw [x.property]
    _ = _ := by simp

/-- Exact transverse incidences determine the block count. -/
theorem GroupDesign.count {α G : Type*} [Fintype α] [DecidableEq α]
    (g : α → G) {k t : ℕ} {C : Family α} (hC : GroupDesign g k t C) :
    k.choose t * C.card =
      Nat.card {T : Finset α // T.card = t ∧ Transverse g T} := by
  classical
  let all := (univ : Finset α).powersetCard t |>.filter (Transverse g)
  have hshadow : C.biUnion (fun B => B.powersetCard t) = all := by
    ext T
    constructor
    · intro hT
      obtain ⟨B,hB,hTB⟩ := mem_biUnion.mp hT
      obtain ⟨hs,hcard⟩ := mem_powersetCard.mp hTB
      exact mem_filter.mpr ⟨mem_powersetCard_univ.mpr hcard,
        (hC.transverse B hB).mono hs⟩
    · intro hT
      obtain ⟨hc,ht⟩ := mem_filter.mp hT
      obtain ⟨B,⟨hB,hs⟩,_⟩ := hC.exact T (mem_powersetCard_univ.mp hc) ht
      exact mem_biUnion.mpr ⟨B,hB,mem_powersetCard.mpr ⟨hs,mem_powersetCard_univ.mp hc⟩⟩
  have hd : (C : Set (Finset α)).PairwiseDisjoint (fun B => B.powersetCard t) := by
    intro B hB D hD hne
    apply disjoint_left.mpr
    intro T hTB hTD
    obtain ⟨hs,hcard⟩ := mem_powersetCard.mp hTB
    obtain ⟨E,he,unique⟩ := hC.exact T hcard ((hC.transverse B hB).mono hs)
    exact hne ((unique B ⟨hB,hs⟩).trans (unique D ⟨hD,(mem_powersetCard.mp hTD).1⟩).symm)
  have hc : all.card = C.card * k.choose t := by
    rw [← hshadow, card_biUnion hd]
    simp only [card_powersetCard]
    rw [sum_const_nat (fun B hB => congrArg (fun n => n.choose t) (hC.uniform B hB))]
  rw [Nat.mul_comm, ← hc]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.subtype_card]
  congr 1
  ext T
  simp [all]

end CoveringDesigns.QuadrupleAssembly
