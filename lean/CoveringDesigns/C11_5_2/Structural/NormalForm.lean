import CoveringDesigns.C11_5_2.Structural.Grid
import CoveringDesigns.C11_5_2.Structural.DoubledEdges
import CoveringDesigns.C11_5_2.Structural.Partition
import CoveringDesigns.C11_5_2.Structural.Residual
import Mathlib.Tactic.FinCases

/-! Assembling the structural frame into Stanton's seven-block template.
All reorderings below concern the four named double-intersection blocks. -/

namespace CoveringDesigns.StantonStructural

open Finset

variable {α : Type*} [DecidableEq α]

private theorem image_four_perm {β : Type*} [DecidableEq β]
    (f : Fin 4 → β) (e : Equiv.Perm (Fin 4)) :
    univ.image f = {f (e 0), f (e 1), f (e 2), f (e 3)} := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by
    ext i
    fin_cases i <;> simp
  calc
    univ.image f = (univ.image e).image f := by
      rw [image_univ_of_surjective e.surjective]
    _ = univ.image (fun i => f (e i)) := by rw [image_image]; rfl
    _ = _ := by rw [hu]; simp

private theorem residual_not_in_grid_line {X T W B : Finset α}
    (G : GridCells X T W)
    (hB : B = {G.s} ∪ G.C ∨ B = {G.t} ∪ G.D ∨
      B = {G.s} ∪ G.D ∨ B = {G.t} ∪ G.C)
    {x y : α} (hx : x ∈ B) (hy : y ∈ B)
    (he : residualEdge G.C G.D G.s G.t x y) : False := by
  have hd := G.pairwise_disjoint
  simp only [List.pairwise_cons, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    disjoint_left, mem_singleton] at hd
  rcases hB with rfl | rfl | rfl | rfl <;>
    simp only [mem_union, mem_singleton] at hx hy <;>
    simp only [residualEdge] at he
  all_goals aesop

variable [Fintype α]

set_option maxHeartbeats 800000 in
/-- The doubled-edge structure and the residual graph force the normal form. -/
theorem DoubledFrame.nonempty_templatePartition {S : SixBlockFrame α}
    (E : DoubledFrame S) : Nonempty (TemplatePartition S.family) := by
  have h20 : S.trace (E.order 2) ≠ S.trace (E.order 0) := by
    intro h
    have hi := E.order.injective (S.toFourTraceSystem.trace_injective h)
    exact (by decide : (2 : Fin 4) ≠ 0) hi
  have h21 : S.trace (E.order 2) ≠ S.X \ S.trace (E.order 0) := by
    intro h
    rw [← E.trace01] at h
    have hi := E.order.injective (S.toFourTraceSystem.trace_injective h)
    exact (by decide : (2 : Fin 4) ≠ 1) hi
  obtain ⟨G⟩ := exists_grid_cells S.cardX (S.trace_subset (E.order 0))
    (S.trace_subset (E.order 2)) (S.trace_card (E.order 0))
    (S.trace_card (E.order 2)) h20 h21
  have hline (i : Fin 4) : S.trace i = {G.s} ∪ G.C ∨
      S.trace i = {G.t} ∪ G.D ∨ S.trace i = {G.s} ∪ G.D ∨
      S.trace i = {G.t} ∪ G.C := by
    obtain ⟨k, rfl⟩ := E.order.surjective i
    fin_cases k
    · exact Or.inl G.T_eq
    · exact Or.inr (Or.inl (E.trace01.trans G.T_compl_eq))
    · rcases G.W_eq_or with h | h
      · exact Or.inr (Or.inr (Or.inl h.1))
      · exact Or.inr (Or.inr (Or.inr h.1))
    · rcases G.W_eq_or with h | h
      · exact Or.inr (Or.inr (Or.inr (E.trace23.trans h.2)))
      · exact Or.inr (Or.inr (Or.inl (E.trace23.trans h.2)))
  have hgrid := G.pairwise_disjoint
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, disjoint_singleton_left, mem_singleton] at hgrid
  have hst : G.s ≠ G.t := by tauto
  have hsCD : G.s ∉ G.C ∪ G.D := by simp only [mem_union]; tauto
  have htCD : G.t ∉ G.C ∪ G.D := by simp only [mem_union]; tauto
  have hCD : Disjoint G.C G.D := by tauto
  have hres (x y : α) (hx : x ∈ S.X) (hy : y ∈ S.X) (hne : x ≠ y)
      (he : residualEdge G.C G.D G.s G.t x y) :
      (x ∈ S.U ∧ y ∈ S.U) ∨ (x ∈ S.V ∧ y ∈ S.V) := by
    rcases S.right_cover x hx y hy hne with ⟨i, hxi, hyi⟩ | hu | hv
    · exact False.elim (residual_not_in_grid_line G (hline i) hxi hyi he)
    · exact Or.inl hu
    · exact Or.inr hv
  have hST := hres G.s G.t G.s_mem_X G.t_mem_X hst (Or.inl ⟨rfl, rfl⟩)
  have hCross : ∀ c ∈ G.C, ∀ d ∈ G.D,
      (c ∈ S.U ∧ d ∈ S.U) ∨ (c ∈ S.V ∧ d ∈ S.V) := by
    intro c hc d hd
    have hne : c ≠ d := by
      intro he
      subst d
      exact disjoint_left.mp hCD hc hd
    exact hres c d (G.C_subset hc) (G.D_subset hd) hne
      (Or.inr (Or.inr (Or.inl ⟨hc, hd⟩)))
  obtain ⟨R, hR, hRc, hUV⟩ := residual_completion G.C_card G.D_card hst hCD
    hsCD htCD S.U_card S.V_card (E.right_union.trans G.span.symm) hST hCross
  have hcross (L : Finset α) (hL : L ⊆ S.A) :
      Disjoint L {G.s} ∧ Disjoint L {G.t} ∧ Disjoint L G.C ∧ Disjoint L G.D := by
    exact ⟨S.disjointAX.mono hL (singleton_subset_iff.mpr G.s_mem_X),
      S.disjointAX.mono hL (singleton_subset_iff.mpr G.t_mem_X),
      S.disjointAX.mono hL G.C_subset, S.disjointAX.mono hL G.D_subset⟩
  have ha := hcross {S.a} (singleton_subset_iff.mpr S.a_mem)
  have hF := hcross (S.edge (E.order 0)) (S.edge_subset (E.order 0))
  have hH := hcross (S.edge (E.order 2)) (S.edge_subset (E.order 2))
  have hsF := hF.1.symm
  have htF := hF.2.1.symm
  have hsH := hH.1.symm
  have htH := hH.2.1.symm
  have hdis : List.Pairwise Disjoint
      [{S.a}, {G.s}, {G.t}, S.edge (E.order 0), S.edge (E.order 2), G.C, G.D] := by
    have hl := E.left_disjoint
    have hr := G.pairwise_disjoint
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hl hr ⊢
    tauto
  have hspan : {S.a, G.s, G.t} ∪ S.edge (E.order 0) ∪ S.edge (E.order 2) ∪
      G.C ∪ G.D = univ := by
    calc
      _ = S.A ∪ S.X := by
        simp only [E.left_eq, ← G.span]
        ext x
        simp only [mem_union, mem_insert, mem_singleton]
        tauto
      _ = univ := S.spans
  have himage : (univ.image fun i => S.edge i ∪ S.trace i) =
      {S.edge (E.order 0) ∪ {G.s} ∪ G.C,
       S.edge (E.order 0) ∪ {G.t} ∪ G.D,
       S.edge (E.order 2) ∪ {G.s} ∪ G.D,
       S.edge (E.order 2) ∪ {G.t} ∪ G.C} := by
    have hi := image_four_perm (fun i => S.edge i ∪ S.trace i) E.order
    rw [E.edge01, E.edge23] at hi
    have ht1 := E.trace01.trans G.T_compl_eq
    rcases G.W_eq_or with ⟨hw, hwc⟩ | ⟨hw, hwc⟩
    · have ht3 := E.trace23.trans hwc
      simp only [G.T_eq, ht1, hw, ht3] at hi
      simpa only [union_assoc] using hi
    · have ht3 := E.trace23.trans hwc
      simp only [G.T_eq, ht1, hw, ht3] at hi
      simpa only [union_assoc, ← insert_empty, insert_comm] using hi
  have hblocks : S.family =
      {{S.a} ∪ S.edge (E.order 0) ∪ S.edge (E.order 2),
       S.edge (E.order 0) ∪ {G.s} ∪ G.C,
       S.edge (E.order 0) ∪ {G.t} ∪ G.D,
       S.edge (E.order 2) ∪ {G.s} ∪ G.D,
       S.edge (E.order 2) ∪ {G.t} ∪ G.C,
       {S.a} ∪ G.C ∪ G.D, {S.a, G.s, G.t} ∪ R} := by
    rcases hUV with ⟨hu, hv⟩ | ⟨hv, hu⟩
    all_goals
      simp only [SixBlockFrame.family, himage, ← E.same_singleton, hu, hv, E.left_eq,
        singleton_union, insert_union, union_assoc, insert_comm]
      all_goals simp only [← insert_empty, insert_comm]
  exact ⟨{
    a := S.a, s := G.s, t := G.t
    F := S.edge (E.order 0), G := S.edge (E.order 2), Cpair := G.C, D := G.D, R := R
    F_card := S.edge_card (E.order 0), G_card := S.edge_card (E.order 2)
    Cpair_card := G.C_card, D_card := G.D_card
    cells_disjoint := hdis, spans := hspan, R_subset := hR, R_card := hRc
    blocks_eq := hblocks }⟩

#guard_standard_axioms DoubledFrame.nonempty_templatePartition

/-- Every six-block frame has the structural seven-block partition. -/
theorem SixBlockFrame.nonempty_templatePartition (S : SixBlockFrame α) :
    Nonempty (TemplatePartition S.family) := by
  obtain ⟨E⟩ := S.exists_doubled_frame
  exact E.nonempty_templatePartition

#guard_standard_axioms SixBlockFrame.nonempty_templatePartition

end CoveringDesigns.StantonStructural
