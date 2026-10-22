import CoveringDesigns.QuadrupleAssembly.Counting
import CoveringDesigns.QuadrupleAssembly.Transport
import CoveringDesigns.QuadrupleAssembly.Coverage
import CoveringDesigns.QuadrupleAssembly.Arithmetic

namespace CoveringDesigns.QuadrupleAssembly
open Finset

private theorem choose_two (n : ℕ) : 2 * n.choose 2 = n*(n-1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  simpa [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial, Nat.mul_comm] using h.symm

private theorem choose_three (n : ℕ) : 6 * n.choose 3 = n*(n-1)*(n-2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 3
  simpa [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial,
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h.symm

theorem h_seed_card {u : ℕ} {H : Family (Core u)} (hH : HSeed H) :
    H.card = 54 * (2*u).choose 3 := by
  have h := hH.count Prod.fst
  rw [transverse_card] at h
  norm_num [Core, Group] at h
  rw [Nat.mul_comm u 2] at h
  omega

theorem gdd_seed_card {u : ℕ} {G : Family (Core u)} (hG : GDDSeed G) :
    G.card = 24*u*(u-1) := by
  let e : Core u ≃ Fin u × (Fin 2 × Fin 6) := Equiv.prodAssoc _ _ _
  have he : ∀ x, (e x).1 = hole x := fun _ => rfl
  have h := (hG.relabel e he).count Prod.fst
  rw [transverse_card, relabel_card] at h
  norm_num at h
  have hc := choose_two u
  nlinarith

theorem factor_card {F : Fin 5 → Family (Fin 6)} (hF : Factors F) (r : Fin 5) :
    (F r).card = 3 := by
  have hs : (F r).biUnion id = univ := by
    ext x
    simp only [mem_biUnion, id_eq, mem_univ, iff_true]
    obtain ⟨E,hE,_⟩ := hF.partition r x
    exact ⟨E,hE⟩
  have hd : (F r : Set (Finset (Fin 6))).PairwiseDisjoint id := by
    intro E hE D hD hne
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨B,hB,huniq⟩ := hF.partition r x
    exact hne ((huniq E ⟨hE,hx⟩).trans (huniq D ⟨hD,hy⟩).symm)
  have hc := congrArg Finset.card hs
  rw [card_biUnion hd] at hc
  simp only [id_eq] at hc
  rw [sum_const_nat (fun E hE => hF.uniform r E hE)] at hc
  norm_num at hc
  omega

private theorem hole_pair_card (u : ℕ) : Fintype.card (HolePair u) = u.choose 2 := by
  let f : HolePair u → {S : Finset (Fin u) // S.card = 2} :=
    fun p => ⟨{p.val.1,p.val.2}, by simp [ne_of_lt p.property]⟩
  have hi : Function.Injective f := by
    intro p q he
    have he' := congrArg Subtype.val he
    have hx : p.val.1 = q.val.1 ∨ p.val.1 = q.val.2 := by
      have hm : p.val.1 ∈ (f p).val := by simp [f]
      rw [he'] at hm
      simpa [f] using hm
    have hy : p.val.2 = q.val.1 ∨ p.val.2 = q.val.2 := by
      have hm : p.val.2 ∈ (f p).val := by simp [f]
      rw [he'] at hm
      simpa [f] using hm
    have hp := p.property
    have hq := q.property
    apply Subtype.ext
    apply Prod.ext <;> rcases hx with hx | hx <;> rcases hy with hy | hy <;> omega
  have hs : Function.Surjective f := by
    rintro ⟨S,hS⟩
    obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hS
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨⟨(a,b),h⟩,rfl⟩
    · exact ⟨⟨(b,a),h⟩,Subtype.ext (by simp [f,pair_comm])⟩
  have h := Fintype.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)
  simpa using h

theorem pair_index_card {u : ℕ} {F : Fin 5 → Family (Fin 6)} (hF : Factors F) :
    Fintype.card (PairIndex u F) = 90*u*(u-1) := by
  simp only [PairIndex, Fintype.card_prod, Fintype.card_sigma, Fintype.card_coe,
    factor_card hF, hole_pair_card, Fintype.card_fin]
  have hc := choose_two u
  norm_num
  nlinarith

private theorem total_budget {u : ℕ} (hu : 3 ≤ u) :
    54*(2*u).choose 3 + 24*u*(u-1) + 78*u + 90*u*(u-1) = 6*u^2*(12*u+1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hu
  have h := choose_three (2*(3+n))
  have h1 : 2*(3+n)-1 = 5+2*n := by omega
  have h2 : 2*(3+n)-2 = 4+2*n := by omega
  have h3 : 3+n-1 = 2+n := by omega
  rw [h1,h2] at h
  rw [h3]
  nlinarith

/-- Upper budgets, before using any optimality argument. -/
theorem class_budgets {u : ℕ} {H G : Family (Core u)} {L : Family Local}
    {F : Fin 5 → Family (Fin 6)} (hH : HSeed H) (hG : GDDSeed G)
    (hL : L.card = 78) (hF : Factors F) :
    (classA H).card ≤ 54*(2*u).choose 3 ∧
    (classB G).card ≤ 24*u*(u-1) ∧
    (classC (u := u) L).card ≤ 78*u ∧
    (classD (u := u) F).card ≤ 90*u*(u-1) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact (card_image_le).trans_eq (h_seed_card hH)
  · exact (card_image_le).trans_eq (gdd_seed_card hG)
  · apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _h : Fin u, L.card := sum_le_sum (fun _ _ => card_image_le)
      _ = _ := by simp [hL,Nat.mul_comm]
  · exact card_image_le.trans_eq (by rw [card_univ,pair_index_card hF])

/-- Sharpness forces all four images to attain their budgets and all unions to be disjoint. -/
theorem assembly_sharp {u : ℕ} (hu : 3 ≤ u) {H G : Family (Core u)} {L : Family Local}
    {F : Fin 5 → Family (Fin 6)} (hH : HSeed H) (hG : GDDSeed G)
    (hL : IsCover L 4 3) (hLc : L.card = 78) (hF : Factors F) :
    (assembly H G L F).card = 6*u^2*(12*u+1) ∧
    (classA H).card = 54*(2*u).choose 3 ∧
    (classB G).card = 24*u*(u-1) ∧
    (classC (u := u) L).card = 78*u ∧
    (classD (u := u) F).card = 90*u*(u-1) ∧
    Disjoint (classA H) (classB G) ∧
    Disjoint (classA H ∪ classB G) (classC L) ∧
    Disjoint (classA H ∪ classB G ∪ classC L) (classD F) := by
  have low := lower_bound hu (card_point u) (assembly_isCover hH hG hL hF)
  obtain ⟨ha,hb,hc,hd⟩ := class_budgets hH hG hLc hF
  have hab := card_union_le (classA H) (classB G)
  have habc := card_union_le (classA H ∪ classB G) (classC (u := u) L)
  have habcd := card_union_le (classA H ∪ classB G ∪ classC L) (classD (u := u) F)
  have ht := total_budget hu
  change 6*u^2*(12*u+1) ≤ (classA H ∪ classB G ∪ classC L ∪ classD F).card at low
  refine ⟨by unfold assembly; omega, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
  all_goals apply card_union_eq_card_add_card.mp; omega

/-- The actual ordinary family returned by the shared structural construction. -/
theorem assembly_optimal {u : ℕ} (hu : 3 ≤ u) {H G : Family (Core u)} {L : Family Local}
    {F : Fin 5 → Family (Fin 6)} (hH : HSeed H) (hG : GDDSeed G)
    (hL : IsCover L 4 3) (hLc : L.card = 78) (hF : Factors F) :
    IsCover (assembly H G L F) 4 3 ∧ (assembly H G L F).card = 6*u^2*(12*u+1) :=
  ⟨assembly_isCover hH hG hL hF,(assembly_sharp hu hH hG hL hLc hF).1⟩

end CoveringDesigns.QuadrupleAssembly
