import CoveringDesigns.C14_5_3.ExactLink

/-! Exact residual capacity, slack and the original completion obstruction.
This module must remain independent of the parent lower bound forty-one. -/
namespace CoveringDesigns.C14_5_3
open Finset
open LabelledCliques (extensions)
universe u v w
variable {α : Type u} {ι : Type v} {κ : Type w}
  [Fintype α] [DecidableEq α] [Fintype ι] [Fintype κ]

def collinearCount (L : ι → Finset α) (A : Finset α) : ℕ :=
  ((collinearTriples L).filter (· ⊆ A)).card

/-- Only noncollinear triples are required; occurrence images may repeat. -/
def IsCompletion (L : ι → Finset α) (B : κ → Finset α) : Prop :=
  Multicover.Uniform B 5 ∧
    ∀ T ∈ noncollinearTriples L, 1 ≤ indexedSubsetDegree B T

def completionLoss (L : ι → Finset α) (B : κ → Finset α) : ℕ :=
  ∑ i, (collinearCount L (B i) - 1)

def completionExcess (L : ι → Finset α) (B : κ → Finset α) : ℕ :=
  ∑ T ∈ noncollinearTriples L, (indexedSubsetDegree B T - 1)

theorem collinearCount_pos {L : ι → Finset α} (hv : Fintype.card α = 13)
    (hL : ExactDesign.IsDesign L 4 2 1) {A : Finset α} (hA : A.card = 5) :
    1 ≤ collinearCount L A := by
  obtain ⟨T, hT, hp⟩ := no_five_arc hv hL A hA
  apply Nat.succ_le_of_lt
  apply card_pos.mpr
  refine ⟨T, ?_⟩
  have h := mem_powersetCard.mp hT
  simp only [mem_filter, collinearTriples, mem_powersetCard, subset_univ, true_and]
  exact ⟨⟨h.2, hp⟩, h.1⟩

theorem collinear_sum (L : ι → Finset α) (B : κ → Finset α) :
    (∑ T ∈ collinearTriples L, indexedSubsetDegree B T) =
      ∑ i, collinearCount L (B i) :=
  selected_subset_count B (collinearTriples L)

theorem triple_sum_split (L : ι → Finset α) (B : κ → Finset α) :
    (∑ T ∈ collinearTriples L, indexedSubsetDegree B T) +
      (∑ T ∈ noncollinearTriples L, indexedSubsetDegree B T) =
        ∑ T ∈ (univ : Finset α).powersetCard 3, indexedSubsetDegree B T := by
  have hn : noncollinearTriples L = ((univ : Finset α).powersetCard 3).filter
      (fun T => ¬ 0 < indexedSubsetDegree L T) := by
    ext T
    simp [noncollinearTriples]
  rw [collinearTriples, hn]
  exact sum_filter_add_sum_filter_not _ _ _

/-- Subtraction-free form of the exact loss-plus-excess identity. -/
theorem completion_slack {L : ι → Finset α} {B : κ → Finset α}
    (hv : Fintype.card α = 13) (hL : ExactDesign.IsDesign L 4 2 1)
    (hB : IsCompletion L B) :
    completionLoss L B + completionExcess L B + 234 = 9 * Fintype.card κ := by
  have hC : completionLoss L B + Fintype.card κ = ∑ i, collinearCount L (B i) := by
    have he : Fintype.card κ = ∑ _i : κ, 1 := by simp
    rw [completionLoss, he, ← sum_add_distrib]
    exact sum_congr rfl (fun i _ => Nat.sub_add_cancel (collinearCount_pos hv hL (hB.1 i)))
  have hE : completionExcess L B + 234 =
      ∑ T ∈ noncollinearTriples L, indexedSubsetDegree B T := by
    rw [← noncollinear_card hv hL, completionExcess, card_eq_sum_ones, ← sum_add_distrib]
    exact sum_congr rfl (fun T hT => Nat.sub_add_cancel (hB.2 T hT))
  have hs := triple_sum_split L B
  rw [collinear_sum, Multicover.subsetDegree_sum_of_uniform hB.1] at hs
  norm_num [Nat.choose] at hs
  omega

theorem completion_capacity {L : ι → Finset α} {B : κ → Finset α}
    (hv : Fintype.card α = 13) (hL : ExactDesign.IsDesign L 4 2 1)
    (hB : IsCompletion L B) : 26 ≤ Fintype.card κ := by
  have := completion_slack hv hL hB
  omega

theorem completion_equality {L : ι → Finset α} {B : κ → Finset α}
    (hv : Fintype.card α = 13) (hL : ExactDesign.IsDesign L 4 2 1)
    (hB : IsCompletion L B) (hn : Fintype.card κ = 26) :
    (∀ i, collinearCount L (B i) = 1) ∧
      (∀ T ∈ noncollinearTriples L, indexedSubsetDegree B T = 1) := by
  have hs := completion_slack hv hL hB
  have hl : completionLoss L B = 0 := by omega
  have he : completionExcess L B = 0 := by omega
  constructor
  · intro i
    have hz := (sum_eq_zero_iff.mp hl) i (mem_univ i)
    have hp := collinearCount_pos hv hL (hB.1 i)
    omega
  · intro T hT
    have hz := (sum_eq_zero_iff.mp he) T hT
    have hp := hB.2 T hT
    omega

theorem collinear_pair_count {L : ι → Finset α} (hL : ExactDesign.IsDesign L 4 2 1)
    {P : Finset α} (hP : P.card = 2) :
    ((extensions P).filter (fun T => 0 < indexedSubsetDegree L T)).card = 2 := by
  have hs := LabelledCliques.extension_sum hL.1 P
  rw [hP, hL.2 P hP] at hs
  have he : (∑ T ∈ extensions P, indexedSubsetDegree L T) =
      ((extensions P).filter (fun T => 0 < indexedSubsetDegree L T)).card := by
    rw [card_eq_sum_ones, sum_filter]
    apply sum_congr rfl
    intro T hT
    have hm := exact_multiplicity_le_one hL (T := T)
      (by have := (LabelledCliques.mem_extensions.mp hT).2; omega)
    split_ifs <;> omega
  rw [← he]
  exact hs

theorem noncollinear_pair_count {L : ι → Finset α} (hv : Fintype.card α = 13)
    (hL : ExactDesign.IsDesign L 4 2 1) {P : Finset α} (hP : P.card = 2) :
    ((extensions P).filter (fun T => indexedSubsetDegree L T = 0)).card = 9 := by
  have hs := card_filter_add_card_filter_not (s := extensions P)
    (fun T => 0 < indexedSubsetDegree L T)
  have he : (extensions P).filter (fun T => ¬ 0 < indexedSubsetDegree L T) =
      (extensions P).filter (fun T => indexedSubsetDegree L T = 0) := by
    ext T
    simp
  rw [he, collinear_pair_count hL hP, LabelledCliques.card_extensions, hv, hP] at hs
  omega

/-- Exact pair identity retains the location of every noncollinear excess. -/
theorem completion_pair_identity {L : ι → Finset α} {B : κ → Finset α}
    (hv : Fintype.card α = 13) (hL : ExactDesign.IsDesign L 4 2 1)
    (hB : IsCompletion L B) {P : Finset α} (hP : P.card = 2) :
    3 * indexedSubsetDegree B P = 9 +
      (∑ T ∈ (extensions P).filter (fun T => indexedSubsetDegree L T = 0),
        (indexedSubsetDegree B T - 1)) +
      ∑ T ∈ (extensions P).filter (fun T => 0 < indexedSubsetDegree L T),
        indexedSubsetDegree B T := by
  have hs := LabelledCliques.extension_sum hB.1 P
  rw [hP] at hs
  have hp (T : Finset α)
      (hT : T ∈ (extensions P).filter (fun T => indexedSubsetDegree L T = 0)) :
      1 ≤ indexedSubsetDegree B T := by
    have hm := mem_filter.mp hT
    apply hB.2
    have hc := (LabelledCliques.mem_extensions.mp hm.1).2
    simp only [noncollinearTriples, mem_filter, mem_powersetCard, subset_univ, true_and]
    exact ⟨by omega, hm.2⟩
  have he : (∑ T ∈ (extensions P).filter (fun T => indexedSubsetDegree L T = 0),
      (indexedSubsetDegree B T - 1)) + 9 =
      ∑ T ∈ (extensions P).filter (fun T => indexedSubsetDegree L T = 0),
        indexedSubsetDegree B T := by
    have hh := sum_congr rfl (fun T hT => Nat.sub_add_cancel (hp T hT))
    rw [sum_add_distrib, sum_const, Nat.nsmul_eq_mul, mul_one,
      noncollinear_pair_count hv hL hP] at hh
    exact hh
  have hsplit := sum_filter_add_sum_filter_not (extensions P)
    (fun T => indexedSubsetDegree L T = 0) (fun T => indexedSubsetDegree B T)
  have hne : (extensions P).filter (fun T => ¬ indexedSubsetDegree L T = 0) =
      (extensions P).filter (fun T => 0 < indexedSubsetDegree L T) := by
    ext T
    simp [Nat.pos_iff_ne_zero]
  rw [hne] at hsplit
  omega

theorem extensions_inside_pair (P : Finset α) {c d : α}
    (hc : c ∉ P) (hd : d ∉ P) (hcd : c ≠ d) :
    (extensions P).filter (· ⊆ insert c (insert d P)) = {insert c P, insert d P} := by
  ext T
  simp only [mem_filter, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hT, hsub⟩
    obtain ⟨x, hx, rfl⟩ := LabelledCliques.extension_eq_insert hT
    have hm := hsub (mem_insert_self x P)
    simp only [mem_insert] at hm
    rcases hm with rfl | rfl | hm
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (hx hm).elim
  · rintro (rfl | rfl)
    · exact ⟨LabelledCliques.mem_extensions.mpr
        ⟨subset_insert _ _, card_insert_of_notMem hc⟩,
        insert_subset_insert _ (subset_insert _ _)⟩
    · refine ⟨LabelledCliques.mem_extensions.mpr
        ⟨subset_insert _ _, card_insert_of_notMem hd⟩, ?_⟩
      exact subset_insert _ _

theorem collinear_extensions_eq {L : ι → Finset α}
    (hL : ExactDesign.IsDesign L 4 2 1) {P : Finset α} (hP : P.card = 2)
    {i : ι} (hPi : P ⊆ L i) :
    (extensions P).filter (fun T => 0 < indexedSubsetDegree L T) =
      (extensions P).filter (· ⊆ L i) := by
  ext T
  simp only [mem_filter]
  constructor
  · rintro ⟨hT, hp⟩
    obtain ⟨j, hj⟩ := (multiplicity_pos_iff L T).mp hp
    obtain ⟨k, hk, hu⟩ := exact_unique_line hL hP
    have hji : j = i := (hu j ((LabelledCliques.mem_extensions.mp hT).1.trans hj)).trans
      (hu i hPi).symm
    exact ⟨hT, hji ▸ hj⟩
  · rintro ⟨hT, hi⟩
    exact ⟨hT, (multiplicity_pos_iff L T).mpr ⟨i, hi⟩⟩

theorem line_pair_sum {L : ι → Finset α} (hL : ExactDesign.IsDesign L 4 2 1)
    (w : Finset α → ℕ) {P : Finset α} (hP : P.card = 2) {i : ι} {c d : α}
    (hc : c ∉ P) (hd : d ∉ P) (hcd : c ≠ d)
    (he : L i = insert c (insert d P)) :
    (∑ T ∈ (extensions P).filter (fun T => 0 < indexedSubsetDegree L T), w T) =
      w (insert c P) + w (insert d P) := by
  have hPi : P ⊆ L i := by rw [he]; exact (subset_insert _ _).trans (subset_insert _ _)
  rw [collinear_extensions_eq hL hP hPi, he, extensions_inside_pair P hc hd hcd]
  have hne : insert c P ≠ insert d P := by
    intro hh
    have hm : c ∈ insert d P := hh ▸ mem_insert_self c P
    simpa [hc, hcd] using hm
  rw [sum_pair hne]

/-- Three pair-sum congruences on an actual line suffice for each triple weight. -/
theorem linewise_divisibility {L : ι → Finset α}
    (hL : ExactDesign.IsDesign L 4 2 1) (w : Finset α → ℕ)
    (hp : ∀ P : Finset α, P.card = 2 →
      3 ∣ ∑ T ∈ (extensions P).filter (fun T => 0 < indexedSubsetDegree L T), w T)
    {T : Finset α} (hT : T ∈ collinearTriples L) : 3 ∣ w T := by
  have hm := mem_filter.mp hT
  have ht := (mem_powersetCard.mp hm.1).2
  obtain ⟨i, hi⟩ := (multiplicity_pos_iff L T).mp hm.2
  have hc : (L i \ T).card = 1 := by rw [card_sdiff_of_subset hi, hL.1 i, ht]
  obtain ⟨d, hd⟩ := card_eq_one.mp hc
  have hdT : d ∉ T := (mem_sdiff.mp (hd.symm ▸ mem_singleton_self d)).2
  have he : L i = insert d T := by rw [insert_eq, ← hd, sdiff_union_of_subset hi]
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht
  have hda : d ≠ a := by simpa using fun h => hdT (by simp [h])
  have hdb : d ≠ b := by simpa using fun h => hdT (by simp [h])
  have hdc : d ≠ c := by simpa using fun h => hdT (by simp [h])
  have h1 := hp {a,b} (by simp [hab])
  have h2 := hp {a,c} (by simp [hac])
  have h3 := hp {a,d} (by simp [Ne.symm hda])
  have he1 : L i = insert c (insert d {a,b}) := by
    rw [he]; ext x; simp only [mem_insert, mem_singleton]; tauto
  have he2 : L i = insert b (insert d {a,c}) := by
    rw [he]; ext x; simp only [mem_insert, mem_singleton]; tauto
  have he3 : L i = insert b (insert c {a,d}) := by
    rw [he]; ext x; simp only [mem_insert, mem_singleton]; tauto
  rw [line_pair_sum hL w (by simp [hab]) (by simp [Ne.symm hac, Ne.symm hbc])
    (by simp [hda, hdb]) (Ne.symm hdc) he1] at h1
  rw [line_pair_sum hL w (by simp [hac]) (by simp [Ne.symm hab, hbc])
    (by simp [hda, hdc]) (Ne.symm hdb) he2] at h2
  rw [line_pair_sum hL w (by simp [Ne.symm hda]) (by simp [Ne.symm hab, Ne.symm hdb])
    (by simp [Ne.symm hac, Ne.symm hdc]) hbc he3] at h3
  have hcycle (x y z : α) : w {z,x,y} = w {x,y,z} := by
    congr 1
    ext p
    simp only [mem_insert, mem_singleton]
    tauto
  have hswap (x y z : α) : w {y,x,z} = w {x,y,z} := by rw [insert_comm y x]
  rw [hcycle a b c, hcycle a b d] at h1
  rw [hswap a b c, hcycle a c d] at h2
  rw [hswap a b d, hswap a c d] at h3
  rw [Nat.dvd_iff_mod_eq_zero] at h1 h2 h3 ⊢
  omega

/-- Universal original completion bound, proved before any parent exclusion. -/
theorem completion_at_least_27 {L : ι → Finset α} {B : κ → Finset α}
    (hv : Fintype.card α = 13) (hL : ExactDesign.IsDesign L 4 2 1)
    (hB : IsCompletion L B) : 27 ≤ Fintype.card κ := by
  have hlo := completion_capacity hv hL hB
  by_contra hn
  have hn : Fintype.card κ = 26 := by omega
  obtain ⟨hc, hm⟩ := completion_equality hv hL hB hn
  have hp (P : Finset α) (hP : P.card = 2) :
      3 ∣ ∑ T ∈ (extensions P).filter (fun T => 0 < indexedSubsetDegree L T),
        indexedSubsetDegree B T := by
    have hs := completion_pair_identity hv hL hB hP
    have hz : (∑ T ∈ (extensions P).filter (fun T => indexedSubsetDegree L T = 0),
        (indexedSubsetDegree B T - 1)) = 0 := by
      apply sum_eq_zero
      intro T hT
      have hh := mem_filter.mp hT
      have ht := (LabelledCliques.mem_extensions.mp hh.1).2
      rw [hm T (by simp only [noncollinearTriples, mem_filter, mem_powersetCard,
        subset_univ, true_and]; exact ⟨by omega, hh.2⟩)]
      norm_num
    rw [hz] at hs
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hd : 3 ∣ ∑ T ∈ collinearTriples L, indexedSubsetDegree B T :=
    dvd_sum (fun T hT => linewise_divisibility hL (indexedSubsetDegree B) hp hT)
  rw [collinear_sum] at hd
  simp only [hc, sum_const, card_univ, Nat.nsmul_eq_mul, mul_one, hn] at hd
  norm_num at hd

end CoveringDesigns.C14_5_3
