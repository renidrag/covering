import CoveringDesigns.C17_9_5
import CoveringDesigns.Foundations.StandardAxioms

/-! Full theorem contracts, explicit covering conditions, boundary cases and
transitive foundational-axiom guards for the weighted-partition application. -/
open CoveringDesigns CoveringDesigns.WeightedPartition
open CoveringDesigns.Applications.ZeroDefect CoveringDesigns.HorsleySingh Finset
universe u

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.WeightedPartition.classDegree
#print CoveringDesigns.WeightedPartition.potential
#print CoveringDesigns.Applications.ZeroDefect.nextPairs
#print CoveringDesigns.HorsleySingh.excess
#print CoveringDesigns.HorsleySingh.diagonal
#print CoveringDesigns.HorsleySingh.defect

section GraphContracts
variable {α : Type u} [Fintype α]

#check (potential_update : ∀ [DecidableEq α] {q : ℕ} (w : α → α → ℤ)
    (_hsym : ∀ x y, w x y = w y x) (_hdiag : ∀ x, w x x = 0)
    (c : α → Fin q) (x : α) (i : Fin q),
    potential w (Function.update c x i) = potential w c +
      2*(classDegree w c x i - classDegree w c x (c x)))

#check (exists_balanced_partition : ∀ {q : ℕ} (_hq : 0 < q) (w : α → α → ℤ)
    (_hsym : ∀ x y, w x y = w y x) (_hdiag : ∀ x, w x x = 0),
    ∃ c : α → Fin q, ∀ x,
      (q : ℤ)*classDegree w c x (c x) ≤ ∑ y, w x y)

#check (exists_large_part : ∀ {q : ℕ} (_hq : 0 < q) (c : α → Fin q),
    ∃ i : Fin q, Fintype.card α ≤ q*(univ.filter (fun x => c x = i)).card ∧
      (Fintype.card α+q-1)/q ≤ (univ.filter (fun x => c x = i)).card)

#check (exists_bounded_partition : ∀ {q : ℕ} (_hq : 0 < q) (w : α → α → ℤ)
    (_hsym : ∀ x y, w x y = w y x) (_hdiag : ∀ x, w x x = 0)
    (D : ℤ) (_hdegree : ∀ x, ∑ y, w x y ≤ D),
    ∃ c : α → Fin q,
      (∀ x, classDegree w c x (c x) ≤ D/(q : ℤ)) ∧
      ∃ i : Fin q, Fintype.card α ≤ q*(univ.filter (fun x => c x = i)).card ∧
        (Fintype.card α+q-1)/q ≤ (univ.filter (fun x => c x = i)).card)

end GraphContracts

#check (exists_large_subset : ∀ {β : Type u} [DecidableEq β] (V : Finset β)
    {q : ℕ} (_hq : 0 < q) (w : β → β → ℤ)
    (_hsym : ∀ x ∈ V, ∀ y ∈ V, w x y = w y x)
    (_hdiag : ∀ x ∈ V, w x x = 0)
    (D : ℤ) (_hdegree : ∀ x ∈ V, ∑ y ∈ V, w x y ≤ D),
    ∃ T ⊆ V, V.card ≤ q*T.card ∧
      ∀ x ∈ T, ∑ y ∈ T, w x y ≤ D/(q : ℤ))

section CoveringContracts
variable {α : Type u} [Fintype α] [DecidableEq α]

#check (minimum_pair_excess_zero : ∀ {C : Family α} {k b₂ b₃ b₄ : ℕ}
    (_hu : Uniform C k)
    (_h₃ : ∀ X : Finset α, X.card = 3 → b₃ ≤ multiplicity C X)
    (_h₄ : ∀ X : Finset α, X.card = 4 → b₄ ≤ multiplicity C X)
    (_hd : defect (Fintype.card α) k b₂ b₃ b₄ = 0)
    {X Y : Finset α} (_hX : X.card = 2) (_hm : multiplicity C X = b₂)
    (_hY : Y.card = 2), excess C b₃ b₄ X Y = 0)

#check (zero_defect_rank_bound : ∀ {C : Family α} {k b₂ b₃ b₄ q : ℕ}
    (_hu : Uniform C k) (_h₄₃ : b₄ ≤ b₃)
    (_h₃ : ∀ X : Finset α, X.card = 3 → b₃ ≤ multiplicity C X)
    (_h₄ : ∀ X : Finset α, X.card = 4 → b₄ ≤ multiplicity C X)
    (_hd : defect (Fintype.card α) k b₂ b₃ b₄ = 0)
    (_ha : 0 < diagonal b₂ b₃ b₄) (_hq : 0 < q)
    (_hpart : ((k.choose 2 : ℤ)-1)/(q : ℤ) < diagonal b₂ b₃ b₄+1),
    q*(minimumPairs C b₂).card + (nextPairs C b₂).card ≤ q*C.card)

#check (C17_9_5.counting_bound : ∀ {C : Family α},
    Fintype.card α = 17 → IsCover C 9 5 → (15368 : ℤ) ≤ 260*C.card)

#check (C17_9_5.lower_bound : ∀ {C : Family α},
    Fintype.card α = 17 → IsCover C 9 5 → 60 ≤ C.card)

end CoveringContracts

#check (two_level_count : ∀ {ι : Type u} (S : Finset ι) (u : ι → ℕ)
    {m K b q : ℕ} (_hq : 2 ≤ q)
    (_hl : ∀ x ∈ S, m ≤ u x) (_hs : ∑ x ∈ S, u x = K*b)
    (_hr : q*(S.filter (fun x => u x = m)).card +
      (S.filter (fun x => u x = m+1)).card ≤ q*b),
    (((q : ℤ)-1)*m+q)*S.card ≤ (((q : ℤ)-1)*K+q)*b)

namespace CoveringDesigns.Audit17_9_5

/-- The exact covering statement, with both uniformity and coverage expanded. -/
theorem lower_bound_explicit {α : Type u} [Fintype α] [DecidableEq α]
    {C : Finset (Finset α)} (hn : Fintype.card α = 17)
    (hsize : ∀ B ∈ C, B.card = 9)
    (hcover : ∀ T : Finset α, T.card = 5 → ∃ B ∈ C, T ⊆ B) :
    60 ≤ C.card := C17_9_5.lower_bound hn ⟨hsize, hcover⟩

/-- The requested nonnegative-weight formulation follows from the stronger
signed-weight balance theorem; no sign hypothesis is lost in the application. -/
theorem nonnegative_partition {α : Type u} [Fintype α] {q : ℕ}
    (hq : 0 < q) (w : α → α → ℤ) (_hnonneg : ∀ x y, 0 ≤ w x y)
    (hsym : ∀ x y, w x y = w y x) (hdiag : ∀ x, w x x = 0) :
    ∃ c : α → Fin q, ∀ x,
      (q : ℤ)*classDegree w c x (c x) ≤ ∑ y, w x y :=
  exists_balanced_partition hq w hsym hdiag

theorem empty_vertices {q : ℕ} (hq : 0 < q) :
    ∃ c : Fin 0 → Fin q, ∀ x,
      (q : ℤ)*classDegree (fun _ _ => 0) c x (c x) ≤ 0 := by
  obtain ⟨c, hc⟩ := exists_balanced_partition (α := Fin 0) hq (fun _ _ => 0)
    (fun _ _ => rfl) (fun _ => rfl)
  exact ⟨c, fun x => by simpa only [sum_const_zero] using hc x⟩

theorem empty_subset {q : ℕ} (hq : 0 < q) :
    ∃ T ⊆ (∅ : Finset ℕ), 0 ≤ q*T.card ∧
      ∀ x ∈ T, ∑ _y ∈ T, (0 : ℤ) ≤ 0/(q : ℤ) := by
  obtain ⟨T, hT, hc, hw⟩ := exists_large_subset (∅ : Finset ℕ) hq (fun _ _ => 0)
    (fun _ _ _ _ => rfl) (fun _ _ => rfl) 0 (by simp)
  exact ⟨T, hT, by simpa only [card_empty] using hc, hw⟩

theorem zero_weights {α : Type u} [Fintype α] {q : ℕ} (hq : 0 < q) :
    ∃ c : α → Fin q, (∀ x, classDegree (fun _ _ => 0) c x (c x) ≤ 0) ∧
      ∃ i : Fin q, Fintype.card α ≤ q*(univ.filter (fun x => c x = i)).card ∧
        (Fintype.card α+q-1)/q ≤ (univ.filter (fun x => c x = i)).card := by
  simpa using exists_bounded_partition (α := α) hq (fun _ _ => 0)
    (by intros; rfl) (by intros; rfl) 0 (by simp)

theorem one_part {α : Type u} [Fintype α] (w : α → α → ℤ)
    (hsym : ∀ x y, w x y = w y x) (hdiag : ∀ x, w x x = 0) :
    ∃ c : α → Fin 1, ∀ x, classDegree w c x (c x) ≤ ∑ y, w x y := by
  simpa using exists_balanced_partition (by decide : 0 < 1) w hsym hdiag

theorem empty_part :
    ((univ : Finset (Fin 2)).filter (fun _ => (0 : Fin 5) = 1)) = ∅ := by simp

end CoveringDesigns.Audit17_9_5

#guard_standard_axioms CoveringDesigns.WeightedPartition.potential_update
  CoveringDesigns.WeightedPartition.exists_balanced_partition
  CoveringDesigns.WeightedPartition.exists_large_part
  CoveringDesigns.WeightedPartition.exists_bounded_partition
  CoveringDesigns.WeightedPartition.exists_large_subset
  CoveringDesigns.Applications.ZeroDefect.minimum_pair_excess_zero
  CoveringDesigns.Applications.ZeroDefect.zero_defect_rank_bound
  CoveringDesigns.Applications.ZeroDefect.two_level_count
  CoveringDesigns.C17_9_5.counting_bound CoveringDesigns.C17_9_5.lower_bound
  CoveringDesigns.Audit17_9_5.lower_bound_explicit
  CoveringDesigns.Audit17_9_5.nonnegative_partition
  CoveringDesigns.Audit17_9_5.empty_vertices
  CoveringDesigns.Audit17_9_5.empty_subset
  CoveringDesigns.Audit17_9_5.zero_weights
  CoveringDesigns.Audit17_9_5.one_part
  CoveringDesigns.Audit17_9_5.empty_part

#print axioms CoveringDesigns.WeightedPartition.potential_update
#print axioms CoveringDesigns.WeightedPartition.exists_balanced_partition
#print axioms CoveringDesigns.WeightedPartition.exists_large_part
#print axioms CoveringDesigns.WeightedPartition.exists_bounded_partition
#print axioms CoveringDesigns.WeightedPartition.exists_large_subset
#print axioms CoveringDesigns.Applications.ZeroDefect.minimum_pair_excess_zero
#print axioms CoveringDesigns.Applications.ZeroDefect.zero_defect_rank_bound
#print axioms CoveringDesigns.Applications.ZeroDefect.two_level_count
#print axioms CoveringDesigns.C17_9_5.counting_bound
#print axioms CoveringDesigns.C17_9_5.lower_bound
#print axioms CoveringDesigns.Audit17_9_5.lower_bound_explicit
#print axioms CoveringDesigns.Audit17_9_5.nonnegative_partition
#print axioms CoveringDesigns.Audit17_9_5.empty_vertices
#print axioms CoveringDesigns.Audit17_9_5.empty_subset
#print axioms CoveringDesigns.Audit17_9_5.zero_weights
#print axioms CoveringDesigns.Audit17_9_5.one_part
#print axioms CoveringDesigns.Audit17_9_5.empty_part
