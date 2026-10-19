import CoveringDesigns.TwoKMinusCGeneral

open CoveringDesigns CoveringDesigns.TwoKMinusCGeneral
open Finset Matrix
set_option linter.unusedVariables false

#print CoveringDesigns.Family
#print CoveringDesigns.Uniform
#print CoveringDesigns.Covers
#print CoveringDesigns.IsCover
#print CoveringDesigns.degree
#print CoveringDesigns.star
#print CoveringDesigns.C20_11_3.onlyBlocks
#print CoveringDesigns.TwoKMinusTwo.capacity
#print CoveringDesigns.TwoKMinusCGeneral.integerExcess

namespace CoveringDesigns.AuditTwoKMinusCGeneral

theorem uniform_explicit {α : Type*} [Fintype α] {c k : ℕ}
    (hv : Fintype.card α=2*k-c) (hc : 2≤c) (hk : 25*c≤k) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card=k) ∧
      (∀ T : Finset α, T.card=3 → ∃ B ∈ C, T⊆B) ∧ C.card=14) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card=k) →
      (∀ T : Finset α, T.card=3 → ∃ B ∈ C, T⊆B) → 14≤C.card) := by
  obtain ⟨⟨C,hC,hb⟩,hl⟩ := exactness_uniform hv hc hk
  exact ⟨⟨C,hC.1,hC.2,hb⟩,fun C hu ht => hl C ⟨hu,ht⟩⟩

theorem three_explicit {α : Type*} [Fintype α] {k : ℕ}
    (hv : Fintype.card α=2*k-3) (hk : 59≤k) :
    (∃ C : Finset (Finset α), (∀ B ∈ C, B.card=k) ∧
      (∀ T : Finset α, T.card=3 → ∃ B ∈ C, T⊆B) ∧ C.card=14) ∧
    (∀ C : Finset (Finset α), (∀ B ∈ C, B.card=k) →
      (∀ T : Finset α, T.card=3 → ∃ B ∈ C, T⊆B) → 14≤C.card) := by
  obtain ⟨⟨C,hC,hb⟩,hl⟩ := exactness_offset_three hv hk
  exact ⟨⟨C,hC.1,hC.2,hb⟩,fun C hu ht => hl C ⟨hu,ht⟩⟩

theorem floors_rank_explicit {α : Type*} [Fintype α] [DecidableEq α]
    {c k : ℕ} (C : Finset (Finset α)) (hv : Fintype.card α+c=2*k) (hc : 2≤c)
    (hu : ∀ B ∈ C, B.card=k) (hp : ∀ x, 6≤(C.filter (fun B => x∈B)).card)
    (hpq : ∀ x y, x≠y → 3≤(C.filter (fun B => x∈B ∧ y∈B)).card) :
    7*Fintype.card α≤(k+c)*C.card := by
  apply conditional_rank hv hc hu hp
  intro x y hxy
  simpa only [degree,star,filter_filter] using hpq x y hxy

/-- Target labels may inhabit a different universe; image deduplication is allowed. -/
theorem reduction_transport {α : Type u} {β : Type v}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {C : Finset (Finset α)} {k t : ℕ}
    (hu : ∀ B ∈ C, B.card=k) (ht : ∀ T : Finset α, T.card=t → ∃ B ∈ C, T⊆B)
    (hk : k≤Fintype.card β) (hv : Fintype.card β≤Fintype.card α) :
    ∃ D : Finset (Finset β), (∀ B ∈ D, B.card=k) ∧
      (∀ T : Finset β, T.card=t → ∃ B ∈ D, T⊆B) ∧ D.card≤C.card := by
  obtain ⟨D,hD,hb⟩ := PointReduction.family_reduce_points ⟨hu,ht⟩ hk hv
  exact ⟨D,hD.1,hD.2,hb⟩

end CoveringDesigns.AuditTwoKMinusCGeneral

-- Kernel-checked boundary checks. Adjacent failure is not an existence assertion.
example : TwoKMinusC.Q 3 58=22939/1765 := by
  norm_num [TwoKMinusC.Q,TwoKMinusC.numerator,TwoKMinusC.denominator,TwoKMinusC.offsetDefect]
example : TwoKMinusC.Q 3 58<13 := by
  norm_num [TwoKMinusC.Q,TwoKMinusC.numerator,TwoKMinusC.denominator,TwoKMinusC.offsetDefect]
example : TwoKMinusC.Q 3 59-13=103/7299 := by
  norm_num [TwoKMinusC.Q,TwoKMinusC.numerator,TwoKMinusC.denominator,TwoKMinusC.offsetDefect]
example : 3*(56-3)*(56-3)+8*(56/2) < 11*TwoKMinusTwo.capacity 56+32 := by decide
example : 11*TwoKMinusTwo.capacity 57+32 < 3*(57-3)*(57-3)+8*(57/2) := by decide
example : 11*TwoKMinusTwo.capacity 58+32 < 3*(58-3)*(58-3)+8*(58/2) := by decide
example : 3*TwoKMinusTwo.capacity (17-1) < (17-3)*(17-3) :=
  link_capacity_strict (c := 3) (k := 17) (by decide) (by decide)

-- The reusable rank helper admits empty row and column types with zero weights.
example : Fintype.card (Fin 0) ≤ 2*Fintype.card (Fin 0) := by
  apply Weighted.partitioned_gram_card_le (R := (0 : Matrix (Fin 0) (Fin 0) ℝ))
    (w := fun _ _ => 0) (P := 0) (ρ := 3) (D := 0) (by decide) (by norm_num)
    (by intros; rfl) (by intros; norm_num) (by intros; rfl)
    (by intro x; exact Fin.elim0 x) (by norm_num) (Matrix.PosSemidef.zero)
  ext x
  exact Fin.elim0 x

example : (∃ C : Family (Fin 98), IsCover C 50 3 ∧ C.card=14) ∧
    (∀ C : Family (Fin 98), IsCover C 50 3 → 14≤C.card) := exactness_98_50_3_on (by simp)
example : (∃ C : Family (Fin 196), IsCover C 100 3 ∧ C.card=14) ∧
    (∀ C : Family (Fin 196), IsCover C 100 3 → 14≤C.card) := exactness_196_100_3_on (by simp)
example : (∃ C : Family (Fin 115), IsCover C 59 3 ∧ C.card=14) ∧
    (∀ C : Family (Fin 115), IsCover C 59 3 → 14≤C.card) := exactness_115_59_3_on (by simp)

-- Complete public contracts, including actual-family and arbitrary-label types.
universe u_1 u_2

#check (@CoveringDesigns.Weighted.partitioned_gram_card_le : ∀ {ι : Type u_1} {κ : Type u_2} [inst : Fintype ι]
  [inst_1 : DecidableEq ι] [inst_2 : Fintype κ] (R : Matrix ι κ ℝ) (w : ι → ι → ℤ) (P : Matrix ι ι ℝ) {q : ℕ},
  0 < q →
    ∀ {ρ : ℝ},
      0 < ρ →
        ∀ {D : ℤ},
          (∀ (x y : ι), w x y = w y x) →
            (∀ (x y : ι), 0 ≤ w x y) →
              (∀ (x : ι), w x x = 0) →
                (∀ (x : ι), ∑ y, w x y ≤ D) →
                  ↑D < ↑q * ρ →
                    P.PosSemidef →
                      R * R.transpose = ((Matrix.diagonal fun x => ρ) + Matrix.of fun x y => ↑(w x y)) + P →
                        Fintype.card ι ≤ q * Fintype.card κ)

#check (@CoveringDesigns.TwoKMinusCGeneral.link_capacity_strict : ∀ {c k : ℕ},
  2 ≤ c → 8 * c ≤ k + 7 → 3 * CoveringDesigns.TwoKMinusTwo.capacity (k - 1) < (k - c) * (k - c))

#check (@CoveringDesigns.TwoKMinusCGeneral.capacity_uniform_impossible : ∀ {c k : ℕ},
  2 ≤ c →
    25 * c ≤ k →
      3 * (k - c) * (k - c) ≤
          11 * CoveringDesigns.TwoKMinusTwo.capacity k + 30 * CoveringDesigns.TwoKMinusTwo.capacity c →
        False)

#check (@CoveringDesigns.TwoKMinusCGeneral.endpoint_budget_three : ∀ {u w r : ℕ},
  4 ≤ u → 4 ≤ w → u + w ≤ 11 → 28 ≤ r → 2 * u * w + 8 * r ≤ r * (u + w) + 32)

#check (@CoveringDesigns.TwoKMinusCGeneral.capacity_three_impossible : ∀ {k : ℕ},
  57 ≤ k → 3 * (k - 3) * (k - 3) + 8 * (k / 2) ≤ 11 * CoveringDesigns.TwoKMinusTwo.capacity k + 32 → False)

#check (@CoveringDesigns.TwoKMinusCGeneral.exists_cross_assignment : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {c k : ℕ} {C : CoveringDesigns.Family α} {p q : α} {B D : Finset α},
  Fintype.card α + c = 2 * k →
    CoveringDesigns.IsCover C k 3 →
      CoveringDesigns.star (CoveringDesigns.star C p) q = {B, D} →
        have T := {z ∈ (B \ D) ×ˢ (D \ B) | CoveringDesigns.degree (CoveringDesigns.star C z.1) z.2 = 2};
        ∃ f : α × α → Finset α × Finset α,
          (∀ z ∈ T,
              (f z).1 ∈ CoveringDesigns.C20_11_3.onlyBlocks C p q ∧
                (f z).2 ∈ CoveringDesigns.C20_11_3.onlyBlocks C q p ∧
                  CoveringDesigns.star (CoveringDesigns.star C z.1) z.2 = {(f z).1, (f z).2} ∧
                    ((f z).1 ∩ (f z).2).card = c ∧ {z.1, z.2} ⊆ (f z).1 ∩ (f z).2) ∧
            ∀ (a : Finset α × Finset α), {z ∈ T | f z = a}.card ≤ CoveringDesigns.TwoKMinusTwo.capacity c)

#check (@CoveringDesigns.TwoKMinusCGeneral.saturated_cross_card_le : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {c k : ℕ} {C : CoveringDesigns.Family α} {p q : α} {B D : Finset α},
  Fintype.card α + c = 2 * k →
    CoveringDesigns.IsCover C k 3 →
      CoveringDesigns.star (CoveringDesigns.star C p) q = {B, D} →
        {z ∈ (B \ D) ×ˢ (D \ B) | CoveringDesigns.degree (CoveringDesigns.star C z.1) z.2 = 2}.card ≤
          CoveringDesigns.TwoKMinusTwo.capacity c * Finset.card (CoveringDesigns.C20_11_3.onlyBlocks C p q) *
            Finset.card (CoveringDesigns.C20_11_3.onlyBlocks C q p))

#check (@CoveringDesigns.TwoKMinusCGeneral.upper_bound : ∀ {α : Type u_1} [inst : Fintype α] {c k : ℕ},
  Fintype.card α + c = 2 * k → 2 ≤ c → c ≤ k → 3 ≤ k → ∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 3 ∧ Finset.card C ≤ 14)

#check (@CoveringDesigns.TwoKMinusCGeneral.endpoint_trace_capacity : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α] {k : ℕ}
  {p : α} {X Y B : Finset α},
  Disjoint X Y →
    p ∉ X ∪ Y → B.card = k → p ∈ B → (X ∩ B).card * (Y ∩ B).card ≤ CoveringDesigns.TwoKMinusTwo.capacity (k - 1))

#check (@CoveringDesigns.TwoKMinusCGeneral.saturated_capacity : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {c k : ℕ} {C : CoveringDesigns.Family α},
  Fintype.card α + c = 2 * k →
    2 ≤ c →
      c < k →
        CoveringDesigns.IsCover C k 3 →
          ∀ {p q : α},
            p ≠ q →
              CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 →
                3 * (k - c) * (k - c) +
                    k / 2 *
                      (Finset.card (CoveringDesigns.C20_11_3.onlyBlocks C p q) +
                        Finset.card (CoveringDesigns.C20_11_3.onlyBlocks C q p)) ≤
                  (Finset.card C - 2) * CoveringDesigns.TwoKMinusTwo.capacity k +
                    CoveringDesigns.TwoKMinusTwo.capacity c * Finset.card (CoveringDesigns.C20_11_3.onlyBlocks C p q) *
                      Finset.card (CoveringDesigns.C20_11_3.onlyBlocks C q p))

#check (@CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_uniform : ∀ {α : Type u_1} [inst : Fintype α] {c k : ℕ},
  Fintype.card α = 2 * k - c → 2 ≤ c → 25 * c ≤ k → ∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14)

#check (@CoveringDesigns.TwoKMinusCGeneral.exactness_uniform : ∀ {α : Type u_1} [inst : Fintype α] {c k : ℕ},
  Fintype.card α = 2 * k - c →
    2 ≤ c →
      25 * c ≤ k →
        (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14) ∧
          ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)

#check (@CoveringDesigns.TwoKMinusCGeneral.covering_number_uniform : ∀ {c k : ℕ},
  2 ≤ c →
    25 * c ≤ k →
      (∃ C : CoveringDesigns.Family (Fin (2*k-c)), CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14) ∧
        ∀ (C : CoveringDesigns.Family (Fin (2 * k - c))), CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)

#check (@CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_offset_three : ∀ {α : Type u_1} [inst : Fintype α] {k : ℕ},
  Fintype.card α = 2 * k - 3 → 59 ≤ k → ∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14)

#check (@CoveringDesigns.TwoKMinusCGeneral.exactness_offset_three : ∀ {α : Type u_1} [inst : Fintype α] {k : ℕ},
  Fintype.card α = 2 * k - 3 →
    59 ≤ k →
      (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14) ∧
        ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)

#check (@CoveringDesigns.TwoKMinusCGeneral.covering_number_offset_three : ∀ {k : ℕ},
  59 ≤ k →
    (∃ C : CoveringDesigns.Family (Fin (2*k-3)), CoveringDesigns.IsCover C k 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family (Fin (2 * k - 3))), CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)

#check (@CoveringDesigns.TwoKMinusCGeneral.exactness_98_50_3_on : ∀ {α : Type u_1} [inst : Fintype α],
  Fintype.card α = 98 →
    (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 50 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 50 3 → 14 ≤ Finset.card C)

#check (@CoveringDesigns.TwoKMinusCGeneral.exactness_196_100_3_on : ∀ {α : Type u_1} [inst : Fintype α],
  Fintype.card α = 196 →
    (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 100 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 100 3 → 14 ≤ Finset.card C)

#check (@CoveringDesigns.TwoKMinusCGeneral.exactness_115_59_3_on : ∀ {α : Type u_1} [inst : Fintype α],
  Fintype.card α = 115 →
    (∃ C : CoveringDesigns.Family α, CoveringDesigns.IsCover C 59 3 ∧ Finset.card C = 14) ∧
      ∀ (C : CoveringDesigns.Family α), CoveringDesigns.IsCover C 59 3 → 14 ≤ Finset.card C)

#check (@CoveringDesigns.TwoKMinusCGeneral.saturated_pair_inter_card : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {c k : ℕ} {C : CoveringDesigns.Family α} {p q : α} {B D : Finset α},
  Fintype.card α + c = 2 * k →
    CoveringDesigns.IsCover C k 3 →
      p ≠ q → CoveringDesigns.star (CoveringDesigns.star C p) q = {B, D} → (B ∩ D).card = c)

#check (@CoveringDesigns.TwoKMinusCGeneral.saturated_pair_blocks : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {c k : ℕ} {C : CoveringDesigns.Family α} {p q : α},
  Fintype.card α + c = 2 * k →
    CoveringDesigns.IsCover C k 3 →
      p ≠ q →
        CoveringDesigns.degree (CoveringDesigns.star C p) q = 2 →
          ∃ B ∈ C,
            ∃ D ∈ C,
              B ≠ D ∧
                CoveringDesigns.star (CoveringDesigns.star C p) q = {B, D} ∧
                  B ∪ D = Finset.univ ∧ (B ∩ D).card = c ∧ (B \ D).card = k - c ∧ (D \ B).card = k - c)

#check (@CoveringDesigns.TwoKMinusCGeneral.oriented_blocks_unique : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  {C : CoveringDesigns.Family α} {p q x y : α} {A E A' E' : Finset α},
  A ∈ CoveringDesigns.C20_11_3.onlyBlocks C p q →
    E ∈ CoveringDesigns.C20_11_3.onlyBlocks C q p →
      A' ∈ CoveringDesigns.C20_11_3.onlyBlocks C p q →
        E' ∈ CoveringDesigns.C20_11_3.onlyBlocks C q p →
          CoveringDesigns.star (CoveringDesigns.star C x) y = {A, E} →
            CoveringDesigns.star (CoveringDesigns.star C x) y = {A', E'} → A = A' ∧ E = E')

#check (@CoveringDesigns.TwoKMinusCGeneral.cross_partner_exists : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {c k : ℕ} {C : CoveringDesigns.Family α} {p q x y : α} {B D : Finset α},
  Fintype.card α + c = 2 * k →
    CoveringDesigns.IsCover C k 3 →
      CoveringDesigns.star (CoveringDesigns.star C p) q = {B, D} →
        x ∈ B \ D →
          y ∈ D \ B →
            CoveringDesigns.degree (CoveringDesigns.star C x) y = 2 →
              ∃ A ∈ CoveringDesigns.C20_11_3.onlyBlocks C p q,
                ∃ E ∈ CoveringDesigns.C20_11_3.onlyBlocks C q p,
                  CoveringDesigns.star (CoveringDesigns.star C x) y = {A, E} ∧ (A ∩ E).card = c ∧ {x, y} ⊆ A ∩ E)

#check (@CoveringDesigns.TwoKMinusCGeneral.link_lower_bound : ∀ {α : Type u_1} [inst : Fintype α] [DecidableEq α] {c k : ℕ}
  {C : CoveringDesigns.Family α},
  Fintype.card α + c + 1 = 2 * k → 2 ≤ c → 8 * c ≤ k + 7 → CoveringDesigns.IsCover C (k - 1) 2 → 6 ≤ Finset.card C)

#check (@CoveringDesigns.TwoKMinusCGeneral.degree_ge_six : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {c k : ℕ} {C : CoveringDesigns.Family α},
  Fintype.card α + c = 2 * k →
    2 ≤ c → 8 * c ≤ k + 7 → CoveringDesigns.IsCover C k 3 → ∀ (p : α), 6 ≤ CoveringDesigns.degree C p)

#check (@CoveringDesigns.TwoKMinusCGeneral.pair_ge_two : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {c k : ℕ}
  {C : CoveringDesigns.Family α},
  Fintype.card α + c = 2 * k →
    2 ≤ c →
      c < k →
        CoveringDesigns.IsCover C k 3 → ∀ {p q : α}, p ≠ q → 2 ≤ CoveringDesigns.degree (CoveringDesigns.star C p) q)

#check (@CoveringDesigns.TwoKMinusCGeneral.Q_three : ∀ (k : ℕ),
  CoveringDesigns.TwoKMinusC.Q 3 k = 14 * ↑k * (2 * ↑k - 3) / (2 * ↑k ^ 2 + 5 * ↑k + 42))

#check (@CoveringDesigns.TwoKMinusCGeneral.thirteen_lt_Q_three : ∀ {k : ℕ}, 59 ≤ k → 13 < CoveringDesigns.TwoKMinusC.Q 3 k)

#check (@CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_offset_three : ∀ {α : Type u_1} [inst : Fintype α] {k : ℕ}
  {C : CoveringDesigns.Family α},
  Fintype.card α = 2 * k - 3 → 59 ≤ k → CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)

#check (@CoveringDesigns.TwoKMinusCGeneral.integerExcess_cast : ∀ {α : Type u_1} [inst : DecidableEq α]
  (C : CoveringDesigns.Family α) (x y : α),
  ↑(CoveringDesigns.TwoKMinusCGeneral.integerExcess C x y) = CoveringDesigns.TwoKMinusTwo.excess C x y)

#check (@CoveringDesigns.TwoKMinusCGeneral.integerExcess_nonneg : ∀ {α : Type u_1} [Fintype α] [inst : DecidableEq α]
  {C : CoveringDesigns.Family α},
  (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
    ∀ (x y : α), 0 ≤ CoveringDesigns.TwoKMinusCGeneral.integerExcess C x y)

#check (@CoveringDesigns.TwoKMinusCGeneral.low_row_le : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {c k : ℕ}
  {C : CoveringDesigns.Family α},
  Fintype.card α + c = 2 * k →
    CoveringDesigns.Uniform C k →
      (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
        ∀ (x : CoveringDesigns.TwoKMinusTwo.Low C),
          ∑ y : CoveringDesigns.TwoKMinusTwo.Low C, CoveringDesigns.TwoKMinusCGeneral.integerExcess C ↑x ↑y ≤ 3 * (↑c - 1))

#check (@CoveringDesigns.TwoKMinusCGeneral.low_card_le : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {c k : ℕ}
  {C : CoveringDesigns.Family α},
  Fintype.card α + c = 2 * k →
    2 ≤ c →
      CoveringDesigns.Uniform C k →
        (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
          (CoveringDesigns.minimumPoints C 6).card ≤ c * Finset.card C)

#check (@CoveringDesigns.TwoKMinusCGeneral.conditional_rank : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {c k : ℕ} {C : CoveringDesigns.Family α},
  Fintype.card α + c = 2 * k →
    2 ≤ c →
      CoveringDesigns.Uniform C k →
        (∀ (x : α), 6 ≤ CoveringDesigns.degree C x) →
          (∀ (x y : α), x ≠ y → 3 ≤ CoveringDesigns.degree (CoveringDesigns.star C x) y) →
            7 * Fintype.card α ≤ (k + c) * Finset.card C)

#check (@CoveringDesigns.TwoKMinusCGeneral.no_saturation_uniform : ∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α]
  {c k : ℕ} {C : CoveringDesigns.Family α},
  Fintype.card α + c = 2 * k →
    2 ≤ c →
      25 * c ≤ k →
        CoveringDesigns.IsCover C k 3 →
          Finset.card C ≤ 13 → ∀ {p q : α}, p ≠ q → CoveringDesigns.degree (CoveringDesigns.star C p) q ≠ 2)

#check (@CoveringDesigns.TwoKMinusCGeneral.no_saturation_offset_three : ∀ {α : Type u_1} [inst : Fintype α]
  [inst_1 : DecidableEq α] {k : ℕ} {C : CoveringDesigns.Family α},
  Fintype.card α + 3 = 2 * k →
    57 ≤ k →
      CoveringDesigns.IsCover C k 3 →
        Finset.card C ≤ 13 → ∀ {p q : α}, p ≠ q → CoveringDesigns.degree (CoveringDesigns.star C p) q ≠ 2)

#check (@CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_uniform : ∀ {α : Type u_1} [inst : Fintype α] {c k : ℕ}
  {C : CoveringDesigns.Family α},
  Fintype.card α = 2 * k - c → 2 ≤ c → 25 * c ≤ k → CoveringDesigns.IsCover C k 3 → 14 ≤ Finset.card C)

#guard_standard_axioms CoveringDesigns.Weighted.partitioned_gram_card_le
#print axioms CoveringDesigns.Weighted.partitioned_gram_card_le
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.link_capacity_strict
#print axioms CoveringDesigns.TwoKMinusCGeneral.link_capacity_strict
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.capacity_uniform_impossible
#print axioms CoveringDesigns.TwoKMinusCGeneral.capacity_uniform_impossible
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.endpoint_budget_three
#print axioms CoveringDesigns.TwoKMinusCGeneral.endpoint_budget_three
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.capacity_three_impossible
#print axioms CoveringDesigns.TwoKMinusCGeneral.capacity_three_impossible
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exists_cross_assignment
#print axioms CoveringDesigns.TwoKMinusCGeneral.exists_cross_assignment
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.saturated_cross_card_le
#print axioms CoveringDesigns.TwoKMinusCGeneral.saturated_cross_card_le
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.upper_bound
#print axioms CoveringDesigns.TwoKMinusCGeneral.upper_bound
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.endpoint_trace_capacity
#print axioms CoveringDesigns.TwoKMinusCGeneral.endpoint_trace_capacity
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.saturated_capacity
#print axioms CoveringDesigns.TwoKMinusCGeneral.saturated_capacity
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_uniform
#print axioms CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_uniform
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exactness_uniform
#print axioms CoveringDesigns.TwoKMinusCGeneral.exactness_uniform
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.covering_number_uniform
#print axioms CoveringDesigns.TwoKMinusCGeneral.covering_number_uniform
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_offset_three
#print axioms CoveringDesigns.TwoKMinusCGeneral.exists_fourteen_offset_three
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exactness_offset_three
#print axioms CoveringDesigns.TwoKMinusCGeneral.exactness_offset_three
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.covering_number_offset_three
#print axioms CoveringDesigns.TwoKMinusCGeneral.covering_number_offset_three
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exactness_98_50_3_on
#print axioms CoveringDesigns.TwoKMinusCGeneral.exactness_98_50_3_on
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exactness_196_100_3_on
#print axioms CoveringDesigns.TwoKMinusCGeneral.exactness_196_100_3_on
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.exactness_115_59_3_on
#print axioms CoveringDesigns.TwoKMinusCGeneral.exactness_115_59_3_on
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.saturated_pair_inter_card
#print axioms CoveringDesigns.TwoKMinusCGeneral.saturated_pair_inter_card
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.saturated_pair_blocks
#print axioms CoveringDesigns.TwoKMinusCGeneral.saturated_pair_blocks
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.oriented_blocks_unique
#print axioms CoveringDesigns.TwoKMinusCGeneral.oriented_blocks_unique
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.cross_partner_exists
#print axioms CoveringDesigns.TwoKMinusCGeneral.cross_partner_exists
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.link_lower_bound
#print axioms CoveringDesigns.TwoKMinusCGeneral.link_lower_bound
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.degree_ge_six
#print axioms CoveringDesigns.TwoKMinusCGeneral.degree_ge_six
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.pair_ge_two
#print axioms CoveringDesigns.TwoKMinusCGeneral.pair_ge_two
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.Q_three
#print axioms CoveringDesigns.TwoKMinusCGeneral.Q_three
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.thirteen_lt_Q_three
#print axioms CoveringDesigns.TwoKMinusCGeneral.thirteen_lt_Q_three
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_offset_three
#print axioms CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_offset_three
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.integerExcess_cast
#print axioms CoveringDesigns.TwoKMinusCGeneral.integerExcess_cast
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.integerExcess_nonneg
#print axioms CoveringDesigns.TwoKMinusCGeneral.integerExcess_nonneg
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.low_row_le
#print axioms CoveringDesigns.TwoKMinusCGeneral.low_row_le
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.low_card_le
#print axioms CoveringDesigns.TwoKMinusCGeneral.low_card_le
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.conditional_rank
#print axioms CoveringDesigns.TwoKMinusCGeneral.conditional_rank
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.no_saturation_uniform
#print axioms CoveringDesigns.TwoKMinusCGeneral.no_saturation_uniform
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.no_saturation_offset_three
#print axioms CoveringDesigns.TwoKMinusCGeneral.no_saturation_offset_three
#guard_standard_axioms CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_uniform
#print axioms CoveringDesigns.TwoKMinusCGeneral.fourteen_le_card_uniform
#guard_standard_axioms CoveringDesigns.AuditTwoKMinusCGeneral.uniform_explicit
#print axioms CoveringDesigns.AuditTwoKMinusCGeneral.uniform_explicit
#guard_standard_axioms CoveringDesigns.AuditTwoKMinusCGeneral.three_explicit
#print axioms CoveringDesigns.AuditTwoKMinusCGeneral.three_explicit
#guard_standard_axioms CoveringDesigns.AuditTwoKMinusCGeneral.floors_rank_explicit
#print axioms CoveringDesigns.AuditTwoKMinusCGeneral.floors_rank_explicit
#guard_standard_axioms CoveringDesigns.AuditTwoKMinusCGeneral.reduction_transport
#print axioms CoveringDesigns.AuditTwoKMinusCGeneral.reduction_transport
