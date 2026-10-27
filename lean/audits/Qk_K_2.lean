import CoveringDesigns.Qk_K_2
import CoveringDesigns.Foundations.StandardAxioms

namespace CoveringDesigns.AuditQk_K_2
open Finset Matrix PairEquality PairDivisibility TruncatedPlaneLoads TwistedArithmetic Qk_K_2
universe u

/-- Explicit actual-family contract, with no supplied geometry or arithmetic premise. -/
theorem exactness_explicit {α : Type*} [Fintype α] (hv : Fintype.card α = 90) :
    (∃ C : Finset (Finset α),
      (∀ B ∈ C, B.card = 10) ∧
      (∀ T : Finset α, T.card = 2 → ∃ B ∈ C, T ⊆ B) ∧ C.card = 91) ∧
    (∀ C : Finset (Finset α),
      (∀ B ∈ C, B.card = 10) →
      (∀ T : Finset α, T.card = 2 → ∃ B ∈ C, T ⊆ B) → 91 ≤ C.card) := by
  obtain ⟨⟨C,hC,hb⟩,hl⟩ := exact_90_10_2 hv
  exact ⟨⟨C,hC.1,hC.2,hb⟩,fun C hu hc => hl C ⟨hu,hc⟩⟩
#guard_standard_axioms exactness_explicit
#print axioms exactness_explicit

section
open CoveringDesigns.Qk_K_2
#check (@CoveringDesigns.Qk_K_2.indexed_open_floor :
∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : q*k < Fintype.card X) (hB : Multicover.IsCover B k 2 1),
  q*(q+1)+1 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.Qk_K_2.indexed_open_floor
#print axioms CoveringDesigns.Qk_K_2.indexed_open_floor

#check (@CoveringDesigns.Qk_K_2.open_floor :
∀ {X : Type*} [Fintype X] {C : Family X} {q k : ℕ}
    (hq : 4 ≤ q) (hk : q ≤ k) (hv : q*k < Fintype.card X)
    (hC : IsCover C k 2),
  q*(q+1)+1 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.open_floor
#print axioms CoveringDesigns.Qk_K_2.open_floor

end

section
open CoveringDesigns.Qk_K_2
#check (@CoveringDesigns.Qk_K_2.weighted_expanded :
∀ {α : Type*} [Fintype α] {q u r : ℕ}
    (hq : IsPrimePow q) (hq2 : 2 ≤ q) (hr : 1 ≤ r) (hru : r ≤ u)
    (hv : Fintype.card α = q*(q*u+r)+r),
  ∃ C : Family α, IsCover C (q*u+r) 2 ∧ C.card ≤ q*q+q+1)
#guard_standard_axioms CoveringDesigns.Qk_K_2.weighted_expanded
#print axioms CoveringDesigns.Qk_K_2.weighted_expanded

#check (@CoveringDesigns.Qk_K_2.weighted_interval :
∀ {α : Type*} [Fintype α] {q u r v : ℕ}
    (hq : IsPrimePow q) (hq2 : 2 ≤ q) (hr : 1 ≤ r) (hru : r ≤ u)
    (hv : Fintype.card α = v) (hlo : q*(q*u+r) ≤ v) (hhi : v ≤ q*(q*u+r)+r),
  ∃ C : Family α, IsCover C (q*u+r) 2 ∧ C.card ≤ q*q+q+1)
#guard_standard_axioms CoveringDesigns.Qk_K_2.weighted_interval
#print axioms CoveringDesigns.Qk_K_2.weighted_interval

end

section
open CoveringDesigns.Qk_K_2.DeHeerMuir
#check (@CoveringDesigns.Qk_K_2.DeHeerMuir.blocks :
List (Finset (Fin 95)))
#guard_standard_axioms CoveringDesigns.Qk_K_2.DeHeerMuir.blocks
#print axioms CoveringDesigns.Qk_K_2.DeHeerMuir.blocks

#check (@CoveringDesigns.Qk_K_2.DeHeerMuir.blocks_distinct :
blocks.Nodup)
#guard_standard_axioms CoveringDesigns.Qk_K_2.DeHeerMuir.blocks_distinct
#print axioms CoveringDesigns.Qk_K_2.DeHeerMuir.blocks_distinct

#check (@CoveringDesigns.Qk_K_2.DeHeerMuir.family :
Family (Fin 95))
#guard_standard_axioms CoveringDesigns.Qk_K_2.DeHeerMuir.family
#print axioms CoveringDesigns.Qk_K_2.DeHeerMuir.family

#check (@CoveringDesigns.Qk_K_2.DeHeerMuir.family_card :
family.card = 31)
#guard_standard_axioms CoveringDesigns.Qk_K_2.DeHeerMuir.family_card
#print axioms CoveringDesigns.Qk_K_2.DeHeerMuir.family_card

#check (@CoveringDesigns.Qk_K_2.DeHeerMuir.family_uniform :
Uniform family 19)
#guard_standard_axioms CoveringDesigns.Qk_K_2.DeHeerMuir.family_uniform
#print axioms CoveringDesigns.Qk_K_2.DeHeerMuir.family_uniform

#check (@CoveringDesigns.Qk_K_2.DeHeerMuir.family_covers :
Covers family 2)
#guard_standard_axioms CoveringDesigns.Qk_K_2.DeHeerMuir.family_covers
#print axioms CoveringDesigns.Qk_K_2.DeHeerMuir.family_covers

#check (@CoveringDesigns.Qk_K_2.DeHeerMuir.family_isCover :
IsCover family 19 2)
#guard_standard_axioms CoveringDesigns.Qk_K_2.DeHeerMuir.family_isCover
#print axioms CoveringDesigns.Qk_K_2.DeHeerMuir.family_isCover

#check (@CoveringDesigns.Qk_K_2.DeHeerMuir.attainment :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 95),
  ∃ C : Family α, IsCover C 19 2 ∧ C.card = 31)
#guard_standard_axioms CoveringDesigns.Qk_K_2.DeHeerMuir.attainment
#print axioms CoveringDesigns.Qk_K_2.DeHeerMuir.attainment

end

section
open CoveringDesigns.Qk_K_2
#check (@CoveringDesigns.Qk_K_2.twisted_determinant :
∀ {I : Type*} [Fintype I] [DecidableEq I] {H : Finset (Finset I)} {q : ℕ} (hq : 1 ≤ q) (T : IsTwistedPlane q H),
  (squareIncidence T).det ^ 2 =
      ((q-1 : ℕ) : ℤ)^(q*(q+1)/2) * (q+1 : ℕ)^(q*(q+1)/2+1))
#guard_standard_axioms CoveringDesigns.Qk_K_2.twisted_determinant
#print axioms CoveringDesigns.Qk_K_2.twisted_determinant

#check (@CoveringDesigns.Qk_K_2.exclude_twisted :
∀ {I : Type*} [Fintype I] [DecidableEq I] {H : Finset (Finset I)} {q : ℕ} (hq : 1 ≤ q)
    (hn : ∀ d : ℤ, d^2 ≠ ((q-1 : ℕ) : ℤ)^(q*(q+1)/2) * (q+1 : ℕ)^(q*(q+1)/2+1))
    (T : IsTwistedPlane q H),
  False)
#guard_standard_axioms CoveringDesigns.Qk_K_2.exclude_twisted
#print axioms CoveringDesigns.Qk_K_2.exclude_twisted

end

section
open CoveringDesigns.Qk_K_2
#check (@CoveringDesigns.Qk_K_2.twenty_description :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {t : ℕ} {B : I → Finset X}
    (ht : 1 ≤ t) (hv : Fintype.card X = 16*t) (hi : Fintype.card I = 20)
    (hB : Multicover.IsCover B (4*t) 2 1),
  ∃ P : Plane 4 I (Fin 5), P.core ⊆ occupied B ∧
      NatDescription P (occupied B) (multiplicity B) t ∧
      ∃ e : X ≃ Point (occupied B) (multiplicity B),
        (∀ p, (e p).1.val = support B p) ∧
        ∀ p i, e p ∈ block (occupied B) (multiplicity B) i ↔ p ∈ B i)
#guard_standard_axioms CoveringDesigns.Qk_K_2.twenty_description
#print axioms CoveringDesigns.Qk_K_2.twenty_description

#check (@CoveringDesigns.Qk_K_2.twenty_unit_pure :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 16) (hi : Fintype.card I = 20)
    (hB : Multicover.IsCover B 4 2 1),
  ∃ P : Plane 4 I (Fin 5), occupied B = P.core ∧
      ∀ E ∈ P.core, multiplicity B E = 1)
#guard_standard_axioms CoveringDesigns.Qk_K_2.twenty_unit_pure
#print axioms CoveringDesigns.Qk_K_2.twenty_unit_pure

#check (@CoveringDesigns.Qk_K_2.twenty_converse :
∀ {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (P : Plane 4 I (Fin 5)) {H : Finset (Finset I)} {m : Finset I → ℕ} {t : ℕ}
    (ht : 1 ≤ t) (hd : NatDescription P H m t) (hv : Fintype.card X = 16*t),
  Fintype.card (Point H m) = 16*t ∧
      Multicover.IsCover (block H m) (4*t) 2 1 ∧ Function.Injective (block H m) ∧
      ∃ C : Family X, IsCover C (4*t) 2 ∧ C.card = 20)
#guard_standard_axioms CoveringDesigns.Qk_K_2.twenty_converse
#print axioms CoveringDesigns.Qk_K_2.twenty_converse

end

section
open CoveringDesigns.Qk_K_2
#check (@CoveringDesigns.Qk_K_2.affine_exact :
∀ {α : Type*} [Fintype α] {q k : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hk : q ≤ k)
    (hd : q ∣ k) (hv : Fintype.card α = q*k),
  (∃ C : Family α, IsCover C k 2 ∧ C.card = q*(q+1)) ∧
      (∀ C : Family α, IsCover C k 2 → q*(q+1) ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.affine_exact
#print axioms CoveringDesigns.Qk_K_2.affine_exact

#check (@CoveringDesigns.Qk_K_2.weighted_open_exact :
∀ {α : Type*} [Fintype α] {q u r v : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hr : 1 ≤ r) (hrq : r < q) (hru : r ≤ u)
    (hv : Fintype.card α = v) (hlo : q*(q*u+r) < v) (hhi : v ≤ q*(q*u+r)+r),
  (∃ C : Family α, IsCover C (q*u+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*u+r) 2 → q*q+q+1 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.weighted_open_exact
#print axioms CoveringDesigns.Qk_K_2.weighted_open_exact

#check (@CoveringDesigns.Qk_K_2.weighted_endpoint_divisibility :
∀ {α : Type*} [Fintype α] {q u r : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hr : 1 ≤ r) (hrq : r < q) (hru : r ≤ u)
    (hv : Fintype.card α = q*(q*u+r)) (hnd : ¬ (q+1) ∣ q*u+r),
  (∃ C : Family α, IsCover C (q*u+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*u+r) 2 → q*q+q+1 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.weighted_endpoint_divisibility
#print axioms CoveringDesigns.Qk_K_2.weighted_endpoint_divisibility

#check (@CoveringDesigns.Qk_K_2.weighted_endpoint_exclusion :
∀ {α : Type u} [Fintype α] {q a r : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hr : 1 ≤ r) (hrq : r < q) (hra : r ≤ a)
    (hv : Fintype.card α = q*(q*a+r))
    (hn : ∀ {I : Type u} [Fintype I] [DecidableEq I] {H : Finset (Finset I)},
      IsTwistedPlane q H → False),
  (∃ C : Family α, IsCover C (q*a+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*a+r) 2 → q*q+q+1 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.weighted_endpoint_exclusion
#print axioms CoveringDesigns.Qk_K_2.weighted_endpoint_exclusion

end

section
open CoveringDesigns.Qk_K_2
#check (@CoveringDesigns.Qk_K_2.nonsquare_seven :
∀ (d : ℤ),
  d^2 ≠ (6 : ℤ)^28 * 8^29)
#guard_standard_axioms CoveringDesigns.Qk_K_2.nonsquare_seven
#print axioms CoveringDesigns.Qk_K_2.nonsquare_seven

#check (@CoveringDesigns.Qk_K_2.no_twisted_seven :
∀ {I : Type*} [Fintype I] [DecidableEq I]
    {H : Finset (Finset I)} (T : IsTwistedPlane 7 H),
  False)
#guard_standard_axioms CoveringDesigns.Qk_K_2.no_twisted_seven
#print axioms CoveringDesigns.Qk_K_2.no_twisted_seven

#check (@CoveringDesigns.Qk_K_2.nonsquare_nine :
∀ (d : ℤ),
  d^2 ≠ (8 : ℤ)^45 * 10^46)
#guard_standard_axioms CoveringDesigns.Qk_K_2.nonsquare_nine
#print axioms CoveringDesigns.Qk_K_2.nonsquare_nine

#check (@CoveringDesigns.Qk_K_2.no_twisted_nine :
∀ {I : Type*} [Fintype I] [DecidableEq I]
    {H : Finset (Finset I)} (T : IsTwistedPlane 9 H),
  False)
#guard_standard_axioms CoveringDesigns.Qk_K_2.no_twisted_nine
#print axioms CoveringDesigns.Qk_K_2.no_twisted_nine

#check (@CoveringDesigns.Qk_K_2.indexed_exclusion :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {q k : ℕ} {B : I → Finset X}
    (hq : 4 ≤ q) (hk : q ≤ k) (hv : Fintype.card X = q*k)
    (hB : Multicover.IsCover B k 2 1) (hnd : ¬ q ∣ k)
    (hn : ∀ {H : Finset (Finset I)}, IsTwistedPlane q H → False),
  q*(q+1)+1 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.Qk_K_2.indexed_exclusion
#print axioms CoveringDesigns.Qk_K_2.indexed_exclusion

end

section
open CoveringDesigns.Qk_K_2
#check (@CoveringDesigns.Qk_K_2.lifted_lower_bound :
∀ {α : Type*} [Fintype α] {C : Family α}
    (k : ℕ) (hk : 8 ≤ k) (hnd : ¬ 4 ∣ k) (j : ℕ)
    (hv : Fintype.card α = 4*k+j) (hC : IsCover C (k+j) (2+j)),
  Multicover.bound 21 (4*k+j) (k+j) j ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lifted_lower_bound
#print axioms CoveringDesigns.Qk_K_2.lifted_lower_bound

end

section
open CoveringDesigns.Qk_K_2
#check (@CoveringDesigns.Qk_K_2.ceilings_9 :
Multicover.bound 21 36 9 0 = 21 ∧
    Multicover.bound 21 37 10 1 = 78 ∧
    Multicover.bound 21 38 11 2 = 270 ∧
    Multicover.bound 21 39 12 3 = 878 ∧
    Multicover.bound 21 40 13 4 = 2702 ∧
    Multicover.bound 21 41 14 5 = 7913 ∧
    Multicover.bound 21 42 15 6 = 22157)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_9
#print axioms CoveringDesigns.Qk_K_2.ceilings_9

#check (@CoveringDesigns.Qk_K_2.ceilings_10 :
Multicover.bound 21 40 10 0 = 21 ∧
    Multicover.bound 21 41 11 1 = 79 ∧
    Multicover.bound 21 42 12 2 = 277 ∧
    Multicover.bound 21 43 13 3 = 917 ∧
    Multicover.bound 21 44 14 4 = 2882 ∧
    Multicover.bound 21 45 15 5 = 8646 ∧
    Multicover.bound 21 46 16 6 = 24858)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_10
#print axioms CoveringDesigns.Qk_K_2.ceilings_10

#check (@CoveringDesigns.Qk_K_2.ceilings_11 :
Multicover.bound 21 44 11 0 = 21 ∧
    Multicover.bound 21 45 12 1 = 79 ∧
    Multicover.bound 21 46 13 2 = 280 ∧
    Multicover.bound 21 47 14 3 = 940 ∧
    Multicover.bound 21 48 15 4 = 3008 ∧
    Multicover.bound 21 49 16 5 = 9212 ∧
    Multicover.bound 21 50 17 6 = 27095)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_11
#print axioms CoveringDesigns.Qk_K_2.ceilings_11

#check (@CoveringDesigns.Qk_K_2.ceilings_13 :
Multicover.bound 21 52 13 0 = 21 ∧
    Multicover.bound 21 53 14 1 = 80 ∧
    Multicover.bound 21 54 15 2 = 288 ∧
    Multicover.bound 21 55 16 3 = 990 ∧
    Multicover.bound 21 56 17 4 = 3262 ∧
    Multicover.bound 21 57 18 5 = 10330 ∧
    Multicover.bound 21 58 19 6 = 31534)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_13
#print axioms CoveringDesigns.Qk_K_2.ceilings_13

#check (@CoveringDesigns.Qk_K_2.ceilings_14 :
Multicover.bound 21 56 14 0 = 21 ∧
    Multicover.bound 21 57 15 1 = 80 ∧
    Multicover.bound 21 58 16 2 = 290 ∧
    Multicover.bound 21 59 17 3 = 1007 ∧
    Multicover.bound 21 60 18 4 = 3357 ∧
    Multicover.bound 21 61 19 5 = 10778 ∧
    Multicover.bound 21 62 20 6 = 33412)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_14
#print axioms CoveringDesigns.Qk_K_2.ceilings_14

#check (@CoveringDesigns.Qk_K_2.ceilings_15 :
Multicover.bound 21 60 15 0 = 21 ∧
    Multicover.bound 21 61 16 1 = 81 ∧
    Multicover.bound 21 62 17 2 = 296 ∧
    Multicover.bound 21 63 18 3 = 1036 ∧
    Multicover.bound 21 64 19 4 = 3490 ∧
    Multicover.bound 21 65 20 5 = 11343 ∧
    Multicover.bound 21 66 21 6 = 35650)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_15
#print axioms CoveringDesigns.Qk_K_2.ceilings_15

#check (@CoveringDesigns.Qk_K_2.ceilings_17 :
Multicover.bound 21 68 17 0 = 21 ∧
    Multicover.bound 21 69 18 1 = 81 ∧
    Multicover.bound 21 70 19 2 = 299 ∧
    Multicover.bound 21 71 20 3 = 1062 ∧
    Multicover.bound 21 72 21 4 = 3642 ∧
    Multicover.bound 21 73 22 5 = 12085 ∧
    Multicover.bound 21 74 23 6 = 38883)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_17
#print axioms CoveringDesigns.Qk_K_2.ceilings_17

#check (@CoveringDesigns.Qk_K_2.ceilings_18 :
Multicover.bound 21 72 18 0 = 21 ∧
    Multicover.bound 21 73 19 1 = 81 ∧
    Multicover.bound 21 74 20 2 = 300 ∧
    Multicover.bound 21 75 21 3 = 1072 ∧
    Multicover.bound 21 76 22 4 = 3704 ∧
    Multicover.bound 21 77 23 5 = 12401 ∧
    Multicover.bound 21 78 24 6 = 40304)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_18
#print axioms CoveringDesigns.Qk_K_2.ceilings_18

#check (@CoveringDesigns.Qk_K_2.ceilings_19 :
Multicover.bound 21 76 19 0 = 21 ∧
    Multicover.bound 21 77 20 1 = 81 ∧
    Multicover.bound 21 78 21 2 = 301 ∧
    Multicover.bound 21 79 22 3 = 1081 ∧
    Multicover.bound 21 80 23 4 = 3760 ∧
    Multicover.bound 21 81 24 5 = 12690)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_19
#print axioms CoveringDesigns.Qk_K_2.ceilings_19

#check (@CoveringDesigns.Qk_K_2.ceilings_21 :
Multicover.bound 21 84 21 0 = 21 ∧
    Multicover.bound 21 85 22 1 = 82 ∧
    Multicover.bound 21 86 23 2 = 307 ∧
    Multicover.bound 21 87 24 3 = 1113)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_21
#print axioms CoveringDesigns.Qk_K_2.ceilings_21

#check (@CoveringDesigns.Qk_K_2.ceilings_22 :
Multicover.bound 21 88 22 0 = 21 ∧
    Multicover.bound 21 89 23 1 = 82 ∧
    Multicover.bound 21 90 24 2 = 308)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_22
#print axioms CoveringDesigns.Qk_K_2.ceilings_22

#check (@CoveringDesigns.Qk_K_2.ceilings_23 :
Multicover.bound 21 92 23 0 = 21 ∧
    Multicover.bound 21 93 24 1 = 82)
#guard_standard_axioms CoveringDesigns.Qk_K_2.ceilings_23
#print axioms CoveringDesigns.Qk_K_2.ceilings_23

#check (@CoveringDesigns.Qk_K_2.lower_bound_37_10_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 37) (hC : IsCover C 10 3),
  78 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_37_10_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_37_10_3

#check (@CoveringDesigns.Qk_K_2.lower_bound_38_11_4 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 38) (hC : IsCover C 11 4),
  270 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_38_11_4
#print axioms CoveringDesigns.Qk_K_2.lower_bound_38_11_4

#check (@CoveringDesigns.Qk_K_2.lower_bound_39_12_5 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 39) (hC : IsCover C 12 5),
  878 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_39_12_5
#print axioms CoveringDesigns.Qk_K_2.lower_bound_39_12_5

#check (@CoveringDesigns.Qk_K_2.lower_bound_40_13_6 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 40) (hC : IsCover C 13 6),
  2702 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_40_13_6
#print axioms CoveringDesigns.Qk_K_2.lower_bound_40_13_6

#check (@CoveringDesigns.Qk_K_2.lower_bound_41_14_7 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 41) (hC : IsCover C 14 7),
  7913 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_41_14_7
#print axioms CoveringDesigns.Qk_K_2.lower_bound_41_14_7

#check (@CoveringDesigns.Qk_K_2.lower_bound_42_15_8 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 42) (hC : IsCover C 15 8),
  22157 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_42_15_8
#print axioms CoveringDesigns.Qk_K_2.lower_bound_42_15_8

#check (@CoveringDesigns.Qk_K_2.lower_bound_41_11_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 41) (hC : IsCover C 11 3),
  79 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_41_11_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_41_11_3

#check (@CoveringDesigns.Qk_K_2.lower_bound_42_12_4 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 42) (hC : IsCover C 12 4),
  277 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_42_12_4
#print axioms CoveringDesigns.Qk_K_2.lower_bound_42_12_4

#check (@CoveringDesigns.Qk_K_2.lower_bound_43_13_5 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 43) (hC : IsCover C 13 5),
  917 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_43_13_5
#print axioms CoveringDesigns.Qk_K_2.lower_bound_43_13_5

#check (@CoveringDesigns.Qk_K_2.lower_bound_44_14_6 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 44) (hC : IsCover C 14 6),
  2882 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_44_14_6
#print axioms CoveringDesigns.Qk_K_2.lower_bound_44_14_6

#check (@CoveringDesigns.Qk_K_2.lower_bound_45_15_7 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 45) (hC : IsCover C 15 7),
  8646 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_45_15_7
#print axioms CoveringDesigns.Qk_K_2.lower_bound_45_15_7

#check (@CoveringDesigns.Qk_K_2.lower_bound_46_16_8 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 46) (hC : IsCover C 16 8),
  24858 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_46_16_8
#print axioms CoveringDesigns.Qk_K_2.lower_bound_46_16_8

#check (@CoveringDesigns.Qk_K_2.lower_bound_45_12_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 45) (hC : IsCover C 12 3),
  79 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_45_12_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_45_12_3

#check (@CoveringDesigns.Qk_K_2.lower_bound_46_13_4 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 46) (hC : IsCover C 13 4),
  280 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_46_13_4
#print axioms CoveringDesigns.Qk_K_2.lower_bound_46_13_4

#check (@CoveringDesigns.Qk_K_2.lower_bound_47_14_5 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 47) (hC : IsCover C 14 5),
  940 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_47_14_5
#print axioms CoveringDesigns.Qk_K_2.lower_bound_47_14_5

#check (@CoveringDesigns.Qk_K_2.lower_bound_48_15_6 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 48) (hC : IsCover C 15 6),
  3008 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_48_15_6
#print axioms CoveringDesigns.Qk_K_2.lower_bound_48_15_6

#check (@CoveringDesigns.Qk_K_2.lower_bound_49_16_7 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 49) (hC : IsCover C 16 7),
  9212 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_49_16_7
#print axioms CoveringDesigns.Qk_K_2.lower_bound_49_16_7

#check (@CoveringDesigns.Qk_K_2.lower_bound_53_14_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 53) (hC : IsCover C 14 3),
  80 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_53_14_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_53_14_3

#check (@CoveringDesigns.Qk_K_2.lower_bound_54_15_4 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 54) (hC : IsCover C 15 4),
  288 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_54_15_4
#print axioms CoveringDesigns.Qk_K_2.lower_bound_54_15_4

#check (@CoveringDesigns.Qk_K_2.lower_bound_55_16_5 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 55) (hC : IsCover C 16 5),
  990 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_55_16_5
#print axioms CoveringDesigns.Qk_K_2.lower_bound_55_16_5

#check (@CoveringDesigns.Qk_K_2.lower_bound_56_17_6 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 56) (hC : IsCover C 17 6),
  3262 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_56_17_6
#print axioms CoveringDesigns.Qk_K_2.lower_bound_56_17_6

#check (@CoveringDesigns.Qk_K_2.lower_bound_57_18_7 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 57) (hC : IsCover C 18 7),
  10330 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_57_18_7
#print axioms CoveringDesigns.Qk_K_2.lower_bound_57_18_7

#check (@CoveringDesigns.Qk_K_2.lower_bound_57_15_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 57) (hC : IsCover C 15 3),
  80 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_57_15_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_57_15_3

#check (@CoveringDesigns.Qk_K_2.lower_bound_58_16_4 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 58) (hC : IsCover C 16 4),
  290 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_58_16_4
#print axioms CoveringDesigns.Qk_K_2.lower_bound_58_16_4

#check (@CoveringDesigns.Qk_K_2.lower_bound_59_17_5 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 59) (hC : IsCover C 17 5),
  1007 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_59_17_5
#print axioms CoveringDesigns.Qk_K_2.lower_bound_59_17_5

#check (@CoveringDesigns.Qk_K_2.lower_bound_60_18_6 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 60) (hC : IsCover C 18 6),
  3357 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_60_18_6
#print axioms CoveringDesigns.Qk_K_2.lower_bound_60_18_6

#check (@CoveringDesigns.Qk_K_2.lower_bound_61_19_7 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 61) (hC : IsCover C 19 7),
  10778 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_61_19_7
#print axioms CoveringDesigns.Qk_K_2.lower_bound_61_19_7

#check (@CoveringDesigns.Qk_K_2.lower_bound_61_16_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 61) (hC : IsCover C 16 3),
  81 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_61_16_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_61_16_3

#check (@CoveringDesigns.Qk_K_2.lower_bound_62_17_4 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 62) (hC : IsCover C 17 4),
  296 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_62_17_4
#print axioms CoveringDesigns.Qk_K_2.lower_bound_62_17_4

#check (@CoveringDesigns.Qk_K_2.lower_bound_63_18_5 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 63) (hC : IsCover C 18 5),
  1036 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_63_18_5
#print axioms CoveringDesigns.Qk_K_2.lower_bound_63_18_5

#check (@CoveringDesigns.Qk_K_2.lower_bound_64_19_6 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 64) (hC : IsCover C 19 6),
  3490 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_64_19_6
#print axioms CoveringDesigns.Qk_K_2.lower_bound_64_19_6

#check (@CoveringDesigns.Qk_K_2.lower_bound_65_20_7 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 65) (hC : IsCover C 20 7),
  11343 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_65_20_7
#print axioms CoveringDesigns.Qk_K_2.lower_bound_65_20_7

#check (@CoveringDesigns.Qk_K_2.lower_bound_69_18_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 69) (hC : IsCover C 18 3),
  81 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_69_18_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_69_18_3

#check (@CoveringDesigns.Qk_K_2.lower_bound_70_19_4 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 70) (hC : IsCover C 19 4),
  299 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_70_19_4
#print axioms CoveringDesigns.Qk_K_2.lower_bound_70_19_4

#check (@CoveringDesigns.Qk_K_2.lower_bound_71_20_5 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 71) (hC : IsCover C 20 5),
  1062 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_71_20_5
#print axioms CoveringDesigns.Qk_K_2.lower_bound_71_20_5

#check (@CoveringDesigns.Qk_K_2.lower_bound_72_21_6 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 72) (hC : IsCover C 21 6),
  3642 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_72_21_6
#print axioms CoveringDesigns.Qk_K_2.lower_bound_72_21_6

#check (@CoveringDesigns.Qk_K_2.lower_bound_73_22_7 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 73) (hC : IsCover C 22 7),
  12085 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_73_22_7
#print axioms CoveringDesigns.Qk_K_2.lower_bound_73_22_7

#check (@CoveringDesigns.Qk_K_2.lower_bound_73_19_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 73) (hC : IsCover C 19 3),
  81 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_73_19_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_73_19_3

#check (@CoveringDesigns.Qk_K_2.lower_bound_74_20_4 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 74) (hC : IsCover C 20 4),
  300 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_74_20_4
#print axioms CoveringDesigns.Qk_K_2.lower_bound_74_20_4

#check (@CoveringDesigns.Qk_K_2.lower_bound_75_21_5 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 75) (hC : IsCover C 21 5),
  1072 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_75_21_5
#print axioms CoveringDesigns.Qk_K_2.lower_bound_75_21_5

#check (@CoveringDesigns.Qk_K_2.lower_bound_76_22_6 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 76) (hC : IsCover C 22 6),
  3704 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_76_22_6
#print axioms CoveringDesigns.Qk_K_2.lower_bound_76_22_6

#check (@CoveringDesigns.Qk_K_2.lower_bound_77_23_7 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 77) (hC : IsCover C 23 7),
  12401 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_77_23_7
#print axioms CoveringDesigns.Qk_K_2.lower_bound_77_23_7

#check (@CoveringDesigns.Qk_K_2.lower_bound_77_20_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 77) (hC : IsCover C 20 3),
  81 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_77_20_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_77_20_3

#check (@CoveringDesigns.Qk_K_2.lower_bound_78_21_4 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 78) (hC : IsCover C 21 4),
  301 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_78_21_4
#print axioms CoveringDesigns.Qk_K_2.lower_bound_78_21_4

#check (@CoveringDesigns.Qk_K_2.lower_bound_79_22_5 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 79) (hC : IsCover C 22 5),
  1081 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_79_22_5
#print axioms CoveringDesigns.Qk_K_2.lower_bound_79_22_5

#check (@CoveringDesigns.Qk_K_2.lower_bound_80_23_6 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 80) (hC : IsCover C 23 6),
  3760 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_80_23_6
#print axioms CoveringDesigns.Qk_K_2.lower_bound_80_23_6

#check (@CoveringDesigns.Qk_K_2.lower_bound_81_24_7 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 81) (hC : IsCover C 24 7),
  12690 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_81_24_7
#print axioms CoveringDesigns.Qk_K_2.lower_bound_81_24_7

#check (@CoveringDesigns.Qk_K_2.lower_bound_85_22_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 85) (hC : IsCover C 22 3),
  82 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_85_22_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_85_22_3

#check (@CoveringDesigns.Qk_K_2.lower_bound_86_23_4 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 86) (hC : IsCover C 23 4),
  307 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_86_23_4
#print axioms CoveringDesigns.Qk_K_2.lower_bound_86_23_4

#check (@CoveringDesigns.Qk_K_2.lower_bound_87_24_5 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 87) (hC : IsCover C 24 5),
  1113 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_87_24_5
#print axioms CoveringDesigns.Qk_K_2.lower_bound_87_24_5

#check (@CoveringDesigns.Qk_K_2.lower_bound_89_23_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 89) (hC : IsCover C 23 3),
  82 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_89_23_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_89_23_3

#check (@CoveringDesigns.Qk_K_2.lower_bound_90_24_4 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 90) (hC : IsCover C 24 4),
  308 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_90_24_4
#print axioms CoveringDesigns.Qk_K_2.lower_bound_90_24_4

#check (@CoveringDesigns.Qk_K_2.lower_bound_93_24_3 :
∀ {α : Type*} [Fintype α] {C : Family α}
    (hv : Fintype.card α = 93) (hC : IsCover C 24 3),
  82 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_93_24_3
#print axioms CoveringDesigns.Qk_K_2.lower_bound_93_24_3

end

section
open CoveringDesigns.Qk_K_2
#check (@CoveringDesigns.Qk_K_2.exact_55_11_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 55),
  (∃ C : Family α, IsCover C 11 2 ∧ C.card = 31) ∧
      (∀ C : Family α, IsCover C 11 2 → 31 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.exact_55_11_2
#print axioms CoveringDesigns.Qk_K_2.exact_55_11_2

#check (@CoveringDesigns.Qk_K_2.attainment_55_11_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 55),
  ∃ C : Family α, IsCover C 11 2 ∧ C.card = 31)
#guard_standard_axioms CoveringDesigns.Qk_K_2.attainment_55_11_2
#print axioms CoveringDesigns.Qk_K_2.attainment_55_11_2

#check (@CoveringDesigns.Qk_K_2.covering_number_55_11_2 :
(∃ C : Family (Fin 55), IsCover C 11 2 ∧ C.card = 31) ∧
      (∀ C : Family (Fin 55), IsCover C 11 2 → 31 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.covering_number_55_11_2
#print axioms CoveringDesigns.Qk_K_2.covering_number_55_11_2

#check (@CoveringDesigns.Qk_K_2.exact_65_13_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 65),
  (∃ C : Family α, IsCover C 13 2 ∧ C.card = 31) ∧
      (∀ C : Family α, IsCover C 13 2 → 31 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.exact_65_13_2
#print axioms CoveringDesigns.Qk_K_2.exact_65_13_2

#check (@CoveringDesigns.Qk_K_2.attainment_65_13_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 65),
  ∃ C : Family α, IsCover C 13 2 ∧ C.card = 31)
#guard_standard_axioms CoveringDesigns.Qk_K_2.attainment_65_13_2
#print axioms CoveringDesigns.Qk_K_2.attainment_65_13_2

#check (@CoveringDesigns.Qk_K_2.covering_number_65_13_2 :
(∃ C : Family (Fin 65), IsCover C 13 2 ∧ C.card = 31) ∧
      (∀ C : Family (Fin 65), IsCover C 13 2 → 31 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.covering_number_65_13_2
#print axioms CoveringDesigns.Qk_K_2.covering_number_65_13_2

#check (@CoveringDesigns.Qk_K_2.exact_80_16_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 80),
  (∃ C : Family α, IsCover C 16 2 ∧ C.card = 31) ∧
      (∀ C : Family α, IsCover C 16 2 → 31 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.exact_80_16_2
#print axioms CoveringDesigns.Qk_K_2.exact_80_16_2

#check (@CoveringDesigns.Qk_K_2.attainment_80_16_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 80),
  ∃ C : Family α, IsCover C 16 2 ∧ C.card = 31)
#guard_standard_axioms CoveringDesigns.Qk_K_2.attainment_80_16_2
#print axioms CoveringDesigns.Qk_K_2.attainment_80_16_2

#check (@CoveringDesigns.Qk_K_2.covering_number_80_16_2 :
(∃ C : Family (Fin 80), IsCover C 16 2 ∧ C.card = 31) ∧
      (∀ C : Family (Fin 80), IsCover C 16 2 → 31 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.covering_number_80_16_2
#print axioms CoveringDesigns.Qk_K_2.covering_number_80_16_2

#check (@CoveringDesigns.Qk_K_2.exact_85_17_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 85),
  (∃ C : Family α, IsCover C 17 2 ∧ C.card = 31) ∧
      (∀ C : Family α, IsCover C 17 2 → 31 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.exact_85_17_2
#print axioms CoveringDesigns.Qk_K_2.exact_85_17_2

#check (@CoveringDesigns.Qk_K_2.attainment_85_17_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 85),
  ∃ C : Family α, IsCover C 17 2 ∧ C.card = 31)
#guard_standard_axioms CoveringDesigns.Qk_K_2.attainment_85_17_2
#print axioms CoveringDesigns.Qk_K_2.attainment_85_17_2

#check (@CoveringDesigns.Qk_K_2.covering_number_85_17_2 :
(∃ C : Family (Fin 85), IsCover C 17 2 ∧ C.card = 31) ∧
      (∀ C : Family (Fin 85), IsCover C 17 2 → 31 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.covering_number_85_17_2
#print axioms CoveringDesigns.Qk_K_2.covering_number_85_17_2

#check (@CoveringDesigns.Qk_K_2.exact_95_19_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 95),
  (∃ C : Family α, IsCover C 19 2 ∧ C.card = 31) ∧
      (∀ C : Family α, IsCover C 19 2 → 31 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.exact_95_19_2
#print axioms CoveringDesigns.Qk_K_2.exact_95_19_2

#check (@CoveringDesigns.Qk_K_2.attainment_95_19_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 95),
  ∃ C : Family α, IsCover C 19 2 ∧ C.card = 31)
#guard_standard_axioms CoveringDesigns.Qk_K_2.attainment_95_19_2
#print axioms CoveringDesigns.Qk_K_2.attainment_95_19_2

#check (@CoveringDesigns.Qk_K_2.covering_number_95_19_2 :
(∃ C : Family (Fin 95), IsCover C 19 2 ∧ C.card = 31) ∧
      (∀ C : Family (Fin 95), IsCover C 19 2 → 31 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.covering_number_95_19_2
#print axioms CoveringDesigns.Qk_K_2.covering_number_95_19_2

#check (@CoveringDesigns.Qk_K_2.exact_56_8_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 56),
  (∃ C : Family α, IsCover C 8 2 ∧ C.card = 57) ∧
      (∀ C : Family α, IsCover C 8 2 → 57 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.exact_56_8_2
#print axioms CoveringDesigns.Qk_K_2.exact_56_8_2

#check (@CoveringDesigns.Qk_K_2.attainment_56_8_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 56),
  ∃ C : Family α, IsCover C 8 2 ∧ C.card = 57)
#guard_standard_axioms CoveringDesigns.Qk_K_2.attainment_56_8_2
#print axioms CoveringDesigns.Qk_K_2.attainment_56_8_2

#check (@CoveringDesigns.Qk_K_2.covering_number_56_8_2 :
(∃ C : Family (Fin 56), IsCover C 8 2 ∧ C.card = 57) ∧
      (∀ C : Family (Fin 56), IsCover C 8 2 → 57 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.covering_number_56_8_2
#print axioms CoveringDesigns.Qk_K_2.covering_number_56_8_2

#check (@CoveringDesigns.Qk_K_2.exact_90_10_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 90),
  (∃ C : Family α, IsCover C 10 2 ∧ C.card = 91) ∧
      (∀ C : Family α, IsCover C 10 2 → 91 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.exact_90_10_2
#print axioms CoveringDesigns.Qk_K_2.exact_90_10_2

#check (@CoveringDesigns.Qk_K_2.attainment_90_10_2 :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 90),
  ∃ C : Family α, IsCover C 10 2 ∧ C.card = 91)
#guard_standard_axioms CoveringDesigns.Qk_K_2.attainment_90_10_2
#print axioms CoveringDesigns.Qk_K_2.attainment_90_10_2

#check (@CoveringDesigns.Qk_K_2.covering_number_90_10_2 :
(∃ C : Family (Fin 90), IsCover C 10 2 ∧ C.card = 91) ∧
      (∀ C : Family (Fin 90), IsCover C 10 2 → 91 ≤ C.card))
#guard_standard_axioms CoveringDesigns.Qk_K_2.covering_number_90_10_2
#print axioms CoveringDesigns.Qk_K_2.covering_number_90_10_2

end

section
open CoveringDesigns.Qk_K_2
#check (@CoveringDesigns.Qk_K_2.indexed_lower_55_11_2 :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 55) (hB : Multicover.IsCover B 11 2 1),
  31 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.Qk_K_2.indexed_lower_55_11_2
#print axioms CoveringDesigns.Qk_K_2.indexed_lower_55_11_2

#check (@CoveringDesigns.Qk_K_2.lower_bound_55_11_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 55) (hC : IsCover C 11 2),
  31 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_55_11_2
#print axioms CoveringDesigns.Qk_K_2.lower_bound_55_11_2

#check (@CoveringDesigns.Qk_K_2.indexed_lower_65_13_2 :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 65) (hB : Multicover.IsCover B 13 2 1),
  31 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.Qk_K_2.indexed_lower_65_13_2
#print axioms CoveringDesigns.Qk_K_2.indexed_lower_65_13_2

#check (@CoveringDesigns.Qk_K_2.lower_bound_65_13_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 65) (hC : IsCover C 13 2),
  31 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_65_13_2
#print axioms CoveringDesigns.Qk_K_2.lower_bound_65_13_2

#check (@CoveringDesigns.Qk_K_2.indexed_lower_80_16_2 :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 80) (hB : Multicover.IsCover B 16 2 1),
  31 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.Qk_K_2.indexed_lower_80_16_2
#print axioms CoveringDesigns.Qk_K_2.indexed_lower_80_16_2

#check (@CoveringDesigns.Qk_K_2.lower_bound_80_16_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 80) (hC : IsCover C 16 2),
  31 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_80_16_2
#print axioms CoveringDesigns.Qk_K_2.lower_bound_80_16_2

#check (@CoveringDesigns.Qk_K_2.indexed_lower_85_17_2 :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 85) (hB : Multicover.IsCover B 17 2 1),
  31 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.Qk_K_2.indexed_lower_85_17_2
#print axioms CoveringDesigns.Qk_K_2.indexed_lower_85_17_2

#check (@CoveringDesigns.Qk_K_2.lower_bound_85_17_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 85) (hC : IsCover C 17 2),
  31 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_85_17_2
#print axioms CoveringDesigns.Qk_K_2.lower_bound_85_17_2

#check (@CoveringDesigns.Qk_K_2.indexed_lower_95_19_2 :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 95) (hB : Multicover.IsCover B 19 2 1),
  31 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.Qk_K_2.indexed_lower_95_19_2
#print axioms CoveringDesigns.Qk_K_2.indexed_lower_95_19_2

#check (@CoveringDesigns.Qk_K_2.lower_bound_95_19_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 95) (hC : IsCover C 19 2),
  31 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_95_19_2
#print axioms CoveringDesigns.Qk_K_2.lower_bound_95_19_2

#check (@CoveringDesigns.Qk_K_2.indexed_lower_70_14_2 :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 70) (hB : Multicover.IsCover B 14 2 1),
  31 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.Qk_K_2.indexed_lower_70_14_2
#print axioms CoveringDesigns.Qk_K_2.indexed_lower_70_14_2

#check (@CoveringDesigns.Qk_K_2.lower_bound_70_14_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 70) (hC : IsCover C 14 2),
  31 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_70_14_2
#print axioms CoveringDesigns.Qk_K_2.lower_bound_70_14_2

#check (@CoveringDesigns.Qk_K_2.indexed_lower_56_8_2 :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 56) (hB : Multicover.IsCover B 8 2 1),
  57 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.Qk_K_2.indexed_lower_56_8_2
#print axioms CoveringDesigns.Qk_K_2.indexed_lower_56_8_2

#check (@CoveringDesigns.Qk_K_2.lower_bound_56_8_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 56) (hC : IsCover C 8 2),
  57 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_56_8_2
#print axioms CoveringDesigns.Qk_K_2.lower_bound_56_8_2

#check (@CoveringDesigns.Qk_K_2.indexed_lower_90_10_2 :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 90) (hB : Multicover.IsCover B 10 2 1),
  91 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.Qk_K_2.indexed_lower_90_10_2
#print axioms CoveringDesigns.Qk_K_2.indexed_lower_90_10_2

#check (@CoveringDesigns.Qk_K_2.lower_bound_90_10_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 90) (hC : IsCover C 10 2),
  91 ≤ C.card)
#guard_standard_axioms CoveringDesigns.Qk_K_2.lower_bound_90_10_2
#print axioms CoveringDesigns.Qk_K_2.lower_bound_90_10_2

end

section
open CoveringDesigns.Qk_K_2.Perona
#check (@CoveringDesigns.Qk_K_2.Perona.blocks :
List (Finset (Fin 65)))
#guard_standard_axioms CoveringDesigns.Qk_K_2.Perona.blocks
#print axioms CoveringDesigns.Qk_K_2.Perona.blocks

#check (@CoveringDesigns.Qk_K_2.Perona.blocks_distinct :
blocks.Nodup)
#guard_standard_axioms CoveringDesigns.Qk_K_2.Perona.blocks_distinct
#print axioms CoveringDesigns.Qk_K_2.Perona.blocks_distinct

#check (@CoveringDesigns.Qk_K_2.Perona.family :
Family (Fin 65))
#guard_standard_axioms CoveringDesigns.Qk_K_2.Perona.family
#print axioms CoveringDesigns.Qk_K_2.Perona.family

#check (@CoveringDesigns.Qk_K_2.Perona.family_card :
family.card = 31)
#guard_standard_axioms CoveringDesigns.Qk_K_2.Perona.family_card
#print axioms CoveringDesigns.Qk_K_2.Perona.family_card

#check (@CoveringDesigns.Qk_K_2.Perona.family_uniform :
Uniform family 13)
#guard_standard_axioms CoveringDesigns.Qk_K_2.Perona.family_uniform
#print axioms CoveringDesigns.Qk_K_2.Perona.family_uniform

#check (@CoveringDesigns.Qk_K_2.Perona.family_covers :
Covers family 2)
#guard_standard_axioms CoveringDesigns.Qk_K_2.Perona.family_covers
#print axioms CoveringDesigns.Qk_K_2.Perona.family_covers

#check (@CoveringDesigns.Qk_K_2.Perona.family_isCover :
IsCover family 13 2)
#guard_standard_axioms CoveringDesigns.Qk_K_2.Perona.family_isCover
#print axioms CoveringDesigns.Qk_K_2.Perona.family_isCover

#check (@CoveringDesigns.Qk_K_2.Perona.attainment :
∀ {α : Type*} [Fintype α] (hv : Fintype.card α = 65),
  ∃ C : Family α, IsCover C 13 2 ∧ C.card = 31)
#guard_standard_axioms CoveringDesigns.Qk_K_2.Perona.attainment
#print axioms CoveringDesigns.Qk_K_2.Perona.attainment

end

end CoveringDesigns.AuditQk_K_2
