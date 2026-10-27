import CoveringDesigns.PairConsequences
import CoveringDesigns.Foundations.StandardAxioms
universe u v
namespace CoveringDesigns.AuditPairConsequences
open Finset PairConsequences PairEquality PairDivisibility TruncatedPlaneLoads
theorem lower_explicit {X : Type*} [Fintype X] (hv : Fintype.card X = 99)
    (C : Finset (Finset X)) (hu : ∀ B ∈ C, B.card = 23)
    (hc : ∀ T : Finset X, T.card = 6 → ∃ B ∈ C, T ⊆ B) : 13215 ≤ C.card :=
  PairConsequences.lower_bound_99_23_6 hv ⟨hu,hc⟩
#guard_standard_axioms lower_explicit
#print axioms lower_explicit

#check (@CoveringDesigns.PairConsequences.determinantValue :
∀ (q : ℕ),
    ℤ)
#guard_standard_axioms CoveringDesigns.PairConsequences.determinantValue
#print axioms CoveringDesigns.PairConsequences.determinantValue

#check (@CoveringDesigns.PairConsequences.square_factor_iff :
∀ (c z : ℤ) (hc : c ≠ 0),
    IsSquare (c^2*z) ↔ IsSquare z)
#guard_standard_axioms CoveringDesigns.PairConsequences.square_factor_iff
#print axioms CoveringDesigns.PairConsequences.square_factor_iff

#check (@CoveringDesigns.PairConsequences.determinant_square_parity :
∀ {q : ℕ} (hq : 2 ≤ q),
    IsSquare (determinantValue q) ↔
      if Even (q*(q+1)/2) then IsSquare (q+1 : ℤ) else IsSquare ((q-1 : ℕ) : ℤ))
#guard_standard_axioms CoveringDesigns.PairConsequences.determinant_square_parity
#print axioms CoveringDesigns.PairConsequences.determinant_square_parity

#check (@CoveringDesigns.PairConsequences.nonsquare_six :
∀ (d : ℤ),
    d^2 ≠ (5 : ℤ)^21 * 7^22)
#guard_standard_axioms CoveringDesigns.PairConsequences.nonsquare_six
#print axioms CoveringDesigns.PairConsequences.nonsquare_six

#check (@CoveringDesigns.PairConsequences.no_twisted_six :
∀ {I : Type*} [Fintype I] [DecidableEq I]
    {H : Finset (Finset I)} (T : IsTwistedPlane 6 H),
    False)
#guard_standard_axioms CoveringDesigns.PairConsequences.no_twisted_six
#print axioms CoveringDesigns.PairConsequences.no_twisted_six

#check (@CoveringDesigns.PairConsequences.indexed_six :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {k : ℕ} {B : I → Finset X}
    (hk : 6 ≤ k) (hv : Fintype.card X = 6*k)
    (hB : Multicover.IsCover B k 2 1) (hnd : ¬ 6 ∣ k),
    43 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_six
#print axioms CoveringDesigns.PairConsequences.indexed_six

#check (@CoveringDesigns.PairConsequences.lower_bound_six :
∀ {X : Type*} [Fintype X] {C : Family X} {k : ℕ}
    (hk : 6 ≤ k) (hv : Fintype.card X = 6*k) (hC : IsCover C k 2)
    (hnd : ¬ 6 ∣ k),
    43 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_six
#print axioms CoveringDesigns.PairConsequences.lower_bound_six

#check (@CoveringDesigns.PairConsequences.equality_description :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {q k : ℕ} {B : I → Finset X}
    (hq : 4 ≤ q) (hk : q ≤ k) (hv : Fintype.card X = q*k)
    (hi : Fintype.card I = q*(q+1)) (hB : Multicover.IsCover B k 2 1)
    (hn : ∀ {H : Finset (Finset I)}, IsTwistedPlane q H → False),
    ∃ P : Plane q I (Fin (q+1)), P.core ⊆ occupied B ∧
      ∃ t : ℕ, 0 < t ∧ k = q*t ∧
        NatDescription P (occupied B) (multiplicity B) t ∧
        ∃ e : X ≃ Point (occupied B) (multiplicity B),
          (∀ p, (e p).1.val = support B p) ∧
          ∀ p i, e p ∈ block (occupied B) (multiplicity B) i ↔ p ∈ B i)
#guard_standard_axioms CoveringDesigns.PairConsequences.equality_description
#print axioms CoveringDesigns.PairConsequences.equality_description

#check (@CoveringDesigns.PairConsequences.determinant_equality_description :
∀ {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {q k : ℕ} {B : I → Finset X}
    (hq : 4 ≤ q) (hk : q ≤ k) (hv : Fintype.card X = q*k)
    (hi : Fintype.card I = q*(q+1)) (hB : Multicover.IsCover B k 2 1)
    (hn : ¬ IsSquare (determinantValue q)),
    ∃ P : Plane q I (Fin (q+1)), P.core ⊆ occupied B ∧
      ∃ t : ℕ, 0 < t ∧ k = q*t ∧
        NatDescription P (occupied B) (multiplicity B) t ∧
        ∃ e : X ≃ Point (occupied B) (multiplicity B),
          (∀ p, (e p).1.val = support B p) ∧
          ∀ p i, e p ∈ block (occupied B) (multiplicity B) i ↔ p ∈ B i)
#guard_standard_axioms CoveringDesigns.PairConsequences.determinant_equality_description
#print axioms CoveringDesigns.PairConsequences.determinant_equality_description

#check (@CoveringDesigns.PairConsequences.equality_converse :
∀ {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    {q t : ℕ} (P : Plane q I (Fin (q+1))) {H : Finset (Finset I)} {m : Finset I → ℕ}
    (hq : 4 ≤ q) (ht : 0 < t) (hd : NatDescription P H m t)
    (hv : Fintype.card X = q*(q*t)),
    Fintype.card (Point H m) = q*(q*t) ∧
      Multicover.IsCover (block H m) (q*t) 2 1 ∧ Function.Injective (block H m) ∧
      ∃ C : Family X, IsCover C (q*t) 2 ∧ C.card = q*(q+1))
#guard_standard_axioms CoveringDesigns.PairConsequences.equality_converse
#print axioms CoveringDesigns.PairConsequences.equality_converse

#check (@CoveringDesigns.PairConsequences.primitiveBlock :
∀ {I : Type u} [DecidableEq I] (H : Finset (Finset I)) (i : I),
    Finset H)
#guard_standard_axioms CoveringDesigns.PairConsequences.primitiveBlock
#print axioms CoveringDesigns.PairConsequences.primitiveBlock

#check (@CoveringDesigns.PairConsequences.primitiveFamily :
∀ {I : Type u} [Fintype I] [DecidableEq I] (H : Finset (Finset I)),
    Family H)
#guard_standard_axioms CoveringDesigns.PairConsequences.primitiveFamily
#print axioms CoveringDesigns.PairConsequences.primitiveFamily

#check (@CoveringDesigns.PairConsequences.mem_primitiveBlock :
∀ {I : Type u} [DecidableEq I] (H : Finset (Finset I)) (i : I) (E : H),
    E ∈ primitiveBlock H i ↔ i ∈ E.val)
#guard_standard_axioms CoveringDesigns.PairConsequences.mem_primitiveBlock
#print axioms CoveringDesigns.PairConsequences.mem_primitiveBlock

#check (@CoveringDesigns.PairConsequences.primitive_block_card :
∀ {I : Type u} [Fintype I] [DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
    (T : IsTwistedPlane q H) (i : I),
    (primitiveBlock H i).card = q+1)
#guard_standard_axioms CoveringDesigns.PairConsequences.primitive_block_card
#print axioms CoveringDesigns.PairConsequences.primitive_block_card

#check (@CoveringDesigns.PairConsequences.primitive_blocks_injective :
∀ {I : Type u} [Fintype I] [DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
    (hq : 2 ≤ q) (T : IsTwistedPlane q H),
    Function.Injective (primitiveBlock H))
#guard_standard_axioms CoveringDesigns.PairConsequences.primitive_blocks_injective
#print axioms CoveringDesigns.PairConsequences.primitive_blocks_injective

#check (@CoveringDesigns.PairConsequences.primitive_cover :
∀ {I : Type u} [Fintype I] [DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
    (T : IsTwistedPlane q H),
    IsCover (primitiveFamily H) (q+1) 2)
#guard_standard_axioms CoveringDesigns.PairConsequences.primitive_cover
#print axioms CoveringDesigns.PairConsequences.primitive_cover

#check (@CoveringDesigns.PairConsequences.primitive_parameters :
∀ {I : Type u} [Fintype I] [DecidableEq I] {q : ℕ} {H : Finset (Finset I)}
    (hq : 2 ≤ q) (T : IsTwistedPlane q H),
    Fintype.card H = q*(q+1) ∧ (primitiveFamily H).card = q*(q+1) ∧
      IsCover (primitiveFamily H) (q+1) 2)
#guard_standard_axioms CoveringDesigns.PairConsequences.primitive_parameters
#print axioms CoveringDesigns.PairConsequences.primitive_parameters

#check (@CoveringDesigns.PairConsequences.twisted_replication :
∀ {I : Type u} [Fintype I] [DecidableEq I] {X : Type v} [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 4 ≤ q)
    (hB : Multicover.IsCover B k 2 1) (T : IsTwistedPlane q (occupied B)),
    0 < k/(q+1) ∧
      (∀ E ∈ occupied B, multiplicity B E = k/(q+1)) ∧
      ∃ e : X ≃ (occupied B) × Fin (k/(q+1)),
        (∀ p, (e p).1.val = support B p) ∧
        ∀ p i, (e p).1 ∈ primitiveBlock (occupied B) i ↔ p ∈ B i)
#guard_standard_axioms CoveringDesigns.PairConsequences.twisted_replication
#print axioms CoveringDesigns.PairConsequences.twisted_replication

#check (@CoveringDesigns.PairConsequences.primitive_quotient :
∀ {I : Type u} [Fintype I] [DecidableEq I] {X : Type v} [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hi : Fintype.card I = q*(q+1))
    (hB : Multicover.IsCover B k 2 1) (hnd : ¬ q ∣ k),
    Fintype.card (occupied B) = q*(q+1) ∧
      (primitiveFamily (occupied B)).card = q*(q+1) ∧
      IsCover (primitiveFamily (occupied B)) (q+1) 2 ∧
      Function.Injective (primitiveBlock (occupied B)) ∧
      0 < k/(q+1) ∧ (∀ E ∈ occupied B, multiplicity B E = k/(q+1)) ∧
      ∃ e : X ≃ (occupied B) × Fin (k/(q+1)),
        (∀ p, (e p).1.val = support B p) ∧
        ∀ p i, (e p).1 ∈ primitiveBlock (occupied B) i ↔ p ∈ B i)
#guard_standard_axioms CoveringDesigns.PairConsequences.primitive_quotient
#print axioms CoveringDesigns.PairConsequences.primitive_quotient

#check (@CoveringDesigns.PairConsequences.indexed_primitive_exclusion :
∀ {I : Type u} [Fintype I] [DecidableEq I] {X : Type v} [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 4 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hB : Multicover.IsCover B k 2 1) (hnd : ¬ q ∣ k)
    (hn : ∀ {Y : Type u} [Fintype Y], Fintype.card Y = q*(q+1) →
      ∀ C : Family Y, IsCover C (q+1) 2 → C.card ≠ q*(q+1)),
    q*(q+1)+1 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_primitive_exclusion
#print axioms CoveringDesigns.PairConsequences.indexed_primitive_exclusion

#check (@CoveringDesigns.PairConsequences.indexed_pair_incidence :
∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 2 ≤ q) (hk : q ≤ k)
    (hv : q*k ≤ Fintype.card X) (hB : Multicover.IsCover B k 2 1),
    Fintype.card X*(q+1) ≤ k*Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_pair_incidence
#print axioms CoveringDesigns.PairConsequences.indexed_pair_incidence

#check (@CoveringDesigns.PairConsequences.indexed_pair_floor :
∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 2 ≤ q) (hk : q ≤ k)
    (hv : Fintype.card X = q*k) (hB : Multicover.IsCover B k 2 1),
    q*(q+1) ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_pair_floor
#print axioms CoveringDesigns.PairConsequences.indexed_pair_floor

#check (@CoveringDesigns.PairConsequences.indexed_open_floor :
∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {q k : ℕ} {B : I → Finset X} (hq : 2 ≤ q) (hk : q ≤ k)
    (hv : q*k < Fintype.card X) (hB : Multicover.IsCover B k 2 1),
    q*(q+1)+1 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_open_floor
#print axioms CoveringDesigns.PairConsequences.indexed_open_floor

#check (@CoveringDesigns.PairConsequences.weighted_open_exact :
∀ {α : Type*} [Fintype α] {q a r v : ℕ}
    (hq : IsPrimePow q) (hq2 : 2 ≤ q) (hr : 1 ≤ r) (hra : r ≤ a)
    (hv : Fintype.card α = v) (hlo : q*(q*a+r) < v) (hhi : v ≤ q*(q*a+r)+r),
    (∃ C : Family α, IsCover C (q*a+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*a+r) 2 → q*q+q+1 ≤ C.card))
#guard_standard_axioms CoveringDesigns.PairConsequences.weighted_open_exact
#print axioms CoveringDesigns.PairConsequences.weighted_open_exact

#check (@CoveringDesigns.PairConsequences.affine_exact :
∀ {α : Type*} [Fintype α] {q k : ℕ}
    (hq : IsPrimePow q) (hq2 : 2 ≤ q) (hk : q ≤ k)
    (hd : q ∣ k) (hv : Fintype.card α = q*k),
    (∃ C : Family α, IsCover C k 2 ∧ C.card = q*(q+1)) ∧
      (∀ C : Family α, IsCover C k 2 → q*(q+1) ≤ C.card))
#guard_standard_axioms CoveringDesigns.PairConsequences.affine_exact
#print axioms CoveringDesigns.PairConsequences.affine_exact

#check (@CoveringDesigns.PairConsequences.weighted_endpoint_divisibility :
∀ {α : Type*} [Fintype α] {q a r : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hr : 1 ≤ r) (hra : r ≤ a)
    (hv : Fintype.card α = q*(q*a+r))
    (hnd : ¬ q ∣ q*a+r) (hnd' : ¬ (q+1) ∣ q*a+r),
    (∃ C : Family α, IsCover C (q*a+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*a+r) 2 → q*q+q+1 ≤ C.card))
#guard_standard_axioms CoveringDesigns.PairConsequences.weighted_endpoint_divisibility
#print axioms CoveringDesigns.PairConsequences.weighted_endpoint_divisibility

#check (@CoveringDesigns.PairConsequences.weighted_endpoint_exclusion :
∀ {α : Type u} [Fintype α] {q a r : ℕ}
    (hq : IsPrimePow q) (hq4 : 4 ≤ q) (hr : 1 ≤ r) (hra : r ≤ a)
    (hv : Fintype.card α = q*(q*a+r)) (hnd : ¬ q ∣ q*a+r)
    (hn : ∀ {I : Type u} [Fintype I] [DecidableEq I] {H : Finset (Finset I)},
      IsTwistedPlane q H → False),
    (∃ C : Family α, IsCover C (q*a+r) 2 ∧ C.card = q*q+q+1) ∧
      (∀ C : Family α, IsCover C (q*a+r) 2 → q*q+q+1 ≤ C.card))
#guard_standard_axioms CoveringDesigns.PairConsequences.weighted_endpoint_exclusion
#print axioms CoveringDesigns.PairConsequences.weighted_endpoint_exclusion

#check (@CoveringDesigns.PairConsequences.exact_twenty_interval :
∀ {α : Type*} [Fintype α] (hlo : 81 ≤ Fintype.card α)
    (hhi : Fintype.card α ≤ 84),
    (∃ C : Family α, IsCover C 20 2 ∧ C.card = 21) ∧
      (∀ C : Family α, IsCover C 20 2 → 21 ≤ C.card))
#guard_standard_axioms CoveringDesigns.PairConsequences.exact_twenty_interval
#print axioms CoveringDesigns.PairConsequences.exact_twenty_interval

#check (@CoveringDesigns.PairConsequences.exact_twenty_four_interval :
∀ {α : Type*} [Fintype α] (hlo : 97 ≤ Fintype.card α)
    (hhi : Fintype.card α ≤ 99),
    (∃ C : Family α, IsCover C 24 2 ∧ C.card = 21) ∧
      (∀ C : Family α, IsCover C 24 2 → 21 ≤ C.card))
#guard_standard_axioms CoveringDesigns.PairConsequences.exact_twenty_four_interval
#print axioms CoveringDesigns.PairConsequences.exact_twenty_four_interval

#check (@CoveringDesigns.PairConsequences.replicatedFamily :
∀ {X : Type*} [DecidableEq X] (C : Family X) (m : ℕ),
    Family (X × Fin m))
#guard_standard_axioms CoveringDesigns.PairConsequences.replicatedFamily
#print axioms CoveringDesigns.PairConsequences.replicatedFamily

#check (@CoveringDesigns.PairConsequences.replication_injective :
∀ {X : Type*} [DecidableEq X] {m : ℕ} (hm : 0 < m),
    Function.Injective (fun A : Finset X => A ×ˢ (univ : Finset (Fin m))))
#guard_standard_axioms CoveringDesigns.PairConsequences.replication_injective
#print axioms CoveringDesigns.PairConsequences.replication_injective

#check (@CoveringDesigns.PairConsequences.primitive_replication :
∀ {X : Type*} [Fintype X] [DecidableEq X]
    {q m : ℕ} {C : Family X} (hq : 2 ≤ q) (hm : 0 < m)
    (hv : Fintype.card X = q*(q+1)) (hC : IsCover C (q+1) 2)
    (hc : C.card = q*(q+1)),
    Fintype.card (X × Fin m) = q*((q+1)*m) ∧
      IsCover (replicatedFamily C m) ((q+1)*m) 2 ∧
      (replicatedFamily C m).card = q*(q+1) ∧
      ∀ A ∈ C, ∀ p : X × Fin m, p ∈ A ×ˢ (univ : Finset (Fin m)) ↔ p.1 ∈ A)
#guard_standard_axioms CoveringDesigns.PairConsequences.primitive_replication
#print axioms CoveringDesigns.PairConsequences.primitive_replication

#check (@CoveringDesigns.PairConsequences.replication_exact :
∀ {X Y : Type*} [Fintype X] [Fintype Y]
    {q m : ℕ} {C : Family X} (hq : 2 ≤ q) (hm : 0 < m)
    (hv : Fintype.card X = q*(q+1)) (hC : IsCover C (q+1) 2)
    (hc : C.card = q*(q+1)) (hy : Fintype.card Y = q*((q+1)*m)),
    (∃ D : Family Y, IsCover D ((q+1)*m) 2 ∧ D.card = q*(q+1)) ∧
      (∀ D : Family Y, IsCover D ((q+1)*m) 2 → q*(q+1) ≤ D.card))
#guard_standard_axioms CoveringDesigns.PairConsequences.replication_exact
#print axioms CoveringDesigns.PairConsequences.replication_exact

#check (@CoveringDesigns.PairConsequences.indexed_lower_42_7_2 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 42) (hB : Multicover.IsCover B 7 2 1),
    43 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_42_7_2
#print axioms CoveringDesigns.PairConsequences.indexed_lower_42_7_2

#check (@CoveringDesigns.PairConsequences.lower_bound_42_7_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 42) (hC : IsCover C 7 2),
    43 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_42_7_2
#print axioms CoveringDesigns.PairConsequences.lower_bound_42_7_2

#check (@CoveringDesigns.PairConsequences.indexed_lower_78_13_2 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 78) (hB : Multicover.IsCover B 13 2 1),
    43 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_78_13_2
#print axioms CoveringDesigns.PairConsequences.indexed_lower_78_13_2

#check (@CoveringDesigns.PairConsequences.lower_bound_78_13_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 78) (hC : IsCover C 13 2),
    43 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_78_13_2
#print axioms CoveringDesigns.PairConsequences.lower_bound_78_13_2

#check (@CoveringDesigns.PairConsequences.indexed_lower_84_14_2 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 84) (hB : Multicover.IsCover B 14 2 1),
    43 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_84_14_2
#print axioms CoveringDesigns.PairConsequences.indexed_lower_84_14_2

#check (@CoveringDesigns.PairConsequences.lower_bound_84_14_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 84) (hC : IsCover C 14 2),
    43 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_84_14_2
#print axioms CoveringDesigns.PairConsequences.lower_bound_84_14_2

#check (@CoveringDesigns.PairConsequences.indexed_lower_90_15_2 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 90) (hB : Multicover.IsCover B 15 2 1),
    43 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_90_15_2
#print axioms CoveringDesigns.PairConsequences.indexed_lower_90_15_2

#check (@CoveringDesigns.PairConsequences.lower_bound_90_15_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 90) (hC : IsCover C 15 2),
    43 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_90_15_2
#print axioms CoveringDesigns.PairConsequences.lower_bound_90_15_2

#check (@CoveringDesigns.PairConsequences.indexed_lower_96_16_2 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 96) (hB : Multicover.IsCover B 16 2 1),
    43 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_96_16_2
#print axioms CoveringDesigns.PairConsequences.indexed_lower_96_16_2

#check (@CoveringDesigns.PairConsequences.lower_bound_96_16_2 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 96) (hC : IsCover C 16 2),
    43 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_96_16_2
#print axioms CoveringDesigns.PairConsequences.lower_bound_96_16_2

#check (@CoveringDesigns.PairConsequences.indexed_lower_43_8_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 43) (hB : Multicover.IsCover B 8 3 1),
    232 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_43_8_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_43_8_3

#check (@CoveringDesigns.PairConsequences.lower_bound_43_8_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 43) (hC : IsCover C 8 3),
    232 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_43_8_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_43_8_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_56_12_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 56) (hB : Multicover.IsCover B 12 3 1),
    145 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_56_12_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_56_12_3

#check (@CoveringDesigns.PairConsequences.lower_bound_56_12_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 56) (hC : IsCover C 12 3),
    145 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_56_12_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_56_12_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_57_9_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 57) (hB : Multicover.IsCover B 9 3 1),
    361 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_57_9_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_57_9_3

#check (@CoveringDesigns.PairConsequences.lower_bound_57_9_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 57) (hC : IsCover C 9 3),
    361 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_57_9_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_57_9_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_66_14_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 66) (hB : Multicover.IsCover B 14 3 1),
    147 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_66_14_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_66_14_3

#check (@CoveringDesigns.PairConsequences.lower_bound_66_14_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 66) (hC : IsCover C 14 3),
    147 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_66_14_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_66_14_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_71_15_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 71) (hB : Multicover.IsCover B 15 3 1),
    147 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_71_15_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_71_15_3

#check (@CoveringDesigns.PairConsequences.lower_bound_71_15_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 71) (hC : IsCover C 15 3),
    147 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_71_15_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_71_15_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_79_14_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 79) (hB : Multicover.IsCover B 14 3 1),
    243 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_79_14_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_79_14_3

#check (@CoveringDesigns.PairConsequences.lower_bound_79_14_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 79) (hC : IsCover C 14 3),
    243 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_79_14_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_79_14_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_81_17_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 81) (hB : Multicover.IsCover B 17 3 1),
    148 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_81_17_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_81_17_3

#check (@CoveringDesigns.PairConsequences.lower_bound_81_17_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 81) (hC : IsCover C 17 3),
    148 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_81_17_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_81_17_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_85_15_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 85) (hB : Multicover.IsCover B 15 3 1),
    244 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_85_15_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_85_15_3

#check (@CoveringDesigns.PairConsequences.lower_bound_85_15_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 85) (hC : IsCover C 15 3),
    244 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_85_15_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_85_15_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_86_18_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 86) (hB : Multicover.IsCover B 18 3 1),
    149 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_86_18_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_86_18_3

#check (@CoveringDesigns.PairConsequences.lower_bound_86_18_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 86) (hC : IsCover C 18 3),
    149 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_86_18_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_86_18_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_91_11_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 91) (hB : Multicover.IsCover B 11 3 1),
    753 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_91_11_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_91_11_3

#check (@CoveringDesigns.PairConsequences.lower_bound_91_11_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 91) (hC : IsCover C 11 3),
    753 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_91_11_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_91_11_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_91_16_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 91) (hB : Multicover.IsCover B 16 3 1),
    245 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_91_16_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_91_16_3

#check (@CoveringDesigns.PairConsequences.lower_bound_91_16_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 91) (hC : IsCover C 16 3),
    245 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_91_16_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_91_16_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_96_20_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 96) (hB : Multicover.IsCover B 20 3 1),
    149 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_96_20_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_96_20_3

#check (@CoveringDesigns.PairConsequences.lower_bound_96_20_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 96) (hC : IsCover C 20 3),
    149 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_96_20_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_96_20_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_97_17_3 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 97) (hB : Multicover.IsCover B 17 3 1),
    246 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_97_17_3
#print axioms CoveringDesigns.PairConsequences.indexed_lower_97_17_3

#check (@CoveringDesigns.PairConsequences.lower_bound_97_17_3 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 97) (hC : IsCover C 17 3),
    246 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_97_17_3
#print axioms CoveringDesigns.PairConsequences.lower_bound_97_17_3

#check (@CoveringDesigns.PairConsequences.indexed_lower_44_9_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 44) (hB : Multicover.IsCover B 9 4 1),
    1135 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_44_9_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_44_9_4

#check (@CoveringDesigns.PairConsequences.lower_bound_44_9_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 44) (hC : IsCover C 9 4),
    1135 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_44_9_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_44_9_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_57_13_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 57) (hB : Multicover.IsCover B 13 4 1),
    636 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_57_13_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_57_13_4

#check (@CoveringDesigns.PairConsequences.lower_bound_57_13_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 57) (hC : IsCover C 13 4),
    636 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_57_13_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_57_13_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_58_10_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 58) (hB : Multicover.IsCover B 10 4 1),
    2094 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_58_10_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_58_10_4

#check (@CoveringDesigns.PairConsequences.lower_bound_58_10_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 58) (hC : IsCover C 10 4),
    2094 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_58_10_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_58_10_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_67_15_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 67) (hB : Multicover.IsCover B 15 4 1),
    657 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_67_15_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_67_15_4

#check (@CoveringDesigns.PairConsequences.lower_bound_67_15_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 67) (hC : IsCover C 15 4),
    657 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_67_15_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_67_15_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_72_16_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 72) (hB : Multicover.IsCover B 16 4 1),
    662 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_72_16_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_72_16_4

#check (@CoveringDesigns.PairConsequences.lower_bound_72_16_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 72) (hC : IsCover C 16 4),
    662 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_72_16_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_72_16_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_80_15_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 80) (hB : Multicover.IsCover B 15 4 1),
    1296 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_80_15_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_80_15_4

#check (@CoveringDesigns.PairConsequences.lower_bound_80_15_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 80) (hC : IsCover C 15 4),
    1296 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_80_15_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_80_15_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_82_18_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 82) (hB : Multicover.IsCover B 18 4 1),
    675 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_82_18_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_82_18_4

#check (@CoveringDesigns.PairConsequences.lower_bound_82_18_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 82) (hC : IsCover C 18 4),
    675 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_82_18_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_82_18_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_86_16_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 86) (hB : Multicover.IsCover B 16 4 1),
    1312 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_86_16_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_86_16_4

#check (@CoveringDesigns.PairConsequences.lower_bound_86_16_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 86) (hC : IsCover C 16 4),
    1312 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_86_16_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_86_16_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_87_19_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 87) (hB : Multicover.IsCover B 19 4 1),
    683 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_87_19_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_87_19_4

#check (@CoveringDesigns.PairConsequences.lower_bound_87_19_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 87) (hC : IsCover C 19 4),
    683 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_87_19_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_87_19_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_92_12_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 92) (hB : Multicover.IsCover B 12 4 1),
    5773 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_92_12_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_92_12_4

#check (@CoveringDesigns.PairConsequences.lower_bound_92_12_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 92) (hC : IsCover C 12 4),
    5773 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_92_12_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_92_12_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_92_17_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 92) (hB : Multicover.IsCover B 17 4 1),
    1326 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_92_17_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_92_17_4

#check (@CoveringDesigns.PairConsequences.lower_bound_92_17_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 92) (hC : IsCover C 17 4),
    1326 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_92_17_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_92_17_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_97_21_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 97) (hB : Multicover.IsCover B 21 4 1),
    689 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_97_21_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_97_21_4

#check (@CoveringDesigns.PairConsequences.lower_bound_97_21_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 97) (hC : IsCover C 21 4),
    689 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_97_21_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_97_21_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_98_18_4 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 98) (hB : Multicover.IsCover B 18 4 1),
    1340 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_98_18_4
#print axioms CoveringDesigns.PairConsequences.indexed_lower_98_18_4

#check (@CoveringDesigns.PairConsequences.lower_bound_98_18_4 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 98) (hC : IsCover C 18 4),
    1340 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_98_18_4
#print axioms CoveringDesigns.PairConsequences.lower_bound_98_18_4

#check (@CoveringDesigns.PairConsequences.indexed_lower_45_10_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 45) (hB : Multicover.IsCover B 10 5 1),
    5108 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_45_10_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_45_10_5

#check (@CoveringDesigns.PairConsequences.lower_bound_45_10_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 45) (hC : IsCover C 10 5),
    5108 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_45_10_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_45_10_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_58_14_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 58) (hB : Multicover.IsCover B 14 5 1),
    2635 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_58_14_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_58_14_5

#check (@CoveringDesigns.PairConsequences.lower_bound_58_14_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 58) (hC : IsCover C 14 5),
    2635 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_58_14_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_58_14_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_59_11_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 59) (hB : Multicover.IsCover B 11 5 1),
    11232 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_59_11_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_59_11_5

#check (@CoveringDesigns.PairConsequences.lower_bound_59_11_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 59) (hC : IsCover C 11 5),
    11232 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_59_11_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_59_11_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_68_16_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 68) (hB : Multicover.IsCover B 16 5 1),
    2793 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_68_16_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_68_16_5

#check (@CoveringDesigns.PairConsequences.lower_bound_68_16_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 68) (hC : IsCover C 16 5),
    2793 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_68_16_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_68_16_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_73_17_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 73) (hB : Multicover.IsCover B 17 5 1),
    2843 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_73_17_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_73_17_5

#check (@CoveringDesigns.PairConsequences.lower_bound_73_17_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 73) (hC : IsCover C 17 5),
    2843 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_73_17_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_73_17_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_81_16_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 81) (hB : Multicover.IsCover B 16 5 1),
    6561 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_81_16_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_81_16_5

#check (@CoveringDesigns.PairConsequences.lower_bound_81_16_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 81) (hC : IsCover C 16 5),
    6561 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_81_16_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_81_16_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_83_19_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 83) (hB : Multicover.IsCover B 19 5 1),
    2949 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_83_19_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_83_19_5

#check (@CoveringDesigns.PairConsequences.lower_bound_83_19_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 83) (hC : IsCover C 19 5),
    2949 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_83_19_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_83_19_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_87_17_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 87) (hB : Multicover.IsCover B 17 5 1),
    6715 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_87_17_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_87_17_5

#check (@CoveringDesigns.PairConsequences.lower_bound_87_17_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 87) (hC : IsCover C 17 5),
    6715 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_87_17_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_87_17_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_88_20_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 88) (hB : Multicover.IsCover B 20 5 1),
    3006 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_88_20_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_88_20_5

#check (@CoveringDesigns.PairConsequences.lower_bound_88_20_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 88) (hC : IsCover C 20 5),
    3006 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_88_20_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_88_20_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_93_13_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 93) (hB : Multicover.IsCover B 13 5 1),
    41300 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_93_13_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_93_13_5

#check (@CoveringDesigns.PairConsequences.lower_bound_93_13_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 93) (hC : IsCover C 13 5),
    41300 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_93_13_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_93_13_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_93_18_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 93) (hB : Multicover.IsCover B 18 5 1),
    6851 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_93_18_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_93_18_5

#check (@CoveringDesigns.PairConsequences.lower_bound_93_18_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 93) (hC : IsCover C 18 5),
    6851 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_93_18_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_93_18_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_98_22_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 98) (hB : Multicover.IsCover B 22 5 1),
    3070 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_98_22_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_98_22_5

#check (@CoveringDesigns.PairConsequences.lower_bound_98_22_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 98) (hC : IsCover C 22 5),
    3070 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_98_22_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_98_22_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_99_19_5 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 99) (hB : Multicover.IsCover B 19 5 1),
    6983 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_99_19_5
#print axioms CoveringDesigns.PairConsequences.indexed_lower_99_19_5

#check (@CoveringDesigns.PairConsequences.lower_bound_99_19_5 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 99) (hC : IsCover C 19 5),
    6983 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_99_19_5
#print axioms CoveringDesigns.PairConsequences.lower_bound_99_19_5

#check (@CoveringDesigns.PairConsequences.indexed_lower_46_11_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 46) (hB : Multicover.IsCover B 11 6 1),
    21361 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_46_11_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_46_11_6

#check (@CoveringDesigns.PairConsequences.lower_bound_46_11_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 46) (hC : IsCover C 11 6),
    21361 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_46_11_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_46_11_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_59_15_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 59) (hB : Multicover.IsCover B 15 6 1),
    10365 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_59_15_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_59_15_6

#check (@CoveringDesigns.PairConsequences.lower_bound_59_15_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 59) (hC : IsCover C 15 6),
    10365 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_59_15_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_59_15_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_60_12_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 60) (hB : Multicover.IsCover B 12 6 1),
    56160 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_60_12_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_60_12_6

#check (@CoveringDesigns.PairConsequences.lower_bound_60_12_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 60) (hC : IsCover C 12 6),
    56160 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_60_12_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_60_12_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_69_17_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 69) (hB : Multicover.IsCover B 17 6 1),
    11337 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_69_17_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_69_17_6

#check (@CoveringDesigns.PairConsequences.lower_bound_69_17_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 69) (hC : IsCover C 17 6),
    11337 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_69_17_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_69_17_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_74_18_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 74) (hB : Multicover.IsCover B 18 6 1),
    11688 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_74_18_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_74_18_6

#check (@CoveringDesigns.PairConsequences.lower_bound_74_18_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 74) (hC : IsCover C 18 6),
    11688 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_74_18_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_74_18_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_82_17_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 82) (hB : Multicover.IsCover B 17 6 1),
    31648 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_82_17_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_82_17_6

#check (@CoveringDesigns.PairConsequences.lower_bound_82_17_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 82) (hC : IsCover C 17 6),
    31648 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_82_17_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_82_17_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_84_20_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 84) (hB : Multicover.IsCover B 20 6 1),
    12386 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_84_20_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_84_20_6

#check (@CoveringDesigns.PairConsequences.lower_bound_84_20_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 84) (hC : IsCover C 20 6),
    12386 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_84_20_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_84_20_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_88_18_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 88) (hB : Multicover.IsCover B 18 6 1),
    32829 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_88_18_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_88_18_6

#check (@CoveringDesigns.PairConsequences.lower_bound_88_18_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 88) (hC : IsCover C 18 6),
    32829 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_88_18_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_88_18_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_89_21_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 89) (hB : Multicover.IsCover B 21 6 1),
    12740 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_89_21_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_89_21_6

#check (@CoveringDesigns.PairConsequences.lower_bound_89_21_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 89) (hC : IsCover C 21 6),
    12740 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_89_21_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_89_21_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_94_14_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 94) (hB : Multicover.IsCover B 14 6 1),
    277300 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_94_14_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_94_14_6

#check (@CoveringDesigns.PairConsequences.lower_bound_94_14_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 94) (hC : IsCover C 14 6),
    277300 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_94_14_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_94_14_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_94_19_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 94) (hB : Multicover.IsCover B 19 6 1),
    33895 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_94_19_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_94_19_6

#check (@CoveringDesigns.PairConsequences.lower_bound_94_19_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 94) (hC : IsCover C 19 6),
    33895 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_94_19_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_94_19_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_99_23_6 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 99) (hB : Multicover.IsCover B 23 6 1),
    13215 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_99_23_6
#print axioms CoveringDesigns.PairConsequences.indexed_lower_99_23_6

#check (@CoveringDesigns.PairConsequences.lower_bound_99_23_6 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 99) (hC : IsCover C 23 6),
    13215 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_99_23_6
#print axioms CoveringDesigns.PairConsequences.lower_bound_99_23_6

#check (@CoveringDesigns.PairConsequences.indexed_lower_47_12_7 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 47) (hB : Multicover.IsCover B 12 7 1),
    83664 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_47_12_7
#print axioms CoveringDesigns.PairConsequences.indexed_lower_47_12_7

#check (@CoveringDesigns.PairConsequences.lower_bound_47_12_7 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 47) (hC : IsCover C 12 7),
    83664 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_47_12_7
#print axioms CoveringDesigns.PairConsequences.lower_bound_47_12_7

#check (@CoveringDesigns.PairConsequences.indexed_lower_60_16_7 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 60) (hB : Multicover.IsCover B 16 7 1),
    38869 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_60_16_7
#print axioms CoveringDesigns.PairConsequences.indexed_lower_60_16_7

#check (@CoveringDesigns.PairConsequences.lower_bound_60_16_7 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 60) (hC : IsCover C 16 7),
    38869 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_60_16_7
#print axioms CoveringDesigns.PairConsequences.lower_bound_60_16_7

#check (@CoveringDesigns.PairConsequences.indexed_lower_61_13_7 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 61) (hB : Multicover.IsCover B 13 7 1),
    263520 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_61_13_7
#print axioms CoveringDesigns.PairConsequences.indexed_lower_61_13_7

#check (@CoveringDesigns.PairConsequences.lower_bound_61_13_7 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 61) (hC : IsCover C 13 7),
    263520 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_61_13_7
#print axioms CoveringDesigns.PairConsequences.lower_bound_61_13_7

#check (@CoveringDesigns.PairConsequences.indexed_lower_70_18_7 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 70) (hB : Multicover.IsCover B 18 7 1),
    44089 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_70_18_7
#print axioms CoveringDesigns.PairConsequences.indexed_lower_70_18_7

#check (@CoveringDesigns.PairConsequences.lower_bound_70_18_7 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 70) (hC : IsCover C 18 7),
    44089 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_70_18_7
#print axioms CoveringDesigns.PairConsequences.lower_bound_70_18_7

#check (@CoveringDesigns.PairConsequences.indexed_lower_75_19_7 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 75) (hB : Multicover.IsCover B 19 7 1),
    46137 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_75_19_7
#print axioms CoveringDesigns.PairConsequences.indexed_lower_75_19_7

#check (@CoveringDesigns.PairConsequences.lower_bound_75_19_7 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 75) (hC : IsCover C 19 7),
    46137 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_75_19_7
#print axioms CoveringDesigns.PairConsequences.lower_bound_75_19_7

#check (@CoveringDesigns.PairConsequences.indexed_lower_83_18_7 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 83) (hB : Multicover.IsCover B 18 7 1),
    145933 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_83_18_7
#print axioms CoveringDesigns.PairConsequences.indexed_lower_83_18_7

#check (@CoveringDesigns.PairConsequences.lower_bound_83_18_7 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 83) (hC : IsCover C 18 7),
    145933 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_83_18_7
#print axioms CoveringDesigns.PairConsequences.lower_bound_83_18_7

#check (@CoveringDesigns.PairConsequences.indexed_lower_85_21_7 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 85) (hB : Multicover.IsCover B 21 7 1),
    50134 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_85_21_7
#print axioms CoveringDesigns.PairConsequences.indexed_lower_85_21_7

#check (@CoveringDesigns.PairConsequences.lower_bound_85_21_7 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 85) (hC : IsCover C 21 7),
    50134 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_85_21_7
#print axioms CoveringDesigns.PairConsequences.lower_bound_85_21_7

#check (@CoveringDesigns.PairConsequences.indexed_lower_89_19_7 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 89) (hB : Multicover.IsCover B 19 7 1),
    153778 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_89_19_7
#print axioms CoveringDesigns.PairConsequences.indexed_lower_89_19_7

#check (@CoveringDesigns.PairConsequences.lower_bound_89_19_7 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 89) (hC : IsCover C 19 7),
    153778 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_89_19_7
#print axioms CoveringDesigns.PairConsequences.lower_bound_89_19_7

#check (@CoveringDesigns.PairConsequences.indexed_lower_90_22_7 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 90) (hB : Multicover.IsCover B 22 7 1),
    52119 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_90_22_7
#print axioms CoveringDesigns.PairConsequences.indexed_lower_90_22_7

#check (@CoveringDesigns.PairConsequences.lower_bound_90_22_7 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 90) (hC : IsCover C 22 7),
    52119 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_90_22_7
#print axioms CoveringDesigns.PairConsequences.lower_bound_90_22_7

#check (@CoveringDesigns.PairConsequences.indexed_lower_95_15_7 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 95) (hB : Multicover.IsCover B 15 7 1),
    1756234 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_95_15_7
#print axioms CoveringDesigns.PairConsequences.indexed_lower_95_15_7

#check (@CoveringDesigns.PairConsequences.lower_bound_95_15_7 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 95) (hC : IsCover C 15 7),
    1756234 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_95_15_7
#print axioms CoveringDesigns.PairConsequences.lower_bound_95_15_7

#check (@CoveringDesigns.PairConsequences.indexed_lower_95_20_7 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 95) (hB : Multicover.IsCover B 20 7 1),
    161002 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_95_20_7
#print axioms CoveringDesigns.PairConsequences.indexed_lower_95_20_7

#check (@CoveringDesigns.PairConsequences.lower_bound_95_20_7 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 95) (hC : IsCover C 20 7),
    161002 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_95_20_7
#print axioms CoveringDesigns.PairConsequences.lower_bound_95_20_7

#check (@CoveringDesigns.PairConsequences.indexed_lower_48_13_8 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 48) (hB : Multicover.IsCover B 13 8 1),
    308914 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_48_13_8
#print axioms CoveringDesigns.PairConsequences.indexed_lower_48_13_8

#check (@CoveringDesigns.PairConsequences.lower_bound_48_13_8 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 48) (hC : IsCover C 13 8),
    308914 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_48_13_8
#print axioms CoveringDesigns.PairConsequences.lower_bound_48_13_8

#check (@CoveringDesigns.PairConsequences.indexed_lower_61_17_8 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 61) (hB : Multicover.IsCover B 17 8 1),
    139472 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_61_17_8
#print axioms CoveringDesigns.PairConsequences.indexed_lower_61_17_8

#check (@CoveringDesigns.PairConsequences.lower_bound_61_17_8 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 61) (hC : IsCover C 17 8),
    139472 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_61_17_8
#print axioms CoveringDesigns.PairConsequences.lower_bound_61_17_8

#check (@CoveringDesigns.PairConsequences.indexed_lower_62_14_8 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 62) (hB : Multicover.IsCover B 14 8 1),
    1167018 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_62_14_8
#print axioms CoveringDesigns.PairConsequences.indexed_lower_62_14_8

#check (@CoveringDesigns.PairConsequences.lower_bound_62_14_8 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 62) (hC : IsCover C 14 8),
    1167018 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_62_14_8
#print axioms CoveringDesigns.PairConsequences.lower_bound_62_14_8

#check (@CoveringDesigns.PairConsequences.indexed_lower_71_19_8 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 71) (hB : Multicover.IsCover B 19 8 1),
    164754 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_71_19_8
#print axioms CoveringDesigns.PairConsequences.indexed_lower_71_19_8

#check (@CoveringDesigns.PairConsequences.lower_bound_71_19_8 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 71) (hC : IsCover C 19 8),
    164754 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_71_19_8
#print axioms CoveringDesigns.PairConsequences.lower_bound_71_19_8

#check (@CoveringDesigns.PairConsequences.indexed_lower_76_20_8 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 76) (hB : Multicover.IsCover B 20 8 1),
    175321 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_76_20_8
#print axioms CoveringDesigns.PairConsequences.indexed_lower_76_20_8

#check (@CoveringDesigns.PairConsequences.lower_bound_76_20_8 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 76) (hC : IsCover C 20 8),
    175321 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_76_20_8
#print axioms CoveringDesigns.PairConsequences.lower_bound_76_20_8

#check (@CoveringDesigns.PairConsequences.indexed_lower_84_19_8 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 84) (hB : Multicover.IsCover B 19 8 1),
    645178 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_84_19_8
#print axioms CoveringDesigns.PairConsequences.indexed_lower_84_19_8

#check (@CoveringDesigns.PairConsequences.lower_bound_84_19_8 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 84) (hC : IsCover C 19 8),
    645178 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_84_19_8
#print axioms CoveringDesigns.PairConsequences.lower_bound_84_19_8

#check (@CoveringDesigns.PairConsequences.indexed_lower_86_22_8 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 86) (hB : Multicover.IsCover B 22 8 1),
    195979 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_86_22_8
#print axioms CoveringDesigns.PairConsequences.indexed_lower_86_22_8

#check (@CoveringDesigns.PairConsequences.lower_bound_86_22_8 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 86) (hC : IsCover C 22 8),
    195979 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_86_22_8
#print axioms CoveringDesigns.PairConsequences.lower_bound_86_22_8

#check (@CoveringDesigns.PairConsequences.indexed_lower_90_20_8 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 90) (hB : Multicover.IsCover B 20 8 1),
    692001 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_90_20_8
#print axioms CoveringDesigns.PairConsequences.indexed_lower_90_20_8

#check (@CoveringDesigns.PairConsequences.lower_bound_90_20_8 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 90) (hC : IsCover C 20 8),
    692001 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_90_20_8
#print axioms CoveringDesigns.PairConsequences.lower_bound_90_20_8

#check (@CoveringDesigns.PairConsequences.indexed_lower_91_23_8 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 91) (hB : Multicover.IsCover B 23 8 1),
    206210 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_91_23_8
#print axioms CoveringDesigns.PairConsequences.indexed_lower_91_23_8

#check (@CoveringDesigns.PairConsequences.lower_bound_91_23_8 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 91) (hC : IsCover C 23 8),
    206210 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_91_23_8
#print axioms CoveringDesigns.PairConsequences.lower_bound_91_23_8

#check (@CoveringDesigns.PairConsequences.indexed_lower_96_16_8 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 96) (hB : Multicover.IsCover B 16 8 1),
    10537404 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_96_16_8
#print axioms CoveringDesigns.PairConsequences.indexed_lower_96_16_8

#check (@CoveringDesigns.PairConsequences.lower_bound_96_16_8 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 96) (hC : IsCover C 16 8),
    10537404 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_96_16_8
#print axioms CoveringDesigns.PairConsequences.lower_bound_96_16_8

#check (@CoveringDesigns.PairConsequences.indexed_lower_96_21_8 :
∀ {I X : Type*} [Fintype I]
    [Fintype X] [DecidableEq X] {B : I → Finset X}
    (hv : Fintype.card X = 96) (hB : Multicover.IsCover B 21 8 1),
    736010 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.PairConsequences.indexed_lower_96_21_8
#print axioms CoveringDesigns.PairConsequences.indexed_lower_96_21_8

#check (@CoveringDesigns.PairConsequences.lower_bound_96_21_8 :
∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 96) (hC : IsCover C 21 8),
    736010 ≤ C.card)
#guard_standard_axioms CoveringDesigns.PairConsequences.lower_bound_96_21_8
#print axioms CoveringDesigns.PairConsequences.lower_bound_96_21_8

end CoveringDesigns.AuditPairConsequences
