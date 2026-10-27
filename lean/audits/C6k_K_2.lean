import CoveringDesigns.C6k_K_2
import CoveringDesigns.Foundations.StandardAxioms

open Matrix
open scoped BigOperators

namespace CoveringDesigns.AuditC6k_K_2

theorem lower_explicit {X : Type*} [Fintype X] (k : ℕ) (hk : 6 ≤ k)
    (hv : Fintype.card X = 6*k) (C : Finset (Finset X))
    (hu : ∀ B ∈ C, B.card = k)
    (hc : ∀ T : Finset X, T.card = 2 → ∃ B ∈ C, T ⊆ B) : 43 ≤ C.card :=
  C6k_K_2.lower_bound hk hv ⟨hu, hc⟩
#guard_standard_axioms lower_explicit
#print axioms lower_explicit

theorem indexed_explicit {I X : Type*} [Fintype I] [Fintype X]
    (k : ℕ) (hk : 6 ≤ k) (hv : Fintype.card X = 6*k) (B : I → Finset X)
    (hu : ∀ i, (B i).card = k)
    (hc : ∀ T : Finset X, T.card = 2 → ∃ i, T ⊆ B i) : 43 ≤ Fintype.card I := by
  classical
  exact C6k_K_2.indexed_lower_bound hk hv ⟨hu, (Multicover.covers_one_iff B 2).mpr hc⟩
#guard_standard_axioms indexed_explicit
#print axioms indexed_explicit

#check (@CoveringDesigns.C6k_K_2.no_isotropic_half :
  ∀ (U : Submodule (ZMod 3) (Fin 42 → ZMod 3))
    (G : Matrix (Fin 42) (Fin 42) (ZMod 3)), G.IsSymm → G.det = 1 →
    Module.finrank (ZMod 3) U = 21 →
    (∀ x ∈ U, ∀ y ∈ U, x ⬝ᵥ (G *ᵥ y) = 0) → False)
#guard_standard_axioms CoveringDesigns.C6k_K_2.no_isotropic_half
#print axioms CoveringDesigns.C6k_K_2.no_isotropic_half

#check (@CoveringDesigns.C6k_K_2.kernel_totally_isotropic :
  ∀ {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    {p : ℕ} [Fact (Nat.Prime p)] {a : ℤ} (B : Matrix S T ℤ),
    (¬ (p : ℤ) ∣ a) →
    B.transpose * B = ((p : ℤ)*a) • 1 + Matrix.of (fun (_ _ : T) => (1 : ℤ)) →
    ∀ (x y : T → ZMod p),
    (B.map (Int.castRingHom (ZMod p))) *ᵥ x = 0 →
    (B.map (Int.castRingHom (ZMod p))) *ᵥ y = 0 → x ⬝ᵥ y = 0)
#guard_standard_axioms CoveringDesigns.C6k_K_2.kernel_totally_isotropic
#print axioms CoveringDesigns.C6k_K_2.kernel_totally_isotropic

#check (@CoveringDesigns.C6k_K_2.isotropic_finrank_le :
  ∀ {K T : Type*} [Field K] [Fintype T] (U : Submodule K (T → K)),
    (∀ x ∈ U, ∀ y ∈ U, x ⬝ᵥ y = 0) → 2 * Module.finrank K U ≤ Fintype.card T)
#guard_standard_axioms CoveringDesigns.C6k_K_2.isotropic_finrank_le
#print axioms CoveringDesigns.C6k_K_2.isotropic_finrank_le

#check (@CoveringDesigns.C6k_K_2.coordinateSum :
  ∀ {K T : Type*} [Field K] [Fintype T], (T → K) →ₗ[K] K)
#guard_standard_axioms CoveringDesigns.C6k_K_2.coordinateSum
#print axioms CoveringDesigns.C6k_K_2.coordinateSum

#check (@CoveringDesigns.C6k_K_2.sum_zero_isotropic_finrank_le :
  ∀ {T : Type*} [Fintype T], Fintype.card T = 43 →
    ∀ (U : Submodule (ZMod 3) (T → ZMod 3)),
    (∀ x ∈ U, ∑ i, x i = 0) → (∀ x ∈ U, ∀ y ∈ U, x ⬝ᵥ y = 0) →
    Module.finrank (ZMod 3) U ≤ 20)
#guard_standard_axioms CoveringDesigns.C6k_K_2.sum_zero_isotropic_finrank_le
#print axioms CoveringDesigns.C6k_K_2.sum_zero_isotropic_finrank_le

#check (@CoveringDesigns.C6k_K_2.no_order_six_matrix :
  ∀ {L T : Type*} [Fintype L] [Fintype T] [DecidableEq L] [DecidableEq T],
    Fintype.card L = 43 → Fintype.card T = 43 → ∀ (A : Matrix L T ℤ),
    (∀ l, ∑ t, A l t = 7) →
    A * A.transpose = (6 : ℤ) • 1 + Matrix.of (fun (_ _ : L) => (1 : ℤ)) →
    A.transpose * A = (6 : ℤ) • 1 + Matrix.of (fun (_ _ : T) => (1 : ℤ)) → False)
#guard_standard_axioms CoveringDesigns.C6k_K_2.no_order_six_matrix
#print axioms CoveringDesigns.C6k_K_2.no_order_six_matrix

#check (@CoveringDesigns.C6k_K_2.no_plane_six :
  ∀ {I : Type*} [Fintype I] [DecidableEq I],
    TruncatedPlaneLoads.Plane 6 I (Fin 7) → False)
#guard_standard_axioms CoveringDesigns.C6k_K_2.no_plane_six
#print axioms CoveringDesigns.C6k_K_2.no_plane_six

#check (@CoveringDesigns.C6k_K_2.indexed_lower_bound :
  ∀ {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    {k : ℕ} {B : I → Finset X}, 6 ≤ k → Fintype.card X = 6*k →
    Multicover.IsCover B k 2 1 → 43 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_bound
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_bound

#check (@CoveringDesigns.C6k_K_2.lower_bound :
  ∀ {X : Type*} [Fintype X] {C : Family X} {k : ℕ},
    6 ≤ k → Fintype.card X = 6*k → IsCover C k 2 → 43 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound
#print axioms CoveringDesigns.C6k_K_2.lower_bound

#check (@CoveringDesigns.C6k_K_2.completedLine :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    P.core ⊕ Fin 7 → Finset (Option I))
#guard_standard_axioms CoveringDesigns.C6k_K_2.completedLine
#print axioms CoveringDesigns.C6k_K_2.completedLine

#check (@CoveringDesigns.C6k_K_2.completed_points_card :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    Fintype.card (Option I) = 43)
#guard_standard_axioms CoveringDesigns.C6k_K_2.completed_points_card
#print axioms CoveringDesigns.C6k_K_2.completed_points_card

#check (@CoveringDesigns.C6k_K_2.completed_lines_card :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    Fintype.card (P.core ⊕ Fin 7) = 43)
#guard_standard_axioms CoveringDesigns.C6k_K_2.completed_lines_card
#print axioms CoveringDesigns.C6k_K_2.completed_lines_card

#check (@CoveringDesigns.C6k_K_2.completed_line_size :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    ∀ l : P.core ⊕ Fin 7, (C6k_K_2.completedLine P l).card = 7)
#guard_standard_axioms CoveringDesigns.C6k_K_2.completed_line_size
#print axioms CoveringDesigns.C6k_K_2.completed_line_size

#check (@CoveringDesigns.C6k_K_2.completed_intersection :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    ∀ l m : P.core ⊕ Fin 7, l ≠ m →
    (C6k_K_2.completedLine P l ∩ C6k_K_2.completedLine P m).card = 1)
#guard_standard_axioms CoveringDesigns.C6k_K_2.completed_intersection
#print axioms CoveringDesigns.C6k_K_2.completed_intersection

#check (@CoveringDesigns.C6k_K_2.completed_lines_injective :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    Function.Injective (C6k_K_2.completedLine P))
#guard_standard_axioms CoveringDesigns.C6k_K_2.completed_lines_injective
#print axioms CoveringDesigns.C6k_K_2.completed_lines_injective

#check (@CoveringDesigns.C6k_K_2.completed_degree :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    ∀ x : Option I, (Finset.univ.filter (fun l => x ∈ C6k_K_2.completedLine P l)).card = 7)
#guard_standard_axioms CoveringDesigns.C6k_K_2.completed_degree
#print axioms CoveringDesigns.C6k_K_2.completed_degree

#check (@CoveringDesigns.C6k_K_2.completed_codegree :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    ∀ x y : Option I, x ≠ y →
    (Finset.univ.filter (fun l => x ∈ C6k_K_2.completedLine P l ∧ y ∈ C6k_K_2.completedLine P l)).card = 1)
#guard_standard_axioms CoveringDesigns.C6k_K_2.completed_codegree
#print axioms CoveringDesigns.C6k_K_2.completed_codegree

#check (@CoveringDesigns.C6k_K_2.completedIncidence :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    Matrix (P.core ⊕ Fin 7) (Option I) ℤ)
#guard_standard_axioms CoveringDesigns.C6k_K_2.completedIncidence
#print axioms CoveringDesigns.C6k_K_2.completedIncidence

#check (@CoveringDesigns.C6k_K_2.completed_row_sum :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    ∀ l : P.core ⊕ Fin 7, ∑ x, C6k_K_2.completedIncidence P l x = 7)
#guard_standard_axioms CoveringDesigns.C6k_K_2.completed_row_sum
#print axioms CoveringDesigns.C6k_K_2.completed_row_sum

#check (@CoveringDesigns.C6k_K_2.completed_row_gram :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    C6k_K_2.completedIncidence P * (C6k_K_2.completedIncidence P).transpose =
    (6 : ℤ) • 1 + Matrix.of (fun (_ _ : P.core ⊕ Fin 7) => (1 : ℤ)))
#guard_standard_axioms CoveringDesigns.C6k_K_2.completed_row_gram
#print axioms CoveringDesigns.C6k_K_2.completed_row_gram

#check (@CoveringDesigns.C6k_K_2.completed_column_gram :
  ∀ {I : Type*} [Fintype I] [DecidableEq I]
    (P : TruncatedPlaneLoads.Plane 6 I (Fin 7)),
    (C6k_K_2.completedIncidence P).transpose * C6k_K_2.completedIncidence P =
    (6 : ℤ) • 1 + Matrix.of (fun (_ _ : Option I) => (1 : ℤ)))
#guard_standard_axioms CoveringDesigns.C6k_K_2.completed_column_gram
#print axioms CoveringDesigns.C6k_K_2.completed_column_gram

#check (@CoveringDesigns.C6k_K_2.indexed_lower_36_6_2 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 36)
    (hB : Multicover.IsCover B 6 2 1), 43 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_36_6_2
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_36_6_2

#check (@CoveringDesigns.C6k_K_2.lower_bound_36_6_2 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 36) (hC : IsCover C 6 2), 43 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_36_6_2
#print axioms CoveringDesigns.C6k_K_2.lower_bound_36_6_2

#check (@CoveringDesigns.C6k_K_2.indexed_lower_72_12_2 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 72)
    (hB : Multicover.IsCover B 12 2 1), 43 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_72_12_2
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_72_12_2

#check (@CoveringDesigns.C6k_K_2.lower_bound_72_12_2 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 72) (hC : IsCover C 12 2), 43 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_72_12_2
#print axioms CoveringDesigns.C6k_K_2.lower_bound_72_12_2

#check (@CoveringDesigns.C6k_K_2.indexed_lower_37_7_3 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 37)
    (hB : Multicover.IsCover B 7 3 1), 228 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_37_7_3
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_37_7_3

#check (@CoveringDesigns.C6k_K_2.lower_bound_37_7_3 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 37) (hC : IsCover C 7 3), 228 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_37_7_3
#print axioms CoveringDesigns.C6k_K_2.lower_bound_37_7_3

#check (@CoveringDesigns.C6k_K_2.indexed_lower_73_13_3 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 73)
    (hB : Multicover.IsCover B 13 3 1), 242 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_73_13_3
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_73_13_3

#check (@CoveringDesigns.C6k_K_2.lower_bound_73_13_3 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 73) (hC : IsCover C 13 3), 242 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_73_13_3
#print axioms CoveringDesigns.C6k_K_2.lower_bound_73_13_3

#check (@CoveringDesigns.C6k_K_2.indexed_lower_38_8_4 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 38)
    (hB : Multicover.IsCover B 8 4 1), 1083 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_38_8_4
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_38_8_4

#check (@CoveringDesigns.C6k_K_2.lower_bound_38_8_4 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 38) (hC : IsCover C 8 4), 1083 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_38_8_4
#print axioms CoveringDesigns.C6k_K_2.lower_bound_38_8_4

#check (@CoveringDesigns.C6k_K_2.indexed_lower_74_14_4 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 74)
    (hB : Multicover.IsCover B 14 4 1), 1280 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_74_14_4
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_74_14_4

#check (@CoveringDesigns.C6k_K_2.lower_bound_74_14_4 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 74) (hC : IsCover C 14 4), 1280 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_74_14_4
#print axioms CoveringDesigns.C6k_K_2.lower_bound_74_14_4

#check (@CoveringDesigns.C6k_K_2.indexed_lower_39_9_5 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 39)
    (hB : Multicover.IsCover B 9 5 1), 4693 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_39_9_5
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_39_9_5

#check (@CoveringDesigns.C6k_K_2.lower_bound_39_9_5 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 39) (hC : IsCover C 9 5), 4693 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_39_9_5
#print axioms CoveringDesigns.C6k_K_2.lower_bound_39_9_5

#check (@CoveringDesigns.C6k_K_2.indexed_lower_75_15_5 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 75)
    (hB : Multicover.IsCover B 15 5 1), 6400 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_75_15_5
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_75_15_5

#check (@CoveringDesigns.C6k_K_2.lower_bound_75_15_5 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 75) (hC : IsCover C 15 5), 6400 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_75_15_5
#print axioms CoveringDesigns.C6k_K_2.lower_bound_75_15_5

#check (@CoveringDesigns.C6k_K_2.indexed_lower_40_10_6 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 40)
    (hB : Multicover.IsCover B 10 6 1), 18772 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_40_10_6
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_40_10_6

#check (@CoveringDesigns.C6k_K_2.lower_bound_40_10_6 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 40) (hC : IsCover C 10 6), 18772 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_40_10_6
#print axioms CoveringDesigns.C6k_K_2.lower_bound_40_10_6

#check (@CoveringDesigns.C6k_K_2.indexed_lower_76_16_6 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 76)
    (hB : Multicover.IsCover B 16 6 1), 30400 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_76_16_6
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_76_16_6

#check (@CoveringDesigns.C6k_K_2.lower_bound_76_16_6 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 76) (hC : IsCover C 16 6), 30400 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_76_16_6
#print axioms CoveringDesigns.C6k_K_2.lower_bound_76_16_6

#check (@CoveringDesigns.C6k_K_2.indexed_lower_41_11_7 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 41)
    (hB : Multicover.IsCover B 11 7 1), 69969 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_41_11_7
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_41_11_7

#check (@CoveringDesigns.C6k_K_2.lower_bound_41_11_7 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 41) (hC : IsCover C 11 7), 69969 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_41_11_7
#print axioms CoveringDesigns.C6k_K_2.lower_bound_41_11_7

#check (@CoveringDesigns.C6k_K_2.indexed_lower_77_17_7 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 77)
    (hB : Multicover.IsCover B 17 7 1), 137695 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_77_17_7
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_77_17_7

#check (@CoveringDesigns.C6k_K_2.lower_bound_77_17_7 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 77) (hC : IsCover C 17 7), 137695 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_77_17_7
#print axioms CoveringDesigns.C6k_K_2.lower_bound_77_17_7

#check (@CoveringDesigns.C6k_K_2.indexed_lower_42_12_8 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 42)
    (hB : Multicover.IsCover B 12 8 1), 244892 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_42_12_8
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_42_12_8

#check (@CoveringDesigns.C6k_K_2.lower_bound_42_12_8 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 42) (hC : IsCover C 12 8), 244892 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_42_12_8
#print axioms CoveringDesigns.C6k_K_2.lower_bound_42_12_8

#check (@CoveringDesigns.C6k_K_2.indexed_lower_78_18_8 :
  ∀ {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]
    {B : I → Finset X} (hv : Fintype.card X = 78)
    (hB : Multicover.IsCover B 18 8 1), 596679 ≤ Fintype.card I)
#guard_standard_axioms CoveringDesigns.C6k_K_2.indexed_lower_78_18_8
#print axioms CoveringDesigns.C6k_K_2.indexed_lower_78_18_8

#check (@CoveringDesigns.C6k_K_2.lower_bound_78_18_8 :
  ∀ {X : Type*} [Fintype X] {C : Family X}
    (hv : Fintype.card X = 78) (hC : IsCover C 18 8), 596679 ≤ C.card)
#guard_standard_axioms CoveringDesigns.C6k_K_2.lower_bound_78_18_8
#print axioms CoveringDesigns.C6k_K_2.lower_bound_78_18_8

end CoveringDesigns.AuditC6k_K_2
