import CoveringDesigns.AffineConstructions.Transformations
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness

/-! Affine hyperplanes indexed by projective directions in the dual space. -/

namespace CoveringDesigns.AffineConstructions

open Finset Module
open scoped LinearAlgebra.Projectivization

/-- A nonzero functional is constant on any nonempty set with at most
`finrank F V` points. The differences from one point span a proper subspace. -/
theorem exists_constant_functional {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (T : Finset V) (hpos : T.Nonempty)
    (hcard : T.card ≤ finrank F V) :
    ∃ f : Module.Dual F V, f ≠ 0 ∧ ∃ c : F, ∀ x ∈ T, f x = c := by
  classical
  obtain ⟨p, hp⟩ := hpos
  let D := (T.erase p).image (fun x => x-p)
  have hdim : finrank F (Submodule.span F (D : Set V)) < finrank F V := by
    calc
      _ ≤ D.card := finrank_span_finset_le_card D
      _ ≤ (T.erase p).card := card_image_le
      _ < T.card := card_erase_lt_of_mem hp
      _ ≤ finrank F V := hcard
  obtain ⟨f, hf, hkill⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (Submodule.lt_top_of_finrank_lt_finrank hdim) (inferInstance : Module.Projective F
      (V ⧸ Submodule.span F (D : Set V)))
  refine ⟨f, hf, f p, ?_⟩
  intro x hx
  by_cases hxp : x = p
  · simp [hxp]
  have hxD : x-p ∈ D := mem_image.mpr ⟨x, mem_erase.mpr ⟨hxp, hx⟩, rfl⟩
  have hmem : f (x-p) ∈ (Submodule.span F (D : Set V)).map f :=
    Submodule.mem_map.mpr ⟨x-p, Submodule.subset_span hxD, rfl⟩
  rw [hkill, Submodule.mem_bot] at hmem
  simpa [map_sub, sub_eq_zero] using hmem

noncomputable def functionalFiber {F V : Type*} [Field F] [AddCommGroup V]
    [Module F V] [Fintype V] (f : Module.Dual F V) (c : F) : Finset V :=
  @Finset.filter _ (fun x => f x = c) (Classical.decPred _) univ

/-- Fibres of a nonzero functional have the cardinality of its kernel. -/
theorem functional_fiber_card {F V : Type*} [Field F] [Fintype F]
    [AddCommGroup V] [Module F V] [Fintype V] [FiniteDimensional F V]
    (f : Module.Dual F V) (hf : f ≠ 0) (c : F) :
    (functionalFiber f c).card =
      Fintype.card F ^ (finrank F V - 1) := by
  classical
  obtain ⟨p, hp⟩ := LinearMap.surjective hf c
  let e : {x : V // f x = c} ≃ LinearMap.ker f :=
    { toFun := fun x => ⟨x.val-p, by simp [map_sub, x.property, hp]⟩
      invFun := fun y => ⟨y.val+p, by simp [map_add, hp]⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro y; ext; simp }
  have hr := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hdim : finrank F (LinearMap.ker f) = finrank F V - 1 := by omega
  calc
    _ = Nat.card {x : V // f x = c} := by
      simp [functionalFiber, Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card (LinearMap.ker f) := Nat.card_congr e
    _ = Nat.card F ^ finrank F (LinearMap.ker f) := Module.natCard_eq_pow_finrank
    _ = _ := by rw [hdim, Nat.card_eq_fintype_card]

/-- A direction is a projective class of nonzero linear functionals. -/
abbrev Direction (F : Type*) [Field F] (t : ℕ) := ℙ F (Module.Dual F (Fin t → F))

/-- One equation for every projective direction and every constant. -/
noncomputable def hyperplane {F : Type*} [Field F] [Fintype F] {t : ℕ}
    (p : Direction F t) (c : F) : Finset (Fin t → F) :=
  functionalFiber p.rep c

theorem affine_points_card (F : Type*) [Field F] [Fintype F] (t : ℕ) :
    Fintype.card (Fin t → F) = Fintype.card F ^ t := by simp

theorem direction_card (F : Type*) [Field F] [Fintype F] (t : ℕ) :
    Nat.card (Direction F t) = (Fintype.card F ^ t - 1) / (Fintype.card F - 1) := by
  rw [Projectivization.card'', Module.natCard_eq_pow_finrank (K := F)]
  simp [Subspace.dual_finrank_eq, Nat.card_eq_fintype_card]

theorem direction_count_exact (F : Type*) [Field F] [Fintype F] (t : ℕ) :
    Nat.card (Direction F t) * (Fintype.card F - 1) = Fintype.card F ^ t - 1 := by
  rw [direction_card]
  exact Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one _ _)

/-- Count indices, separately from counting distinct image blocks. -/
theorem hyperplane_indices_card (F : Type*) [Field F] [Fintype F] (t : ℕ) :
    Nat.card (Direction F t × F) =
      Fintype.card F * ((Fintype.card F ^ t - 1) / (Fintype.card F - 1)) := by
  rw [Nat.card_prod, direction_card, Nat.card_eq_fintype_card, Nat.mul_comm]

theorem hyperplane_card {F : Type*} [Field F] [Fintype F] {t : ℕ}
    (p : Direction F t) (c : F) :
    (hyperplane p c).card = Fintype.card F ^ (t-1) := by
  simpa [hyperplane] using functional_fiber_card p.rep p.rep_nonzero c

theorem hyperplanes_cover {F : Type*} [Field F] [Fintype F] {t : ℕ}
    (ht : 0 < t) (T : Finset (Fin t → F)) (hT : T.card = t) :
    ∃ p : Direction F t, ∃ c : F, T ⊆ hyperplane p c := by
  classical
  obtain ⟨f, hf, c, hc⟩ := exists_constant_functional (F := F) T
    (card_pos.mp (by omega)) (by simpa using hT.le)
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F f hf
  refine ⟨Projectivization.mk F f hf, (a : F)*c, ?_⟩
  intro x hx
  apply mem_filter.mpr
  refine ⟨mem_univ x, ?_⟩
  rw [← ha]
  simp [Units.smul_def, hc x hx]

/-- The classical affine hyperplane covering, as a distinct-block family.
Only an upper bound on the image cardinality is claimed. -/
theorem affine_cover (F : Type*) [Field F] [Fintype F] {t : ℕ} (ht : 0 < t) :
    ∃ C : Family (Fin t → F), IsCover C (Fintype.card F ^ (t-1)) t ∧
      C.card ≤ Fintype.card F * ((Fintype.card F ^ t - 1) / (Fintype.card F - 1)) := by
  classical
  have : Finite (Module.Dual F (Fin t → F)) := Module.finite_of_finite F
  let : Fintype (Direction F t) := Fintype.ofFinite _
  obtain ⟨C, hC, hn⟩ := exists_family_of_blocks
    (fun i : Direction F t × F => hyperplane i.1 i.2)
    (fun i => hyperplane_card i.1 i.2) (by
      intro T hT
      obtain ⟨p, c, h⟩ := hyperplanes_cover ht T hT
      exact ⟨(p,c), h⟩)
  refine ⟨C, hC, ?_⟩
  rwa [← Nat.card_eq_fintype_card, hyperplane_indices_card] at hn

end CoveringDesigns.AffineConstructions
