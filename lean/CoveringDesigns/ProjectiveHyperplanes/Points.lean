import CoveringDesigns.AffineConstructions.Geometry
import CoveringDesigns.ProjectiveHyperplanes.GeometricSum

/-! Projective points of subspaces, without any covering optimality dependency.
GKP §III; supplied structural details/formalisation: Rob Gardiner. -/
namespace CoveringDesigns.ProjectiveHyperplanes
open Finset Module
open scoped LinearAlgebra.Projectivization

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Intrinsic incidence: the whole one-dimensional subspace lies in S. -/
def LiesIn (p : ℙ F V) (S : Submodule F V) : Prop := p.submodule ≤ S

theorem mk_liesIn (S : Submodule F V) (x : V) (hx : x ≠ 0) :
    LiesIn (Projectivization.mk F x hx) S ↔ x ∈ S := by
  simp [LiesIn, Submodule.span_singleton_le_iff_mem]

theorem liesIn_iff_rep (p : ℙ F V) (S : Submodule F V) :
    LiesIn p S ↔ p.rep ∈ S := by
  rw [← mk_liesIn S p.rep p.rep_nonzero, Projectivization.mk_rep]

/-- Inclusion of a subspace on projective points, with its intrinsic range. -/
noncomputable def subspacePointsEquiv (S : Submodule F V) :
    ℙ F S ≃ {p : ℙ F V // LiesIn p S} := by
  let f : ℙ F S → {p : ℙ F V // LiesIn p S} := fun p =>
    ⟨Projectivization.map S.subtype S.injective_subtype p, by
      induction p using Projectivization.ind with
      | h x hx =>
        rw [Projectivization.map_mk, mk_liesIn]
        exact x.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro p r h
    exact Projectivization.map_injective S.subtype S.injective_subtype
      (congrArg Subtype.val h)
  · intro p
    let x : S := ⟨p.val.rep, (liesIn_iff_rep p.val S).mp p.property⟩
    have hx : x ≠ 0 := by
      intro h
      exact p.val.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk F x hx, ?_⟩
    apply Subtype.ext
    exact p.val.mk_rep

/-- The actual finite point set of a subspace. -/
noncomputable def points [Finite V] (S : Submodule F V) : Finset (ℙ F V) := by
  classical
  let _ := Fintype.ofFinite (ℙ F V)
  exact univ.filter (fun p => LiesIn p S)

@[simp] theorem mem_points [Finite V] (S : Submodule F V) (p : ℙ F V) :
    p ∈ points S ↔ LiesIn p S := by
  classical
  simp [points]

theorem points_card [Fintype F] [Finite V] [FiniteDimensional F V]
    (S : Submodule F V) : (points S).card = G (Fintype.card F) (finrank F S) := by
  classical
  let _ := Fintype.ofFinite (ℙ F V)
  calc
    _ = Nat.card {p : ℙ F V // LiesIn p S} := by
      simp [points, Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card (ℙ F S) := (Nat.card_congr (subspacePointsEquiv S)).symm
    _ = _ := by
      rw [Projectivization.card_of_finrank F S rfl]
      simp [G, AffineSchoenheim.geom, Nat.card_eq_fintype_card]

/-- Recover a subspace from all of its projective points, including zero separately. -/
theorem points_injective [Finite V] : Function.Injective (points (F := F) (V := V)) := by
  intro S T h
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · simpa only [mem_points, mk_liesIn] using
      (show Projectivization.mk F x hx ∈ points S ↔
        Projectivization.mk F x hx ∈ points T by rw [h])

abbrev Point (F : Type*) [Field F] (n : ℕ) := ℙ F (Fin n → F)

theorem point_card (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    Nat.card (Point F n) = G (Fintype.card F) n := by
  rw [Projectivization.card_of_finrank F (Fin n → F) (n := n) (by simp)]
  simp [G, AffineSchoenheim.geom, Nat.card_eq_fintype_card]

end CoveringDesigns.ProjectiveHyperplanes
