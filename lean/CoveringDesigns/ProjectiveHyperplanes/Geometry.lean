import CoveringDesigns.ProjectiveHyperplanes.Points

/-! Reusable projective hyperplane geometry and the actual distinct-block family.
GKP §III, attributed there to Ray–Chaudhuri. Formalisation: Rob Gardiner. -/
namespace CoveringDesigns.ProjectiveHyperplanes
open Finset Module
open scoped LinearAlgebra.Projectivization

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem functional_mk_liesIn (f : Module.Dual F V) (x : V) (hx : x ≠ 0) :
    LiesIn (Projectivization.mk F x hx) (LinearMap.ker f) ↔ f x = 0 :=
  mk_liesIn _ x hx

/-- Explicit invariance under nonzero rescaling of either equation or vector. -/
theorem rescale_incidence (f : Module.Dual F V) (x : V) (a b : F)
    (ha : a ≠ 0) (hb : b ≠ 0) : (a • f) (b • x) = 0 ↔ f x = 0 := by
  simp [ha, hb]

theorem kernel_mk_rep (f : Module.Dual F V) (hf : f ≠ 0) :
    LinearMap.ker (Projectivization.mk F f hf).rep = LinearMap.ker f := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep F f hf
  ext x
  rw [LinearMap.mem_ker, ← ha]
  simp [Units.smul_def, a.ne_zero]

/-- Equal kernels force the same dual projective direction. -/
theorem dual_eq_of_kernel_eq (p r : ℙ F (Module.Dual F V))
    (h : LinearMap.ker p.rep = LinearMap.ker r.rep) : p = r := by
  have hs : r.rep ∈ Submodule.span F ({p.rep} : Set (Module.Dual F V)) := by
    have hh := mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => p.rep) (K := r.rep)
      (by simpa using h.le)
    simpa using hh
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hs
  have he := (Projectivization.mk_eq_mk_iff' F r.rep p.rep
    r.rep_nonzero p.rep_nonzero).mpr ⟨a, ha⟩
  simpa only [Projectivization.mk_rep] using he.symm

/-- Span version: dependent sets are allowed, even when their cardinality is large. -/
theorem exists_annihilating_of_span_lt [FiniteDimensional F V] [DecidableEq V]
    (T : Finset (ℙ F V))
    (hT : finrank F (Submodule.span F
      ((T.image Projectivization.rep : Finset V) : Set V)) < finrank F V) :
    ∃ d : ℙ F (Module.Dual F V), ∀ p ∈ T, LiesIn p (LinearMap.ker d.rep) := by
  classical
  let R := T.image Projectivization.rep
  let W := Submodule.span F (R : Set V)
  obtain ⟨f, hf, hkill⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (Submodule.lt_top_of_finrank_lt_finrank hT)
    (inferInstance : Module.Projective F (V ⧸ W))
  refine ⟨Projectivization.mk F f hf, ?_⟩
  intro p hp
  rw [kernel_mk_rep, liesIn_iff_rep, LinearMap.mem_ker]
  have hmem : f p.rep ∈ W.map f := Submodule.mem_map.mpr
    ⟨p.rep, Submodule.subset_span (mem_image.mpr ⟨p, hp, rfl⟩), rfl⟩
  change W.map f = ⊥ at hkill
  rwa [hkill, Submodule.mem_bot] at hmem

/-- At most dimension-minus-one points have a proper span; independence is unnecessary. -/
theorem exists_annihilating_direction [FiniteDimensional F V]
    (T : Finset (ℙ F V)) (hT : T.card < finrank F V) :
    ∃ d : ℙ F (Module.Dual F V), ∀ p ∈ T, LiesIn p (LinearMap.ker d.rep) := by
  classical
  apply exists_annihilating_of_span_lt T
  calc
    _ ≤ (T.image Projectivization.rep).card := finrank_span_finset_le_card _
    _ ≤ T.card := card_image_le
    _ < finrank F V := hT

abbrev Direction (F : Type*) [Field F] (n : ℕ) := AffineConstructions.Direction F n

/-- A hyperplane is the finite point set of the representative functional's kernel. -/
noncomputable def hyperplane [Fintype F] {n : ℕ} (d : Direction F n) :
    Finset (Point F n) := points (LinearMap.ker d.rep)

theorem mem_hyperplane [Fintype F] {n : ℕ} (d : Direction F n) (p : Point F n) :
    p ∈ hyperplane d ↔ d.rep p.rep = 0 := by
  simp only [hyperplane, mem_points, liesIn_iff_rep, LinearMap.mem_ker]

theorem hyperplane_mk [Fintype F] {n : ℕ} (f : Module.Dual F (Fin n → F))
    (hf : f ≠ 0) (x : Fin n → F) (hx : x ≠ 0) :
    Projectivization.mk F x hx ∈ hyperplane (Projectivization.mk F f hf) ↔ f x = 0 := by
  rw [hyperplane, kernel_mk_rep, mem_points, functional_mk_liesIn]

theorem kernel_finrank [Fintype F] {m : ℕ} (d : Direction F (m+1)) :
    finrank F (LinearMap.ker d.rep) = m := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero d.rep_nonzero
  simpa using h

theorem hyperplane_card [Fintype F] {m : ℕ} (d : Direction F (m+1)) :
    (hyperplane d).card = G (Fintype.card F) m := by
  rw [hyperplane, points_card, kernel_finrank]

theorem direction_card (F : Type*) [Field F] [Fintype F] (n : ℕ) :
    Nat.card (Direction F n) = G (Fintype.card F) n := by
  rw [AffineConstructions.direction_card]
  exact (AffineSchoenheim.geom_quotient (show 2 ≤ Fintype.card F from Fintype.one_lt_card) n).symm

theorem hyperplane_injective [Fintype F] (n : ℕ) :
    Function.Injective (hyperplane (F := F) (n := n)) := by
  intro d e h
  exact dual_eq_of_kernel_eq d e (points_injective h)

/-- Covers all sets of at most m points, without any independence assumption. -/
theorem hyperplanes_cover [Fintype F] {m : ℕ} (T : Finset (Point F (m+1)))
    (hT : T.card ≤ m) : ∃ d : Direction F (m+1), T ⊆ hyperplane d := by
  obtain ⟨d, hd⟩ := exists_annihilating_direction T (by simpa using Nat.lt_succ_of_le hT)
  exact ⟨d, fun p hp => (mem_points _ _).mpr (hd p hp)⟩

/-- Finite image, so its elements are actual distinct ordinary blocks. -/
noncomputable def family (F : Type*) [Field F] [Fintype F] (m : ℕ) :
    Family (Point F (m+1)) := by
  classical
  have : Finite (Module.Dual F (Fin (m+1) → F)) := Module.finite_of_finite F
  let _ := Fintype.ofFinite (Direction F (m+1))
  exact univ.image hyperplane

theorem family_card (F : Type*) [Field F] [Fintype F] (m : ℕ) :
    (family F m).card = G (Fintype.card F) (m+1) := by
  classical
  have : Finite (Module.Dual F (Fin (m+1) → F)) := Module.finite_of_finite F
  let _ := Fintype.ofFinite (Direction F (m+1))
  rw [family, card_image_of_injective _ (hyperplane_injective _), card_univ,
    ← Nat.card_eq_fintype_card, direction_card]

theorem family_isCover (F : Type*) [Field F] [Fintype F] (m : ℕ) :
    IsCover (family F m) (G (Fintype.card F) m) m := by
  classical
  have : Finite (Module.Dual F (Fin (m+1) → F)) := Module.finite_of_finite F
  let _ := Fintype.ofFinite (Direction F (m+1))
  constructor
  · intro B hB
    obtain ⟨d, _, rfl⟩ := mem_image.mp hB
    exact hyperplane_card d
  · intro T hT
    obtain ⟨d, hd⟩ := hyperplanes_cover T hT.le
    exact ⟨hyperplane d, mem_image.mpr ⟨d, mem_univ _, rfl⟩, hd⟩

theorem empty_covered (F : Type*) [Field F] [Fintype F] (m : ℕ) :
    ∃ d : Direction F (m+1), (∅ : Finset (Point F (m+1))) ⊆ hyperplane d :=
  hyperplanes_cover ∅ (by simp)

end CoveringDesigns.ProjectiveHyperplanes
