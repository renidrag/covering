import CoveringDesigns.Foundations.Relabelling
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma

/-! Precise finite inputs for the directly proved even-case HMM adaptation.
No cross-seed symmetry or compatibility is required. -/

namespace CoveringDesigns.QuadrupleAssembly
open Finset

abbrev Group (u : ℕ) := Fin u × Fin 2
abbrev Core (u : ℕ) := Group u × Fin 6
abbrev Point (u : ℕ) := Option (Core u)
abbrev Local := Option (Fin 2 × Fin 6)

def hole {u : ℕ} (p : Core u) : Fin u := p.1.1

def Transverse {α γ : Type*} (group : α → γ) (T : Finset α) : Prop :=
  Set.InjOn group (T : Set α)

/-- Exact transverse incidence; ordinary blocks retain their point identities. -/
structure GroupDesign {α γ : Type*} (group : α → γ)
    (k t : ℕ) (C : Family α) : Prop where
  uniform : Uniform C k
  transverse : ∀ B ∈ C, Transverse group B
  exact : ∀ T : Finset α, T.card = t → Transverse group T →
    ∃! B : Finset α, B ∈ C ∧ T ⊆ B

abbrev HSeed {u : ℕ} (H : Family (Core u)) := GroupDesign Prod.fst 4 3 H
abbrev GDDSeed {u : ℕ} (G : Family (Core u)) := GroupDesign hole 3 2 G

/-- Five perfect matchings partition all local pairs. No relation to H or GDD. -/
structure Factors (F : Fin 5 → Family (Fin 6)) : Prop where
  uniform : ∀ r, Uniform (F r) 2
  partition : ∀ r x, ∃! E : Finset (Fin 6), E ∈ F r ∧ x ∈ E
  pairs : ∀ E : Finset (Fin 6), E.card = 2 → ∃! r : Fin 5, E ∈ F r

def coreEquiv (u : ℕ) : Core u ≃ Fin (12*u) :=
  ((Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin 6))).trans
    finProdFinEquiv).trans (finCongr (by omega))

def labelEquiv (u : ℕ) : Point u ≃ Fin (12*u+1) :=
  (Equiv.optionCongr (coreEquiv u)).trans finSuccEquivLast.symm

def localEquiv : Local ≃ Fin 13 :=
  (Equiv.optionCongr finProdFinEquiv).trans finSuccEquivLast.symm

def coreEmbedding (u : ℕ) : Core u ↪ Point u :=
  ⟨some, Option.some_injective _⟩

def holeEmbedding {u : ℕ} (h : Fin u) : Local ↪ Point u where
  toFun := fun x => x.map (fun p => ((h,p.1),p.2))
  inj' := by
    intro x y hxy
    cases x <;> cases y <;> simp_all
    exact Prod.ext hxy.1 hxy.2

def groupEmbedding {u : ℕ} (g : Group u) : Fin 6 ↪ Point u where
  toFun := fun x => some (g,x)
  inj' := by intro x y h; simpa using h

@[simp] theorem card_point (u : ℕ) : Fintype.card (Point u) = 12*u+1 := by
  simp [Point, Core, Group]
  omega

@[simp] theorem label_none (u : ℕ) : labelEquiv u none = Fin.last (12*u) := rfl

/-- The exact labels used in the distributed JSON, not an opaque cardinality transport. -/
theorem label_some {u : ℕ} (h : Fin u) (b : Fin 2) (i : Fin 6) :
    (labelEquiv u (some ((h,b),i))).val = 12*h.val+6*b.val+i.val := by
  simp [labelEquiv, coreEquiv, finProdFinEquiv, finSuccEquivLast_symm_some]
  omega

end CoveringDesigns.QuadrupleAssembly
