import CoveringDesigns.QuadrupleAssembly.Contracts
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset

namespace CoveringDesigns.QuadrupleAssembly
open Finset
/-- A mixed-block exact transverse design, used only as a substitution master. -/
structure Master {α γ : Type*} (g : α → γ) (t : ℕ) (M : Family α) : Prop where
  transverse : ∀ B ∈ M, Transverse g B
  exact : ∀ T : Finset α, T.card = t → Transverse g T → ∃! B, B ∈ M ∧ T ⊆ B

theorem GroupDesign.master {α γ : Type*} {g : α → γ} {t k : ℕ} {M : Family α}
    (h : GroupDesign g k t M) : Master g t M := ⟨h.transverse,h.exact⟩

end CoveringDesigns.QuadrupleAssembly
