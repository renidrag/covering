import CoveringDesigns.QuadrupleAssembly.Substitution
import CoveringDesigns.QuadrupleAssembly.Transport
import Mathlib.Data.Finset.Sort

namespace CoveringDesigns.QuadrupleAssembly
open Finset

/-- Increasing local-to-master map, with the coordinate in a fibre unchanged. -/
def blockLift {β A : Type*} [LinearOrder β] (B : Finset β) :
    (Fin B.card × A) ↪ (β × A) :=
  (B.orderEmbOfFin rfl).toEmbedding.prodMap (Function.Embedding.refl A)

def replaceBlock {β A : Type*} [LinearOrder β] [DecidableEq A]
    (template : (n : ℕ) → Family (Fin n × A)) (B : Finset β) : Family (β × A) :=
  (template B.card).image (fun D => D.map (blockLift B))

def productSubstitute {β A : Type*} [LinearOrder β] [DecidableEq A]
    (M : Family β) (template : (n : ℕ) → Family (Fin n × A)) : Family (β × A) :=
  M.biUnion (replaceBlock template)

/-- One structural substitution covers H-design substitution, binary inflation,
Latin triple inflation and the 4-GDD substitution used in the retained chains. -/
theorem productSubstitute_valid {β A γ : Type*} [LinearOrder β] [DecidableEq A]
    (g : β → γ) {k t : ℕ} {M : Family β} (hM : Master g t M)
    (template : (n : ℕ) → Family (Fin n × A))
    (hT : ∀ B ∈ M, GroupDesign Prod.fst k t (template B.card)) :
    GroupDesign (fun p : β × A => g p.1) k t (productSubstitute M template) := by
  apply substitute Prod.fst g hM
  intro B hB
  apply patch_of_embedding Prod.fst B (blockLift B) Prod.fst
    (B.orderEmbOfFin rfl).toEmbedding (fun _ => rfl) _ (hT B hB)
  rintro ⟨b,a⟩
  constructor
  · intro hb
    refine ⟨((B.orderIsoOfFin rfl).symm ⟨b,hb⟩,a),?_⟩
    apply Prod.ext
    · change ((B.orderIsoOfFin rfl) ((B.orderIsoOfFin rfl).symm ⟨b,hb⟩)).val = b
      simp
    · rfl
  · rintro ⟨⟨i,c⟩,he⟩
    have hmem := B.orderEmbOfFin_mem rfl i
    have he' := congrArg Prod.fst he
    change B.orderEmbOfFin rfl i = b at he'
    simpa only [he'] using hmem

end CoveringDesigns.QuadrupleAssembly
