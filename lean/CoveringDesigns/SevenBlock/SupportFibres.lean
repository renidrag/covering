import CoveringDesigns.SevenBlock.Degrees
import CoveringDesigns.SevenBlock.Fano

/-! Support-fibre transport retains distinct actual point identities. -/
namespace CoveringDesigns.SevenBlock
open Finset

/-- Equal fibre cardinalities construct an actual point equivalence. No
injectivity of the support maps is required. -/
theorem support_fibre_isomorphism {V I W J : Type*}
    [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] [Fintype J] [DecidableEq J]
    (B : I → Finset V) (C : J → Finset W) (f : I ≃ J)
    (hc : ∀ T : Finset J,
      Fintype.card {x : V // (pointSupport B x).map f.toEmbedding = T} =
      Fintype.card {y : W // pointSupport C y = T}) : IndexedIsomorphic B C := by
  classical
  let g : V → Finset J := fun x => (pointSupport B x).map f.toEmbedding
  let h : W → Finset J := pointSupport C
  let fibres (T : Finset J) : {x : V // g x = T} ≃ {y : W // h y = T} :=
    Fintype.equivOfCardEq (hc T)
  let e : V ≃ W := (Equiv.sigmaFiberEquiv g).symm.trans
    ((Equiv.sigmaCongrRight fibres).trans (Equiv.sigmaFiberEquiv h))
  have he (x : V) : h (e x) = g x := (fibres (g x) ⟨x,rfl⟩).property
  refine ⟨e,f,?_⟩
  intro x i
  have hx := congrArg (fun T : Finset J => f i ∈ T) (he x)
  change (f i ∈ pointSupport C (e x)) =
    (f i ∈ (pointSupport B x).map f.toEmbedding) at hx
  simpa only [mem_pointSupport, mem_map_equiv,Equiv.symm_apply_apply] using (Iff.of_eq hx).symm

def fibreWeight {X : Type*} [Fintype X] (f : X → Fin 7) (l : Fin 7) : ℕ :=
  (univ.filter fun x => f x = l).card

theorem fibre_weight_sum {X : Type*} [Fintype X] (f : X → Fin 7) :
    ∑ l, fibreWeight f l = Fintype.card X := by
  simp only [fibreWeight,card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  simp

/-- The actual row degree is the sum of weights of its three Fano lines. -/
theorem fibre_weight_row {X I : Type*} [Fintype X] [Fintype I] [DecidableEq I]
    (S : X → Finset I) (e : I ≃ Fin 7) (f : X → Fin 7)
    (hf : ∀ x, (S x).map e.toEmbedding = line (f x)) (i : I) :
    (∑ l : Fin 7, if e i ∈ line l then fibreWeight f l else 0) = indexedDegree S i := by
  simp only [fibreWeight,card_eq_sum_ones,sum_filter,indexedDegree]
  have hc (l : Fin 7) :
      (if e i ∈ line l then ∑ x, if f x = l then 1 else 0 else 0) =
        ∑ x, if f x = l then (if e i ∈ line l then 1 else 0) else 0 := by
    by_cases h : e i ∈ line l <;> simp [h]
  simp_rw [hc]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  have hx : e i ∈ line (f x) ↔ i ∈ S x := by rw [← hf x]; simp
  simp [hx]

#guard_standard_axioms support_fibre_isomorphism fibre_weight_sum fibre_weight_row

end CoveringDesigns.SevenBlock
