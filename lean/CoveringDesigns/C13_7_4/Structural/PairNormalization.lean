import CoveringDesigns.C13_7_4.Structural.CoreAutomorphisms
import CoveringDesigns.C13_7_4.Structural.SwapObstruction

/-!
Prescribed translations of the four spouse indices normalize one spouse swap.
The index set is the affine plane with four points; translation fixes its
three parallel classes. A common Boolean flip chooses the foreign half.
Only identities of these eight explicit coordinate changes are checked here;
there is no search over automorphisms, completions, or coverings.
-/

namespace CoveringDesigns.C13Structural
open Finset
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

/-- Addition in the four-point affine plane, in its fixed labelling. -/
def indexTranslate (v w : Fin 4) : Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] v w

def normalizeTrace (v : Fin 4) (b : Bool) : TracePoint → TracePoint
  | Sum.inl m => Sum.inl m
  | Sum.inr (w, c) => Sum.inr (indexTranslate v w, Bool.xor b c)

theorem normalizeTrace_involutive : ∀ v b,
    Function.Involutive (normalizeTrace v b) := by
  unfold Function.Involutive
  decide +kernel

def traceNormalization (v : Fin 4) (b : Bool) : Equiv.Perm TracePoint :=
  { toFun := normalizeTrace v b
    invFun := normalizeTrace v b
    left_inv := normalizeTrace_involutive v b
    right_inv := normalizeTrace_involutive v b }

def pairNormalization (v : Fin 4) (b : Bool) : Equiv.Perm SwapPoint :=
  Equiv.sumCongr (Equiv.refl Bool) (traceNormalization v b)

@[simp] theorem traceNormalization_apply (v : Fin 4) (b : Bool) (x : TracePoint) :
    traceNormalization v b x = normalizeTrace v b x := rfl

@[simp] theorem traceNormalization_symm (v : Fin 4) (b : Bool) :
    (traceNormalization v b).symm = traceNormalization v b := rfl

@[simp] theorem pairNormalization_root (v : Fin 4) (b r : Bool) :
    pairNormalization v b (swapRoot r) = swapRoot r := rfl

@[simp] theorem pairNormalization_trace (v : Fin 4) (b : Bool) (x : TracePoint) :
    pairNormalization v b (Sum.inr x) = Sum.inr (normalizeTrace v b x) := rfl

theorem normalization_zero : ∀ v b,
    traceNormalization v b (Sum.inr (0, false)) = Sum.inr (v, b) := by decide +kernel

theorem normalization_zero_mate : ∀ v b,
    traceNormalization v b (Sum.inr (0, true)) = Sum.inr (v, !b) := by decide +kernel

theorem normalization_common : ∀ v b,
    relabel (traceNormalization v b) commonTraceFamily = commonTraceFamily := by decide +kernel

theorem normalization_private : ∀ v b,
    relabel (traceNormalization v b) privateTraceFamily = privateTraceFamily := by decide +kernel

theorem normalization_companions : ∀ v b,
    companions.map (traceNormalization v b).toEmbedding = companions := by decide +kernel

theorem normalization_transverse : ∀ v b,
    (transverse false).map (traceNormalization v b).toEmbedding = transverse b := by decide +kernel

/-- The arbitrary spouse swap is conjugate to the displayed swap at zero. -/
theorem normalization_conjugates_swap : ∀ v b x,
    normalizeTrace v b (swapTrace x) =
      Equiv.swap (Sum.inr (v, !b)) (Sum.inr (v, b)) (normalizeTrace v b x) := by
  decide +kernel

theorem normalization_foreign : ∀ v b,
    swappedForeignBlock.map (pairNormalization v b).toEmbedding =
      insert (swapRoot false) (insert (swapRoot true)
        ((insert (Sum.inr (v, !b)) (transverse b)).image Sum.inr)) := by decide +kernel

#guard_standard_axioms normalization_common normalization_private
  normalization_companions normalization_transverse normalization_conjugates_swap
  normalization_foreign

end CoveringDesigns.C13Structural
