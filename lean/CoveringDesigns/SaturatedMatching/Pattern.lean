import CoveringDesigns.BoundaryRank.IndexedIncidence
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Finite indexed matching patterns. Named supporting occurrences remain
distinct even when the ambient block map has repeated values.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset
variable {α ι M : Type*} [Fintype α] [Fintype ι] [Fintype M]
  [DecidableEq α] [DecidableEq ι] [DecidableEq M]

/-- An oriented matching of complementary actual supporting occurrences.
The off-diagonal sign is just a choice of endpoint label in the plus block.
The membership equation expresses own-pair containment and mutual separation. -/
structure Pattern (B : ι → Finset α) where
  point : M × Bool → α
  point_injective : Function.Injective point
  block : M × Bool → ι
  block_injective : Function.Injective block
  sign : M → M → Bool
  matched : ∀ e a f b, point (f,b) ∈ B (block (e,a)) ↔
    e = f ∨ b = (a == sign e f)
  outside : ∀ x, (∀ e b, x ≠ point (e,b)) → ∀ e,
    (x ∈ B (block (e,true)) ↔ x ∉ B (block (e,false)))

namespace Pattern
variable {B : ι → Finset α} (P : Pattern (M := M) B)

def named : Finset ι := univ.image P.block
def free : Finset ι := univ \ P.named

theorem named_card : P.named.card = 2*Fintype.card M := by
  rw [named,card_image_of_injective _ P.block_injective]
  simp [Nat.mul_comm]

theorem free_card : P.free.card + 2*Fintype.card M = Fintype.card ι := by
  have hh := card_sdiff_add_card_eq_card (subset_univ P.named)
  simpa only [free,P.named_card,card_univ] using hh

/-- A complete occurrence partition for any natural-valued weight. -/
theorem sum_partition (w : ι → ℕ) :
    ∑ i, w i =
      (∑ e, (w (P.block (e,true)) + w (P.block (e,false)))) +
      ∑ i ∈ P.free, w i := by
  have hh := sum_sdiff (f := w) (subset_univ P.named)
  have hn : ∑ i ∈ P.named, w i = ∑ e, (w (P.block (e,true)) + w (P.block (e,false))) := by
    rw [named,sum_image]
    · simp only [Fintype.sum_prod_type,Fintype.sum_bool]
    · intro x _ y _ h; exact P.block_injective h
  change (∑ i ∈ P.free, w i) + (∑ i ∈ P.named, w i) = ∑ i, w i at hh
  rw [hn] at hh
  omega

theorem degree_named (f : M) (b : Bool) :
    ∑ e, ((if P.point (f,b) ∈ B (P.block (e,true)) then 1 else 0) +
      (if P.point (f,b) ∈ B (P.block (e,false)) then 1 else 0)) =
      Fintype.card M + 1 := by
  have he (e : M) :
      ((if P.point (f,b) ∈ B (P.block (e,true)) then 1 else 0) +
       (if P.point (f,b) ∈ B (P.block (e,false)) then 1 else 0)) =
      1 + if e = f then 1 else 0 := by
    simp only [P.matched]
    by_cases hef : e = f
    · simp [hef]
    · cases hs : P.sign e f <;> cases b <;> simp [hef,hs]
  simp_rw [he]
  simp [sum_add_distrib]

/-- The precise number of remaining occurrences of each matched endpoint. -/
theorem endpoint_degree (f : M) (b : Bool) :
    indexedDegree B (P.point (f,b)) =
      Fintype.card M + 1 + (P.free.filter (fun i => P.point (f,b) ∈ B i)).card := by
  classical
  change (univ.filter (fun i => P.point (f,b) ∈ B i)).card = _
  rw [card_eq_sum_ones,sum_filter,P.sum_partition,P.degree_named]
  simp only [card_eq_sum_ones,sum_filter]

/-- At five pairs, degree-six endpoints occur in no remaining block. -/
theorem five_no_free (hM : Fintype.card M = 5)
    (hdeg : ∀ f b, indexedDegree B (P.point (f,b)) = 6) :
    ∀ i ∈ P.free, ∀ f b, P.point (f,b) ∉ B i := by
  intro i hi f b hmem
  have he := P.endpoint_degree f b
  rw [hM,hdeg] at he
  have hz : (P.free.filter (fun j => P.point (f,b) ∈ B j)).card = 0 := by omega
  have hf := card_eq_zero.mp hz
  have hh : i ∈ P.free.filter (fun j => P.point (f,b) ∈ B j) := mem_filter.mpr ⟨hi,hmem⟩
  rw [hf] at hh
  exact notMem_empty _ hh

/-- At four pairs, each degree-six endpoint has exactly one remaining
occurrence; this is a statement about actual occurrence identities. -/
theorem four_unique_free (hM : Fintype.card M = 4)
    (hdeg : ∀ f b, indexedDegree B (P.point (f,b)) = 6) (f : M) (b : Bool) :
    ∃ i ∈ P.free, ∀ j ∈ P.free, P.point (f,b) ∈ B j ↔ j = i := by
  have he := P.endpoint_degree f b
  rw [hM,hdeg] at he
  have ho : (P.free.filter (fun j => P.point (f,b) ∈ B j)).card = 1 := by omega
  obtain ⟨i,hi⟩ := card_eq_one.mp ho
  have him : i ∈ P.free.filter (fun j => P.point (f,b) ∈ B j) := by rw [hi]; simp
  refine ⟨i,(mem_filter.mp him).1,?_⟩
  intro j hj
  have hh := congrArg (fun s : Finset ι => j ∈ s) hi
  simpa only [mem_filter,hj,true_and,mem_singleton] using (Iff.of_eq hh)

/-- Contribution of one supporting pair to endpoints of two other pairs.
Both endpoint combinations of either correlation type are retained. -/
theorem cross_named_contribution (e f g : M) (b c : Bool)
    (hef : e ≠ f) (heg : e ≠ g) :
    ((if P.point (f,b) ∈ B (P.block (e,true)) ∧
        P.point (g,c) ∈ B (P.block (e,true)) then 1 else 0) +
     (if P.point (f,b) ∈ B (P.block (e,false)) ∧
        P.point (g,c) ∈ B (P.block (e,false)) then 1 else 0)) =
      if (b == P.sign e f) = (c == P.sign e g) then 1 else 0 := by
  simp only [P.matched,hef,heg,false_or]
  cases hs : P.sign e f <;> cases ht : P.sign e g <;>
    cases b <;> cases c <;> simp [hs,ht]

/-- Each of the two own supporting pairs contributes exactly one. -/
theorem own_named_contribution (f g : M) (b c : Bool) (hfg : f ≠ g) :
    ((if P.point (f,b) ∈ B (P.block (f,true)) ∧
        P.point (g,c) ∈ B (P.block (f,true)) then 1 else 0) +
     (if P.point (f,b) ∈ B (P.block (f,false)) ∧
        P.point (g,c) ∈ B (P.block (f,false)) then 1 else 0)) = 1 := by
  simp only [P.matched,hfg,or_true,or_false,eq_self_iff_true,true_or,false_or,true_and]
  cases hs : P.sign f g <;> cases c <;> simp [hs]

/-- Exact pair multiplicity, split into the two own occurrences, the
correlations of all other supporting pairs, and all remaining occurrences. -/
theorem pair_partition (f g : M) (b c : Bool) (hfg : f ≠ g) :
    indexedSubsetDegree B {P.point (f,b),P.point (g,c)} =
      2 + (∑ e ∈ univ \ {f,g},
        if (b == P.sign e f) = (c == P.sign e g) then 1 else 0) +
      (P.free.filter (fun i => P.point (f,b) ∈ B i ∧ P.point (g,c) ∈ B i)).card := by
  classical
  let w : ι → ℕ := fun i => if P.point (f,b) ∈ B i ∧ P.point (g,c) ∈ B i then 1 else 0
  let v : M → ℕ := fun e => w (P.block (e,true)) + w (P.block (e,false))
  have hp := P.sum_partition w
  have hf : v f = 1 := P.own_named_contribution f g b c hfg
  have hg : v g = 1 := by
    simpa only [v,w,and_comm] using P.own_named_contribution g f c b hfg.symm
  have he := sum_sdiff (f := v) (subset_univ ({f,g} : Finset M))
  have hsum : ∑ e ∈ univ \ {f,g}, v e =
      ∑ e ∈ univ \ {f,g}, if (b == P.sign e f) = (c == P.sign e g) then 1 else 0 := by
    apply sum_congr rfl
    intro e he
    have hn := (mem_sdiff.mp he).2
    apply P.cross_named_contribution
    · intro h; exact hn (by simp [h])
    · intro h; exact hn (by simp [h])
  rw [hsum] at he
  simp only [sum_pair hfg,hf,hg] at he
  have hmul : indexedSubsetDegree B {P.point (f,b),P.point (g,c)} = ∑ i, w i := by
    simp only [indexedSubsetDegree,card_eq_sum_ones,sum_filter,
      insert_subset_iff,singleton_subset_iff,w]
  have hfree : (P.free.filter (fun i => P.point (f,b) ∈ B i ∧ P.point (g,c) ∈ B i)).card =
      ∑ i ∈ P.free, w i := by simp only [card_eq_sum_ones,sum_filter,w]
  change (∑ i, w i) = (∑ e, v e) + ∑ i ∈ P.free, w i at hp
  rw [hmul,hfree]
  omega

/-- At five pairs the exact formula has no unaccounted remaining term. -/
theorem five_pair_multiplicity (hM : Fintype.card M = 5)
    (hdeg : ∀ f b, indexedDegree B (P.point (f,b)) = 6)
    (f g : M) (b c : Bool) (hfg : f ≠ g) :
    indexedSubsetDegree B {P.point (f,b),P.point (g,c)} =
      2 + (∑ e ∈ univ \ {f,g},
        if (b == P.sign e f) = (c == P.sign e g) then 1 else 0) := by
  rw [P.pair_partition f g b c hfg]
  have hz : P.free.filter (fun i => P.point (f,b) ∈ B i ∧ P.point (g,c) ∈ B i) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hi,hm,_⟩ := mem_filter.mp hi
    exact P.five_no_free hM hdeg i hi f b hm
  rw [hz,card_empty,Nat.add_zero]

/-- At four pairs, a multiplicity-three pair with a matched endpoint needs
at least two named occurrences. Its endpoint has only one free occurrence. -/
theorem four_named_lower (hM : Fintype.card M = 4)
    (hdeg : ∀ f b, indexedDegree B (P.point (f,b)) = 6)
    (f : M) (b : Bool) (x : α)
    (hpair : 3 ≤ indexedSubsetDegree B {x,P.point (f,b)}) :
    2 ≤ ∑ e,
      ((if x ∈ B (P.block (e,true)) ∧ P.point (f,b) ∈ B (P.block (e,true)) then 1 else 0) +
       (if x ∈ B (P.block (e,false)) ∧ P.point (f,b) ∈ B (P.block (e,false)) then 1 else 0)) := by
  classical
  let w : ι → ℕ := fun i => if x ∈ B i ∧ P.point (f,b) ∈ B i then 1 else 0
  have he := P.endpoint_degree f b
  rw [hM,hdeg] at he
  have hfree : (P.free.filter (fun i => P.point (f,b) ∈ B i)).card = 1 := by omega
  have hsub : P.free.filter (fun i => x ∈ B i ∧ P.point (f,b) ∈ B i) ⊆
      P.free.filter (fun i => P.point (f,b) ∈ B i) := by
    intro i hi
    obtain ⟨hi,_,hp⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi,hp⟩
  have hf := card_le_card hsub
  rw [hfree] at hf
  have hf' : ∑ i ∈ P.free, w i ≤ 1 := by
    simpa only [card_eq_sum_ones,sum_filter,w] using hf
  have hp := P.sum_partition w
  have hm : indexedSubsetDegree B {x,P.point (f,b)} = ∑ i, w i := by
    simp only [indexedSubsetDegree,card_eq_sum_ones,sum_filter,
      insert_subset_iff,singleton_subset_iff,w]
  rw [hm] at hpair
  change 2 ≤ ∑ e, (w (P.block (e,true))+w (P.block (e,false)))
  omega

end Pattern
end CoveringDesigns.SaturatedMatching
