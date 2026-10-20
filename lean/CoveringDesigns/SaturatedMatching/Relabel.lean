import CoveringDesigns.SaturatedMatching.FourGroups

/-! Reindexing matching edges and independently reversing endpoint labels
and supporting occurrences. These operations preserve actual identities.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset
variable {α ι M N : Type*} [Fintype α] [Fintype ι] [Fintype M] [Fintype N]
  [DecidableEq α] [DecidableEq ι] [DecidableEq M] [DecidableEq N]
variable {B : ι → Finset α}

namespace Pattern
variable (P : Pattern (M := M) B)

/-- XNOR with a fixed label is an involution. -/
def labels (r : N ≃ M) (p : N → Bool) : N × Bool ≃ M × Bool where
  toFun z := (r z.1,z.2 == p z.1)
  invFun z := (r.symm z.1,z.2 == p (r.symm z.1))
  left_inv := by rintro ⟨e,b⟩; simp
  right_inv := by rintro ⟨e,b⟩; simp

def relabel (r : N ≃ M) (p q : N → Bool) : Pattern (M := N) B where
  point z := P.point (labels r p z)
  point_injective := P.point_injective.comp (labels r p).injective
  block z := P.block (labels r q z)
  block_injective := P.block_injective.comp (labels r q).injective
  sign e f := (q e == P.sign (r e) (r f)) == p f
  matched := by
    intro e a f b
    simp only [labels,Equiv.coe_fn_mk,P.matched,Equiv.apply_eq_iff_eq]
    by_cases hef : e = f
    · simp [hef]
    · simp only [hef,false_or]
      cases q e <;> cases p f <;> cases P.sign (r e) (r f) <;>
        cases a <;> cases b <;> decide
  outside := by
    intro x hx e
    have hn : ∀ f b, x ≠ P.point (f,b) := by
      intro f b
      obtain ⟨⟨g,c⟩,he⟩ := (labels r p).surjective (f,b)
      simpa only [he] using hx g c
    have hh := P.outside x hn (r e)
    simp only [labels,Equiv.coe_fn_mk]
    cases hq : q e <;> simp_all

theorem relabel_degree (r : N ≃ M) (p q : N → Bool)
    (h : ∀ f b, indexedDegree B (P.point (f,b)) = 6) :
    ∀ f b, indexedDegree B ((P.relabel r p q).point (f,b)) = 6 :=
  fun f b => h (r f) (b == p f)

theorem relabel_pair_floor (r : N ≃ M) (p q : N → Bool)
    (h : ∀ x f b, x ≠ P.point (f,b) → x ≠ P.point (f,!b) →
      3 ≤ indexedSubsetDegree B {x,P.point (f,b)}) :
    ∀ x f b, x ≠ (P.relabel r p q).point (f,b) →
      x ≠ (P.relabel r p q).point (f,!b) →
      3 ≤ indexedSubsetDegree B {x,(P.relabel r p q).point (f,b)} := by
  intro x f b hx hy
  apply h x (r f) (b == p f) hx
  change x ≠ P.point (r f,(!b) == p f) at hy
  convert hy using 1 <;> cases b <;> cases hp : p f <;> rfl

theorem relabel_named (r : N ≃ M) (p q : N → Bool) :
    (P.relabel r p q).named = P.named := by
  ext i
  simp only [named,mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨z,rfl⟩; exact ⟨labels r q z,rfl⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨w,rfl⟩ := (labels r q).surjective z
    exact ⟨w,rfl⟩

end Pattern

namespace Remaining
variable {P : Pattern (M := M) B} (R : Remaining P)
def relabel (r : N ≃ M) (p q : N → Bool) : Remaining (P.relabel r p q) where
  index z := R.index (Pattern.labels r p z)
  mem z := by
    simpa only [Pattern.free,P.relabel_named] using R.mem (Pattern.labels r p z)
  exact z i hi := by
    apply R.exact
    simpa only [Pattern.free,P.relabel_named] using hi

theorem relabel_signature (r : N ≃ M) (p q : N → Bool) (f : N) :
    (R.relabel r p q).signature f = R.signature (r f) := by
  simp only [signature,relabel,Pattern.labels,Equiv.coe_fn_mk]
  cases p f <;> simp [pair_comm]
end Remaining

namespace FourCompatibility
variable {P : Pattern (M := M) B} (H : FourCompatibility P)
def relabel (r : N ≃ M) (p q : N → Bool) :
    FourCompatibility (P.relabel r p q) where
  pairs := (Fintype.card_congr r).trans H.pairs
  occurrences := H.occurrences
  degree := P.relabel_degree r p q H.degree
  saturated := by
    intro f
    have hh := H.saturated (r f)
    change indexedSubsetDegree B
      {P.point (r f,true == p f),P.point (r f,false == p f)} = 2
    cases p f <;> simpa [pair_comm] using hh
  floor := by
    intro f g hfg b c
    exact H.floor (r f) (r g) (fun he => hfg (r.injective he)) _ _
  cross := by
    intro e f g hef heg hfg b c hc
    apply H.cross (r e) (r f) (r g)
      (fun he => hef (r.injective he)) (fun he => heg (r.injective he))
      (fun he => hfg (r.injective he)) (b == p f) (c == p g)
    change (b == ((q e == P.sign (r e) (r f)) == p f)) ≠
      (c == ((q e == P.sign (r e) (r g)) == p g)) at hc
    cases hq : q e <;> cases hf : p f <;> cases hg : p g <;>
      cases hs : P.sign (r e) (r f) <;> cases ht : P.sign (r e) (r g) <;>
      cases b <;> cases c <;> simp_all

end FourCompatibility
end CoveringDesigns.SaturatedMatching
