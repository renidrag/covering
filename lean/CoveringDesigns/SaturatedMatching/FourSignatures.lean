import CoveringDesigns.SaturatedMatching.Pattern

/-! Remaining-occurrence signatures for four complementary matching pairs.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset
variable {α ι M : Type*} [Fintype α] [Fintype ι] [Fintype M]
  [DecidableEq α] [DecidableEq ι] [DecidableEq M]
variable {B : ι → Finset α}

/-- The unique remaining occurrence of each matched endpoint, retaining
the actual occurrence type and exact membership in every free block. -/
structure Remaining (P : Pattern (M := M) B) where
  index : M × Bool → ι
  mem : ∀ z, index z ∈ P.free
  exact : ∀ z i, i ∈ P.free → (P.point z ∈ B i ↔ i = index z)

namespace Remaining
variable (P : Pattern (M := M) B)

theorem exists_of_four (hM : Fintype.card M = 4)
    (hdeg : ∀ f b, indexedDegree B (P.point (f,b)) = 6) :
    Nonempty (Remaining P) := by
  classical
  have hh (z : M × Bool) := P.four_unique_free hM hdeg z.1 z.2
  choose a ha he using hh
  exact ⟨⟨a,ha,he⟩⟩

variable {P} (R : Remaining P)

def signature (f : M) : Finset ι := {R.index (f,true),R.index (f,false)}

theorem point_mem (z : M × Bool) : P.point z ∈ B (R.index z) :=
  (R.exact z _ (R.mem z)).mpr rfl

/-- Saturation makes each remaining-block signature genuinely two-element. -/
theorem index_ne (hsat : ∀ f,
    indexedSubsetDegree B {P.point (f,true),P.point (f,false)} = 2) (f : M) :
    R.index (f,true) ≠ R.index (f,false) := by
  classical
  intro he
  let a := P.block (f,true)
  let b := P.block (f,false)
  let c := R.index (f,true)
  have hab : a ≠ b := by
    intro hh
    have hg := congrArg Prod.snd (P.block_injective hh)
    simp at hg
  have hcn : c ∉ P.named := (mem_sdiff.mp (R.mem (f,true))).2
  have hca : c ≠ a := by
    intro hh
    apply hcn
    rw [hh]
    exact mem_image_of_mem _ (mem_univ _)
  have hcb : c ≠ b := by
    intro hh
    apply hcn
    rw [hh]
    exact mem_image_of_mem _ (mem_univ _)
  have hboth (i : ι) (hi : i ∈ ({a,b,c} : Finset ι)) :
      P.point (f,true) ∈ B i ∧ P.point (f,false) ∈ B i := by
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · simp [a,P.matched]
    · simp [b,P.matched]
    · exact ⟨R.point_mem _,by simpa only [c,he] using R.point_mem (f,false)⟩
  have hc : ({a,b,c} : Finset ι).card = 3 := by
    simp [hab,hca.symm,hcb.symm]
  have hsub : ({a,b,c} : Finset ι) ⊆
      univ.filter (fun i => ({P.point (f,true),P.point (f,false)} : Finset α) ⊆ B i) := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _,by
      simpa only [insert_subset_iff,singleton_subset_iff] using hboth i hi⟩
  have hh := card_le_card hsub
  change ({a,b,c} : Finset ι).card ≤ indexedSubsetDegree B _ at hh
  rw [hc,hsat] at hh
  omega

theorem signature_card (hsat : ∀ f,
    indexedSubsetDegree B {P.point (f,true),P.point (f,false)} = 2) (f : M) :
    (R.signature f).card = 2 := card_pair (R.index_ne hsat f)

theorem pair_count (f g : M) (b c : Bool) :
    (P.free.filter (fun i => P.point (f,b) ∈ B i ∧ P.point (g,c) ∈ B i)).card =
      if R.index (f,b) = R.index (g,c) then 1 else 0 := by
  classical
  by_cases he : R.index (f,b) = R.index (g,c)
  · have hf : P.free.filter (fun i => P.point (f,b) ∈ B i ∧ P.point (g,c) ∈ B i) =
        {R.index (f,b)} := by
      ext i
      simp only [mem_filter,mem_singleton]
      constructor
      · rintro ⟨hi,hf,_⟩
        exact (R.exact (f,b) i hi).mp hf
      · intro hi
        subst i
        exact ⟨R.mem _,(R.exact _ _ (R.mem _)).mpr rfl,
          (R.exact _ _ (R.mem _)).mpr he⟩
    simp [hf,he]
  · have hf : P.free.filter (fun i => P.point (f,b) ∈ B i ∧ P.point (g,c) ∈ B i) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨hi,hf,hg⟩ := mem_filter.mp hi
      exact he (((R.exact _ _ hi).mp hf).symm.trans ((R.exact _ _ hi).mp hg))
    simp [hf,he]

/-- The exact four-pair formula when the other two matching indices are
named. The exhaustiveness premise is solely a finite-index identity. -/
theorem four_pair_count (e h f g : M) (b c : Bool)
    (hfg : f ≠ g) (heh : e ≠ h)
    (hrest : (univ : Finset M) \ {f,g} = {e,h}) :
    indexedSubsetDegree B {P.point (f,b),P.point (g,c)} =
      2 + (if (b == P.sign e f) = (c == P.sign e g) then 1 else 0) +
      (if (b == P.sign h f) = (c == P.sign h g) then 1 else 0) +
      (if R.index (f,b) = R.index (g,c) then 1 else 0) := by
  rw [P.pair_partition f g b c hfg,hrest,sum_pair heh,R.pair_count]
  omega

/-- If both other supporting pairs miss an endpoint combination, the
multiplicity-three floor forces equality of the remaining occurrences. -/
theorem equal_of_missing (e h f g : M) (b c : Bool)
    (hfg : f ≠ g) (heh : e ≠ h)
    (hrest : (univ : Finset M) \ {f,g} = {e,h})
    (he : (b == P.sign e f) ≠ (c == P.sign e g))
    (hh : (b == P.sign h f) ≠ (c == P.sign h g))
    (hpair : 3 ≤ indexedSubsetDegree B {P.point (f,b),P.point (g,c)}) :
    R.index (f,b) = R.index (g,c) := by
  have hc := R.four_pair_count e h f g b c hfg heh hrest
  simp only [if_neg he,if_neg hh,Nat.add_zero] at hc
  by_contra hn
  simp only [if_neg hn,Nat.add_zero] at hc
  omega

/-- Mixed correlations leave three supporting occurrences, so exact cross
multiplicity three forbids a shared remaining occurrence. -/
theorem ne_of_mixed (e h f g : M) (b c : Bool)
    (hfg : f ≠ g) (heh : e ≠ h)
    (hrest : (univ : Finset M) \ {f,g} = {e,h})
    (he : (b == P.sign e f) ≠ (c == P.sign e g))
    (hh : (b == P.sign h f) = (c == P.sign h g))
    (hpair : indexedSubsetDegree B {P.point (f,b),P.point (g,c)} = 3) :
    R.index (f,b) ≠ R.index (g,c) := by
  have hc := R.four_pair_count e h f g b c hfg heh hrest
  simp only [if_neg he,if_pos hh,Nat.add_zero] at hc
  intro heq
  simp only [if_pos heq] at hc
  omega

/-- Equal or disjoint signatures, derived from actual multiplicities.
The exactness premise concerns combinations separated by either of the
two other supporting partitions. -/
theorem signatures_equal_or_disjoint (e h f g : M)
    (hfg : f ≠ g) (heh : e ≠ h)
    (hrest : (univ : Finset M) \ {f,g} = {e,h})
    (hfloor : ∀ b c, 3 ≤ indexedSubsetDegree B {P.point (f,b),P.point (g,c)})
    (hexact : ∀ b c,
      ((b == P.sign e f) ≠ (c == P.sign e g) ∨
       (b == P.sign h f) ≠ (c == P.sign h g)) →
      indexedSubsetDegree B {P.point (f,b),P.point (g,c)} = 3) :
    R.signature f = R.signature g ∨ Disjoint (R.signature f) (R.signature g) := by
  classical
  by_cases hsame : (P.sign e f = P.sign e g ↔ P.sign h f = P.sign h g)
  · left
    have hi (b : Bool) :
        R.index (f,b) = R.index (g,if P.sign e f = P.sign e g then !b else b) := by
      apply R.equal_of_missing e h f g b _ hfg heh hrest
      · cases hf : P.sign e f <;> cases hg : P.sign e g <;> cases b <;> simp [hf,hg]
      · cases hf : P.sign e f <;> cases hg : P.sign e g <;>
          cases hf' : P.sign h f <;> cases hg' : P.sign h g <;>
          cases b <;> simp_all
      · exact hfloor _ _
    have ht := hi true
    have hf := hi false
    by_cases he : P.sign e f = P.sign e g
    · simp only [if_pos he,Bool.not_true,Bool.not_false] at ht hf
      simp [signature,ht,hf,pair_comm]
    · simp only [if_neg he] at ht hf
      simp [signature,ht,hf]
  · right
    have hne (b c : Bool) : R.index (f,b) ≠ R.index (g,c) := by
      have hc : ((b == P.sign e f) = (c == P.sign e g)) ↔
          ¬((b == P.sign h f) = (c == P.sign h g)) := by
        cases hf : P.sign e f <;> cases hg : P.sign e g <;>
          cases hf' : P.sign h f <;> cases hg' : P.sign h g <;>
          cases b <;> cases c <;> simp_all
      by_cases he : (b == P.sign e f) = (c == P.sign e g)
      · have hh := hc.mp he
        exact R.ne_of_mixed h e f g b c hfg heh.symm
          (by simpa [pair_comm] using hrest) hh he (hexact b c (Or.inr hh))
      · have hh : (b == P.sign h f) = (c == P.sign h g) := by tauto
        exact R.ne_of_mixed e h f g b c hfg heh hrest he hh (hexact b c (Or.inl he))
    apply disjoint_left.mpr
    intro i hi hj
    simp only [signature,mem_insert,mem_singleton] at hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact hne true true (hi.symm.trans hj)
    · exact hne true false (hi.symm.trans hj)
    · exact hne false true (hi.symm.trans hj)
    · exact hne false false (hi.symm.trans hj)

/-- Complementing one endpoint reverses its correlation. -/
theorem flip_correlation (b c u v : Bool) :
    ((!b) == u) = (c == v) ↔ ¬((b == u) = (c == v)) := by
  cases b <;> cases c <;> cases u <;> cases v <;> decide

/-- Sharing a remaining occurrence forces the endpoints to be separated
by either other supporting partition. This is the key no-three-signatures
constraint, derived before choosing orientations. -/
theorem shared_free_separated (e h f g : M) (b c : Bool)
    (hfg : f ≠ g) (heh : e ≠ h)
    (hrest : (univ : Finset M) \ {f,g} = {e,h})
    (hsat : ∀ f, indexedSubsetDegree B {P.point (f,true),P.point (f,false)} = 2)
    (hfloor : ∀ b c, 3 ≤ indexedSubsetDegree B {P.point (f,b),P.point (g,c)})
    (hexact : ∀ b c,
      ((b == P.sign e f) ≠ (c == P.sign e g) ∨
       (b == P.sign h f) ≠ (c == P.sign h g)) →
      indexedSubsetDegree B {P.point (f,b),P.point (g,c)} = 3)
    (hshared : R.index (f,b) = R.index (g,c)) :
    (b == P.sign e f) ≠ (c == P.sign e g) := by
  intro he
  by_cases hh : (b == P.sign h f) = (c == P.sign h g)
  · have he' : ((!b) == P.sign e f) ≠ (c == P.sign e g) := by
      intro h
      exact (flip_correlation b c _ _).mp h he
    have hh' : ((!b) == P.sign h f) ≠ (c == P.sign h g) := by
      intro h
      exact (flip_correlation b c _ _).mp h hh
    have hm := R.equal_of_missing e h f g (!b) c hfg heh hrest he' hh' (hfloor _ _)
    have hc : R.index (f,!b) = R.index (f,b) := hm.trans hshared.symm
    cases b
    · exact R.index_ne hsat f hc
    · exact R.index_ne hsat f hc.symm
  · exact R.ne_of_mixed h e f g b c hfg heh.symm
      (by simpa [pair_comm] using hrest) hh he (hexact b c (Or.inr hh)) hshared

end Remaining
end CoveringDesigns.SaturatedMatching
