import CoveringDesigns.SevenBlock.Indexed
import CoveringDesigns.SevenBlock.Fano

/-! Weighted Fano constructions with actual point identities, including the
empty Type-II fibre at a=1. `false` is Type I and `true` is Type II. -/
namespace CoveringDesigns.SevenBlock
open Finset

def weight (a : ℕ) (tag : Bool) : Fin 7 → ℕ :=
  if tag then ![a+1,a+1,a,a+1,a,a,a-1] else ![a+1,a+1,a,a,a,a,a]

/-- A dependent fibre keeps every low point distinct, even for equal support. -/
abbrev TemplatePoint (a : ℕ) (tag : Bool) := Bool ⊕ (Σ l : Fin 7, Fin (weight a tag l))

def templateSupport (a : ℕ) (tag : Bool) : TemplatePoint a tag → Finset (Fin 7)
  | .inl h => highSupport tag h
  | .inr p => line p.1

def templateBlock (a : ℕ) (tag : Bool) (i : Fin 7) : Finset (TemplatePoint a tag) :=
  univ.filter fun x => i ∈ templateSupport a tag x

@[simp] theorem mem_templateBlock (a : ℕ) (tag : Bool) (i : Fin 7) (x : TemplatePoint a tag) :
    x ∈ templateBlock a tag i ↔ i ∈ templateSupport a tag x := by simp [templateBlock]

theorem template_point_card {a : ℕ} (ha : 1 ≤ a) (tag : Bool) :
    Fintype.card (TemplatePoint a tag) = 7*a+4 := by
  cases tag <;> simp [TemplatePoint, Fintype.card_sigma, weight, Fin.sum_univ_succ] <;> omega

theorem template_uniform {a : ℕ} (ha : 1 ≤ a) (tag : Bool) :
    Multicover.Uniform (templateBlock a tag) (3*a+2) := by
  intro i
  unfold templateBlock
  rw [card_eq_sum_ones, sum_filter]
  change (∑ x : Bool ⊕ (Σ l : Fin 7, Fin (weight a tag l)),
    if i ∈ templateSupport a tag x then 1 else 0) = _
  rw [Fintype.sum_sum_type, Fintype.sum_bool, Fintype.sum_sigma]
  change ((if i ∈ highSupport tag true then 1 else 0) +
    (if i ∈ highSupport tag false then 1 else 0)) +
    (∑ l : Fin 7, ∑ _ : Fin (weight a tag l), if i ∈ line l then 1 else 0) = _
  have hf (l : Fin 7) : (∑ _ : Fin (weight a tag l), if i ∈ line l then 1 else 0) =
      if i ∈ line l then weight a tag l else 0 := by
    by_cases hi : i ∈ line l <;> simp [hi]
  simp_rw [hf]
  fin_cases i <;> cases tag <;>
    simp [weight, highSupport, line, Fin.sum_univ_succ] <;> omega

theorem template_supports_meet (a : ℕ) (tag : Bool) (x y : TemplatePoint a tag) :
    (templateSupport a tag x ∩ templateSupport a tag y).Nonempty := by
  cases x with
  | inl h =>
    cases y with
    | inl g => exact high_high_meet tag h g
    | inr p => exact high_line_meet tag h p.1
  | inr p =>
    cases y with
    | inl h => simpa only [templateSupport, inter_comm] using high_line_meet tag h p.1
    | inr q => exact line_meet p.1 q.1

theorem template_covers (a : ℕ) (tag : Bool) :
    Multicover.Covers (templateBlock a tag) 2 1 := by
  rw [Multicover.covers_one_iff]
  intro T hT
  obtain ⟨x,y,_,rfl⟩ := card_eq_two.mp hT
  obtain ⟨i,hi⟩ := template_supports_meet a tag x y
  exact ⟨i, by simpa only [insert_subset_iff, singleton_subset_iff, mem_templateBlock,
    mem_inter] using hi⟩

theorem template_isCover {a : ℕ} (ha : 1 ≤ a) (tag : Bool) :
    Multicover.IsCover (templateBlock a tag) (3*a+2) 2 1 :=
  ⟨template_uniform ha tag, template_covers a tag⟩

theorem template_injective {a : ℕ} (ha : 1 ≤ a) (tag : Bool) :
    Function.Injective (templateBlock a tag) :=
  blocks_injective ha (template_point_card ha tag) (template_isCover ha tag) (by simp)

theorem template_degree (a : ℕ) (tag : Bool) (x : TemplatePoint a tag) :
    indexedDegree (templateBlock a tag) x =
      match x with | .inl _ => 4 | .inr _ => 3 := by
  have hs : univ.filter (fun i => x ∈ templateBlock a tag i) = templateSupport a tag x := by
    ext i
    simp
  unfold indexedDegree
  rw [hs]
  cases x with
  | inl h => exact high_card tag h
  | inr p => exact line_card p.1

theorem template_degree_four_iff (a : ℕ) (tag : Bool) (x : TemplatePoint a tag) :
    indexedDegree (templateBlock a tag) x = 4 ↔ ∃ h, x = Sum.inl h := by
  rw [template_degree]
  cases x <;> simp

/-- Exact cardinality of an actual low-support fibre, including the empty
Type-II fibre at a=1. -/
theorem template_line_fibre_card (a : ℕ) (tag : Bool) (l : Fin 7) :
    Fintype.card {x : TemplatePoint a tag // templateSupport a tag x = line l} = weight a tag l := by
  have hh (b : Bool) : highSupport tag b ≠ line l := by
    intro he
    have hc := congrArg Finset.card he
    rw [high_card,line_card] at hc
    contradiction
  simp only [Fintype.card_subtype,card_eq_sum_ones,sum_filter]
  rw [Fintype.sum_sum_type,Fintype.sum_bool,Fintype.sum_sigma]
  simp only [templateSupport,hh,if_false,zero_add,line_injective.eq_iff]
  have hf (m : Fin 7) : (∑ _ : Fin (weight a tag m), if m = l then 1 else 0) =
      if m = l then weight a tag m else 0 := by
    by_cases he : m = l <;> simp [he]
  simp_rw [hf]
  simp

theorem template_exceptional_codegree (a : ℕ) (tag : Bool) :
    indexedSubsetDegree (templateBlock a tag) {Sum.inl false, Sum.inl true} =
      if tag then 4 else 2 := by
  have hs : univ.filter (fun i => ({Sum.inl false, Sum.inl true} : Finset (TemplatePoint a tag)) ⊆
      templateBlock a tag i) = highSupport tag false ∩ highSupport tag true := by
    ext i
    simp only [mem_filter, mem_univ, true_and, insert_subset_iff,
      singleton_subset_iff, mem_templateBlock, templateSupport, mem_inter]
  unfold indexedSubsetDegree
  rw [hs]
  exact exceptional_codegree tag

/-- Nonisomorphism is the codegree invariant of the unique degree-four pair;
it does not assume that distinct low points have distinct supports. -/
theorem templates_not_isomorphic (a : ℕ) :
    ¬ IndexedIsomorphic (templateBlock a false) (templateBlock a true) := by
  rintro ⟨e, f, he⟩
  have h₀ := incidence_degree_eq e f he (Sum.inl false)
  have h₁ := incidence_degree_eq e f he (Sum.inl true)
  rw [template_degree] at h₀ h₁
  obtain ⟨p,hp⟩ := (template_degree_four_iff a true _).mp h₀.symm
  obtain ⟨q,hq⟩ := (template_degree_four_iff a true _).mp h₁.symm
  have hne : p ≠ q := by
    intro heq
    have hx := e.injective (hp.trans ((congrArg Sum.inl heq).trans hq.symm))
    cases hx
  have hc := incidence_codegree_eq e f he (Sum.inl false) (Sum.inl true)
  rw [hp,hq] at hc
  have hpair : ({Sum.inl p, Sum.inl q} : Finset (TemplatePoint a true)) =
      {Sum.inl false,Sum.inl true} := by
    cases p <;> cases q <;> simp_all [pair_comm]
  rw [hpair, template_exceptional_codegree, template_exceptional_codegree] at hc
  contradiction

def templateFamily (a : ℕ) (tag : Bool) : Family (TemplatePoint a tag) :=
  Multicover.deduplicate (templateBlock a tag)

theorem template_family_isCover {a : ℕ} (ha : 1 ≤ a) (tag : Bool) :
    IsCover (templateFamily a tag) (3*a+2) 2 :=
  (Multicover.deduplicate_isCover_one _ _ _).mpr (template_isCover ha tag)

theorem template_family_card {a : ℕ} (ha : 1 ≤ a) (tag : Bool) :
    (templateFamily a tag).card = 7 := by
  rw [templateFamily, Multicover.deduplicate, card_image_of_injective _ (template_injective ha tag)]
  simp

/-- Both actual constructions are transported to arbitrary point labels. -/
theorem template_attainment {V : Type*} [Fintype V] [DecidableEq V]
    {a : ℕ} (ha : 1 ≤ a) (hv : Fintype.card V = 7*a+4) (tag : Bool) :
    ∃ C : Family V, IsCover C (3*a+2) 2 ∧ C.card = 7 := by
  let e : TemplatePoint a tag ≃ V := Fintype.equivOfCardEq ((template_point_card ha tag).trans hv.symm)
  exact ⟨relabel e (templateFamily a tag), relabel_isCover e (template_family_isCover ha tag),
    (relabel_card e _).trans (template_family_card ha tag)⟩

/-- The known exact numerical family; classification is a stronger, separate
theorem. This contract includes actual attainment on arbitrary labels. -/
theorem covering_number_on {V : Type*} [Fintype V] [DecidableEq V]
    {a : ℕ} (ha : 1 ≤ a) (hv : Fintype.card V = 7*a+4) :
    (∃ C : Family V, IsCover C (3*a+2) 2 ∧ C.card = 7) ∧
    (∀ C : Family V, IsCover C (3*a+2) 2 → 7 ≤ C.card) :=
  ⟨template_attainment ha hv false, fun _ h => ordinary_seven_le_card ha hv h⟩

#guard_standard_axioms template_point_card template_uniform template_supports_meet
  template_covers template_isCover template_injective template_family_isCover
  template_family_card template_attainment covering_number_on template_degree
  template_degree_four_iff template_line_fibre_card template_exceptional_codegree templates_not_isomorphic

end CoveringDesigns.SevenBlock
