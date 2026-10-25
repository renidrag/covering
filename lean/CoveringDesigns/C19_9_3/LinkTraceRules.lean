import CoveringDesigns.C19_9_3.MinimumLinks
import CoveringDesigns.C19_9_3.TraceAgreement

/-! Actual trace rules induced by the classified a=2 links. Every comparison
below uses the parent occurrences; local coordinates only prove the rules. -/
namespace CoveringDesigns.C19_9_3
open Finset SevenBlock
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- Local coordinates embedded in the original occurrence type. The same
embedding represents every column of a minimum link. -/
theorem minimum_incidence_coordinates {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x : V) (hx : indexedDegree B x = 7) :
    ∃ (tag : Bool) (e : {y : V // y ∉ ({x} : Finset V)} ≃ TemplatePoint 2 tag)
      (g : Fin 7 ↪ I),
      pointSupport B x = univ.map g ∧
      ∀ y : {y : V // y ∉ ({x} : Finset V)},
        pointSupport B x ∩ pointSupport B y.val = (templateSupport 2 tag (e y)).map g := by
  obtain ⟨tag,e,f,he⟩ := minimum_link_classification hv h x hx
  let g : Fin 7 ↪ I := f.symm.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨tag,e,g,?_,?_⟩
  · ext i
    simp only [mem_pointSupport,mem_map,mem_univ,true_and]
    constructor
    · intro hi
      let j : {i : I // ({x} : Finset V) ⊆ B i} := ⟨i,by simpa using hi⟩
      exact ⟨f j,by simp [g,j]⟩
    · rintro ⟨j,rfl⟩
      exact (f.symm j).property (by simp)
  · intro y
    rw [← literal_link_trace]
    have hc : pointSupport (Multicover.subsetLink B {x}) y =
        (templateSupport 2 tag (e y)).map f.symm.toEmbedding := by
      ext i
      simp only [mem_pointSupport,mem_map_equiv,Equiv.symm_symm]
      exact (he y i).trans (mem_templateBlock 2 tag (f i) (e y))
    rw [hc,map_map]

private theorem template_pair (tag : Bool) (y z : TemplatePoint 2 tag) :
    indexedSubsetDegree (templateBlock 2 tag) {y,z} =
      (templateSupport 2 tag y ∩ templateSupport 2 tag z).card := by
  rw [← pointSupport_pair]
  congr 1
  ext i
  simp

private theorem template_low_pair (tag : Bool) (y z : TemplatePoint 2 tag)
    (hy : indexedDegree (templateBlock 2 tag) y = 3)
    (hz : indexedDegree (templateBlock 2 tag) z = 3) :
    indexedSubsetDegree (templateBlock 2 tag) {y,z} = 1 ∨
      indexedSubsetDegree (templateBlock 2 tag) {y,z} = 3 := by
  rw [template_pair]
  rw [template_degree] at hy hz
  cases y with
  | inl b => change (4 : ℕ) = 3 at hy; omega
  | inr y =>
    cases z with
    | inl b => change (4 : ℕ) = 3 at hz; omega
    | inr z =>
      by_cases h : y.1 = z.1
      · right
        simpa only [templateSupport,h,inter_self] using line_card z.1
      · left
        exact line_inter_card y.1 z.1 h

/-- At a minimum root, two ordinary neighbours have literal common trace
size one or three, never two. The neighbours need not themselves be minimum. -/
theorem minimum_ordinary_trace {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x y z : V) (hx : indexedDegree B x = 7)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hy : indexedSubsetDegree B {x,y} = 3) (hz : indexedSubsetDegree B {x,z} = 3) :
    indexedSubsetDegree B {x,y,z} = 1 ∨ indexedSubsetDegree B {x,y,z} = 3 := by
  obtain ⟨tag,e,f,he⟩ := minimum_link_classification hv h x hx
  let y' : {v : V // v ∉ ({x} : Finset V)} := ⟨y,by simpa using hxy.symm⟩
  let z' : {v : V // v ∉ ({x} : Finset V)} := ⟨z,by simpa using hxz.symm⟩
  have hy' : indexedDegree (templateBlock 2 tag) (e y') = 3 := by
    rw [← incidence_degree_eq e f he,actual_link_degree]
    exact hy
  have hz' : indexedDegree (templateBlock 2 tag) (e z') = 3 := by
    rw [← incidence_degree_eq e f he,actual_link_degree]
    exact hz
  have ht := template_low_pair tag (e y') (e z') hy' hz'
  rw [← incidence_codegree_eq e f he,actual_link_codegree] at ht
  exact ht

/-- A two-position trace against an ordinary neighbour must be exceptional
at the same minimum root. -/
theorem minimum_two_trace_exceptional {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x y z : V) (hx : indexedDegree B x = 7)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hy : indexedSubsetDegree B {x,y} = 3) (ht : indexedSubsetDegree B {x,y,z} = 2) :
    indexedSubsetDegree B {x,z} = 4 := by
  have hf := pair_floor hv h (card_pair hxz)
  have hu := minimum_pair_le_four hv h x z hx hxz
  by_contra hn
  have hz : indexedSubsetDegree B {x,z} = 3 := by omega
  have hh := minimum_ordinary_trace hv h x y z hx hxy hxz hy hz
  omega

/-- Agreement is on the same actual triple of parent points. A two-trace
therefore identifies exceptional neighbours at both minimum roots. -/
theorem minimum_two_trace_agreement {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x y z : V)
    (hx : indexedDegree B x = 7) (hy : indexedDegree B y = 7)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hpair : indexedSubsetDegree B {x,y} = 3)
    (ht : indexedSubsetDegree B {x,y,z} = 2) :
    indexedSubsetDegree B {x,z} = 4 ∧ indexedSubsetDegree B {y,z} = 4 := by
  exact ⟨minimum_two_trace_exceptional hv h x y z hx hxy hxz hpair ht,
    minimum_two_trace_exceptional hv h y x z hy hxy.symm hyz
      (by simpa only [pair_comm] using hpair) (by simpa only [insert_comm] using ht)⟩

/-- Three distinct neighbours cannot all be exceptional at a minimum root. -/
theorem no_three_minimum_exceptions {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x p q r : V) (hx : indexedDegree B x = 7)
    (hpx : p ≠ x) (hqx : q ≠ x) (hrx : r ≠ x)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : indexedSubsetDegree B {x,p} = 4) (hq : indexedSubsetDegree B {x,q} = 4)
    (hr : indexedSubsetDegree B {x,r} = 4) : False := by
  obtain ⟨u,v,_,_,_,_,_,hrest,_⟩ := minimum_profile hv h x hx
  have mem (z : V) (hzx : z ≠ x) (hz : indexedSubsetDegree B {x,z} = 4) : z = u ∨ z = v := by
    by_contra hn
    push Not at hn
    have := hrest z hzx hn.1 hn.2
    omega
  have hp' := mem p hpx hp
  have hq' := mem q hqx hq
  have hr' := mem r hrx hr
  rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;>
    rcases hr' with rfl | rfl <;> contradiction

def thirdPoints (B : I → Finset V) (x y : V) (r : ℕ) : Finset V :=
  (univ \ {x,y}).filter fun z => indexedSubsetDegree B {x,y,z} = r

private def templateThirds (tag : Bool) (y : TemplatePoint 2 tag) (r : ℕ) :
    Finset (TemplatePoint 2 tag) :=
  (univ.erase y).filter fun z => indexedSubsetDegree (templateBlock 2 tag) {y,z} = r

private theorem template_thirds_profile (tag : Bool) : ∀ y : TemplatePoint 2 tag,
    indexedDegree (templateBlock 2 tag) y = 3 →
    ((templateThirds tag y 3).card = 2 ∧ (templateThirds tag y 2).card = 0) ∨
    ((templateThirds tag y 3).card = 1 ∧ (templateThirds tag y 2).card = 2) := by
  cases tag <;> decide +kernel

private theorem thirds_transport {B : I → Finset V} (x y : V) (hxy : x ≠ y)
    (tag : Bool) (e : {z : V // z ∉ ({x} : Finset V)} ≃ TemplatePoint 2 tag)
    (f : {i : I // ({x} : Finset V) ⊆ B i} ≃ Fin 7)
    (he : ∀ z i, z ∈ Multicover.subsetLink B {x} i ↔ e z ∈ templateBlock 2 tag (f i))
    (r : ℕ) :
    (thirdPoints B x y r).card =
      (templateThirds tag (e ⟨y,by simpa using hxy.symm⟩) r).card := by
  classical
  let y' : {z : V // z ∉ ({x} : Finset V)} := ⟨y,by simpa using hxy.symm⟩
  let L : Finset {z : V // z ∉ ({x} : Finset V)} :=
    univ.filter fun z => z ≠ y' ∧ indexedSubsetDegree B {x,y,z.val} = r
  have hL : L = (thirdPoints B x y r).subtype (· ∉ ({x} : Finset V)) := by
    ext z
    simp only [L,thirdPoints,mem_filter,mem_univ,true_and,mem_subtype,mem_sdiff,
      mem_insert,mem_singleton]
    have hz : z.val ≠ x := by simpa using z.property
    have hy : z ≠ y' ↔ z.val ≠ y := by simp [y',Subtype.ext_iff]
    tauto
  have hc : L.card = (thirdPoints B x y r).card := by
    rw [hL,card_subtype]
    congr 1
    apply filter_eq_self.mpr
    intro z hz
    exact fun hx => (mem_sdiff.mp (mem_filter.mp hz).1).2
      (mem_insert.mpr (Or.inl (mem_singleton.mp hx)))
  rw [← hc]
  apply card_equiv e
  intro z
  have hpair := incidence_codegree_eq e f he y' z
  rw [actual_link_codegree] at hpair
  simp only [L,mem_filter,mem_univ,true_and,templateThirds,mem_erase]
  have hne : e z ≠ e y' ↔ z ≠ y' := e.injective.ne_iff
  simpa only [and_true,hne,y'] using and_congr Iff.rfl (Iff.of_eq (congrArg (· = r) hpair))

/-- The complete third-point count for an ordinary neighbour of a minimum
root. Counts refer to actual parent points, including coincident supports. -/
theorem minimum_ordinary_pair_profile {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x y : V) (hx : indexedDegree B x = 7)
    (hxy : x ≠ y) (hpair : indexedSubsetDegree B {x,y} = 3) :
    ((thirdPoints B x y 3).card = 2 ∧ (thirdPoints B x y 2).card = 0) ∨
    ((thirdPoints B x y 3).card = 1 ∧ (thirdPoints B x y 2).card = 2) := by
  obtain ⟨tag,e,f,he⟩ := minimum_link_classification hv h x hx
  let y' : {z : V // z ∉ ({x} : Finset V)} := ⟨y,by simpa using hxy.symm⟩
  have hy : indexedDegree (templateBlock 2 tag) (e y') = 3 := by
    rw [← incidence_degree_eq e f he,actual_link_degree]
    exact hpair
  have ht := template_thirds_profile tag (e y') hy
  simpa only [thirds_transport x y hxy tag e f he,y'] using ht

#guard_standard_axioms minimum_incidence_coordinates minimum_ordinary_trace minimum_two_trace_exceptional
  minimum_two_trace_agreement no_three_minimum_exceptions minimum_ordinary_pair_profile

end CoveringDesigns.C19_9_3
