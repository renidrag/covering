import CoveringDesigns.C19_9_3.ExcessRoots

/-! Minimum points are pairwise ordinary; their number and the remaining
degrees are consequences, rather than premises, of the parent covering. -/
namespace CoveringDesigns.C19_9_3
open Finset SevenBlock
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

private def pointClass (tag : Bool) : TemplatePoint 2 tag → Bool ⊕ Fin 7
  | .inl b => .inl b
  | .inr v => .inr v.1

private theorem class_injective (tag : Bool) (K : Finset (TemplatePoint 2 tag))
    (hK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v →
      (templateSupport 2 tag u ∩ templateSupport 2 tag v).card ≠ 3) :
    Set.InjOn (pointClass tag) K := by
  intro u hu v hv he
  cases u with
  | inl b => cases v with
    | inl c => exact congrArg Sum.inl (Sum.inl.inj he)
    | inr v => cases he
  | inr u => cases v with
    | inl c => cases he
    | inr v =>
      by_contra hne
      have huv : u.1 = v.1 := Sum.inr.inj he
      apply hK _ hu _ hv hne
      simpa only [templateSupport,huv,inter_self] using line_card v.1

private theorem high_line_counts (tag b : Bool) :
    (univ.filter fun l : Fin 7 => (highSupport tag b ∩ line l).card = 1).card = 3 ∧
      ∀ l : Fin 7, (highSupport tag b ∩ line l).card = 1 ∨
        (highSupport tag b ∩ line l).card = 2 ∨ (highSupport tag b ∩ line l).card = 3 := by
  cases tag <;> cases b <;> decide +kernel

private def lowTwo (tag b : Bool) (K : Finset (TemplatePoint 2 tag)) :=
  K.filter fun u => (templateSupport 2 tag u).card = 3 ∧
    (highSupport tag b ∩ templateSupport 2 tag u).card = 2

private theorem occupied_high_bound (tag b : Bool) (K : Finset (TemplatePoint 2 tag))
    (hb : Sum.inl b ∈ K)
    (hK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v →
      (templateSupport 2 tag u ∩ templateSupport 2 tag v).card ≠ 3)
    (htwo : (lowTwo tag b K).card ≤ 1) : K.card ≤ 6 := by
  let L := univ.filter fun l : Fin 7 => (highSupport tag b ∩ line l).card = 1
  let H : Finset (Bool ⊕ Fin 7) := univ.image Sum.inl
  let A : Finset (Bool ⊕ Fin 7) := L.image Sum.inr
  have hsub : K.image (pointClass tag) ⊆ H ∪ A ∪ (lowTwo tag b K).image (pointClass tag) := by
    intro c hc
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hc
    cases u with
    | inl d => exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨d,mem_univ _,rfl⟩))
    | inr u =>
      rcases (high_line_counts tag b).2 u.1 with h1 | h2 | h3
      · exact mem_union_left _ (mem_union_right _
          (mem_image.mpr ⟨u.1,mem_filter.mpr ⟨mem_univ _,h1⟩,rfl⟩))
      · exact mem_union_right _ (mem_image.mpr ⟨Sum.inr u,
          mem_filter.mpr ⟨hu,line_card u.1,h2⟩,rfl⟩)
      · exact False.elim (hK _ hb _ hu (by simp) h3)
  have hH : H.card = 2 := by
    dsimp only [H]
    rw [card_image_of_injective _ Sum.inl_injective,card_univ,Fintype.card_bool]
  have hA : A.card = 3 := by
    dsimp only [A]
    rw [card_image_of_injective _ Sum.inr_injective]
    exact (high_line_counts tag b).1
  have hcard := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  rw [(card_image_iff.mpr (class_injective tag K hK)),hH,hA] at hcard
  have hc := card_image_le (s := lowTwo tag b K) (f := pointClass tag)
  omega

private def minimumSelection (B : I → Finset V) (x : V) (tag : Bool)
    (e : {v : V // v ∉ ({x} : Finset V)} ≃ TemplatePoint 2 tag) : Finset (TemplatePoint 2 tag) :=
  univ.filter fun u => indexedDegree B (e.symm u).val = 7

private theorem selection_card (B : I → Finset V) (x : V) (hx : indexedDegree B x = 7)
    (tag : Bool) (e : {v : V // v ∉ ({x} : Finset V)} ≃ TemplatePoint 2 tag) :
    (minimumSelection B x tag e).card + 1 = (minimumPoints B).card := by
  have heq : (minimumSelection B x tag e).card = ((minimumPoints B).erase x).card := by
    calc
      _ = (((minimumPoints B).erase x).subtype (· ∉ ({x} : Finset V))).card := by
        apply card_equiv e.symm
        intro u
        have hn : (e.symm u).val ≠ x := by simpa using (e.symm u).property
        simp only [minimumSelection,mem_filter,mem_univ,true_and,mem_subtype,mem_erase,mem_minimumPoints]
        tauto
      _ = _ := by
        rw [card_subtype]
        congr 1
        apply filter_eq_self.mpr
        intro u hu
        simpa only [mem_singleton] using (mem_erase.mp hu).1
  rw [heq,card_erase_of_mem (mem_minimumPoints B x |>.mpr hx)]
  have hp : 1 ≤ (minimumPoints B).card := card_pos.mpr ⟨x,(mem_minimumPoints B x).mpr hx⟩
  omega

private theorem template_codegree (tag : Bool) (u v : TemplatePoint 2 tag) :
    indexedSubsetDegree (templateBlock 2 tag) {u,v} =
      (templateSupport 2 tag u ∩ templateSupport 2 tag v).card := by
  rw [← pointSupport_pair]
  congr 1
  ext i
  simp

private theorem selection_trace_distinct {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16) (x : V)
    (hx : indexedDegree B x = 7) (tag : Bool)
    (e : {v : V // v ∉ ({x} : Finset V)} ≃ TemplatePoint 2 tag)
    (f : {i : I // ({x} : Finset V) ⊆ B i} ≃ Fin 7)
    (he : ∀ u i, u ∈ Multicover.subsetLink B {x} i ↔ e u ∈ templateBlock 2 tag (f i)) :
    ∀ u ∈ minimumSelection B x tag e, ∀ v ∈ minimumSelection B x tag e, u ≠ v →
      (templateSupport 2 tag u ∩ templateSupport 2 tag v).card ≠ 3 := by
  intro u hu v hv' huv ht
  have hux : (e.symm u).val ≠ x := by simpa using (e.symm u).property
  have hvx : (e.symm v).val ≠ x := by simpa using (e.symm v).property
  have huv' : (e.symm u).val ≠ (e.symm v).val := by
    intro heq
    exact huv (e.symm.injective (Subtype.ext heq))
  have hc := incidence_codegree_eq e f he (e.symm u) (e.symm v)
  rw [actual_link_codegree,e.apply_symm_apply,e.apply_symm_apply,template_codegree,ht] at hc
  exact no_minimum_triple_three hv h hi x _ _ hux.symm hvx.symm huv' hx
    (mem_filter.mp hu).2 (mem_filter.mp hv').2 hc

private theorem template_support_degree (tag : Bool) (u : TemplatePoint 2 tag) :
    indexedDegree (templateBlock 2 tag) u = (templateSupport 2 tag u).card := by
  rw [template_degree]
  cases u with
  | inl b => exact (high_card tag b).symm
  | inr v => exact (line_card v.1).symm

/-- Distinct minimum points are ordinary neighbours. In particular there
are no excess edges between minimum points. -/
theorem minimum_pair_ordinary {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (x y : V) (hx : indexedDegree B x = 7) (hy : indexedDegree B y = 7) (hxy : x ≠ y) :
    indexedSubsetDegree B {x,y} = 3 := by
  have hL := pair_floor hv h (card_pair hxy)
  have hU := minimum_pair_le_four hv h x y hx hxy
  by_contra hn
  have hxy4 : indexedSubsetDegree B {x,y} = 4 := by omega
  obtain ⟨tag,e,f,he⟩ := minimum_link_classification hv h x hx
  let y' : {v : V // v ∉ ({x} : Finset V)} := ⟨y,by simpa using hxy.symm⟩
  have hy4 : indexedDegree (templateBlock 2 tag) (e y') = 4 := by
    rw [← incidence_degree_eq e f he,actual_link_degree]
    exact hxy4
  obtain ⟨b,hb⟩ := (template_degree_four_iff 2 tag (e y')).mp hy4
  let K := minimumSelection B x tag e
  have hbK : Sum.inl b ∈ K := by
    rw [← hb]
    apply mem_filter.mpr
    exact ⟨mem_univ _,by simpa only [e.symm_apply_apply] using hy⟩
  have hd (u : TemplatePoint 2 tag) : indexedSubsetDegree B {x,(e.symm u).val} =
      (templateSupport 2 tag u).card := by
    rw [← actual_link_degree B x,incidence_degree_eq e f he,e.apply_symm_apply,template_support_degree]
  have htwo : (lowTwo tag b K).card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv'
    obtain ⟨huK,hu3,hu2⟩ := mem_filter.mp hu
    obtain ⟨hvK,hv3,hv2⟩ := mem_filter.mp hv'
    have hux : (e.symm u).val ≠ x := by simpa using (e.symm u).property
    have hvx : (e.symm v).val ≠ x := by simpa using (e.symm v).property
    have hu3' : indexedSubsetDegree B {x,(e.symm u).val} = 3 := (hd u).trans hu3
    have hv3' : indexedSubsetDegree B {x,(e.symm v).val} = 3 := (hd v).trans hv3
    have huy : (e.symm u).val ≠ y := by intro heq; rw [heq,hxy4] at hu3'; contradiction
    have hvy : (e.symm v).val ≠ y := by intro heq; rw [heq,hxy4] at hv3'; contradiction
    have htrace (a : TemplatePoint 2 tag)
        (ha : (highSupport tag b ∩ templateSupport 2 tag a).card = 2) :
        indexedSubsetDegree B {x,(e.symm a).val,y} = 2 := by
      have hc := incidence_codegree_eq e f he y' (e.symm a)
      rw [actual_link_codegree,hb,e.apply_symm_apply,template_codegree] at hc
      rw [pair_comm]
      exact hc.trans ha
    have hu4 := (minimum_two_trace_agreement hv h x (e.symm u).val y hx
      (mem_filter.mp huK).2 hux.symm hxy huy hu3' (htrace u hu2)).2
    have hv4 := (minimum_two_trace_agreement hv h x (e.symm v).val y hx
      (mem_filter.mp hvK).2 hvx.symm hxy hvy hv3' (htrace v hv2)).2
    by_contra huv
    have huv' : (e.symm u).val ≠ (e.symm v).val :=
      fun heq => huv (e.symm.injective (Subtype.ext heq))
    exact no_three_minimum_exceptions hv h y x (e.symm u).val (e.symm v).val hy
      hxy huy hvy hux.symm hvx.symm huv'
      (by rw [pair_comm]; exact hxy4) (by rw [pair_comm]; exact hu4) (by rw [pair_comm]; exact hv4)
  have hc := occupied_high_bound tag b K hbK (selection_trace_distinct hv h hi x hx tag e f he) htwo
  have hcard := selection_card B x hx tag e
  change K.card + 1 = (minimumPoints B).card at hcard
  have hm := eight_minimum_points hv h hi
  omega

/-- Exactly eight points have degree seven in any hypothetical sixteen-block
cover. All premises follow from the covering conditions. -/
theorem minimum_points_card {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16) :
    (minimumPoints B).card = 8 := by
  have hlo := eight_minimum_points hv h hi
  obtain ⟨x,hxM⟩ := card_pos.mp (show 0 < (minimumPoints B).card by omega)
  have hx := (mem_minimumPoints B x).mp hxM
  obtain ⟨tag,e,f,he⟩ := minimum_link_classification hv h x hx
  let K := minimumSelection B x tag e
  have hsub : K.image (pointClass tag) ⊆ (univ : Finset (Fin 7)).image Sum.inr := by
    intro c hc
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hc
    have hn : x ≠ (e.symm u).val := Ne.symm (by simpa using (e.symm u).property)
    have hp := minimum_pair_ordinary hv h hi x (e.symm u).val hx (mem_filter.mp hu).2 hn
    have hd := incidence_degree_eq e f he (e.symm u)
    rw [actual_link_degree,e.apply_symm_apply,hp,template_degree] at hd
    cases u with
    | inl b => change (3 : ℕ) = 4 at hd; omega
    | inr v => exact mem_image.mpr ⟨v.1,mem_univ _,rfl⟩
  have hc := card_le_card hsub
  rw [card_image_iff.mpr (class_injective tag K (selection_trace_distinct hv h hi x hx tag e f he)),
    card_image_of_injective _ Sum.inr_injective,card_univ,Fintype.card_fin] at hc
  have hs := selection_card B x hx tag e
  change K.card + 1 = (minimumPoints B).card at hs
  omega

/-- The other eleven points all have degree eight. -/
theorem nonminimum_degree {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (w : V) (hw : w ∉ minimumPoints B) : indexedDegree B w = 8 := by
  have hM := minimum_points_card hv h hi
  have hsum := Multicover.degree_sum_of_uniform h.1
  have hf (x : V) : 8 ≤ indexedDegree B x + if x ∈ minimumPoints B then 1 else 0 := by
    by_cases hm : x ∈ minimumPoints B
    · rw [(mem_minimumPoints B x).mp hm,if_pos hm]
    · have hh := degree_floor hv h x
      have hn := (mem_minimumPoints B x).not.mp hm
      rw [if_neg hm]
      omega
  have htotal : (∑ x : V, (indexedDegree B x + if x ∈ minimumPoints B then 1 else 0)) =
      ∑ _x : V, 8 := by
    rw [sum_add_distrib,hsum,hi]
    have hc : (∑ x : V, if x ∈ minimumPoints B then 1 else 0) = (minimumPoints B).card := by
      rw [← sum_filter]
      simp [minimumPoints]
    rw [hc,hM]
    simp [hv]
  have heq := (sum_eq_sum_iff_of_le (fun x (_ : x ∈ (univ : Finset V)) => hf x)).mp htotal.symm w (mem_univ _)
  rw [if_neg hw,add_zero] at heq
  exact heq.symm

/-- Every three distinct minimum points belong to exactly one actual
occurrence. -/
theorem minimum_triple_one {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : indexedDegree B x = 7) (hy : indexedDegree B y = 7) (hz : indexedDegree B z = 7) :
    indexedSubsetDegree B {x,y,z} = 1 :=
  (minimum_ordinary_trace hv h x y z hx hxy hxz
    (minimum_pair_ordinary hv h hi x y hx hy hxy)
    (minimum_pair_ordinary hv h hi x z hx hz hxz)).resolve_right
    (no_minimum_triple_three hv h hi x y z hxy hxz hyz hx hy hz)

#guard_standard_axioms minimum_pair_ordinary minimum_points_card nonminimum_degree minimum_triple_one
end CoveringDesigns.C19_9_3
