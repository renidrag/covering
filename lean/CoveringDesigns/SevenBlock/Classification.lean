import CoveringDesigns.SevenBlock.LowFano
import CoveringDesigns.SevenBlock.SupportFibres
import CoveringDesigns.SevenBlock.FanoSymmetry
import CoveringDesigns.SevenBlock.Templates

/-! General weighted-Fano classification. The a=1 Stanton adapter is kept
separate so applications of a≥2 do not inherit that result's dependencies. -/
namespace CoveringDesigns.SevenBlock
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

private theorem split_two_sum (p q : V) (hpq : p ≠ q) (f : V → ℕ) :
    (∑ x : {x : V // x ∉ ({p,q} : Finset V)}, f x.val) + f p + f q = ∑ x, f x := by
  have he : (∑ x : {x : V // x ∉ ({p,q} : Finset V)}, f x.val) +
      ∑ x ∈ ({p,q} : Finset V), f x = ∑ x, f x := by
    rw [← sum_subtype (univ \ {p,q}) (by simp) f]
    exact sum_sdiff (subset_univ _)
  simpa [sum_pair hpq, Nat.add_assoc] using he

private theorem low_lines {B : I → Finset V} (p q : V) (e : I ≃ Fin 7)
    (he : relabel e (univ.image (remainingSupports B {p,q})) = univ.image line) :
    ∃ f : {x : V // x ∉ ({p,q} : Finset V)} → Fin 7,
      ∀ x, (remainingSupports B {p,q} x).map e.toEmbedding = line (f x) := by
  classical
  have hx (x : {x : V // x ∉ ({p,q} : Finset V)}) :
      ∃ l, (remainingSupports B {p,q} x).map e.toEmbedding = line l := by
    have hm := (mem_relabel e (univ.image (remainingSupports B {p,q})) _).mpr
      (mem_image.mpr ⟨x,mem_univ _,rfl⟩)
    rw [he] at hm
    obtain ⟨l,_,hl⟩ := mem_image.mp hm
    exact ⟨l,hl.symm⟩
  exact ⟨fun x => (hx x).choose, fun x => (hx x).choose_spec⟩

private theorem weight_row_equation {a : ℕ} {B : I → Finset V}
    (hu : Multicover.Uniform B (3*a+2)) (p q : V) (hpq : p ≠ q)
    (e : I ≃ Fin 7) (f : {x : V // x ∉ ({p,q} : Finset V)} → Fin 7)
    (hf : ∀ x, (remainingSupports B {p,q} x).map e.toEmbedding = line (f x)) (j : Fin 7) :
    (∑ l : Fin 7, if j ∈ line l then fibreWeight f l else 0) +
      (if j ∈ (pointSupport B p).map e.toEmbedding then 1 else 0) +
      (if j ∈ (pointSupport B q).map e.toEmbedding then 1 else 0) = 3*a+2 := by
  have he := split_two_sum p q hpq (fun x => if x ∈ B (e.symm j) then 1 else 0)
  have hx : (∑ x : {x : V // x ∉ ({p,q} : Finset V)},
      if x.val ∈ B (e.symm j) then 1 else 0) =
      indexedDegree (remainingSupports B {p,q}) (e.symm j) := by
    simp only [indexedDegree,card_eq_sum_ones,sum_filter,remainingSupports,mem_pointSupport]
  rw [hx,← fibre_weight_row _ e f hf (e.symm j)] at he
  have ht : (∑ x, if x ∈ B (e.symm j) then 1 else 0) = (B (e.symm j)).card := by simp
  rw [ht,hu] at he
  simpa using he

private theorem weight_parity {a : ℕ} (W : Fin 7 → ℕ) (H G : Finset (Fin 7))
    (ht : ∑ l, W l = 7*a+2)
    (hr : ∀ j, (∑ l : Fin 7, if j ∈ line l then W l else 0) +
      (if j ∈ H then 1 else 0) + (if j ∈ G then 1 else 0) = 3*a+2) :
    ∀ l, Even ((H ∩ line l).card + (G ∩ line l).card) := by
  have htz : (∑ l, (W l : ℤ)) = 7*a+2 := by exact_mod_cast ht
  have hrz (j : Fin 7) : (∑ l : Fin 7, if j ∈ line l then (W l : ℤ) else 0) =
      3*a+2 - (if j ∈ H then 1 else 0) - (if j ∈ G then 1 else 0) := by
    have he : (∑ l : Fin 7, if j ∈ line l then (W l : ℤ) else 0) +
        (if j ∈ H then 1 else 0) + (if j ∈ G then 1 else 0) = 3*a+2 := by
      exact_mod_cast hr j
    omega
  have hcount (S T : Finset (Fin 7)) : (∑ i ∈ S, if i ∈ T then (1 : ℤ) else 0) =
      (S ∩ T).card := by
    rw [← sum_filter]
    simp [filter_mem_eq_inter]
  intro l
  have he := fano_incidence_identity (fun l => (W l : ℤ)) l
  simp_rw [hrz] at he
  rw [htz,sum_sub_distrib,sum_sub_distrib,hcount,hcount] at he
  simp only [sum_const,line_card,nsmul_eq_mul] at he
  rw [inter_comm (line l) H,inter_comm (line l) G] at he
  refine ⟨a+2-W l,?_⟩
  omega

private theorem high_meets_lines {a : ℕ} {B : I → Finset V}
    (h : Multicover.IsCover B (3*a+2) 2 1) (p q : V) (e : I ≃ Fin 7)
    (he : relabel e (univ.image (remainingSupports B {p,q})) = univ.image line) :
    ∀ l, ((pointSupport B p).map e.toEmbedding ∩ line l).Nonempty ∧
      ((pointSupport B q).map e.toEmbedding ∩ line l).Nonempty := by
  intro l
  have hl : line l ∈ relabel e (univ.image (remainingSupports B {p,q})) := by
    rw [he]
    exact mem_image.mpr ⟨l,mem_univ _,rfl⟩
  obtain ⟨L,hL,hLl⟩ := mem_map.mp hl
  obtain ⟨x,_,rfl⟩ := mem_image.mp hL
  change (remainingSupports B {p,q} x).map e.toEmbedding = line l at hLl
  rw [← hLl,← map_inter,← map_inter,map_nonempty,map_nonempty]
  exact ⟨pointSupports_meet h p x.val (fun he => x.property (by simp [← he])),
    pointSupports_meet h q x.val (fun he => x.property (by simp [← he]))⟩

private theorem normal_coordinates {a : ℕ} (ha : 2 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1)
    (hi : Fintype.card I = 7) (p q : V) (hpq : p ≠ q)
    (hp : indexedDegree B p = 4) (hq : indexedDegree B q = 4)
    (hr : ∀ x, x ≠ p → x ≠ q → indexedDegree B x = 3) :
    ∃ (e : I ≃ Fin 7) (tag swap : Bool),
      relabel e (univ.image (remainingSupports B {p,q})) = univ.image line ∧
      (pointSupport B p).map e.toEmbedding = highSupport tag swap ∧
      (pointSupport B q).map e.toEmbedding = highSupport tag (!swap) := by
  obtain ⟨e,he⟩ := low_support_fano ha hv h hi p q hpq hp hq hr
  obtain ⟨f,hf⟩ := low_lines p q e he
  let H := (pointSupport B p).map e.toEmbedding
  let G := (pointSupport B q).map e.toEmbedding
  have hw : ∑ l, fibreWeight f l = 7*a+2 := by
    rw [fibre_weight_sum,Multicover.subset_complement_card,card_pair hpq,hv]
    omega
  have hpar := weight_parity (fibreWeight f) H G hw (weight_row_equation h.1 p q hpq e f hf)
  have hint : (H ∩ G).card = 2 ∨ (H ∩ G).card = 4 := by
    have hx := exceptional_codegree_dichotomy ha hv h hi p q hpq hp hq hr
    simpa only [H,G,← map_inter,card_map,pointSupport_pair] using hx
  obtain ⟨g,tag,swap,hg,hH,hG⟩ := exceptional_support_normal_form H G
    (by simpa only [H,card_map,pointSupport_card] using hp)
    (by simpa only [G,card_map,pointSupport_card] using hq) (high_meets_lines h p q e he) hpar hint
  refine ⟨e.trans g,tag,swap,?_,?_,?_⟩
  · rw [← relabel_trans,he,hg]
  · change ((pointSupport B p).map e.toEmbedding).map g.toEmbedding = _ at hH
    rw [map_map] at hH
    exact hH
  · change ((pointSupport B q).map e.toEmbedding).map g.toEmbedding = _ at hG
    rw [map_map] at hG
    exact hG

private theorem template_weight_row {a : ℕ} (ha : 1 ≤ a) (tag swap : Bool) (j : Fin 7) :
    (∑ l : Fin 7, if j ∈ line l then weight a tag l else 0) +
      (if j ∈ highSupport tag swap then 1 else 0) +
      (if j ∈ highSupport tag (!swap) then 1 else 0) = 3*a+2 := by
  fin_cases j <;> cases tag <;> cases swap <;>
    simp [weight,highSupport,line,Fin.sum_univ_succ] <;> omega

private theorem recovered_weights {a : ℕ} (ha : 1 ≤ a) {B : I → Finset V}
    (hu : Multicover.Uniform B (3*a+2)) (p q : V) (hpq : p ≠ q)
    (e : I ≃ Fin 7) (tag swap : Bool)
    (hH : (pointSupport B p).map e.toEmbedding = highSupport tag swap)
    (hG : (pointSupport B q).map e.toEmbedding = highSupport tag (!swap))
    (f : {x : V // x ∉ ({p,q} : Finset V)} → Fin 7)
    (hf : ∀ x, (remainingSupports B {p,q} x).map e.toEmbedding = line (f x)) :
    fibreWeight f = weight a tag := by
  have hr (j : Fin 7) : (∑ l : Fin 7, if j ∈ line l then fibreWeight f l else 0) =
      ∑ l : Fin 7, if j ∈ line l then weight a tag l else 0 := by
    have hB := weight_row_equation hu p q hpq e f hf j
    rw [hH,hG] at hB
    have hT := template_weight_row ha tag swap j
    omega
  have he := fano_weights_unique (fun l => (fibreWeight f l : ℤ))
    (fun l => (weight a tag l : ℤ)) (fun j => by exact_mod_cast hr j)
  funext l
  exact_mod_cast congrFun he l

private theorem fibre_test {X : Type*} [Fintype X] (f : X → Fin 7)
    (P : Fin 7 → Prop) [DecidablePred P] :
    (∑ x, if P (f x) then 1 else 0) =
      ∑ l : Fin 7, if P l then fibreWeight f l else 0 := by
  symm
  simp only [fibreWeight,card_eq_sum_ones,sum_filter]
  have hc (l : Fin 7) : (if P l then ∑ x, if f x = l then 1 else 0 else 0) =
      ∑ x, if f x = l then (if P l then 1 else 0) else 0 := by
    by_cases hl : P l <;> simp [hl]
  simp_rw [hc]
  rw [sum_comm]
  simp

private theorem actual_fibre_count {B : I → Finset V} (p q : V) (hpq : p ≠ q)
    (e : I ≃ Fin 7) (f : {x : V // x ∉ ({p,q} : Finset V)} → Fin 7)
    (hf : ∀ x, (remainingSupports B {p,q} x).map e.toEmbedding = line (f x))
    (T : Finset (Fin 7)) :
    Fintype.card {x : V // (pointSupport B x).map e.toEmbedding = T} =
      (if (pointSupport B p).map e.toEmbedding = T then 1 else 0) +
      (if (pointSupport B q).map e.toEmbedding = T then 1 else 0) +
      ∑ l, if line l = T then fibreWeight f l else 0 := by
  have hs := split_two_sum p q hpq (fun x => if (pointSupport B x).map e.toEmbedding = T then 1 else 0)
  have hl : (∑ x : {x : V // x ∉ ({p,q} : Finset V)},
      if (pointSupport B x.val).map e.toEmbedding = T then 1 else 0) =
      ∑ l, if line l = T then fibreWeight f l else 0 := by
    change (∑ x, if (remainingSupports B {p,q} x).map e.toEmbedding = T then 1 else 0) = _
    simp_rw [hf]
    exact fibre_test f (fun l => line l = T)
  rw [hl] at hs
  simp only [Fintype.card_subtype,card_eq_sum_ones,sum_filter]
  omega

private theorem template_fibre_count (a : ℕ) (tag : Bool) (T : Finset (Fin 7)) :
    Fintype.card {x : TemplatePoint a tag // pointSupport (templateBlock a tag) x = T} =
      (if highSupport tag false = T then 1 else 0) +
      (if highSupport tag true = T then 1 else 0) +
      ∑ l, if line l = T then weight a tag l else 0 := by
  have hs (x : TemplatePoint a tag) : pointSupport (templateBlock a tag) x =
      templateSupport a tag x := by ext i; simp
  simp only [Fintype.card_subtype,card_eq_sum_ones,sum_filter,hs]
  rw [Fintype.sum_sum_type,Fintype.sum_bool,Fintype.sum_sigma]
  change ((if highSupport tag true = T then 1 else 0) +
    (if highSupport tag false = T then 1 else 0)) +
    (∑ l, ∑ _ : Fin (weight a tag l), if line l = T then 1 else 0) = _
  have hl (l : Fin 7) : (∑ _ : Fin (weight a tag l), if line l = T then 1 else 0) =
      if line l = T then weight a tag l else 0 := by
    by_cases h : line l = T <;> simp [h]
  simp_rw [hl]
  omega

/-- Every indexed seven-occurrence covering with a≥2 is one of the two
weighted Fano constructions, up to actual point and occurrence equivalences.
Neither distinct block images nor distinct point supports are premises. -/
theorem classification_ge_two {a : ℕ} (ha : 2 ≤ a) {B : I → Finset V}
    (hv : Fintype.card V = 7*a+4) (h : Multicover.IsCover B (3*a+2) 2 1)
    (hi : Fintype.card I = 7) :
    ∃ tag : Bool, IndexedIsomorphic B (templateBlock a tag) := by
  obtain ⟨p,q,hpq,hp,hq,hr⟩ := covering_degree_profile (by omega : 1 ≤ a) hv h hi
  obtain ⟨e,tag,swap,he,hH,hG⟩ := normal_coordinates ha hv h hi p q hpq hp hq hr
  obtain ⟨f,hf⟩ := low_lines p q e he
  have hW := recovered_weights (by omega : 1 ≤ a) h.1 p q hpq e tag swap hH hG f hf
  refine ⟨tag,support_fibre_isomorphism B (templateBlock a tag) e ?_⟩
  intro T
  rw [actual_fibre_count p q hpq e f hf,template_fibre_count,hH,hG,hW]
  cases swap <;> simp [Nat.add_comm,Nat.add_left_comm]

#guard_standard_axioms classification_ge_two

end CoveringDesigns.SevenBlock
