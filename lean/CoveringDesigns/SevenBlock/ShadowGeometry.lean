import CoveringDesigns.SevenBlock.Fano
import CoveringDesigns.Foundations.Relabelling
import Mathlib.Data.Fintype.Sum

/-! Recognition of an intersecting triple system from its complete pair
shadow. The proof chooses one root triple, then colours the three perfect
matchings on its four-point complement. The only finite reductions below
are incidence facts about those three explicit matchings, not an enumeration
of triple systems or coverings. -/
namespace CoveringDesigns.SevenBlock
open Finset

private def root : Finset (Fin 7) := {0,1,2}

private def matching : Fin 3 → Bool → Finset (Fin 7) :=
  ![fun b => if b then {5,6} else {3,4},
    fun b => if b then {4,6} else {3,5},
    fun b => if b then {4,5} else {3,6}]

private def coloured (c d : Fin 3) (b : Bool) : Finset (Fin 7) :=
  insert (Fin.castAdd 4 c) (matching d b)

section FixedMatchingIncidence
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

private theorem matching_card : ∀ d b, (matching d b).card = 2 := by decide +kernel

private theorem root_disjoint_matching : ∀ d b, Disjoint root (matching d b) := by
  decide +kernel

private theorem matching_third : ∀ d b, ∀ T ∈ (univ : Finset (Fin 7)).powersetCard 3,
    matching d b ⊆ T → (T ∩ root).Nonempty →
    ∃ c : Fin 3, T = coloured c d b := by
  decide +kernel

private theorem complementary_colours : ∀ c e d b,
    (coloured c d b ∩ coloured e d (!b)).Nonempty → c = e := by
  decide +kernel

private theorem constant_colour : ∀ c, ∀ T ∈ (univ : Finset (Fin 7)).powersetCard 3,
    (T ∩ root).Nonempty →
    (∀ d b, (T ∩ coloured c d b).Nonempty) → Fin.castAdd 4 c ∈ T := by
  decide +kernel

set_option synthInstance.maxSize 10000 in
private theorem missing_colour : ∀ c₀ c₁ c₂ : Fin 3,
    ¬ (c₀ = c₁ ∧ c₁ = c₂) → ¬ (c₀ ≠ c₁ ∧ c₀ ≠ c₂ ∧ c₁ ≠ c₂) →
    ∃ i j : Fin 7, i ≠ j ∧
      ∀ T ∈ (univ : Finset (Fin 7)).powersetCard 3,
        i ∈ T → j ∈ T → (T ∩ root).Nonempty →
        ∃ d : Fin 3, ¬ (T ∩ coloured (![c₀,c₁,c₂] d) d false).Nonempty ∨
          ¬ (T ∩ coloured (![c₀,c₁,c₂] d) d true).Nonempty := by
  intro c₀ c₁ c₂
  fin_cases c₀ <;> fin_cases c₁ <;> fin_cases c₂ <;> decide +kernel

private theorem fano_matching_lines :
    (insert root (univ.biUnion fun d : Fin 3 => univ.image (coloured d d))) =
      univ.image line := by
  decide +kernel

private theorem fano_no_additional_triple : ∀ T ∈ (univ : Finset (Fin 7)).powersetCard 3,
    (∀ l, (T ∩ line l).Nonempty) → ∃ l, T = line l := by
  decide +kernel

end FixedMatchingIncidence

private def rootPerm (e : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 7) :=
  finSumFinEquiv.symm.trans ((e.sumCongr (Equiv.refl (Fin 4))).trans finSumFinEquiv)

private theorem rootPerm_low (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    rootPerm e (Fin.castAdd 4 i) = Fin.castAdd 4 (e i) := by
  fin_cases i <;> rfl

private theorem rootPerm_high (e : Equiv.Perm (Fin 3)) (i : Fin 4) :
    rootPerm e (Fin.natAdd 3 i) = Fin.natAdd 3 i := by
  fin_cases i <;> rfl

private theorem rootPerm_root (e : Equiv.Perm (Fin 3)) :
    root.map (rootPerm e).toEmbedding = root := by
  have hr : root = univ.image (Fin.castAdd 4 : Fin 3 → Fin 7) := by decide
  rw [hr, map_eq_image, image_image]
  have he : (rootPerm e ∘ Fin.castAdd 4) = Fin.castAdd 4 ∘ e := by
    funext i
    exact rootPerm_low e i
  change univ.image (rootPerm e ∘ Fin.castAdd 4) = _
  rw [he, ← image_image]
  congr 1
  exact image_univ_of_surjective e.surjective

private theorem rootPerm_coloured (e : Equiv.Perm (Fin 3)) (c d : Fin 3) (b : Bool) :
    (coloured c d b).map (rootPerm e).toEmbedding = coloured (e c) d b := by
  have hm : (matching d b).map (rootPerm e).toEmbedding = matching d b := by
    fin_cases d <;> cases b <;>
      simp only [matching, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Bool.false_eq_true, ↓reduceIte, map_insert, map_singleton] <;>
      congr 2 <;> first | exact rootPerm_high e _ | rfl
  simp only [coloured, map_insert, Equiv.toEmbedding_apply, rootPerm_low, hm]

private theorem meet_map (e : Equiv.Perm (Fin 7)) (S T : Finset (Fin 7)) :
    (S.map e.toEmbedding ∩ T.map e.toEmbedding).Nonempty ↔ (S ∩ T).Nonempty := by
  rw [← map_inter, map_nonempty]

/-- The normalized matching argument. The root is named only within this
lemma; the public theorem below transports actual position identities. -/
private theorem rooted_shadow (H : Family (Fin 7))
    (hc : ∀ T ∈ H, T.card = 3)
    (hm : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty)
    (hp : ∀ i j : Fin 7, i ≠ j → ∃ T ∈ H, i ∈ T ∧ j ∈ T)
    (hr : root ∈ H) :
    (∃ c, H = ((univ : Finset (Fin 7)).powersetCard 3).filter (c ∈ ·)) ∨
    ∃ e : Equiv.Perm (Fin 7), H = (univ.image line).map
      (Finset.mapEmbedding e.toEmbedding).toEmbedding := by
  classical
  have hcolour (d : Fin 3) (b : Bool) : ∃ c, coloured c d b ∈ H := by
    obtain ⟨i,j,hij,hijP⟩ := card_eq_two.mp (matching_card d b)
    obtain ⟨T,hT,hi,hj⟩ := hp i j hij
    obtain ⟨c,hcT⟩ := matching_third d b T (mem_powersetCard_univ.mpr (hc T hT))
      (by rw [hijP]; simp only [insert_subset_iff,singleton_subset_iff]; exact ⟨hi,hj⟩)
      (hm T hT root hr)
    exact ⟨c,hcT ▸ hT⟩
  choose c hcol using fun d => hcolour d false
  have hboth (d : Fin 3) (b : Bool) : coloured (c d) d b ∈ H := by
    cases b with
    | false => exact hcol d
    | true =>
      obtain ⟨e,he⟩ := hcolour d true
      have heq := complementary_colours (c d) e d false (hm _ (hcol d) _ he)
      simpa only [heq] using he
  by_cases he : c 0 = c 1 ∧ c 1 = c 2
  · left
    have hall (d : Fin 3) : c d = c 0 := by fin_cases d <;> simp_all
    have hcentre (T : Finset (Fin 7)) (hT : T ∈ H) : Fin.castAdd 4 (c 0) ∈ T :=
      constant_colour (c 0) T (mem_powersetCard_univ.mpr (hc T hT)) (hm T hT root hr)
        (by intro d b; rw [← hall d]; exact hm T hT _ (hboth d b))
    refine ⟨Fin.castAdd 4 (c 0), ?_⟩
    ext T
    constructor
    · intro hT
      exact mem_filter.mpr ⟨mem_powersetCard_univ.mpr (hc T hT),hcentre T hT⟩
    · intro hT
      obtain ⟨hT,hct⟩ := mem_filter.mp hT
      have hsize := mem_powersetCard_univ.mp hT
      obtain ⟨i,j,hij,hijT⟩ := card_eq_two.mp (show (T.erase (Fin.castAdd 4 (c 0))).card = 2 by
        rw [card_erase_of_mem hct,hsize])
      obtain ⟨U,hU,hi,hj⟩ := hp i j hij
      have hsub : T ⊆ U := by
        rw [← insert_erase hct,hijT]
        simp only [insert_subset_iff,singleton_subset_iff]
        exact ⟨hcentre U hU,hi,hj⟩
      exact (eq_of_subset_of_card_le hsub (by rw [hc U hU,hsize])) ▸ hU
  · have hinj : Function.Injective c := by
      have hdistinct : c 0 ≠ c 1 ∧ c 0 ≠ c 2 ∧ c 1 ≠ c 2 := by
        by_contra hn
        obtain ⟨i,j,hij,hbad⟩ := missing_colour (c 0) (c 1) (c 2) he hn
        obtain ⟨T,hT,hi,hj⟩ := hp i j hij
        obtain ⟨d,hd⟩ := hbad T (mem_powersetCard_univ.mpr (hc T hT)) hi hj
          (hm T hT root hr)
        have hv : ![c 0,c 1,c 2] = c := by funext d; fin_cases d <;> rfl
        rw [hv] at hd
        rcases hd with hd | hd
        · exact hd (hm T hT _ (hboth d false))
        · exact hd (hm T hT _ (hboth d true))
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    let f := Equiv.ofBijective c ⟨hinj,Finite.surjective_of_injective hinj⟩
    let e := rootPerm f
    have hbase : ∀ l, (line l).map e.toEmbedding ∈ H := by
      intro l
      have hl : line l ∈ insert root (univ.biUnion fun d : Fin 3 => univ.image (coloured d d)) := by
        rw [fano_matching_lines]
        exact mem_image.mpr ⟨l,mem_univ _,rfl⟩
      rcases mem_insert.mp hl with hroot | hl
      · rw [hroot,rootPerm_root]
        exact hr
      · obtain ⟨d,_,hl⟩ := mem_biUnion.mp hl
        obtain ⟨b,_,hbl⟩ := mem_image.mp hl
        rw [← hbl,rootPerm_coloured]
        exact hboth d b
    right
    refine ⟨e,?_⟩
    ext T
    constructor
    · intro hT
      have hpre : ∀ l, (T.map e.symm.toEmbedding ∩ line l).Nonempty := by
        intro l
        have hmT := hm T hT _ (hbase l)
        have heq : (T.map e.symm.toEmbedding).map e.toEmbedding = T := by
          ext i
          simp
        rw [← heq] at hmT
        exact (meet_map e _ _).mp hmT
      obtain ⟨l,hl⟩ := fano_no_additional_triple (T.map e.symm.toEmbedding)
        (mem_powersetCard_univ.mpr (by simpa using hc T hT)) hpre
      apply mem_map.mpr
      refine ⟨line l,mem_image.mpr ⟨l,mem_univ _,rfl⟩,?_⟩
      change (line l).map e.toEmbedding = T
      rw [← hl]
      ext i
      simp
    · intro hT
      obtain ⟨L,hL,rfl⟩ := mem_map.mp hT
      obtain ⟨l,_,rfl⟩ := mem_image.mp hL
      exact hbase l

private theorem root_coordinates {I : Type*} [Fintype I] [DecidableEq I]
    (hi : Fintype.card I = 7) (T : Finset I) (ht : T.card = 3) :
    ∃ e : I ≃ Fin 7, T.map e.toEmbedding = root := by
  classical
  have hr : root.card = 3 := by decide
  let f : {i : I // i ∈ T} ≃ {i : Fin 7 // i ∈ root} :=
    Fintype.equivOfCardEq (by simpa using ht.trans hr.symm)
  let g : {i : I // i ∉ T} ≃ {i : Fin 7 // i ∉ root} :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_subtype_compl,
      Fintype.card_coe,hi,ht,hr,Fintype.card_fin])
  let e : I ≃ Fin 7 := (Equiv.sumCompl (· ∈ T)).symm.trans
    ((f.sumCongr g).trans (Equiv.sumCompl (· ∈ root)))
  refine ⟨e,eq_of_subset_of_card_le ?_ (by rw [card_map,ht,hr])⟩
  intro i hi
  obtain ⟨x,hx,rfl⟩ := mem_map.mp hi
  change e x ∈ root
  change (Equiv.sumCompl (· ∈ root))
    ((f.sumCongr g) ((Equiv.sumCompl (· ∈ T)).symm x)) ∈ root
  rw [Equiv.sumCompl_symm_apply_of_pos hx]
  exact (f ⟨x,hx⟩).property

/-- An intersecting family of triples on seven actual positions with complete
pair shadow is the full star or the Fano plane up to position relabelling.
There are no multiplicity or injectivity assumptions on any point indexing
that may have produced this family of supports. -/
theorem complete_pair_shadow {I : Type*} [Fintype I] [DecidableEq I]
    (hi : Fintype.card I = 7) (H : Family I)
    (hc : ∀ T ∈ H, T.card = 3)
    (hm : ∀ S ∈ H, ∀ T ∈ H, (S ∩ T).Nonempty)
    (hp : ∀ i j : I, i ≠ j → ∃ T ∈ H, i ∈ T ∧ j ∈ T) :
    (∃ c : I, ∀ T, T ∈ H ↔ T.card = 3 ∧ c ∈ T) ∨
    ∃ e : I ≃ Fin 7, relabel e H = univ.image line := by
  classical
  let first := Fintype.equivFinOfCardEq hi
  obtain ⟨T,hT,_,_⟩ := hp (first.symm 0) (first.symm 1)
    (by intro he; have := first.symm.injective he; contradiction)
  obtain ⟨f,hf⟩ := root_coordinates hi T (hc T hT)
  let G := relabel f H
  have hGc : ∀ U ∈ G, U.card = 3 := relabel_uniform f hc
  have hGm : ∀ U ∈ G, ∀ W ∈ G, (U ∩ W).Nonempty := by
    intro U hU W hW
    obtain ⟨A,hA,rfl⟩ := mem_map.mp hU
    obtain ⟨B,hB,rfl⟩ := mem_map.mp hW
    change (A.map f.toEmbedding ∩ B.map f.toEmbedding).Nonempty
    rw [← map_inter,map_nonempty]
    exact hm A hA B hB
  have hGp : ∀ i j : Fin 7, i ≠ j → ∃ U ∈ G, i ∈ U ∧ j ∈ U := by
    intro i j hij
    obtain ⟨U,hU,hiU,hjU⟩ := hp (f.symm i) (f.symm j)
      (fun he => hij (f.symm.injective he))
    refine ⟨U.map f.toEmbedding,(mem_relabel f H U).mpr hU,?_,?_⟩
    · exact mem_map.mpr ⟨f.symm i,hiU,f.apply_symm_apply i⟩
    · exact mem_map.mpr ⟨f.symm j,hjU,f.apply_symm_apply j⟩
  have hGr : root ∈ G := hf ▸ (mem_relabel f H T).mpr hT
  rcases rooted_shadow G hGc hGm hGp hGr with ⟨c,hstar⟩ | ⟨g,hfano⟩
  · left
    refine ⟨f.symm c,?_⟩
    intro U
    have he : U ∈ H ↔ U.map f.toEmbedding ∈ G := (mem_relabel f H U).symm
    rw [he,hstar]
    simp
  · right
    refine ⟨f.trans g.symm,?_⟩
    rw [← relabel_trans]
    change relabel g.symm G = _
    rw [hfano]
    change relabel g.symm (relabel g (univ.image line)) = _
    ext L
    simp only [relabel,mem_map]
    constructor
    · rintro ⟨A,⟨B,hB,rfl⟩,he⟩
      have hid : (B.map g.toEmbedding).map g.symm.toEmbedding = B := by
        ext i
        simp
      change (B.map g.toEmbedding).map g.symm.toEmbedding = L at he
      rw [hid] at he
      exact he ▸ hB
    · intro hL
      refine ⟨L.map g.toEmbedding,⟨L,hL,rfl⟩,?_⟩
      change (L.map g.toEmbedding).map g.symm.toEmbedding = L
      ext i
      simp

#guard_standard_axioms complete_pair_shadow

end CoveringDesigns.SevenBlock
