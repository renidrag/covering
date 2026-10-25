import CoveringDesigns.C19_9_3.ThreeRoots

/-! The remaining three-root pattern and exclusion of every minimum triple
of multiplicity three. Occurrence identities are never changed. -/
namespace CoveringDesigns.C19_9_3
open Finset SevenBlock
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- The two exceptional neighbours of a minimum point have common trace
two or four, never three. -/
theorem minimum_exceptional_trace {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x p q : V) (hx : indexedDegree B x = 7)
    (hpx : p ≠ x) (hqx : q ≠ x) (hpq : p ≠ q)
    (hp : indexedSubsetDegree B {x,p} = 4) (hq : indexedSubsetDegree B {x,q} = 4) :
    indexedSubsetDegree B {x,p,q} = 2 ∨ indexedSubsetDegree B {x,p,q} = 4 := by
  obtain ⟨u,v,_,_,_,_,_,hr,ht⟩ := minimum_profile hv h x hx
  have mem (z : V) (hzx : z ≠ x) (hz : indexedSubsetDegree B {x,z} = 4) : z = u ∨ z = v := by
    by_contra hn
    push Not at hn
    have := hr z hzx hn.1 hn.2
    omega
  rcases mem p hpx hp with rfl | rfl <;> rcases mem q hqx hq with rfl | rfl
  · contradiction
  · exact ht
  · simpa only [pair_comm p q] using ht
  · contradiction

private theorem companion_table (tag : Bool) : ∀ a b : TemplatePoint 2 tag,
    (templateSupport 2 tag a).card = 3 → (templateSupport 2 tag b).card = 4 →
    (templateSupport 2 tag a ∩ templateSupport 2 tag b).card = 3 →
    ∃ c : TemplatePoint 2 tag, c ≠ a ∧ c ≠ b ∧
      (((templateSupport 2 tag c).card = 3 ∧ templateSupport 2 tag c = templateSupport 2 tag a) ∨
       ((templateSupport 2 tag c).card = 4 ∧ templateSupport 2 tag c = templateSupport 2 tag b)) := by
  cases tag <;> decide +kernel

/-- A low trace contained in an exceptional trace has an actual companion:
either a second low point with the same trace, or the other exceptional
point with that exceptional trace. This retains point identities. -/
theorem minimum_contained_trace_companion {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (r x z : V) (hr : indexedDegree B r = 7)
    (hrx : r ≠ x) (hrz : r ≠ z)
    (hx : indexedSubsetDegree B {r,x} = 3) (hz : indexedSubsetDegree B {r,z} = 4)
    (ht : indexedSubsetDegree B {r,x,z} = 3) :
    ∃ w : V, w ≠ r ∧ w ≠ x ∧ w ≠ z ∧
      ((indexedSubsetDegree B {r,w} = 3 ∧
        pointSupport B r ∩ pointSupport B w = pointSupport B r ∩ pointSupport B x) ∨
       (indexedSubsetDegree B {r,w} = 4 ∧
        pointSupport B r ∩ pointSupport B w = pointSupport B r ∩ pointSupport B z)) := by
  obtain ⟨tag,e,g,_,hcoord⟩ := minimum_incidence_coordinates hv h r hr
  let x' : {v : V // v ∉ ({r} : Finset V)} := ⟨x,by simpa using hrx.symm⟩
  let z' : {v : V // v ∉ ({r} : Finset V)} := ⟨z,by simpa using hrz.symm⟩
  have hdegree (u : {v : V // v ∉ ({r} : Finset V)}) :
      (templateSupport 2 tag (e u)).card = indexedSubsetDegree B {r,u.val} := by
    rw [← pointSupport_pair,hcoord u,card_map]
  have hpair : (templateSupport 2 tag (e x') ∩ templateSupport 2 tag (e z')).card = 3 := by
    have heq : (pointSupport B r ∩ pointSupport B x) ∩ (pointSupport B r ∩ pointSupport B z) =
        pointSupport B r ∩ pointSupport B x ∩ pointSupport B z := by ext i; simp only [mem_inter]; tauto
    have hc := congrArg Finset.card heq
    rw [pointSupport_triple,ht] at hc
    rw [hcoord x',hcoord z',← map_inter,card_map] at hc
    exact hc
  obtain ⟨c,hcx,hcz,hc⟩ := companion_table tag (e x') (e z')
    ((hdegree x').trans hx) ((hdegree z').trans hz) hpair
  let w := e.symm c
  have hwc : e w = c := e.apply_symm_apply c
  refine ⟨w.val,by simpa using w.property,?_,?_,?_⟩
  · intro he
    apply hcx
    rw [← hwc]
    exact congrArg e (Subtype.ext he)
  · intro he
    apply hcz
    rw [← hwc]
    exact congrArg e (Subtype.ext he)
  rcases hc with hc | hc
  · left
    constructor
    · rw [← hdegree w,hwc,hc.1]
    · rw [hcoord w,hcoord x',hwc,hc.2]
  · right
    constructor
    · rw [← hdegree w,hwc,hc.1]
    · rw [hcoord w,hcoord z',hwc,hc.2]

private theorem pair_trace_subset {B : I → Finset V} (x y z : V)
    (ht : indexedSubsetDegree B {x,y,z} = indexedSubsetDegree B {x,y}) :
    pointSupport B x ∩ pointSupport B y ⊆ pointSupport B z := by
  have he := eq_of_subset_of_card_le
    (inter_subset_left (s₁ := pointSupport B x ∩ pointSupport B y) (s₂ := pointSupport B z))
    (by rw [pointSupport_pair,pointSupport_triple,ht])
  rw [← he]
  exact inter_subset_right

private theorem one_edge_partition (X Y Z T U : Finset I) (hi : Fintype.card I = 16)
    (hx : X.card = 7) (hy : Y.card = 7) (hz : Z.card = 7)
    (hxy : X ∩ Y = T) (hxz : X ∩ Z = T) (hyz : Y ∩ Z = U)
    (hT : T.card = 3) (hU : U.card = 4) :
    (univ \ (X ∪ Y ∪ Z)).card = 2 ∧ (U \ X).card = 1 := by
  have hYZ := card_union_add_card_inter Y Z
  rw [hy,hz,hyz,hU] at hYZ
  have hXi : X ∩ (Y ∪ Z) = T := by rw [inter_union_distrib_left,hxy,hxz,union_self]
  have hall := card_union_add_card_inter X (Y ∪ Z)
  rw [hx,hXi,hT] at hall
  have hN := card_sdiff_add_card_inter (univ : Finset I) (X ∪ Y ∪ Z)
  rw [univ_inter,card_univ,hi,union_assoc] at hN
  have hTX : T ⊆ Z := hxz ▸ inter_subset_right
  have hUi : U ∩ X = T := by
    rw [inter_comm,← hyz,← inter_assoc,hxy,inter_eq_left.mpr hTX]
  have hdiff := card_sdiff_add_card_inter U X
  rw [hUi,hT,hU] at hdiff
  rw [union_assoc]
  omega

private theorem support_union_bound (S X A N : Finset I) (hs : S ⊆ X ∪ A ∪ N) :
    S.card ≤ (S ∩ X).card + A.card + N.card := by
  have hsub : S ⊆ (S ∩ X) ∪ A ∪ N := by
    intro i hi
    have := hs hi
    simp only [mem_union,mem_inter] at this ⊢
    tauto
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))

private theorem no_one_excess_minimum_triple {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : indexedDegree B x = 7) (hy : indexedDegree B y = 7) (hz : indexedDegree B z = 7)
    (hxy₃ : indexedSubsetDegree B {x,y} = 3)
    (hxz₃ : indexedSubsetDegree B {x,z} = 3)
    (hyz₄ : indexedSubsetDegree B {y,z} = 4)
    (ht : indexedSubsetDegree B {x,y,z} = 3) : False := by
  let X := pointSupport B x
  let Y := pointSupport B y
  let Z := pointSupport B z
  let T := X ∩ Y
  let U := Y ∩ Z
  let N := univ \ (X ∪ Y ∪ Z)
  have hT : T.card = 3 := (pointSupport_pair B x y).trans hxy₃
  have hU : U.card = 4 := (pointSupport_pair B y z).trans hyz₄
  have hTZ : T ⊆ Z := pair_trace_subset x y z (ht.trans hxy₃.symm)
  have hXZ : X ∩ Z = T := by
    symm
    apply eq_of_subset_of_card_le (subset_inter inter_subset_left hTZ)
    rw [pointSupport_pair,hxz₃,hT]
  have hpart := one_edge_partition X Y Z T U hi
    ((pointSupport_card B x).trans hx) ((pointSupport_card B y).trans hy)
    ((pointSupport_card B z).trans hz) rfl hXZ rfl hT hU
  have hN : N.card = 2 := hpart.1
  have hUX : (U \ X).card = 1 := hpart.2
  obtain ⟨w,hwy,hwx,hwz,hw⟩ := minimum_contained_trace_companion hv h y x z hy
    hxy.symm hyz (by rw [pair_comm]; exact hxy₃) hyz₄
    (by rw [insert_comm]; exact ht)
  have hfloor := degree_floor hv h w
  have hxw := minimum_pair_le_four hv h x w hx hwx.symm
  have hyw := minimum_pair_le_four hv h y w hy hwy.symm
  have hzw := minimum_pair_le_four hv h z w hz hwz.symm
  rcases hw with ⟨hyw3,hYw⟩ | ⟨hyw4,hYw⟩
  · have hYwT : Y ∩ pointSupport B w = T := hYw.trans (inter_comm Y X)
    have hTw : T ⊆ pointSupport B w := hYwT ▸ inter_subset_right
    have hzyw : indexedSubsetDegree B {z,y,w} = 3 := by
      rw [← pointSupport_triple,inter_assoc,inter_comm Z,hYwT,inter_eq_left.mpr hTZ,hT]
    have hzw3 : indexedSubsetDegree B {z,w} = 3 := by
      have hlo := pair_floor hv h (card_pair hwz.symm)
      by_contra hn
      have hzw4 : indexedSubsetDegree B {z,w} = 4 := by omega
      have ht' := minimum_exceptional_trace hv h z y w hz hyz hwz hwy.symm
        (by rw [pair_comm]; exact hyz₄) hzw4
      omega
    have hZwT : Z ∩ pointSupport B w = T := by
      symm
      apply eq_of_subset_of_card_le (subset_inter hTZ hTw)
      rw [pointSupport_pair,hzw3,hT]
    have hsub : pointSupport B w ⊆ X ∪ ∅ ∪ N := by
      intro i hiw
      by_cases hix : i ∈ X
      · exact mem_union_left _ (mem_union_left _ hix)
      have hiy : i ∉ Y := by
        intro hiY
        have hit : i ∈ T := hYwT ▸ mem_inter.mpr ⟨hiY,hiw⟩
        exact hix (mem_inter.mp hit).1
      have hiz : i ∉ Z := by
        intro hiZ
        have hit : i ∈ T := hZwT ▸ mem_inter.mpr ⟨hiZ,hiw⟩
        exact hix (mem_inter.mp hit).1
      exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,by simp only [mem_union]; tauto⟩)
    have hc := support_union_bound (pointSupport B w) X ∅ N hsub
    rw [pointSupport_card,pointSupport_pair,pair_comm w x,card_empty,hN] at hc
    omega
  · have hYwU : Y ∩ pointSupport B w = U := hYw
    have hUw : U ⊆ pointSupport B w := hYwU ▸ inter_subset_right
    have hZwU : Z ∩ pointSupport B w = U := by
      symm
      apply eq_of_subset_of_card_le (subset_inter inter_subset_right hUw)
      rw [pointSupport_pair,hU]
      exact hzw
    have hzw4 : indexedSubsetDegree B {z,w} = 4 := by
      rw [← pointSupport_pair,hZwU,hU]
    have hsub : pointSupport B w ⊆ X ∪ (U \ X) ∪ N := by
      intro i hiw
      by_cases hix : i ∈ X
      · exact mem_union_left _ (mem_union_left _ hix)
      by_cases hiU : i ∈ U
      · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨hiU,hix⟩))
      have hiy : i ∉ Y := fun hiY => hiU (hYwU ▸ mem_inter.mpr ⟨hiY,hiw⟩)
      have hiz : i ∉ Z := fun hiZ => hiU (hZwU ▸ mem_inter.mpr ⟨hiZ,hiw⟩)
      exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,by simp only [mem_union]; tauto⟩)
    have hc := support_union_bound (pointSupport B w) X (U \ X) N hsub
    rw [pointSupport_card,pointSupport_pair,pair_comm w x,hUX,hN] at hc
    have hw7 : indexedDegree B w = 7 := by omega
    have hxw4 : indexedSubsetDegree B {x,w} = 4 := by omega
    exact no_three_minimum_exceptions hv h w x y z hw7 hwx.symm hwy.symm hwz.symm
      hxy hxz hyz (by rw [pair_comm]; exact hxw4)
      (by rw [pair_comm]; exact hyw4) (by rw [pair_comm]; exact hzw4)

/-- No triple of minimum points can have multiplicity three. Pair floors,
both link forms and all three-root compatibility premises are derived. -/
theorem no_minimum_triple_three {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : indexedDegree B x = 7) (hy : indexedDegree B y = 7) (hz : indexedDegree B z = 7) :
    indexedSubsetDegree B {x,y,z} ≠ 3 := by
  intro ht
  have hxyL := pair_floor hv h (card_pair hxy)
  have hxzL := pair_floor hv h (card_pair hxz)
  have hyzL := pair_floor hv h (card_pair hyz)
  have hxyU := minimum_pair_le_four hv h x y hx hxy
  have hxzU := minimum_pair_le_four hv h x z hx hxz
  have hyzU := minimum_pair_le_four hv h y z hy hyz
  by_cases hxy3 : indexedSubsetDegree B {x,y} = 3
  · by_cases hxz3 : indexedSubsetDegree B {x,z} = 3
    · by_cases hyz3 : indexedSubsetDegree B {y,z} = 3
      · exact no_three_ordinary_minima hv h hi x y z hxy hxz hyz hx hy hz hxy3 hxz3 hyz3 ht
      · exact no_one_excess_minimum_triple hv h hi x y z hxy hxz hyz hx hy hz hxy3 hxz3 (by omega) ht
    · have hxz4 : indexedSubsetDegree B {x,z} = 4 := by omega
      by_cases hyz3 : indexedSubsetDegree B {y,z} = 3
      · exact no_one_excess_minimum_triple hv h hi y x z hxy.symm hyz hxz hy hx hz
          (by rw [pair_comm]; exact hxy3) hyz3 hxz4 (by rw [insert_comm]; exact ht)
      · have hh := minimum_exceptional_trace hv h z x y hz hxz hyz hxy
          (by rw [pair_comm]; exact hxz4) (by rw [pair_comm]; omega)
        have ht' : indexedSubsetDegree B {z,x,y} = 3 := by
          rw [insert_comm z x,pair_comm z y]
          exact ht
        omega
  · have hxy4 : indexedSubsetDegree B {x,y} = 4 := by omega
    by_cases hxz3 : indexedSubsetDegree B {x,z} = 3
    · by_cases hyz3 : indexedSubsetDegree B {y,z} = 3
      · exact no_one_excess_minimum_triple hv h hi z x y hxz.symm hyz.symm hxy hz hx hy
          (by rw [pair_comm]; exact hxz3) (by rw [pair_comm]; exact hyz3) hxy4
          (by rw [insert_comm z x,pair_comm z y]; exact ht)
      · have hh := minimum_exceptional_trace hv h y x z hy hxy hyz.symm hxz
          (by rw [pair_comm]; exact hxy4) (by omega)
        have ht' : indexedSubsetDegree B {y,x,z} = 3 := by rw [insert_comm]; exact ht
        omega
    · have hh := minimum_exceptional_trace hv h x y z hx hxy.symm hxz.symm hyz hxy4 (by omega)
      omega

#guard_standard_axioms minimum_exceptional_trace minimum_contained_trace_companion no_minimum_triple_three
end CoveringDesigns.C19_9_3
