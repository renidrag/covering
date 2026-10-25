import CoveringDesigns.C19_9_3.MinimumPoints
import CoveringDesigns.C19_9_3.AffineModel

/-! Recognition of the common affine configuration from actual minimum-point
traces. The occurrence embeddings in the conclusion refer to the original
parent occurrence type. -/
namespace CoveringDesigns.C19_9_3
open Finset SevenBlock
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- At a minimum root, all seven low Fano lines are occupied exactly once
by the other minimum points. Both embeddings retain actual identities. -/
theorem minimum_root_fano {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (x : V) (hx : indexedDegree B x = 7) :
    ∃ (g : Fin 7 ↪ I) (p : Fin 7 ↪ V),
      pointSupport B x = univ.map g ∧ univ.map p = (minimumPoints B).erase x ∧
      ∀ l i, p l ∈ B (g i) ↔ i ∈ line l := by
  classical
  obtain ⟨tag,e,g,hg,hcoord⟩ := minimum_incidence_coordinates hv h x hx
  let O := {y : V // y ∈ minimumPoints B ∧ y ≠ x}
  have hcO : Fintype.card O = 7 := by
    have he : (univ.filter fun y : V => y ∈ minimumPoints B ∧ y ≠ x) = (minimumPoints B).erase x := by
      ext y
      simp only [mem_filter,mem_univ,true_and,mem_erase,and_comm]
    change Fintype.card {y : V // y ∈ minimumPoints B ∧ y ≠ x} = 7
    rw [Fintype.card_subtype,he,card_erase_of_mem ((mem_minimumPoints B x).mpr hx),minimum_points_card hv h hi]
  have hex (y : O) : ∃ l, pointSupport B x ∩ pointSupport B y.val = (line l).map g := by
    let y' : {v : V // v ∉ ({x} : Finset V)} := ⟨y.val,by simpa using y.property.2⟩
    have hy3 := minimum_pair_ordinary hv h hi x y.val hx
      ((mem_minimumPoints B y.val).mp y.property.1) y.property.2.symm
    have hcard : (templateSupport 2 tag (e y')).card = 3 := by
      rw [← card_map (f := g),← hcoord y',pointSupport_pair,hy3]
    cases he : e y' with
    | inl b => rw [he,templateSupport,high_card] at hcard; contradiction
    | inr v => exact ⟨v.1,by rw [hcoord y',he]; rfl⟩
  choose lab hlab using hex
  have hinj : Function.Injective lab := by
    intro u v huv
    apply Subtype.ext
    by_contra hne
    have hsame := (hlab u).trans (congrArg (fun l => (line l).map g) huv)
    have heq : pointSupport B x ∩ pointSupport B u.val = pointSupport B x ∩ pointSupport B v.val :=
      hsame.trans (hlab v).symm
    have ht : indexedSubsetDegree B {x,u.val,v.val} = 3 := by
      rw [← pointSupport_triple]
      have hs : (pointSupport B x ∩ pointSupport B u.val) ∩ pointSupport B v.val =
          (pointSupport B x ∩ pointSupport B u.val) ∩ (pointSupport B x ∩ pointSupport B v.val) := by
        ext i
        simp only [mem_inter]
        tauto
      rw [hs,heq,inter_self,hlab v,card_map,line_card]
    exact no_minimum_triple_three hv h hi x u.val v.val u.property.2.symm v.property.2.symm hne hx
      ((mem_minimumPoints B u.val).mp u.property.1) ((mem_minimumPoints B v.val).mp v.property.1) ht
  let f : O ≃ Fin 7 := Equiv.ofBijective lab
    ((Fintype.bijective_iff_injective_and_card lab).mpr ⟨hinj,by rw [hcO,Fintype.card_fin]⟩)
  let p : Fin 7 ↪ V := f.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hp (l : Fin 7) : p l ∈ minimumPoints B ∧ p l ≠ x := (f.symm l).property
  refine ⟨g,p,hg,?_,?_⟩
  · ext y
    simp only [mem_map,mem_univ,true_and,mem_erase]
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨(hp l).2,(hp l).1⟩
    · rintro ⟨hyx,hyM⟩
      let y' : O := ⟨y,hyM,hyx⟩
      exact ⟨f y',congrArg Subtype.val (f.symm_apply_apply y')⟩
  · intro l i
    have hc := hlab (f.symm l)
    have hfl : lab (f.symm l) = l := f.apply_symm_apply l
    rw [hfl] at hc
    have hix : g i ∈ pointSupport B x := hg ▸ mem_map.mpr ⟨i,mem_univ _,rfl⟩
    constructor
    · intro hip
      have hmem : g i ∈ (line l).map g := hc ▸ mem_inter.mpr ⟨hix,(mem_pointSupport B (p l) (g i)).mpr hip⟩
      exact mem_map.mp hmem |>.elim fun j hj => (g.injective hj.2) ▸ hj.1
    · intro hil
      have hmem : g i ∈ pointSupport B x ∩ pointSupport B (p l) :=
        hc.symm ▸ mem_map.mpr ⟨i,hil,rfl⟩
      exact (mem_pointSupport B (p l) (g i)).mp (mem_inter.mp hmem).2

/-- Every actual occurrence meeting the minimum points has exactly four of
them. Occurrences avoiding them are allowed and will be identified later. -/
theorem minimum_trace_four {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (i : I) (x : V) (hxM : x ∈ minimumPoints B) (hxi : x ∈ B i) :
    (B i ∩ minimumPoints B).card = 4 := by
  obtain ⟨g,p,hg,hp,hinc⟩ := minimum_root_fano hv h hi x ((mem_minimumPoints B x).mp hxM)
  have him : i ∈ univ.map g := hg ▸ (mem_pointSupport B x i).mpr hxi
  obtain ⟨j,_,rfl⟩ := mem_map.mp him
  have hrest : B (g j) ∩ (minimumPoints B).erase x =
      (univ.filter fun l : Fin 7 => j ∈ line l).map p := by
    ext y
    rw [← hp]
    simp only [mem_inter,mem_map,mem_univ,true_and,mem_filter]
    constructor
    · rintro ⟨hyi,l,rfl⟩
      exact ⟨l,(hinc l j).mp hyi,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨(hinc l j).mpr hl,l,rfl⟩
  have he : B (g j) ∩ minimumPoints B = insert x (B (g j) ∩ (minimumPoints B).erase x) := by
    ext y
    simp only [mem_inter,mem_insert,mem_erase]
    constructor
    · rintro ⟨hyB,hyM⟩
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr ⟨hyB,hyx,hyM⟩
    · rintro (rfl | ⟨hyB,_,hyM⟩)
      · exact ⟨hxi,hxM⟩
      · exact ⟨hyB,hyM⟩
  rw [he,card_insert_of_notMem (by simp),hrest,card_map,position_degree]

theorem minimum_subset_multiplicity {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (T : Finset V) (hT : T ⊆ minimumPoints B) (hc : T.card = 3) :
    indexedSubsetDegree B T = 1 := by
  obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩ := card_eq_three.mp hc
  exact minimum_triple_one hv h hi x y z hxy hxz hyz
    ((mem_minimumPoints B x).mp (hT (by simp)))
    ((mem_minimumPoints B y).mp (hT (by simp)))
    ((mem_minimumPoints B z).mp (hT (by simp)))

/-- Different actual occurrences cannot share three minimum points. -/
theorem minimum_traces_intersection {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (i j : I) (hij : i ≠ j) :
    ((B i ∩ minimumPoints B) ∩ (B j ∩ minimumPoints B)).card ≤ 2 := by
  by_contra hn
  obtain ⟨T,hT,hc⟩ := exists_subset_card_eq (show 3 ≤
    ((B i ∩ minimumPoints B) ∩ (B j ∩ minimumPoints B)).card by omega)
  have hm : T ⊆ minimumPoints B := hT.trans (inter_subset_left.trans inter_subset_right)
  have hcount := minimum_subset_multiplicity hv h hi T hm hc
  have hpair : ({i,j} : Finset I) ⊆ univ.filter fun k => T ⊆ B k := by
    intro k hk
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    simp only [mem_insert,mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hT.trans (inter_subset_left.trans inter_subset_left)
    · exact hT.trans (inter_subset_right.trans inter_subset_left)
  have hle := card_le_card hpair
  change ({i,j} : Finset I).card ≤ indexedSubsetDegree B T at hle
  rw [card_pair hij,hcount] at hle
  omega

private def linePoint : Fin 7 → Fin 8 := ![4,2,6,1,5,3,7]

section FixedGeometry
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

private theorem linePoint_injective : Function.Injective linePoint := by decide +kernel
private theorem linePoint_ne_zero : ∀ l, linePoint l ≠ 0 := by decide +kernel
private theorem linePoint_incidence : ∀ l n, orientation n (linePoint l) = false ↔ n ∈ line l := by
  decide +kernel
private theorem orientation_zero : ∀ n, orientation n 0 = false := by decide +kernel

/-- Recognition tests one four-point trace against the seven planes through
zero. This is a fixed geometry fact, not an enumeration of coverings. -/
private theorem affine_four_trace_recognition : ∀ S ∈ (univ : Finset (Fin 8)).powersetCard 4,
    (∀ n : Fin 7, 3 ≤ (S ∩ affinePlane (n,false)).card → S = affinePlane (n,false)) →
    ∃ n : Fin 7, ∃ b : Bool, S = affinePlane (n,b) := by
  decide +kernel

private theorem affine_planes_injective : Function.Injective affinePlane := by decide +kernel
private theorem affine_planes_intersection : ∀ p q : PlanePosition, p ≠ q →
    (affinePlane p ∩ affinePlane q).card ≤ 2 := by
  rintro ⟨n,b⟩ ⟨m,c⟩
  cases b <;> cases c <;> revert n m <;> decide +kernel

end FixedGeometry

private theorem root_point_coordinates {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (x : V) (hx : indexedDegree B x = 7) :
    ∃ (e : ↥(minimumPoints B) ≃ Fin 8) (g : Fin 7 ↪ I),
      (∀ n, (univ.filter fun v : ↥(minimumPoints B) => v.val ∈ B (g n)).map e.toEmbedding =
        affinePlane (n,false)) := by
  classical
  obtain ⟨g,p,hg,hp,hinc⟩ := minimum_root_fano hv h hi x hx
  have hpx (l : Fin 7) : p l ≠ x := by
    have hh : p l ∈ (minimumPoints B).erase x := hp ▸ mem_map.mpr ⟨l,mem_univ _,rfl⟩
    exact (mem_erase.mp hh).1
  have hex (v : ↥(minimumPoints B)) (hvn : v.val ≠ x) : ∃ l, p l = v.val := by
    have hh : v.val ∈ (minimumPoints B).erase x := mem_erase.mpr ⟨hvn,v.property⟩
    rw [← hp] at hh
    simpa only [mem_map,mem_univ,true_and] using hh
  let coord (v : ↥(minimumPoints B)) : Fin 8 :=
    if hvn : v.val = x then 0 else linePoint (Classical.choose (hex v hvn))
  have hcroot (v : ↥(minimumPoints B)) (hvx : v.val = x) : coord v = 0 := by simp only [coord,dif_pos hvx]
  have hclow (v : ↥(minimumPoints B)) (l : Fin 7) (hvl : p l = v.val) : coord v = linePoint l := by
    have hvn : v.val ≠ x := fun heq => hpx l (hvl.trans heq)
    have hl : Classical.choose (hex v hvn) = l := p.injective ((Classical.choose_spec (hex v hvn)).trans hvl.symm)
    simp only [coord,dif_neg hvn,hl]
  have hinj : Function.Injective coord := by
    intro u v he
    by_cases hux : u.val = x
    · by_cases hvx : v.val = x
      · exact Subtype.ext (hux.trans hvx.symm)
      · obtain ⟨l,hl⟩ := hex v hvx
        rw [hcroot u hux,hclow v l hl] at he
        exact False.elim (linePoint_ne_zero l he.symm)
    · obtain ⟨l,hl⟩ := hex u hux
      by_cases hvx : v.val = x
      · rw [hclow u l hl,hcroot v hvx] at he
        exact False.elim (linePoint_ne_zero l he)
      · obtain ⟨m,hm⟩ := hex v hvx
        rw [hclow u l hl,hclow v m hm] at he
        exact Subtype.ext (hl.symm.trans ((congrArg p (linePoint_injective he)).trans hm))
  let e : ↥(minimumPoints B) ≃ Fin 8 := Equiv.ofBijective coord
    ((Fintype.bijective_iff_injective_and_card coord).mpr
      ⟨hinj,by rw [Fintype.card_coe,minimum_points_card hv h hi,Fintype.card_fin]⟩)
  refine ⟨e,g,?_⟩
  intro n
  ext u
  obtain ⟨v,rfl⟩ := e.surjective u
  simp only [mem_map_equiv,Equiv.symm_apply_apply,mem_filter,mem_univ,true_and,affinePlane]
  change v.val ∈ B (g n) ↔ orientation n (coord v) = false
  by_cases hvx : v.val = x
  · rw [hcroot v hvx,orientation_zero]
    simp only [iff_true,hvx]
    exact (mem_pointSupport B x (g n)).mp (hg.symm ▸ mem_map.mpr ⟨n,mem_univ _,rfl⟩)
  · obtain ⟨l,hl⟩ := hex v hvx
    rw [hclow v l hl,linePoint_incidence,← hl]
    exact hinc l n

private def coordinatedTrace (B : I → Finset V) (e : ↥(minimumPoints B) ≃ Fin 8) (i : I) :
    Finset (Fin 8) := ((B i).subtype (· ∈ minimumPoints B)).map e.toEmbedding

private theorem coordinatedTrace_card (B : I → Finset V) (e : ↥(minimumPoints B) ≃ Fin 8) (i : I) :
    (coordinatedTrace B e i).card = (B i ∩ minimumPoints B).card := by
  rw [coordinatedTrace,card_map,card_subtype,filter_mem_eq_inter]

private theorem coordinatedTrace_inter (B : I → Finset V) (e : ↥(minimumPoints B) ≃ Fin 8) (i j : I) :
    (coordinatedTrace B e i ∩ coordinatedTrace B e j).card =
      ((B i ∩ minimumPoints B) ∩ (B j ∩ minimumPoints B)).card := by
  have heq : coordinatedTrace B e i ∩ coordinatedTrace B e j =
      ((B i ∩ B j).subtype (· ∈ minimumPoints B)).map e.toEmbedding := by
    ext x
    simp [coordinatedTrace]
  rw [heq,card_map,card_subtype,filter_mem_eq_inter]
  congr 1
  ext x
  simp only [mem_inter]
  tauto

private theorem nonempty_trace_card {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (e : ↥(minimumPoints B) ≃ Fin 8) (i : I) (hne : (coordinatedTrace B e i).Nonempty) :
    (coordinatedTrace B e i).card = 4 := by
  obtain ⟨v,hvm⟩ := hne
  obtain ⟨u,hu,_⟩ := mem_map.mp hvm
  rw [coordinatedTrace_card]
  exact minimum_trace_four hv h hi i u.val u.property (mem_subtype.mp hu)

private theorem fourteen_traces {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (e : ↥(minimumPoints B) ≃ Fin 8) :
    (univ.filter fun i => (coordinatedTrace B e i).Nonempty).card = 14 := by
  let A : I → Finset ↥(minimumPoints B) := fun i => (B i).subtype (· ∈ minimumPoints B)
  have hdeg (x : ↥(minimumPoints B)) : indexedDegree A x = 7 := by
    have he : indexedDegree A x = indexedDegree B x.val := by simp only [indexedDegree,A,mem_subtype]
    exact he.trans ((mem_minimumPoints B x.val).mp x.property)
  have hs := Multicover.degree_sum A
  have hc (i : I) : (A i).card = if (coordinatedTrace B e i).Nonempty then 4 else 0 := by
    have hm : (A i).card = (coordinatedTrace B e i).card := (card_map _).symm
    rw [hm]
    by_cases hn : (coordinatedTrace B e i).Nonempty
    · rw [if_pos hn,nonempty_trace_card hv h hi e i hn]
    · rw [if_neg hn,not_nonempty_iff_eq_empty.mp hn,card_empty]
  simp only [hdeg,sum_const,card_univ,Fintype.card_coe,minimum_points_card hv h hi,Nat.nsmul_eq_mul,hc] at hs
  have hsum : (∑ i : I, if (coordinatedTrace B e i).Nonempty then 4 else 0) =
      4 * (univ.filter fun i => (coordinatedTrace B e i).Nonempty).card := by
    rw [← sum_filter,sum_const,Nat.nsmul_eq_mul,mul_comm]
  rw [hsum] at hs
  omega

/-- One shared affine configuration of the actual minimum points and
occurrences, including the two occurrences avoiding every minimum point. -/
structure AffineConfiguration (B : I → Finset V) where
  points : ↥(minimumPoints B) ≃ Fin 8
  planes : PlanePosition ↪ I
  empty : Bool ↪ I
  incidence : ∀ p (x : ↥(minimumPoints B)), x.val ∈ B (planes p) ↔ points x ∈ affinePlane p
  avoidance : ∀ b (x : ↥(minimumPoints B)), x.val ∉ B (empty b)
  partition : ∀ i : I, (∃ p, planes p = i) ∨ ∃ b, empty b = i
  disjoint : ∀ p b, planes p ≠ empty b

/-- Recognition of the actual fourteen affine traces and two empty traces.
All structural premises are derived from the parent covering. -/
theorem actual_affine_configuration {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16) : Nonempty (AffineConfiguration B) := by
  classical
  have hM := minimum_points_card hv h hi
  obtain ⟨x,hxM⟩ := card_pos.mp (show 0 < (minimumPoints B).card by omega)
  obtain ⟨e,g,hroot⟩ := root_point_coordinates hv h hi x ((mem_minimumPoints B x).mp hxM)
  have hroot' (n : Fin 7) : coordinatedTrace B e (g n) = affinePlane (n,false) := by
    have heq : (B (g n)).subtype (· ∈ minimumPoints B) =
        univ.filter fun v : ↥(minimumPoints B) => v.val ∈ B (g n) := by ext v; simp
    rw [coordinatedTrace,heq,hroot]
  let P := univ.filter fun i => (coordinatedTrace B e i).Nonempty
  have hcP : P.card = 14 := fourteen_traces hv h hi e
  have hex (i : ↥P) : ∃ p : PlanePosition, coordinatedTrace B e i.val = affinePlane p := by
    have hfour := nonempty_trace_card hv h hi e i.val (mem_filter.mp i.property).2
    obtain ⟨n,b,hp⟩ := affine_four_trace_recognition (coordinatedTrace B e i.val)
      (mem_powersetCard_univ.mpr hfour) (by
        intro n hn
        by_cases heq : i.val = g n
        · rw [heq,hroot']
        · have hle := minimum_traces_intersection hv h hi i.val (g n) heq
          rw [← coordinatedTrace_inter B e,hroot'] at hle
          omega)
    exact ⟨(n,b),hp⟩
  choose plane hplane using hex
  have hinj : Function.Injective plane := by
    intro i j heq
    apply Subtype.ext
    by_contra hne
    have hh := minimum_traces_intersection hv h hi i.val j.val hne
    rw [← coordinatedTrace_inter B e,hplane i,hplane j,heq,inter_self,affine_plane_card] at hh
    omega
  let f : ↥P ≃ PlanePosition := Equiv.ofBijective plane
    ((Fintype.bijective_iff_injective_and_card plane).mpr
      ⟨hinj,by rw [Fintype.card_coe,hcP,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]⟩)
  let planes : PlanePosition ↪ I := f.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hplanes (p : PlanePosition) : coordinatedTrace B e (planes p) = affinePlane p := by
    have hh := hplane (f.symm p)
    have hf : plane (f.symm p) = p := f.apply_symm_apply p
    exact hh.trans (congrArg affinePlane hf)
  let N := univ \ P
  have hcN : N.card = 2 := by
    have hh := card_sdiff_add_card_inter (univ : Finset I) P
    simp only [univ_inter,card_univ,hi,hcP] at hh
    change N.card + 14 = 16 at hh
    omega
  let k : Bool ≃ ↥N := Fintype.equivOfCardEq (by rw [Fintype.card_bool,Fintype.card_coe,hcN])
  let empty : Bool ↪ I := k.toEmbedding.trans (Function.Embedding.subtype _)
  have hN (b : Bool) : empty b ∉ P := (mem_sdiff.mp (k b).property).2
  refine ⟨⟨e,planes,empty,?_,?_,?_,?_⟩⟩
  · intro p u
    have hh : e u ∈ coordinatedTrace B e (planes p) ↔ u.val ∈ B (planes p) := by
      simp only [coordinatedTrace,mem_map_equiv,Equiv.symm_apply_apply,mem_subtype]
    rw [hplanes] at hh
    exact hh.symm
  · intro b u hu
    apply hN b
    apply mem_filter.mpr
    exact ⟨mem_univ _,⟨e u,mem_map.mpr ⟨u,mem_subtype.mpr hu,rfl⟩⟩⟩
  · intro i
    by_cases hip : i ∈ P
    · left
      exact ⟨f ⟨i,hip⟩,congrArg Subtype.val (f.symm_apply_apply ⟨i,hip⟩)⟩
    · right
      let i' : ↥N := ⟨i,mem_sdiff.mpr ⟨mem_univ _,hip⟩⟩
      exact ⟨k.symm i',congrArg Subtype.val (k.apply_symm_apply i')⟩
  · intro p b heq
    exact hN b (heq ▸ (f.symm p).property)

#guard_standard_axioms minimum_root_fano minimum_trace_four minimum_subset_multiplicity
  minimum_traces_intersection actual_affine_configuration
end CoveringDesigns.C19_9_3
