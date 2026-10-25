import CoveringDesigns.C19_9_3.RootPartition

/-! Compatibility of three minimum roots, with one common occurrence set. -/
namespace CoveringDesigns.C19_9_3
open Finset SevenBlock
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

private theorem full_trace {B : I → Finset V} (x y z : V)
    (ht : indexedSubsetDegree B {x,y,z} = indexedSubsetDegree B {x,y}) :
    pointSupport B x ∩ pointSupport B y ⊆ pointSupport B z := by
  have he : pointSupport B x ∩ pointSupport B y ∩ pointSupport B z =
      pointSupport B x ∩ pointSupport B y := by
    apply eq_of_subset_of_card_le inter_subset_left
    rw [pointSupport_triple,pointSupport_pair,ht]
  rw [← he]
  exact inter_subset_right

private theorem ordinary_thirds_singleton {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : indexedDegree B x = 7) (hy : indexedDegree B y = 7) (hz : indexedDegree B z = 7)
    (hxy₃ : indexedSubsetDegree B {x,y} = 3)
    (hxz₃ : indexedSubsetDegree B {x,z} = 3)
    (hyz₃ : indexedSubsetDegree B {y,z} = 3)
    (ht : indexedSubsetDegree B {x,y,z} = 3) : thirdPoints B x y 3 = {z} := by
  ext w
  constructor
  · intro hw
    have hwxy := (mem_sdiff.mp (mem_filter.mp hw).1).2
    have hwt := (mem_filter.mp hw).2
    have hwx : w ≠ x := fun he => hwxy (by simp [he])
    have hwy : w ≠ y := fun he => hwxy (by simp [he])
    apply mem_singleton.mpr
    by_contra hwz
    apply three_ordinary_roots_no_fourth hv h hi x y z hxy hxz hyz hx hy hz
      hxy₃ hxz₃ hyz₃ ht w hwx hwy hwz
    exact inter_subset_left.trans (full_trace x y w (hwt.trans hxy₃.symm))
  · intro hw
    have hwz := mem_singleton.mp hw
    subst w
    simp only [thirdPoints,mem_filter,mem_sdiff,mem_univ,true_and,mem_insert,mem_singleton]
    exact ⟨by tauto,ht⟩

private theorem two_exceptions_exhaust {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (x p q : V) (hx : indexedDegree B x = 7)
    (hpx : p ≠ x) (hqx : q ≠ x) (hpq : p ≠ q)
    (hp : indexedSubsetDegree B {x,p} = 4) (hq : indexedSubsetDegree B {x,q} = 4)
    (w : V) (hwx : w ≠ x) (hwp : w ≠ p) (hwq : w ≠ q) :
    indexedSubsetDegree B {x,w} = 3 := by
  have hl := pair_floor hv h (card_pair hwx.symm)
  have hu := minimum_pair_le_four hv h x w hx hwx.symm
  have hn : indexedSubsetDegree B {x,w} ≠ 4 := by
    intro hw
    exact no_three_minimum_exceptions hv h x p q w hx hpx hqx hwx hpq hwp.symm hwq.symm hp hq hw
  omega

private theorem ordinary_common_exceptions {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : indexedDegree B x = 7) (hy : indexedDegree B y = 7) (hz : indexedDegree B z = 7)
    (hxy₃ : indexedSubsetDegree B {x,y} = 3)
    (hxz₃ : indexedSubsetDegree B {x,z} = 3)
    (hyz₃ : indexedSubsetDegree B {y,z} = 3)
    (ht : indexedSubsetDegree B {x,y,z} = 3) :
    ∃ p q : V, p ≠ q ∧ p ∉ ({x,y,z} : Finset V) ∧ q ∉ ({x,y,z} : Finset V) ∧
      thirdPoints B x y 2 = {p,q} ∧
      indexedSubsetDegree B {x,p} = 4 ∧ indexedSubsetDegree B {y,p} = 4 ∧
      indexedSubsetDegree B {z,p} = 4 ∧
      indexedSubsetDegree B {x,q} = 4 ∧ indexedSubsetDegree B {y,q} = 4 ∧
      indexedSubsetDegree B {z,q} = 4 ∧
      8 ≤ indexedDegree B p ∧ 8 ≤ indexedDegree B q := by
  have h3 := ordinary_thirds_singleton hv h hi x y z hxy hxz hyz hx hy hz hxy₃ hxz₃ hyz₃ ht
  have h2 : (thirdPoints B x y 2).card = 2 := by
    have hh := minimum_ordinary_pair_profile hv h x y hx hxy hxy₃
    rw [h3,card_singleton] at hh
    omega
  obtain ⟨p,q,hpq,hP⟩ := card_eq_two.mp h2
  have facts (w : V) (hw : w ∈ thirdPoints B x y 2) :
      w ∉ ({x,y,z} : Finset V) ∧
      indexedSubsetDegree B {x,w} = 4 ∧ indexedSubsetDegree B {y,w} = 4 ∧
      indexedSubsetDegree B {z,w} = 4 ∧ 8 ≤ indexedDegree B w := by
    have hxyw := (mem_sdiff.mp (mem_filter.mp hw).1).2
    have htw := (mem_filter.mp hw).2
    have hwx : w ≠ x := fun he => hxyw (by simp [he])
    have hwy : w ≠ y := fun he => hxyw (by simp [he])
    have hwz : w ≠ z := by intro he; subst w; omega
    have hwp := minimum_two_trace_agreement hv h x y w hx hy hxy hwx.symm hwy.symm hxy₃ htw
    have hcore : pointSupport B x ∩ pointSupport B y = pointSupport B x ∩ pointSupport B z := by
      have hL := full_trace x y z (ht.trans hxy₃.symm)
      have hR := full_trace (B := B) x z y (by
        rw [pair_comm z y]
        exact ht.trans hxz₃.symm)
      apply subset_antisymm
      · exact subset_inter inter_subset_left hL
      · exact subset_inter inter_subset_left hR
    have htxz : indexedSubsetDegree B {x,z,w} = 2 := by
      rw [← pointSupport_triple,← hcore,pointSupport_triple]
      exact htw
    have hwz4 := (minimum_two_trace_agreement hv h x z w hx hz hxz hwx.symm hwz.symm hxz₃ htxz).2
    have hfloor := degree_floor hv h w
    have hn : indexedDegree B w ≠ 7 := by
      intro hd
      exact no_three_minimum_exceptions hv h w x y z hd hwx.symm hwy.symm hwz.symm hxy hxz hyz
        (by simpa only [pair_comm] using hwp.1)
        (by simpa only [pair_comm] using hwp.2)
        (by simpa only [pair_comm] using hwz4)
    exact ⟨by simpa only [mem_insert,mem_singleton,not_or] using ⟨hwx,hwy,hwz⟩,
      hwp.1,hwp.2,hwz4,by omega⟩
  have hp := facts p (by rw [hP]; simp)
  have hq := facts q (by rw [hP]; simp)
  exact ⟨p,q,hpq,hp.1,hq.1,hP,hp.2.1,hp.2.2.1,hp.2.2.2.1,
    hq.2.1,hq.2.2.1,hq.2.2.2.1,hp.2.2.2.2,hq.2.2.2.2⟩

section MiddleIncidence
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

private theorem middle_equal_table : ∀ tag b L,
    weight 2 tag L = 2 →
    (highSupport tag b ∩ line L).card = 2 →
    (highSupport tag (!b) ∩ line L).card = 2 →
    highSupport tag b ∩ line L = highSupport tag (!b) ∩ line L →
    ∃ mark : Fin 7, mark ∈ highSupport tag b ∩ line L ∧
      ∀ l j : Fin 7, l ≠ L → line l ∩ line L = {j} →
        (j ∉ highSupport tag b → weight 2 tag l = 3) ∧
        (j ∈ highSupport tag b →
          (line l ∩ highSupport tag b).card + (line l ∩ highSupport tag (!b)).card +
            2 * weight 2 tag l = 8 ∧
          (line l ∩ highSupport tag b).card % 2 = if j = mark then 1 else 0) := by
  decide +kernel

private theorem middle_distinct_table : ∀ tag b L l j,
    weight 2 tag L = 2 →
    (highSupport tag b ∩ line L).card = 2 →
    (highSupport tag (!b) ∩ line L).card = 2 →
    highSupport tag b ∩ line L ≠ highSupport tag (!b) ∩ line L →
    l ≠ L → line l ∩ line L = {j} →
    j ∈ highSupport tag b → j ∉ highSupport tag (!b) →
      (line l ∩ highSupport tag b).card + 2 * weight 2 tag l = 7 := by
  decide +kernel

end MiddleIncidence

private def rootFibre (B : I → Finset V) (r w : V) : Finset V :=
  univ.filter fun u => pointSupport B r ∩ pointSupport B u = pointSupport B r ∩ pointSupport B w

private theorem root_fibre_size {B : I → Finset V} (r : V)
    (hr : indexedDegree B r = 7) (tag : Bool)
    (e : {u : V // u ∉ ({r} : Finset V)} ≃ TemplatePoint 2 tag) (g : Fin 7 ↪ I)
    (he : ∀ u : {u : V // u ∉ ({r} : Finset V)},
      pointSupport B r ∩ pointSupport B u.val = (templateSupport 2 tag (e u)).map g)
    (w : {u : V // u ∉ ({r} : Finset V)}) (l : Fin 7)
    (hw : templateSupport 2 tag (e w) = line l) :
    (rootFibre B r w.val).card = weight 2 tag l := by
  classical
  have hwr : indexedSubsetDegree B {r,w.val} = 3 := by
    rw [← pointSupport_pair,he w,hw,card_map,line_card]
  have hnot : r ∉ rootFibre B r w.val := by
    intro hm
    have hm' := (mem_filter.mp hm).2
    have hc := congrArg Finset.card hm'
    rw [inter_self,pointSupport_card,hr,pointSupport_pair,hwr] at hc
    contradiction
  let F := (rootFibre B r w.val).subtype (· ∉ ({r} : Finset V))
  have hF : F.card = (rootFibre B r w.val).card := by
    dsimp only [F]
    rw [card_subtype]
    congr 1
    apply filter_eq_self.mpr
    intro u hu
    simpa using ne_of_mem_of_not_mem hu hnot
  have hcard : F.card = (univ.filter fun v : TemplatePoint 2 tag => templateSupport 2 tag v = line l).card := by
    apply card_equiv e
    intro u
    simp only [F,mem_subtype,rootFibre,mem_filter,mem_univ,true_and]
    rw [he u,he w,hw,map_inj]
  rw [← hF,hcard]
  exact (Fintype.card_subtype _).symm.trans (template_line_fibre_card 2 tag l)

private theorem middle_coordinates {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (r : V) (hr : indexedDegree B r = 7)
    (y p q : {u : V // u ∉ ({r} : Finset V)}) (hpq : p ≠ q)
    (hy : indexedSubsetDegree B {r,y.val} = 3)
    (hp : indexedSubsetDegree B {r,p.val} = 4) (hq : indexedSubsetDegree B {r,q.val} = 4)
    (hfy : (rootFibre B r y.val).card = 2) :
    ∃ (tag b : Bool) (L : Fin 7)
      (e : {u : V // u ∉ ({r} : Finset V)} ≃ TemplatePoint 2 tag) (g : Fin 7 ↪ I),
      (∀ u : {u : V // u ∉ ({r} : Finset V)},
        pointSupport B r ∩ pointSupport B u.val = (templateSupport 2 tag (e u)).map g) ∧
      pointSupport B r ∩ pointSupport B y.val = (line L).map g ∧
      pointSupport B r ∩ pointSupport B p.val = (highSupport tag b).map g ∧
      pointSupport B r ∩ pointSupport B q.val = (highSupport tag (!b)).map g ∧ weight 2 tag L = 2 := by
  obtain ⟨tag,e,g,_,he⟩ := minimum_incidence_coordinates hv h r hr
  have hc (u : {u : V // u ∉ ({r} : Finset V)}) :
      (templateSupport 2 tag (e u)).card = indexedSubsetDegree B {r,u.val} := by
    rw [← card_map g,← he,pointSupport_pair]
  have hl : ∃ L, templateSupport 2 tag (e y) = line L := by
    have hcy := (hc y).trans hy
    cases hey : e y with
    | inl b => rw [hey] at hcy; change (highSupport tag b).card = 3 at hcy; rw [high_card] at hcy; omega
    | inr v => exact ⟨v.1,rfl⟩
  obtain ⟨L,hL⟩ := hl
  have high (u : {u : V // u ∉ ({r} : Finset V)})
      (hu : indexedSubsetDegree B {r,u.val} = 4) : ∃ b, e u = Sum.inl b := by
    have hcu := (hc u).trans hu
    cases heu : e u with
    | inl b => exact ⟨b,rfl⟩
    | inr v => rw [heu] at hcu; change (line v.1).card = 4 at hcu; rw [line_card] at hcu; omega
  obtain ⟨b,hp'⟩ := high p hp
  obtain ⟨c,hq'⟩ := high q hq
  have hbc : b ≠ c := by
    intro hbc
    apply hpq
    apply e.injective
    rw [hp',hq',hbc]
  have hcb : c = !b := by cases b <;> cases c <;> simp_all
  refine ⟨tag,b,L,e,g,he,?_,?_,?_,?_⟩
  · rw [he,hL]
  · rw [he,hp']; rfl
  · rw [he,hq',hcb]; rfl
  · exact (root_fibre_size r hr tag e g he y L hL).symm.trans hfy

private theorem restrict_inter {R T S : Finset I} (h : T ⊆ R) :
    S ∩ T = (R ∩ S) ∩ T := by
  ext i
  simp only [mem_inter]
  constructor
  · exact fun hi => ⟨⟨h hi.2,hi.1⟩,hi.2⟩
  · exact fun hi => ⟨hi.1.2,hi.2⟩

private theorem triple_trace_inter (B : I → Finset V) (r u v : V) :
    indexedSubsetDegree B {r,u,v} =
      ((pointSupport B r ∩ pointSupport B u) ∩ (pointSupport B r ∩ pointSupport B v)).card := by
  rw [← pointSupport_triple]
  congr 1
  ext i
  simp only [mem_inter]
  tauto

private theorem middle_point_coordinates {B : I → Finset V} (r : V)
    (hr : indexedDegree B r = 7) (tag b : Bool) (L : Fin 7)
    (e : {u : V // u ∉ ({r} : Finset V)} ≃ TemplatePoint 2 tag) (g : Fin 7 ↪ I)
    (he : ∀ u : {u : V // u ∉ ({r} : Finset V)},
      pointSupport B r ∩ pointSupport B u.val = (templateSupport 2 tag (e u)).map g)
    (T : Finset I) (hTR : T ⊆ pointSupport B r) (hT : T = (line L).map g)
    (p q : V)
    (hp : pointSupport B r ∩ pointSupport B p = (highSupport tag b).map g)
    (hq : pointSupport B r ∩ pointSupport B q = (highSupport tag (!b)).map g)
    (w : {u : V // u ∉ ({r} : Finset V)}) (hw : indexedSubsetDegree B {r,w.val} = 3)
    (i : I) (hi : pointSupport B w.val ∩ T = {i}) :
    ∃ l j : Fin 7, l ≠ L ∧ line l ∩ line L = {j} ∧ g j = i ∧
      (rootFibre B r w.val).card = weight 2 tag l ∧
      indexedSubsetDegree B {r,w.val,p} = (line l ∩ highSupport tag b).card ∧
      indexedSubsetDegree B {r,w.val,q} = (line l ∩ highSupport tag (!b)).card ∧
      (i ∈ pointSupport B p ↔ j ∈ highSupport tag b) ∧
      (i ∈ pointSupport B q ↔ j ∈ highSupport tag (!b)) := by
  have hc : (templateSupport 2 tag (e w)).card = 3 := by
    rw [← card_map g,← he,pointSupport_pair,hw]
  obtain ⟨l,hl⟩ : ∃ l, templateSupport 2 tag (e w) = line l := by
    cases hew : e w with
    | inl a => rw [hew] at hc; change (highSupport tag a).card = 3 at hc; rw [high_card] at hc; omega
    | inr v => exact ⟨v.1,rfl⟩
  have hwmap : pointSupport B r ∩ pointSupport B w.val = (line l).map g := by rw [he,hl]
  have hiT : i ∈ T := (mem_inter.mp (hi.symm ▸ mem_singleton_self i)).2
  obtain ⟨j,hj,hji⟩ := mem_map.mp (hT ▸ hiT)
  have hwij : pointSupport B w.val ∩ T = (line l ∩ line L).map g := by
    rw [restrict_inter hTR,hwmap,hT,← map_inter]
  have hlj : line l ∩ line L = {j} := by
    apply (map_injective g)
    rw [map_singleton,hji,← hwij,hi]
  have hne : l ≠ L := by
    intro heq
    have hh := congrArg Finset.card hlj
    rw [heq,inter_self,line_card,card_singleton] at hh
    contradiction
  have hIR : i ∈ pointSupport B r := hTR hiT
  have hpoint (u : V) (H : Finset (Fin 7))
      (hu : pointSupport B r ∩ pointSupport B u = H.map g) :
      i ∈ pointSupport B u ↔ j ∈ H := by
    have heq : i ∈ pointSupport B r ∩ pointSupport B u ↔ j ∈ H := by
      rw [hu,← hji]
      simp
    simpa only [mem_inter,hIR,true_and] using heq
  refine ⟨l,j,hne,hlj,hji,root_fibre_size r hr tag e g he w l hl,?_,?_,hpoint p _ hp,hpoint q _ hq⟩
  · rw [triple_trace_inter,hwmap,hp,← map_inter,card_map]
  · rw [triple_trace_inter,hwmap,hq,← map_inter,card_map]

private theorem middle_equal_actual {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (r : V) (hr : indexedDegree B r = 7)
    (y p q : {u : V // u ∉ ({r} : Finset V)}) (hpq : p ≠ q)
    (hy : indexedSubsetDegree B {r,y.val} = 3)
    (hp : indexedSubsetDegree B {r,p.val} = 4) (hq : indexedSubsetDegree B {r,q.val} = 4)
    (hfy : (rootFibre B r y.val).card = 2)
    (T : Finset I) (hT : T = pointSupport B r ∩ pointSupport B y.val)
    (hpT : (pointSupport B p.val ∩ T).card = 2) (hqT : (pointSupport B q.val ∩ T).card = 2)
    (hequal : pointSupport B p.val ∩ T = pointSupport B q.val ∩ T) :
    ∃ mark ∈ pointSupport B p.val ∩ T,
      ∀ (w : {u : V // u ∉ ({r} : Finset V)}) (i : I),
        indexedSubsetDegree B {r,w.val} = 3 → pointSupport B w.val ∩ T = {i} →
        (i ∉ pointSupport B p.val → (rootFibre B r w.val).card = 3) ∧
        (i ∈ pointSupport B p.val →
          indexedSubsetDegree B {r,w.val,p.val} + indexedSubsetDegree B {r,w.val,q.val} +
            2 * (rootFibre B r w.val).card = 8 ∧
          indexedSubsetDegree B {r,w.val,p.val} % 2 = if i = mark then 1 else 0) := by
  obtain ⟨tag,b,L,e,g,he,hyc,hpc,hqc,hwL⟩ := middle_coordinates hv h r hr y p q hpq hy hp hq hfy
  have hTR : T ⊆ pointSupport B r := hT ▸ inter_subset_left
  have hTc : T = (line L).map g := hT.trans hyc
  have hPT : pointSupport B p.val ∩ T = (highSupport tag b ∩ line L).map g := by
    rw [restrict_inter hTR,hpc,hTc,← map_inter]
  have hQT : pointSupport B q.val ∩ T = (highSupport tag (!b) ∩ line L).map g := by
    rw [restrict_inter hTR,hqc,hTc,← map_inter]
  have hpcard : (highSupport tag b ∩ line L).card = 2 := by simpa only [hPT,card_map] using hpT
  have hqcard : (highSupport tag (!b) ∩ line L).card = 2 := by simpa only [hQT,card_map] using hqT
  have hpeq : highSupport tag b ∩ line L = highSupport tag (!b) ∩ line L := by
    apply map_injective g
    rw [← hPT,← hQT,hequal]
  obtain ⟨mark,hm,hfacts⟩ := middle_equal_table tag b L hwL hpcard hqcard hpeq
  refine ⟨g mark,?_,?_⟩
  · rw [hPT]
    exact mem_map.mpr ⟨mark,hm,rfl⟩
  · intro w i hw hi
    obtain ⟨l,j,hl,hlj,hji,hf,hwp,hwq,hpi,hqi⟩ :=
      middle_point_coordinates r hr tag b L e g he T hTR hTc p.val q.val hpc hqc w hw i hi
    have hs := hfacts l j hl hlj
    constructor
    · intro hn
      rw [hf]
      exact hs.1 (fun hjp => hn (hpi.mpr hjp))
    · intro hip
      have hh := hs.2 (hpi.mp hip)
      refine ⟨?_,?_⟩
      · rw [hf,hwp,hwq]
        exact hh.1
      · rw [hwp,hh.2,← hji]
        simp

private theorem middle_distinct_actual {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (r : V) (hr : indexedDegree B r = 7)
    (y p q : {u : V // u ∉ ({r} : Finset V)}) (hpq : p ≠ q)
    (hy : indexedSubsetDegree B {r,y.val} = 3)
    (hp : indexedSubsetDegree B {r,p.val} = 4) (hq : indexedSubsetDegree B {r,q.val} = 4)
    (hfy : (rootFibre B r y.val).card = 2)
    (T : Finset I) (hT : T = pointSupport B r ∩ pointSupport B y.val)
    (hpT : (pointSupport B p.val ∩ T).card = 2) (hqT : (pointSupport B q.val ∩ T).card = 2)
    (hne : pointSupport B p.val ∩ T ≠ pointSupport B q.val ∩ T) :
    ∀ (w : {u : V // u ∉ ({r} : Finset V)}) (i : I),
      indexedSubsetDegree B {r,w.val} = 3 → pointSupport B w.val ∩ T = {i} →
      i ∈ pointSupport B p.val → i ∉ pointSupport B q.val →
        indexedSubsetDegree B {r,w.val,p.val} + 2 * (rootFibre B r w.val).card = 7 := by
  obtain ⟨tag,b,L,e,g,he,hyc,hpc,hqc,hwL⟩ := middle_coordinates hv h r hr y p q hpq hy hp hq hfy
  have hTR : T ⊆ pointSupport B r := hT ▸ inter_subset_left
  have hTc : T = (line L).map g := hT.trans hyc
  have hPT : pointSupport B p.val ∩ T = (highSupport tag b ∩ line L).map g := by
    rw [restrict_inter hTR,hpc,hTc,← map_inter]
  have hQT : pointSupport B q.val ∩ T = (highSupport tag (!b) ∩ line L).map g := by
    rw [restrict_inter hTR,hqc,hTc,← map_inter]
  have hpcard : (highSupport tag b ∩ line L).card = 2 := by simpa only [hPT,card_map] using hpT
  have hqcard : (highSupport tag (!b) ∩ line L).card = 2 := by simpa only [hQT,card_map] using hqT
  have hne' : highSupport tag b ∩ line L ≠ highSupport tag (!b) ∩ line L := by
    intro heq
    exact hne (by rw [hPT,hQT,heq])
  intro w i hw hi hip hiq
  obtain ⟨l,j,hl,hlj,hji,hf,hwp,hwq,hpi,hqi⟩ :=
    middle_point_coordinates r hr tag b L e g he T hTR hTc p.val q.val hpc hqc w hw i hi
  rw [hf,hwp]
  exact middle_distinct_table tag b L l j hwL hpcard hqcard hne' hl hlj
    (hpi.mp hip) (fun hj => hiq (hqi.mpr hj))

private structure OrdinaryFrame (B : I → Finset V) where
  roots : Fin 3 ↪ V
  T : Finset I
  p : V
  q : V
  pq_ne : p ≠ q
  p_out : p ∉ univ.image roots
  q_out : q ∉ univ.image roots
  root_min : ∀ d, indexedDegree B (roots d) = 7
  T_card : T.card = 3
  T_sub : ∀ d, T ⊆ pointSupport B (roots d)
  root_inter : ∀ d e, d ≠ e → pointSupport B (roots d) ∩ pointSupport B (roots e) = T
  p_trace : (pointSupport B p ∩ T).card = 2
  q_trace : (pointSupport B q ∩ T).card = 2
  high_pairs : ∀ d, indexedSubsetDegree B {roots d,p} = 4 ∧ indexedSubsetDegree B {roots d,q} = 4
  low_pairs : ∀ w, w ∉ univ.image roots → w ≠ p → w ≠ q →
    ∀ d, indexedSubsetDegree B {roots d,w} = 3
  low_trace : ∀ w, w ∉ univ.image roots → w ≠ p → w ≠ q → (pointSupport B w ∩ T).card = 1
  p_high : 8 ≤ indexedDegree B p
  q_high : 8 ≤ indexedDegree B q

private theorem make_ordinary_frame {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : indexedDegree B x = 7) (hy : indexedDegree B y = 7) (hz : indexedDegree B z = 7)
    (hxy₃ : indexedSubsetDegree B {x,y} = 3)
    (hxz₃ : indexedSubsetDegree B {x,z} = 3)
    (hyz₃ : indexedSubsetDegree B {y,z} = 3)
    (ht : indexedSubsetDegree B {x,y,z} = 3) : Nonempty (OrdinaryFrame B) := by
  obtain ⟨p,q,hpq,hpo,hqo,hP,hxp,hyp,hzp,hxq,hyq,hzq,hp8,hq8⟩ :=
    ordinary_common_exceptions hv h hi x y z hxy hxz hyz hx hy hz hxy₃ hxz₃ hyz₃ ht
  let r : Fin 3 ↪ V := ⟨![x,y,z],by intro i j he; fin_cases i <;> fin_cases j <;> simp_all⟩
  have hr0 : r 0 = x := rfl
  have hr1 : r 1 = y := rfl
  have hr2 : r 2 = z := rfl
  have hroots : univ.image r = ({x,y,z} : Finset V) := by
    rw [show (univ : Finset (Fin 3)) = {0,1,2} by decide]
    rw [image_insert,image_insert,image_singleton]
    rfl
  let T := pointSupport B x ∩ pointSupport B y
  have hT : T.card = 3 := (pointSupport_pair B x y).trans hxy₃
  have hsub (d : Fin 3) : T ⊆ pointSupport B (r d) := by
    fin_cases d
    · exact inter_subset_left
    · exact inter_subset_right
    · exact full_trace x y z (ht.trans hxy₃.symm)
  have hmin (d : Fin 3) : indexedDegree B (r d) = 7 := by fin_cases d <;> assumption
  have hpair (d e : Fin 3) (hne : d ≠ e) :
      pointSupport B (r d) ∩ pointSupport B (r e) = T := by
    have hc : (pointSupport B (r d) ∩ pointSupport B (r e)).card = 3 := by
      rw [pointSupport_pair]
      fin_cases d <;> fin_cases e <;> simp only [hr0,hr1,hr2]
      · exact False.elim (hne rfl)
      · exact hxy₃
      · exact hxz₃
      · rw [pair_comm]; exact hxy₃
      · exact False.elim (hne rfl)
      · exact hyz₃
      · rw [pair_comm]; exact hxz₃
      · rw [pair_comm]; exact hyz₃
      · exact False.elim (hne rfl)
    symm
    exact eq_of_subset_of_card_le (subset_inter (hsub d) (hsub e)) (by rw [hc,hT])
  have hhigh (d : Fin 3) : indexedSubsetDegree B {r d,p} = 4 ∧ indexedSubsetDegree B {r d,q} = 4 := by
    fin_cases d <;> constructor <;> assumption
  have hlow (w : V) (hwo : w ∉ univ.image r) (hwp : w ≠ p) (hwq : w ≠ q)
      (d : Fin 3) : indexedSubsetDegree B {r d,w} = 3 := by
    apply two_exceptions_exhaust hv h (r d) p q (hmin d)
      (fun he => hpo (hroots ▸ mem_image.mpr ⟨d,mem_univ _,he.symm⟩))
      (fun he => hqo (hroots ▸ mem_image.mpr ⟨d,mem_univ _,he.symm⟩)) hpq
      (hhigh d).1 (hhigh d).2 w
      (fun he => hwo (mem_image.mpr ⟨d,mem_univ _,he.symm⟩)) hwp hwq
  have hpT : (pointSupport B p ∩ T).card = 2 := by
    have hpP : p ∈ thirdPoints B x y 2 := by rw [hP]; simp
    rw [inter_comm]
    exact (pointSupport_triple B x y p).trans (mem_filter.mp hpP).2
  have hqT : (pointSupport B q ∩ T).card = 2 := by
    have hqP : q ∈ thirdPoints B x y 2 := by rw [hP]; simp
    rw [inter_comm]
    exact (pointSupport_triple B x y q).trans (mem_filter.mp hqP).2
  have htrace (w : V) (hwo : w ∉ univ.image r) (hwp : w ≠ p) (hwq : w ≠ q) :
      (pointSupport B w ∩ T).card = 1 := by
    have hout : w ∉ ({x,y,z} : Finset V) := hroots ▸ hwo
    have hwx : x ≠ w := fun he => hout (by simp [← he])
    have hwz : w ≠ z := fun he => hout (by simp [he])
    have hlowx : indexedSubsetDegree B {x,w} = 3 := hlow w hwo hwp hwq 0
    have hs := minimum_ordinary_trace hv h x y w hx hxy hwx hxy₃ hlowx
    have hh : indexedSubsetDegree B {x,y,w} ≠ 3 := by
      intro hw3
      have hwP : w ∈ thirdPoints B x y 3 := by
        simp only [thirdPoints,mem_filter,mem_sdiff,mem_univ,true_and,mem_insert,mem_singleton]
        exact ⟨fun he => hout (by simp only [mem_insert,mem_singleton]; tauto),hw3⟩
      rw [ordinary_thirds_singleton hv h hi x y z hxy hxz hyz hx hy hz hxy₃ hxz₃ hyz₃ ht] at hwP
      exact hwz (mem_singleton.mp hwP)
    rw [inter_comm]
    exact (pointSupport_triple B x y w).trans (hs.resolve_right hh)
  exact ⟨⟨r,T,p,q,hpq,by simpa only [hroots] using hpo,by simpa only [hroots] using hqo,
    hmin,hT,hsub,hpair,hpT,hqT,hhigh,hlow,htrace,hp8,hq8⟩⟩

private def OrdinaryFrame.group {B : I → Finset V} (F : OrdinaryFrame B) (i : I) : Finset V :=
  univ.filter fun w => pointSupport B w ∩ F.T = {i}

private def OrdinaryFrame.outside {B : I → Finset V} (F : OrdinaryFrame B) : Finset I :=
  univ \ (pointSupport B (F.roots 0) ∪ pointSupport B (F.roots 1) ∪ pointSupport B (F.roots 2))

private theorem OrdinaryFrame.group_ordinary {B : I → Finset V} (F : OrdinaryFrame B)
    (i : I) (w : V) (hw : w ∈ F.group i) : w ∉ univ.image F.roots ∧ w ≠ F.p ∧ w ≠ F.q := by
  have ht : (pointSupport B w ∩ F.T).card = 1 := by rw [(mem_filter.mp hw).2,card_singleton]
  refine ⟨?_,?_,?_⟩
  · intro hroot
    obtain ⟨d,_,rfl⟩ := mem_image.mp hroot
    rw [inter_eq_right.mpr (F.T_sub d),F.T_card] at ht
    contradiction
  · intro he
    rw [he,F.p_trace] at ht
    contradiction
  · intro he
    rw [he,F.q_trace] at ht
    contradiction

private theorem OrdinaryFrame.group_pairs {B : I → Finset V} (F : OrdinaryFrame B)
    (i : I) (w : V) (hw : w ∈ F.group i) (d : Fin 3) :
    indexedSubsetDegree B {F.roots d,w} = 3 := by
  obtain ⟨ho,hp,hq⟩ := F.group_ordinary i w hw
  exact F.low_pairs w ho hp hq d

private theorem OrdinaryFrame.fibre_subset_group {B : I → Finset V} (F : OrdinaryFrame B)
    (i : I) (w : V) (hw : w ∈ F.group i) (d : Fin 3) : rootFibre B (F.roots d) w ⊆ F.group i := by
  intro u hu
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  rw [restrict_inter (F.T_sub d),(mem_filter.mp hu).2,← restrict_inter (F.T_sub d)]
  exact (mem_filter.mp hw).2

private theorem OrdinaryFrame.count {B : I → Finset V} (F : OrdinaryFrame B) (S : Finset I) :
    (S ∩ pointSupport B (F.roots 0)).card + (S ∩ pointSupport B (F.roots 1)).card +
      (S ∩ pointSupport B (F.roots 2)).card + (S ∩ F.outside).card = S.card + 2*(S ∩ F.T).card :=
  three_support_count _ _ _ _ _ (F.root_inter 0 1 (by decide))
    (F.root_inter 0 2 (by decide)) (F.root_inter 1 2 (by decide))

private theorem OrdinaryFrame.outside_card {B : I → Finset V} (F : OrdinaryFrame B)
    (hi : Fintype.card I = 16) : F.outside.card = 1 := by
  have hc := F.count univ
  simp only [univ_inter,pointSupport_card,F.root_min,card_univ,hi,F.T_card] at hc
  omega

private theorem OrdinaryFrame.minimum_avoids_outside {B : I → Finset V} (F : OrdinaryFrame B)
    (i : I) (w : V) (hw : w ∈ F.group i) (hm : indexedDegree B w = 7) :
    pointSupport B w ∩ F.outside = ∅ := by
  have hc := F.count (pointSupport B w)
  have ht : (pointSupport B w ∩ F.T).card = 1 := by rw [(mem_filter.mp hw).2,card_singleton]
  simp only [pointSupport_pair,pair_comm w,F.group_pairs i w hw,pointSupport_card,hm,ht] at hc
  exact card_eq_zero.mp (by omega)

private theorem OrdinaryFrame.group_card {B : I → Finset V} (F : OrdinaryFrame B)
    (hu : Multicover.Uniform B 9) (i : I) (hi : i ∈ F.T) :
    (F.group i).card + (if i ∈ pointSupport B F.p then 1 else 0) +
      (if i ∈ pointSupport B F.q then 1 else 0) = 6 := by
  let R := univ.image F.roots
  let E := R ∪ {F.p,F.q}
  have hR : R ⊆ B i := by
    intro u hu
    obtain ⟨d,_,rfl⟩ := mem_image.mp hu
    exact (mem_pointSupport B (F.roots d) i).mp (F.T_sub d hi)
  have hdis : Disjoint R ({F.p,F.q} : Finset V) := by
    apply disjoint_right.mpr
    intro u hu hru
    simp only [mem_insert,mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact F.p_out hru
    · exact F.q_out hru
  have hpair : (B i ∩ {F.p,F.q}).card =
      (if F.p ∈ B i then 1 else 0) + (if F.q ∈ B i then 1 else 0) := by
    rw [inter_comm,← filter_mem_eq_inter,card_eq_sum_ones,sum_filter,sum_pair F.pq_ne]
  have hE : (B i ∩ E).card = 3 + (if F.p ∈ B i then 1 else 0) + (if F.q ∈ B i then 1 else 0) := by
    change (B i ∩ (R ∪ {F.p,F.q})).card = _
    rw [inter_union_distrib_left,card_union_of_disjoint
      (hdis.mono inter_subset_right inter_subset_right),inter_eq_right.mpr hR,hpair]
    have hRc : R.card = 3 := by
      dsimp only [R]
      rw [card_image_of_injective _ F.roots.injective,card_univ,Fintype.card_fin]
    rw [hRc]
    omega
  have hdiff : B i \ E = F.group i := by
    ext w
    constructor
    · intro hw
      have hwe := (mem_sdiff.mp hw).2
      have hwo : w ∉ univ.image F.roots := fun hr => hwe (mem_union_left _ hr)
      have hwp : w ≠ F.p := fun he => hwe (by simp [E,he])
      have hwq : w ≠ F.q := fun he => hwe (by simp [E,he])
      have ht := F.low_trace w hwo hwp hwq
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      symm
      apply eq_of_subset_of_card_le
        (singleton_subset_iff.mpr (mem_inter.mpr ⟨(mem_pointSupport B w i).mpr (mem_sdiff.mp hw).1,hi⟩))
      rw [ht,card_singleton]
    · intro hw
      obtain ⟨hwo,hwp,hwq⟩ := F.group_ordinary i w hw
      have hiw : i ∈ pointSupport B w :=
        (mem_inter.mp (((mem_filter.mp hw).2).symm ▸ mem_singleton_self i)).1
      refine mem_sdiff.mpr ⟨(mem_pointSupport B w i).mp hiw,?_⟩
      simpa only [E,mem_union,mem_insert,mem_singleton,not_or] using ⟨hwo,hwp,hwq⟩
  have hc := card_sdiff_add_card_inter (B i) E
  rw [hdiff,hE,hu] at hc
  simp only [mem_pointSupport]
  omega

private theorem OrdinaryFrame.minimum_pair_sum {B : I → Finset V} (F : OrdinaryFrame B)
    (i : I) (w : V) (hw : w ∈ F.group i) (hm : indexedDegree B w = 7) (u : V) :
    indexedSubsetDegree B {w,u} + 2 * (if i ∈ pointSupport B u then 1 else 0) =
      ∑ d : Fin 3, indexedSubsetDegree B {F.roots d,w,u} := by
  have hn := F.minimum_avoids_outside i w hw hm
  have hN : (pointSupport B w ∩ pointSupport B u) ∩ F.outside = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hj' : j ∈ pointSupport B w ∩ F.outside :=
      mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hj).1).1,(mem_inter.mp hj).2⟩
    rw [hn] at hj'
    exact notMem_empty _ hj'
  have hT : ((pointSupport B w ∩ pointSupport B u) ∩ F.T).card =
      if i ∈ pointSupport B u then 1 else 0 := by
    have he : (pointSupport B w ∩ pointSupport B u) ∩ F.T =
        (pointSupport B w ∩ F.T) ∩ pointSupport B u := by
      ext j
      simp only [mem_inter]
      tauto
    rw [he,(mem_filter.mp hw).2]
    by_cases hi : i ∈ pointSupport B u <;> simp [hi]
  have hd (d : Fin 3) : ((pointSupport B w ∩ pointSupport B u) ∩ pointSupport B (F.roots d)).card =
      indexedSubsetDegree B {F.roots d,w,u} := by
    rw [inter_comm (pointSupport B w ∩ pointSupport B u),← inter_assoc,pointSupport_triple]
  have hc := F.count (pointSupport B w ∩ pointSupport B u)
  simp only [hd,hN,card_empty,add_zero,pointSupport_pair,hT] at hc
  simpa only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,Fin.reduceFinMk,
    Fin.succ_zero_eq_one,Fin.succ_one_eq_two,add_zero,add_assoc] using hc.symm

private theorem OrdinaryFrame.group_agreement {B : I → Finset V} (F : OrdinaryFrame B)
    (hv : Fintype.card V = 19) (h : Multicover.IsCover B 9 3 1)
    (i : I) (w u : V) (hw : w ∈ F.group i) (hu : u ∈ F.group i)
    (hm : indexedDegree B w = 7) (huw : u ≠ w) :
    (univ.filter fun d : Fin 3 => pointSupport B (F.roots d) ∩ pointSupport B u =
      pointSupport B (F.roots d) ∩ pointSupport B w).card = 1 := by
  have hwo := (F.group_ordinary i w hw).1
  have huo := (F.group_ordinary i u hu).1
  have hrootne (d : Fin 3) (v : V) (hvo : v ∉ univ.image F.roots) : F.roots d ≠ v :=
    fun he => hvo (mem_image.mpr ⟨d,mem_univ _,he⟩)
  have ht (d : Fin 3) : indexedSubsetDegree B {F.roots d,w,u} =
      if pointSupport B (F.roots d) ∩ pointSupport B u =
        pointSupport B (F.roots d) ∩ pointSupport B w then 3 else 1 := by
    have hwc := (pointSupport_pair B (F.roots d) w).trans (F.group_pairs i w hw d)
    have huc := (pointSupport_pair B (F.roots d) u).trans (F.group_pairs i u hu d)
    by_cases he : pointSupport B (F.roots d) ∩ pointSupport B u =
        pointSupport B (F.roots d) ∩ pointSupport B w
    · rw [if_pos he,triple_trace_inter,he,inter_self,hwc]
    · rw [if_neg he]
      have hh := minimum_ordinary_trace hv h (F.roots d) w u (F.root_min d)
        (hrootne d w hwo) (hrootne d u huo) (F.group_pairs i w hw d) (F.group_pairs i u hu d)
      apply hh.resolve_right
      intro h3
      rw [triple_trace_inter] at h3
      have hL := eq_of_subset_of_card_le
        (inter_subset_left (s₁ := pointSupport B (F.roots d) ∩ pointSupport B w)
          (s₂ := pointSupport B (F.roots d) ∩ pointSupport B u)) (by rw [hwc,h3])
      have hR := eq_of_subset_of_card_le
        (inter_subset_right (s₁ := pointSupport B (F.roots d) ∩ pointSupport B w)
          (s₂ := pointSupport B (F.roots d) ∩ pointSupport B u)) (by rw [huc,h3])
      exact he (hR.symm.trans hL)
  have hiu : i ∈ pointSupport B u :=
    (mem_inter.mp (((mem_filter.mp hu).2).symm ▸ mem_singleton_self i)).1
  have hc := F.minimum_pair_sum i w hw hm u
  rw [if_pos hiu] at hc
  let A := (univ.filter fun d : Fin 3 => pointSupport B (F.roots d) ∩ pointSupport B u =
      pointSupport B (F.roots d) ∩ pointSupport B w).card
  have hs : (∑ d : Fin 3, indexedSubsetDegree B {F.roots d,w,u}) = 3 + 2*A := by
    simp_rw [ht]
    have he (d : Fin 3) : (if pointSupport B (F.roots d) ∩ pointSupport B u =
        pointSupport B (F.roots d) ∩ pointSupport B w then 3 else 1) =
        1 + 2 * (if pointSupport B (F.roots d) ∩ pointSupport B u =
          pointSupport B (F.roots d) ∩ pointSupport B w then 1 else 0) := by split_ifs <;> decide
    simp_rw [he]
    rw [sum_add_distrib,← mul_sum]
    have hA : A = ∑ d : Fin 3, if pointSupport B (F.roots d) ∩ pointSupport B u =
        pointSupport B (F.roots d) ∩ pointSupport B w then 1 else 0 := by
      dsimp only [A]
      rw [card_eq_sum_ones,sum_filter]
    rw [← hA]
    simp only [sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,mul_one]
  have hlo := pair_floor hv h (card_pair huw.symm)
  have hhi := minimum_pair_le_four hv h w u hm huw.symm
  change A = 1
  omega

private theorem OrdinaryFrame.agreement_sum {B : I → Finset V} (F : OrdinaryFrame B)
    (hv : Fintype.card V = 19) (h : Multicover.IsCover B 9 3 1)
    (i : I) (w : V) (hw : w ∈ F.group i) (hm : indexedDegree B w = 7) :
    (∑ d : Fin 3, (rootFibre B (F.roots d) w).card) = (F.group i).card + 2 := by
  classical
  let w' : ↥(F.group i) := ⟨w,hw⟩
  let trace (d : Fin 3) (u : ↥(F.group i)) := pointSupport B (F.roots d) ∩ pointSupport B u.val
  have he := complementary_agreement_identity trace w' (by
    intro u huw
    exact F.group_agreement hv h i w u.val hw u.property hm (fun he => huw (Subtype.ext he)))
  have hc (d : Fin 3) : (univ.filter fun u : ↥(F.group i) => trace d u = trace d w').card =
      (rootFibre B (F.roots d) w).card := by
    have heq : (univ.filter fun u : ↥(F.group i) => trace d u = trace d w') =
        (rootFibre B (F.roots d) w).subtype (· ∈ F.group i) := by
      ext u
      simp [trace,w',rootFibre]
    rw [heq,card_subtype]
    congr 1
    exact filter_eq_self.mpr (F.fibre_subset_group i w hw d)
  simp only [hc,Fintype.card_coe] at he
  have hp (d : Fin 3) : 1 ≤ (rootFibre B (F.roots d) w).card := by
    apply card_pos.mpr
    exact ⟨w,by simp [rootFibre]⟩
  have hs : (∑ d : Fin 3, ((rootFibre B (F.roots d) w).card - 1)) + 3 =
      ∑ d : Fin 3, (rootFibre B (F.roots d) w).card := by
    have hh := sum_congr (s₁ := (univ : Finset (Fin 3))) rfl
      (fun d _ => Nat.sub_add_cancel (hp d))
    simpa [sum_add_distrib] using hh
  have hpos : 1 ≤ (F.group i).card := card_pos.mpr ⟨w,hw⟩
  omega

private theorem OrdinaryFrame.root_fibre_card {B : I → Finset V} (F : OrdinaryFrame B)
    (d e : Fin 3) (hde : d ≠ e) : (rootFibre B (F.roots d) (F.roots e)).card = 2 := by
  have heq : rootFibre B (F.roots d) (F.roots e) =
      (univ.image F.roots).erase (F.roots d) := by
    ext u
    simp only [rootFibre,mem_filter,mem_univ,true_and,mem_erase]
    constructor
    · intro ht
      have hut : pointSupport B u ∩ pointSupport B (F.roots d) = F.T := by
        rw [inter_comm,ht,F.root_inter d e hde]
      have huc : indexedSubsetDegree B {F.roots d,u} = 3 := by
        rw [pair_comm,← pointSupport_pair,hut,F.T_card]
      have hun : u ≠ F.roots d := by
        intro he
        have := congrArg Finset.card hut
        rw [he,inter_self,pointSupport_card,F.root_min,F.T_card] at this
        contradiction
      refine ⟨hun,?_⟩
      by_contra huo
      have hup : u ≠ F.p := by intro he; rw [he,(F.high_pairs d).1] at huc; contradiction
      have huq : u ≠ F.q := by intro he; rw [he,(F.high_pairs d).2] at huc; contradiction
      have hc := F.low_trace u huo hup huq
      have hTsub : F.T ⊆ pointSupport B u := hut ▸ inter_subset_left
      rw [inter_eq_right.mpr hTsub,F.T_card] at hc
      contradiction
    · rintro ⟨hun,hu⟩
      obtain ⟨f,_,rfl⟩ := mem_image.mp hu
      have hfd : f ≠ d := fun he => hun (congrArg F.roots he)
      rw [F.root_inter d f hfd.symm,F.root_inter d e hde]
  rw [heq,card_erase_of_mem (mem_image.mpr ⟨d,mem_univ _,rfl⟩),
    card_image_of_injective _ F.roots.injective,card_univ,Fintype.card_fin]

private theorem OrdinaryFrame.root_ne_p {B : I → Finset V} (F : OrdinaryFrame B) (d : Fin 3) :
    F.roots d ≠ F.p := fun he => F.p_out (mem_image.mpr ⟨d,mem_univ _,he⟩)

private theorem OrdinaryFrame.root_ne_q {B : I → Finset V} (F : OrdinaryFrame B) (d : Fin 3) :
    F.roots d ≠ F.q := fun he => F.q_out (mem_image.mpr ⟨d,mem_univ _,he⟩)

private theorem OrdinaryFrame.equal_rules {B : I → Finset V} (F : OrdinaryFrame B)
    (hv : Fintype.card V = 19) (h : Multicover.IsCover B 9 3 1)
    (hequal : pointSupport B F.p ∩ F.T = pointSupport B F.q ∩ F.T) :
    ∃ mark : Fin 3 → I, (∀ d, mark d ∈ pointSupport B F.p ∩ F.T) ∧
      ∀ d i w, w ∈ F.group i →
        (i ∉ pointSupport B F.p → (rootFibre B (F.roots d) w).card = 3) ∧
        (i ∈ pointSupport B F.p →
          indexedSubsetDegree B {F.roots d,w,F.p} + indexedSubsetDegree B {F.roots d,w,F.q} +
            2 * (rootFibre B (F.roots d) w).card = 8 ∧
          indexedSubsetDegree B {F.roots d,w,F.p} % 2 = if i = mark d then 1 else 0) := by
  have hex (d : Fin 3) : ∃ mark : I, mark ∈ pointSupport B F.p ∩ F.T ∧
      ∀ i w, w ∈ F.group i →
        (i ∉ pointSupport B F.p → (rootFibre B (F.roots d) w).card = 3) ∧
        (i ∈ pointSupport B F.p →
          indexedSubsetDegree B {F.roots d,w,F.p} + indexedSubsetDegree B {F.roots d,w,F.q} +
            2 * (rootFibre B (F.roots d) w).card = 8 ∧
          indexedSubsetDegree B {F.roots d,w,F.p} % 2 = if i = mark then 1 else 0) := by
    obtain ⟨e,hde⟩ : ∃ e : Fin 3, d ≠ e := by fin_cases d <;> decide
    let y : {u : V // u ∉ ({F.roots d} : Finset V)} :=
      ⟨F.roots e,by simpa only [mem_singleton] using fun he => hde (F.roots.injective he).symm⟩
    let p : {u : V // u ∉ ({F.roots d} : Finset V)} :=
      ⟨F.p,by simpa only [mem_singleton] using (F.root_ne_p d).symm⟩
    let q : {u : V // u ∉ ({F.roots d} : Finset V)} :=
      ⟨F.q,by simpa only [mem_singleton] using (F.root_ne_q d).symm⟩
    have hy : indexedSubsetDegree B {F.roots d,y.val} = 3 := by
      rw [← pointSupport_pair,F.root_inter d e hde,F.T_card]
    obtain ⟨m,hm,hfacts⟩ := middle_equal_actual hv h (F.roots d) (F.root_min d) y p q
      (fun he => F.pq_ne (congrArg Subtype.val he)) hy (F.high_pairs d).1 (F.high_pairs d).2
      (F.root_fibre_card d e hde) F.T (F.root_inter d e hde).symm F.p_trace F.q_trace hequal
    refine ⟨m,hm,?_⟩
    intro i w hw
    have hwn : w ≠ F.roots d := fun he =>
      (F.group_ordinary i w hw).1 (mem_image.mpr ⟨d,mem_univ _,he.symm⟩)
    exact hfacts ⟨w,by simpa only [mem_singleton] using hwn⟩ i
      (F.group_pairs i w hw d) (mem_filter.mp hw).2
  choose mark hm hfacts using hex
  exact ⟨mark,hm,hfacts⟩

private theorem OrdinaryFrame.minimum_group {B : I → Finset V} (F : OrdinaryFrame B)
    (w : V) (hw : indexedDegree B w = 7) (hwo : w ∉ univ.image F.roots) :
    ∃ i ∈ F.T, w ∈ F.group i := by
  have hwp : w ≠ F.p := by intro he; rw [he] at hw; have := F.p_high; omega
  have hwq : w ≠ F.q := by intro he; rw [he] at hw; have := F.q_high; omega
  obtain ⟨i,hi⟩ := card_eq_one.mp (F.low_trace w hwo hwp hwq)
  refine ⟨i,?_,mem_filter.mpr ⟨mem_univ _,hi⟩⟩
  exact (mem_inter.mp (hi.symm ▸ mem_singleton_self i)).2

private theorem OrdinaryFrame.minimum_bound {B : I → Finset V} (F : OrdinaryFrame B)
    (i : I) (hi : (F.group i).card ≤ 4)
    (hsub : ∀ w, indexedDegree B w = 7 → w ∉ univ.image F.roots → w ∈ F.group i) :
    (minimumPoints B).card ≤ 7 := by
  have hs : minimumPoints B ⊆ univ.image F.roots ∪ F.group i := by
    intro w hw
    by_cases ho : w ∈ univ.image F.roots
    · exact mem_union_left _ ho
    · exact mem_union_right _ (hsub w (mem_filter.mp hw).2 ho)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  rw [card_image_of_injective _ F.roots.injective,card_univ,Fintype.card_fin] at hc
  omega

private theorem OrdinaryFrame.equal_minimum_rule {B : I → Finset V} (F : OrdinaryFrame B)
    (hv : Fintype.card V = 19) (h : Multicover.IsCover B 9 3 1)
    (hequal : pointSupport B F.p ∩ F.T = pointSupport B F.q ∩ F.T)
    (mark : Fin 3 → I)
    (hrules : ∀ d i w, w ∈ F.group i →
      (i ∉ pointSupport B F.p → (rootFibre B (F.roots d) w).card = 3) ∧
      (i ∈ pointSupport B F.p →
        indexedSubsetDegree B {F.roots d,w,F.p} + indexedSubsetDegree B {F.roots d,w,F.q} +
          2 * (rootFibre B (F.roots d) w).card = 8 ∧
        indexedSubsetDegree B {F.roots d,w,F.p} % 2 = if i = mark d then 1 else 0))
    (i : I) (hi : i ∈ F.T) (w : V) (hw : w ∈ F.group i) (hm : indexedDegree B w = 7) :
    i ∈ pointSupport B F.p ∩ F.T ∧
      (∑ d : Fin 3, if i = mark d then 1 else 0) % 2 = 0 := by
  have hmem : i ∈ pointSupport B F.p ↔ i ∈ pointSupport B F.q := by
    constructor
    · intro hp
      exact (mem_inter.mp (hequal ▸ mem_inter.mpr ⟨hp,hi⟩)).1
    · intro hq
      exact (mem_inter.mp (hequal.symm ▸ mem_inter.mpr ⟨hq,hi⟩)).1
  have hcard := F.group_card h.1 i hi
  have hsum := F.agreement_sum hv h i w hw hm
  have hp : i ∈ pointSupport B F.p := by
    by_contra hp
    have hq : i ∉ pointSupport B F.q := fun hq => hp (hmem.mpr hq)
    have hf (d : Fin 3) := (hrules d i w hw).1 hp
    simp only [if_neg hp,if_neg hq,add_zero] at hcard
    simp only [hf,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at hsum
    omega
  have hq := hmem.mp hp
  simp only [if_pos hp,if_pos hq] at hcard
  have hlocal (d : Fin 3) := ((hrules d i w hw).2 hp).1
  have htot := sum_congr (s₁ := (univ : Finset (Fin 3))) rfl (fun d _ => hlocal d)
  simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at htot
  have hsp := F.minimum_pair_sum i w hw hm F.p
  have hsq := F.minimum_pair_sum i w hw hm F.q
  simp only [if_pos hp,if_pos hq] at hsp hsq
  obtain ⟨_,hwp,hwq⟩ := F.group_ordinary i w hw
  have hple := minimum_pair_le_four hv h w F.p hm hwp
  have hqle := minimum_pair_le_four hv h w F.q hm hwq
  have hpsum : (∑ d : Fin 3, indexedSubsetDegree B {F.roots d,w,F.p}) = 6 := by omega
  refine ⟨mem_inter.mpr ⟨hp,hi⟩,?_⟩
  have hpar (d : Fin 3) := ((hrules d i w hw).2 hp).2
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.isValue,Fin.reduceFinMk,
    Fin.succ_zero_eq_one,Fin.succ_one_eq_two,add_zero] at hpsum ⊢
  have h0 := hpar 0
  have h1 := hpar 1
  have h2 := hpar 2
  omega

private theorem OrdinaryFrame.equal_impossible {B : I → Finset V} (F : OrdinaryFrame B)
    (hv : Fintype.card V = 19) (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (hequal : pointSupport B F.p ∩ F.T = pointSupport B F.q ∩ F.T) : False := by
  obtain ⟨mark,hm,hrules⟩ := F.equal_rules hv h hequal
  obtain ⟨b,c,hbc,hH⟩ := card_eq_two.mp F.p_trace
  have hT (i : I) (him : i ∈ ({b,c} : Finset I)) : i ∈ F.T :=
    (mem_inter.mp (hH.symm ▸ him)).2
  have hP (i : I) (him : i ∈ ({b,c} : Finset I)) : i ∈ pointSupport B F.p :=
    (mem_inter.mp (hH.symm ▸ him)).1
  have hc (i : I) (him : i ∈ ({b,c} : Finset I)) : (F.group i).card = 4 := by
    have hp := hP i him
    have hq : i ∈ pointSupport B F.q :=
      (mem_inter.mp (hequal ▸ mem_inter.mpr ⟨hp,hT i him⟩)).1
    have hh := F.group_card h.1 i (hT i him)
    simp only [if_pos hp,if_pos hq] at hh
    omega
  have hneed (i j : I) (hpair : ({b,c} : Finset I) = {i,j}) :
      ∃ w ∈ F.group i, indexedDegree B w = 7 := by
    by_contra hnone
    have hj : j ∈ ({b,c} : Finset I) := hpair.symm ▸ (by simp)
    have hbound := F.minimum_bound j (by rw [hc j hj]) (by
      intro w hw hwo
      obtain ⟨k,hk,hkw⟩ := F.minimum_group w hw hwo
      have hkin := (F.equal_minimum_rule hv h hequal mark hrules k hk w hkw hw).1
      rw [hH,hpair] at hkin
      simp only [mem_insert,mem_singleton] at hkin
      rcases hkin with rfl | rfl
      · exact False.elim (hnone ⟨w,hkw,hw⟩)
      · exact hkw)
    have := eight_minimum_points hv h hi
    omega
  obtain ⟨w,hw,hw7⟩ := hneed b c rfl
  obtain ⟨u,hu,hu7⟩ := hneed c b (pair_comm b c)
  have hb := (F.equal_minimum_rule hv h hequal mark hrules b (hT b (by simp)) w hw hw7).2
  have hc' := (F.equal_minimum_rule hv h hequal mark hrules c (hT c (by simp)) u hu hu7).2
  have ht (d : Fin 3) : (if b = mark d then 1 else 0) + (if c = mark d then 1 else 0) = 1 := by
    have hd := hm d
    rw [hH] at hd
    simp only [mem_insert,mem_singleton] at hd
    rcases hd with hd | hd <;> simp [hd,hbc,hbc.symm]
  have hs := sum_congr (s₁ := (univ : Finset (Fin 3))) rfl (fun d _ => ht d)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,mul_one] at hs
  omega

private def OrdinaryFrame.swap {B : I → Finset V} (F : OrdinaryFrame B) : OrdinaryFrame B :=
  { F with
    p := F.q
    q := F.p
    pq_ne := F.pq_ne.symm
    p_out := F.q_out
    q_out := F.p_out
    p_trace := F.q_trace
    q_trace := F.p_trace
    high_pairs := fun d => ⟨(F.high_pairs d).2,(F.high_pairs d).1⟩
    low_pairs := fun w ho hp hq => F.low_pairs w ho hq hp
    low_trace := fun w ho hp hq => F.low_trace w ho hq hp
    p_high := F.q_high
    q_high := F.p_high }

private theorem OrdinaryFrame.distinct_rule {B : I → Finset V} (F : OrdinaryFrame B)
    (hv : Fintype.card V = 19) (h : Multicover.IsCover B 9 3 1)
    (hne : pointSupport B F.p ∩ F.T ≠ pointSupport B F.q ∩ F.T)
    (d : Fin 3) (i : I) (w : V) (hw : w ∈ F.group i)
    (hp : i ∈ pointSupport B F.p) (hq : i ∉ pointSupport B F.q) :
    indexedSubsetDegree B {F.roots d,w,F.p} + 2 * (rootFibre B (F.roots d) w).card = 7 := by
  obtain ⟨e,hde⟩ : ∃ e : Fin 3, d ≠ e := by fin_cases d <;> decide
  let y : {u : V // u ∉ ({F.roots d} : Finset V)} :=
    ⟨F.roots e,by simpa only [mem_singleton] using fun he => hde (F.roots.injective he).symm⟩
  let p : {u : V // u ∉ ({F.roots d} : Finset V)} :=
    ⟨F.p,by simpa only [mem_singleton] using (F.root_ne_p d).symm⟩
  let q : {u : V // u ∉ ({F.roots d} : Finset V)} :=
    ⟨F.q,by simpa only [mem_singleton] using (F.root_ne_q d).symm⟩
  have hy : indexedSubsetDegree B {F.roots d,y.val} = 3 := by
    rw [← pointSupport_pair,F.root_inter d e hde,F.T_card]
  have hwn : w ≠ F.roots d := fun he =>
    (F.group_ordinary i w hw).1 (mem_image.mpr ⟨d,mem_univ _,he.symm⟩)
  exact middle_distinct_actual hv h (F.roots d) (F.root_min d) y p q
    (fun he => F.pq_ne (congrArg Subtype.val he)) hy (F.high_pairs d).1 (F.high_pairs d).2
    (F.root_fibre_card d e hde) F.T (F.root_inter d e hde).symm F.p_trace F.q_trace hne
    ⟨w,by simpa only [mem_singleton] using hwn⟩ i (F.group_pairs i w hw d)
    (mem_filter.mp hw).2 hp hq

private theorem OrdinaryFrame.distinct_no_minimum {B : I → Finset V} (F : OrdinaryFrame B)
    (hv : Fintype.card V = 19) (h : Multicover.IsCover B 9 3 1)
    (hne : pointSupport B F.p ∩ F.T ≠ pointSupport B F.q ∩ F.T)
    (i : I) (hi : i ∈ F.T) (w : V) (hw : w ∈ F.group i) (hm : indexedDegree B w = 7)
    (hp : i ∈ pointSupport B F.p) (hq : i ∉ pointSupport B F.q) : False := by
  have hc := F.group_card h.1 i hi
  simp only [if_pos hp,if_neg hq,add_zero] at hc
  have hs := F.agreement_sum hv h i w hw hm
  have ht := sum_congr (s₁ := (univ : Finset (Fin 3))) rfl
    (fun d _ => F.distinct_rule hv h hne d i w hw hp hq)
  simp only [sum_add_distrib,← mul_sum,sum_const,card_univ,Fintype.card_fin,Nat.nsmul_eq_mul] at ht
  have hpairs := F.minimum_pair_sum i w hw hm F.p
  rw [if_pos hp] at hpairs
  have hple := minimum_pair_le_four hv h w F.p hm (F.group_ordinary i w hw).2.1
  omega

private theorem OrdinaryFrame.distinct_impossible {B : I → Finset V} (F : OrdinaryFrame B)
    (hv : Fintype.card V = 19) (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (hne : pointSupport B F.p ∩ F.T ≠ pointSupport B F.q ∩ F.T) : False := by
  let H := pointSupport B F.p ∩ F.T
  let G := pointSupport B F.q ∩ F.T
  have hH : H.card = 2 := F.p_trace
  have hG : G.card = 2 := F.q_trace
  have hu : H ∪ G ⊆ F.T := union_subset inter_subset_right inter_subset_right
  have huc := card_le_card hu
  rw [F.T_card] at huc
  have hs := card_union_add_card_inter H G
  have hic := card_le_card (inter_subset_left (s₁ := H) (s₂ := G))
  have hint : (H ∩ G).card = 1 := by
    have hn2 : (H ∩ G).card ≠ 2 := by
      intro hh
      have heH := eq_of_subset_of_card_le (inter_subset_left (s₁ := H) (s₂ := G)) (by rw [hH,hh])
      have heG := eq_of_subset_of_card_le (inter_subset_right (s₁ := H) (s₂ := G)) (by rw [hG,hh])
      exact hne (heH.symm.trans heG)
    omega
  obtain ⟨i,hiHG⟩ := card_eq_one.mp hint
  have hiH : i ∈ H := (mem_inter.mp (hiHG.symm ▸ mem_singleton_self i)).1
  have hiG : i ∈ G := (mem_inter.mp (hiHG.symm ▸ mem_singleton_self i)).2
  have hUT : H ∪ G = F.T := eq_of_subset_of_card_le hu (by rw [F.T_card]; omega)
  have hc := F.group_card h.1 i (mem_inter.mp hiH).2
  simp only [if_pos (mem_inter.mp hiH).1,if_pos (mem_inter.mp hiG).1] at hc
  have hbound := F.minimum_bound i (by omega) (by
    intro w hw hwo
    obtain ⟨j,hj,hwj⟩ := F.minimum_group w hw hwo
    have hjU : j ∈ H ∪ G := hUT.symm ▸ hj
    have hji : j = i := by
      apply mem_singleton.mp
      rw [← hiHG]
      have hpq : j ∈ H ∧ j ∈ G := by
        rcases mem_union.mp hjU with hp | hq
        · refine ⟨hp,?_⟩
          by_contra hnq
          have hnq' : j ∉ pointSupport B F.q := fun hq => hnq (mem_inter.mpr ⟨hq,hj⟩)
          exact F.distinct_no_minimum hv h hne j hj w hwj hw (mem_inter.mp hp).1 hnq'
        · refine ⟨?_,hq⟩
          by_contra hnp
          have hnp' : j ∉ pointSupport B F.p := fun hp => hnp (mem_inter.mpr ⟨hp,hj⟩)
          have hswap : pointSupport B F.swap.p ∩ F.swap.T ≠ pointSupport B F.swap.q ∩ F.swap.T := by
            simpa only [OrdinaryFrame.swap] using hne.symm
          exact F.swap.distinct_no_minimum hv h hswap j
            (by simpa only [OrdinaryFrame.swap] using hj) w
            (by
              apply mem_filter.mpr
              exact ⟨mem_univ _,by simpa only [OrdinaryFrame.swap] using (mem_filter.mp hwj).2⟩) hw
            (by simpa only [OrdinaryFrame.swap] using (mem_inter.mp hq).1)
            (by simpa only [OrdinaryFrame.swap] using hnp')
      exact mem_inter.mpr hpq
    exact hji ▸ hwj)
  have := eight_minimum_points hv h hi
  omega

/-- Three mutually ordinary minimum roots cannot have three common occurrences.
All traces and all point fibres in this exclusion retain their actual identities. -/
theorem no_three_ordinary_minima {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : indexedDegree B x = 7) (hy : indexedDegree B y = 7) (hz : indexedDegree B z = 7)
    (hxy₃ : indexedSubsetDegree B {x,y} = 3)
    (hxz₃ : indexedSubsetDegree B {x,z} = 3)
    (hyz₃ : indexedSubsetDegree B {y,z} = 3) : indexedSubsetDegree B {x,y,z} ≠ 3 := by
  intro ht
  obtain ⟨F⟩ := make_ordinary_frame hv h hi x y z hxy hxz hyz hx hy hz hxy₃ hxz₃ hyz₃ ht
  by_cases he : pointSupport B F.p ∩ F.T = pointSupport B F.q ∩ F.T
  · exact F.equal_impossible hv h hi he
  · exact F.distinct_impossible hv h hi he

#guard_standard_axioms no_three_ordinary_minima
end CoveringDesigns.C19_9_3
