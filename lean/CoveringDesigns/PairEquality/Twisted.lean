import CoveringDesigns.PairEquality.Basic

/-! Actual twisted incidence, including the derivation of coordinate pair coverage. -/

namespace CoveringDesigns.PairEquality
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Finite regular intersecting incidence at the twisted parameters. The mate
theorems below derive both exact incidence relations and pair coverage from
these fields; pair coverage is deliberately not a hypothesis. -/
structure IsTwistedPlane (q : ℕ) (H : Finset (Finset I)) : Prop where
  coordinates : Fintype.card I = q*(q+1)
  supports : H.card = q*(q+1)
  uniform : ∀ E ∈ H, E.card = q+1
  degree_eq : ∀ x, degree H x = q+1
  intersect : ∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).Nonempty

theorem twisted_of_no_degree_q {q : ℕ} {H : Finset (Finset I)}
    {w : Finset I → ℝ} (h : PositiveUnitLoads q H w)
    (hli : LinearIndependent ℝ (fun E : H => indicator E.val))
    (hn : ∀ x, degree H x ≠ q) : IsTwistedPlane q H := by
  have hl (x : I) : q+1 ≤ degree H x := by have := h.degree_lower x; have := hn x; omega
  have hu : H.card ≤ Fintype.card I := by simpa using hli.fintype_card_le_finrank
  have hc := sum_le_sum (fun x (_ : x ∈ (univ : Finset I)) => hl x)
  rw [degree_sum,sum_congr rfl h.uniform] at hc
  simp only [sum_const,card_univ,nsmul_eq_mul] at hc
  have hh : H.card = q*(q+1) := by rw [h.coordinates] at hu hc; nlinarith
  refine ⟨h.coordinates,hh,h.uniform,?_,h.intersect⟩
  have he : (∑ _x : I, (q+1)) = ∑ x, degree H x := by
    rw [degree_sum,sum_congr rfl h.uniform]
    simp [hh,h.coordinates]
  intro x
  exact ((sum_eq_sum_iff_of_le (fun x _ => hl x)).mp he x (mem_univ _)).symm

namespace IsTwistedPlane
variable {q : ℕ} {H : Finset (Finset I)} (T : IsTwistedPlane q H)
include T

private theorem intersection_sum (E : Finset I) :
    (∑ F ∈ H, (E ∩ F).card) = E.card * (q+1) := by
  have he : (∑ F ∈ H, (E ∩ F).card) = ∑ x ∈ E, degree H x := by
    simp only [degree,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro x hx
    simp [hx]
  rw [he]
  simp [T.degree_eq]

private theorem support_pair (E : H) : ∃ F : H, E ≠ F ∧
    (E.val ∩ F.val).card = 2 ∧
    ∀ D : H, D ≠ E → D ≠ F → (E.val ∩ D.val).card = 1 := by
  classical
  let f := fun F : Finset I => (E.val ∩ F).card - 1
  have hp (F : Finset I) (hF : F ∈ H.erase E.val) : 1 ≤ (E.val ∩ F).card := by
    exact card_pos.mpr (T.intersect E.val E.property F (mem_erase.mp hF).2
      (Ne.symm (mem_erase.mp hF).1))
  have hs : (∑ F ∈ H.erase E.val, f F) = 1 := by
    have he := T.intersection_sum E.val
    have hu := sum_erase_add H (fun F => (E.val ∩ F).card) E.property
    rw [inter_self,T.uniform E.val E.property] at hu
    rw [T.uniform E.val E.property] at he
    have hc : 0 < H.card := card_pos.mpr ⟨E.val,E.property⟩
    have hd := T.supports
    have hh : (∑ F ∈ H.erase E.val, (E.val ∩ F).card) = H.card := by nlinarith
    rw [sum_tsub_distrib _ hp]
    simp only [sum_const,nsmul_eq_mul,mul_one,card_erase_of_mem E.property]
    rw [hh]
    change H.card - (H.card - 1) = 1
    omega
  obtain ⟨F,hF,hpos⟩ := sum_pos_iff.mp (by rw [hs]; decide : 0 < ∑ F ∈ H.erase E.val, f F)
  have hf := single_le_sum (fun D (_ : D ∈ H.erase E.val) => Nat.zero_le (f D)) hF
  have hfv : f F = 1 := by omega
  have hz : (∑ D ∈ (H.erase E.val).erase F, f D) = 0 := by
    have he := sum_erase_add (H.erase E.val) f hF
    omega
  refine ⟨⟨F,(mem_erase.mp hF).2⟩,?_,?_,?_⟩
  · intro he
    exact (mem_erase.mp hF).1 (congrArg Subtype.val he).symm
  · change (E.val ∩ F).card = 2
    dsimp [f] at hfv
    omega
  · intro D hDE hDF
    have hd : D.val ∈ (H.erase E.val).erase F := by
      simp only [mem_erase]
      exact ⟨fun he => hDF (Subtype.ext he),fun he => hDE (Subtype.ext he),D.property⟩
    have he := (sum_eq_zero_iff.mp hz) D.val hd
    have hp' := hp D.val (mem_erase.mpr ⟨fun he => hDE (Subtype.ext he),D.property⟩)
    dsimp [f] at he
    omega

/-- The uniquely determined distinct support meeting a support twice. -/
noncomputable def supportMate (E : H) : H := (T.support_pair E).choose

theorem supportMate_ne (E : H) : T.supportMate E ≠ E :=
  Ne.symm (T.support_pair E).choose_spec.1

theorem supportMate_intersection (E : H) : (E.val ∩ (T.supportMate E).val).card = 2 :=
  (T.support_pair E).choose_spec.2.1

theorem support_intersection (E F : H) (hEF : E ≠ F) :
    (E.val ∩ F.val).card = if F = T.supportMate E then 2 else 1 := by
  by_cases he : F = T.supportMate E
  · subst F
    simp [T.supportMate_intersection]
  · rw [ite_eq_right he]
    exact (T.support_pair E).choose_spec.2.2 F (Ne.symm hEF) he

theorem support_mate_unique (E F : H) (hEF : E ≠ F)
    (hcard : (E.val ∩ F.val).card = 2) : F = T.supportMate E := by
  have he := T.support_intersection E F hEF
  split_ifs at he with hf
  · exact hf
  · omega

theorem supportMate_involutive : Function.Involutive T.supportMate := by
  intro E
  apply Eq.symm
  apply T.support_mate_unique (T.supportMate E) E (T.supportMate_ne E)
  rw [inter_comm,T.supportMate_intersection]

private theorem codegree_le_two (x y : I) (hxy : x ≠ y) : codegree H x y ≤ 2 := by
  classical
  let K := H.filter (fun E => x ∈ E ∧ y ∈ E)
  by_cases hK : K.Nonempty
  · obtain ⟨E,hE⟩ := hK
    let e : H := ⟨E,(mem_filter.mp hE).1⟩
    have hsub : K ⊆ {E,(T.supportMate e).val} := by
      intro F hF
      by_cases he : F = E
      · simp [he]
      · have hp : 2 ≤ (E ∩ F).card := by
          have hsub : {x,y} ⊆ E ∩ F := by
            intro z hz
            simp only [mem_insert,mem_singleton] at hz
            rcases hz with rfl | rfl <;> exact mem_inter.mpr
              ⟨by aesop,by aesop⟩
          have := card_le_card hsub
          simpa [hxy] using this
        let f : H := ⟨F,(mem_filter.mp hF).1⟩
        have hne : e ≠ f := fun hh => he (congrArg Subtype.val hh).symm
        have hf := T.support_intersection e f hne
        have hm : f = T.supportMate e := by
          by_contra hh
          rw [ite_eq_right hh] at hf
          dsimp [e,f] at hf
          omega
        exact mem_insert_of_mem (mem_singleton.mpr (congrArg Subtype.val hm))
    exact (card_le_card hsub).trans card_le_two
  · have he : K = ∅ := not_nonempty_iff_eq_empty.mp hK
    change K.card ≤ 2
    simp [he]

private theorem coordinate_count (x : I) :
    (∑ y ∈ univ.erase x, codegree H x y) = q*(q+1) := by
  have he : (∑ y : I, codegree H x y) = (q+1)*(q+1) := by
    simp only [codegree,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
    have ht (E : Finset I) (hE : E ∈ H) :
        (∑ y : I, if x ∈ E ∧ y ∈ E then 1 else 0) = if x ∈ E then q+1 else 0 := by
      by_cases hx : x ∈ E <;> simp [hx,T.uniform E hE]
    rw [sum_congr rfl ht,← sum_filter]
    simpa [degree] using congrArg (fun n => n*(q+1)) (T.degree_eq x)
  have hs := sum_erase_add univ (codegree H x) (mem_univ x)
  have hx : codegree H x x = q+1 := by simpa [codegree,degree] using T.degree_eq x
  rw [hx,he] at hs
  nlinarith

private theorem coordinate_double (x : I) : ∃ y, x ≠ y ∧ codegree H x y = 2 := by
  by_contra hn
  have hs : (∑ y ∈ univ.erase x, codegree H x y) ≤ (univ.erase x).card := by
    calc
      _ ≤ ∑ _y ∈ univ.erase x, 1 := sum_le_sum (fun y hy => by
        have hxy : x ≠ y := Ne.symm (mem_erase.mp hy).1
        have hc := T.codegree_le_two x y hxy
        have hh : codegree H x y ≠ 2 := fun he => hn ⟨y,hxy,he⟩
        omega)
      _ = _ := by simp
  rw [T.coordinate_count,card_erase_of_mem (mem_univ x),card_univ,T.coordinates] at hs
  have hp : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨x⟩
  rw [T.coordinates] at hp
  omega

private noncomputable def overlap (E : H) : Finset I := E.val ∩ (T.supportMate E).val

private theorem overlap_card (E : H) : (T.overlap E).card = 2 := T.supportMate_intersection E

private theorem overlap_mate (E : H) : T.overlap (T.supportMate E) = T.overlap E := by
  dsimp [overlap]
  rw [T.supportMate_involutive E,inter_comm]

private theorem pair_in_overlap {x y : I} (hxy : x ≠ y) (hc : codegree H x y = 2) :
    ∃ E : H, x ∈ T.overlap E ∧ y ∈ T.overlap E := by
  have hp : 1 < (H.filter (fun E => x ∈ E ∧ y ∈ E)).card := by
    change 1 < codegree H x y
    rw [hc]
    decide
  obtain ⟨E,hE,F,hF,hEF⟩ := one_lt_card.mp hp
  obtain ⟨hE,hxE,hyE⟩ := mem_filter.mp hE
  obtain ⟨hF,hxF,hyF⟩ := mem_filter.mp hF
  let e : H := ⟨E,hE⟩
  let f : H := ⟨F,hF⟩
  have hne : e ≠ f := fun he => hEF (congrArg Subtype.val he)
  have hp : 2 ≤ (E ∩ F).card := by
    have hs : {x,y} ⊆ E ∩ F := by
      intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact mem_inter.mpr ⟨hxE,hxF⟩
      · exact mem_inter.mpr ⟨hyE,hyF⟩
    simpa [hxy] using card_le_card hs
  have hm : f = T.supportMate e := by
    have he := T.support_intersection e f hne
    by_contra hn
    rw [ite_eq_right hn] at he
    dsimp [e,f] at he
    omega
  refine ⟨e,?_,?_⟩ <;> dsimp [overlap] <;> rw [← hm]
  · exact mem_inter.mpr ⟨hxE,hxF⟩
  · exact mem_inter.mpr ⟨hyE,hyF⟩

private noncomputable def carriers (x : I) : Finset H := univ.filter (fun E => x ∈ T.overlap E)

private theorem carriers_lower (x : I) : 2 ≤ (T.carriers x).card := by
  obtain ⟨y,hxy,hc⟩ := T.coordinate_double x
  obtain ⟨E,hx,_⟩ := T.pair_in_overlap hxy hc
  have hs : {E,T.supportMate E} ⊆ T.carriers x := by
    intro F hF
    simp only [mem_insert,mem_singleton] at hF
    rcases hF with rfl | rfl <;> simp [carriers,T.overlap_mate,hx]
  simpa [Ne.symm (T.supportMate_ne E)] using card_le_card hs

private theorem carriers_card (x : I) : (T.carriers x).card = 2 := by
  have hs : (∑ x : I, (T.carriers x).card) = ∑ _x : I, 2 := by
    simp only [carriers,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
    have ht (E : H) : (∑ x : I, if x ∈ T.overlap E then 1 else 0) = 2 := by
      simpa using T.overlap_card E
    rw [sum_congr rfl (fun E _ => ht E)]
    simp [T.supports,T.coordinates]
  exact ((sum_eq_sum_iff_of_le (fun x _ => T.carriers_lower x)).mp hs.symm x (mem_univ _)).symm

private theorem carriers_eq {x : I} {E : H} (hx : x ∈ T.overlap E) :
    T.carriers x = {E,T.supportMate E} := by
  apply Eq.symm
  apply eq_of_subset_of_card_le
  · intro F hF
    simp only [mem_insert,mem_singleton] at hF
    rcases hF with rfl | rfl <;> simp [carriers,T.overlap_mate,hx]
  · rw [T.carriers_card]
    simp [Ne.symm (T.supportMate_ne E)]

private theorem coordinate_unique (x : I) : ∃! y, x ≠ y ∧ codegree H x y = 2 := by
  obtain ⟨y,hxy,hc⟩ := T.coordinate_double x
  obtain ⟨E,hx,hy⟩ := T.pair_in_overlap hxy hc
  refine ⟨y,⟨hxy,hc⟩,?_⟩
  intro z hz
  obtain ⟨F,hxF,hzF⟩ := T.pair_in_overlap hz.1 hz.2
  have hF : F ∈ T.carriers x := by simp [carriers,hxF]
  rw [T.carriers_eq hx] at hF
  have hzE : z ∈ T.overlap E := by
    simp only [mem_insert,mem_singleton] at hF
    rcases hF with rfl | rfl
    · exact hzF
    · simpa [T.overlap_mate] using hzF
  have he : T.overlap E = {x,y} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · simp [insert_subset_iff,hx,hy]
    · simp [T.overlap_card,hxy]
  rw [he,mem_insert,mem_singleton] at hzE
  exact hzE.resolve_left (Ne.symm hz.1)

/-- The uniquely determined distinct coordinate of codegree two. -/
noncomputable def coordinateMate (x : I) : I := (T.coordinate_unique x).choose

theorem coordinateMate_ne (x : I) : T.coordinateMate x ≠ x :=
  Ne.symm (T.coordinate_unique x).choose_spec.1.1

theorem coordinateMate_codegree (x : I) : codegree H x (T.coordinateMate x) = 2 :=
  (T.coordinate_unique x).choose_spec.1.2

theorem coordinate_mate_unique (x y : I) (hxy : x ≠ y) (hc : codegree H x y = 2) :
    y = T.coordinateMate x := (T.coordinate_unique x).choose_spec.2 y ⟨hxy,hc⟩

theorem coordinateMate_involutive : Function.Involutive T.coordinateMate := by
  intro x
  apply Eq.symm
  apply T.coordinate_mate_unique _ _ (T.coordinateMate_ne x)
  simpa [codegree,and_comm] using T.coordinateMate_codegree x

/-- In particular every distinct coordinate pair is covered. This conclusion
uses the doubled-pair count; it is not inferred from support intersection alone. -/
theorem coordinate_codegree (x y : I) (hxy : x ≠ y) :
    codegree H x y = if y = T.coordinateMate x then 2 else 1 := by
  have hl (z : I) (hz : z ∈ univ.erase x) :
      codegree H x z ≤ if z = T.coordinateMate x then 2 else 1 := by
    have hxz := Ne.symm (mem_erase.mp hz).1
    have he := T.codegree_le_two x z hxz
    by_cases hh : z = T.coordinateMate x
    · simpa [hh] using he
    · rw [ite_eq_right hh]
      have hn : codegree H x z ≠ 2 := fun hc => hh (T.coordinate_mate_unique x z hxz hc)
      omega
  have hs : (∑ z ∈ univ.erase x, if z = T.coordinateMate x then 2 else 1) = q*(q+1) := by
    have ht (z : I) : (if z = T.coordinateMate x then 2 else 1) =
        1 + if z = T.coordinateMate x then 1 else 0 := by split_ifs <;> rfl
    simp_rw [ht]
    rw [sum_add_distrib]
    simp [T.coordinateMate_ne,card_erase_of_mem,T.coordinates]
    have hp : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨x⟩
    rw [T.coordinates] at hp
    omega
  have he : (∑ z ∈ univ.erase x, codegree H x z) =
      ∑ z ∈ univ.erase x, if z = T.coordinateMate x then 2 else 1 := by
    rw [T.coordinate_count,hs]
  exact (sum_eq_sum_iff_of_le hl).mp he y (mem_erase.mpr ⟨Ne.symm hxy,mem_univ _⟩)

theorem pair_covered (x y : I) (hxy : x ≠ y) :
    ∃ E ∈ H, x ∈ E ∧ y ∈ E := by
  have he := T.coordinate_codegree x y hxy
  have hp : 0 < codegree H x y := by split_ifs at he <;> omega
  obtain ⟨E,hE⟩ := card_pos.mp hp
  exact ⟨E,(mem_filter.mp hE).1,(mem_filter.mp hE).2⟩

private theorem ordered_pair_count (S E : Finset I) :
    (S ∩ E).card * ((S ∩ E).card - 1) =
      ∑ x ∈ S, ∑ y ∈ S.erase x, if x ∈ E ∧ y ∈ E then 1 else 0 := by
  have ht (x : I) (hx : x ∈ S) :
      (∑ y ∈ S.erase x, if x ∈ E ∧ y ∈ E then 1 else 0) =
        if x ∈ E then (S ∩ E).card - 1 else 0 := by
    by_cases he : x ∈ E
    · simp only [he,true_and]
      rw [← sum_filter,← card_eq_sum_ones,filter_mem_eq_inter,erase_inter,
        card_erase_of_mem (mem_inter.mpr ⟨hx,he⟩),ite_true]
    · simp [he]
  rw [sum_congr rfl ht,← sum_filter]
  simp [filter_mem_eq_inter]

/-- Historical twisted maximality: an intersecting (q+1)-set cannot extend
an actual twisted plane when q≥4. -/
theorem maximal (hq : 4 ≤ q) {S : Finset I} (hS : S.card = q+1)
    (hmeet : ∀ E ∈ H, (S ∩ E).Nonempty) : S ∈ H := by
  by_contra hn
  let f := fun E : Finset I => (S ∩ E).card
  have hlo (E : Finset I) (hE : E ∈ H) : 1 ≤ f E := card_pos.mpr (hmeet E hE)
  have hhi (E : Finset I) (hE : E ∈ H) : f E ≤ q := by
    have he : f E ≤ q+1 := by
      simpa [f,hS] using card_le_card (show S ∩ E ⊆ S from inter_subset_left)
    by_contra hh
    have hc : (S ∩ E).card = S.card := by dsimp [f] at he hh; omega
    have hs : S ⊆ E := inter_eq_left.mp (eq_of_subset_of_card_le inter_subset_left hc.ge)
    have heq : S = E := eq_of_subset_of_card_le hs (by rw [hS,T.uniform E hE])
    exact hn (heq ▸ hE)
  have hsum : (∑ E ∈ H, f E) = (q+1)*(q+1) := by
    simpa [f,hS] using T.intersection_sum S
  have hexcess : (∑ E ∈ H, (f E - 1)) = q+1 := by
    rw [sum_tsub_distrib _ hlo,hsum]
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,T.supports]
    have he : (q+1)*(q+1) = q*(q+1)+(q+1) := by ring
    rw [he,Nat.add_sub_cancel_left]
  have hpairs : q*(q+1) ≤ ∑ E ∈ H, f E * (f E - 1) := by
    have he : (∑ E ∈ H, f E * (f E - 1)) =
        ∑ x ∈ S, ∑ y ∈ S.erase x, codegree H x y := by
      simp only [f,T.ordered_pair_count]
      rw [sum_comm]
      apply sum_congr rfl
      intro x hx
      rw [sum_comm]
      apply sum_congr rfl
      intro y hy
      simp only [codegree,card_eq_sum_ones,sum_filter]
    rw [he]
    have hl := sum_le_sum (fun x (hx : x ∈ S) =>
      sum_le_sum (fun y (hy : y ∈ S.erase x) =>
        show 1 ≤ codegree H x y from by
          have hc := T.coordinate_codegree x y (Ne.symm (mem_erase.mp hy).1)
          split_ifs at hc <;> omega))
    have hz : (∑ x ∈ S, ∑ _y ∈ S.erase x, 1) = q*(q+1) := by
      simp only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_one]
      rw [sum_congr rfl (fun x hx => card_erase_of_mem hx)]
      simp [hS,Nat.mul_comm]
    rw [hz] at hl
    exact hl
  have hbound (E : Finset I) (hE : E ∈ H) :
      f E * (f E - 1) ≤ q * (f E - 1) := Nat.mul_le_mul_right _ (hhi E hE)
  have hupper : (∑ E ∈ H, q * (f E - 1)) = q*(q+1) := by rw [← mul_sum,hexcess]
  have hequal : (∑ E ∈ H, f E * (f E - 1)) = ∑ E ∈ H, q * (f E - 1) :=
    le_antisymm (sum_le_sum hbound) (by rw [hupper]; exact hpairs)
  have hshape (E : Finset I) (hE : E ∈ H) : f E = 1 ∨ f E = q := by
    have he := (sum_eq_sum_iff_of_le hbound).mp hequal E hE
    have hp := hlo E hE
    have hh := hhi E hE
    have hz : f E - 1 + 1 = f E := Nat.sub_add_cancel hp
    by_cases hf : f E = 1
    · exact Or.inl hf
    · right
      exact mul_right_cancel₀ (by omega : f E - 1 ≠ 0) he
  have hncard : (H.filter (fun E => f E = q)).card * (q-1) = q+1 := by
    have ht (E : Finset I) (hE : E ∈ H) : f E - 1 = if f E = q then q-1 else 0 := by
      rcases hshape E hE with he | he <;> simp [he] <;> omega
    rw [sum_congr rfl ht,← sum_filter] at hexcess
    simpa using hexcess
  have hqpred : q-1+1 = q := by omega
  have hpos : 0 < (H.filter (fun E => f E = q)).card := by
    by_contra hh
    have hz : (H.filter (fun E => f E = q)).card = 0 := by omega
    rw [hz,zero_mul] at hncard
    omega
  have hle : (H.filter (fun E => f E = q)).card ≤ 1 := by nlinarith
  have heq : (H.filter (fun E => f E = q)).card = 1 := by omega
  rw [heq,one_mul] at hncard
  omega

end IsTwistedPlane
end CoveringDesigns.PairEquality
