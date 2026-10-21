import CoveringDesigns.C18_10_3.RankCases
import CoveringDesigns.Foundations.PairedSupportObstruction

/-! The final exceptional-support contradiction uses actual point labels and
actual block indices. Binary pair margins alone do not imply triple coverage. -/
namespace CoveringDesigns.C18_10_3
open Finset Matrix
variable {α : Type*} [Fintype α] [DecidableEq α]

def pointSupport (C : Family α) (p : α) : Finset C := univ.filter (fun B => p ∈ B.val)

theorem pointSupport_card (C : Family α) (p : α) : (pointSupport C p).card = degree C p := by
  simp only [pointSupport,degree,star,card_eq_sum_ones,sum_filter]
  exact sum_coe_sort C (fun B => if p ∈ B then (1 : ℕ) else 0)

theorem pointSupport_inter (C : Family α) (p q : α) :
    (pointSupport C p ∩ pointSupport C q).card = degree (star C p) q := by
  have he : pointSupport C p ∩ pointSupport C q = univ.filter (fun B : C => p ∈ B.val ∧ q ∈ B.val) := by
    ext B
    simp [pointSupport]
  rw [he]
  simp only [card_eq_sum_ones,sum_filter,degree,star]
  rw [sum_coe_sort C (fun B => if p ∈ B ∧ q ∈ B then (1 : ℕ) else 0)]
  apply sum_congr rfl
  intro B _
  split_ifs <;> simp_all

/-- A zero deficit gives the two exact high intersections, using the derived pair floor. -/
theorem zero_deficit_intersections {C : Family α} {h g : α} (hne : h ≠ g)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    (x : Outside ({h,g} : Finset α)) (hd : rowDeficit C {h,g} x = 0) :
    degree (star C x.val) h = 3 ∧ degree (star C x.val) g = 3 := by
  have hx : x.val ≠ h ∧ x.val ≠ g := by simpa using x.property
  have ht := rowDeficit_add hpair x
  simp only [card_pair hne,sum_pair hne,hd] at ht
  have hh := hpair x.val h hx.1
  have hg := hpair x.val g hx.2
  omega

/-- The odd sum nine excludes deficit-three rows from every agreeing column
pattern. This also proves the stronger original agreeing-row condition. -/
theorem agreeing_high_intersections {C : Family α} {h g : α} (hne : h ≠ g)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    {a b : C}
    (ha : pointSupport C h \ pointSupport C g = {a})
    (hb : pointSupport C g \ pointSupport C h = {b})
    (x : Outside ({h,g} : Finset α))
    (hd : rowDeficit C {h,g} x = 0 ∨ rowDeficit C {h,g} x = 3)
    (hag : a ∈ pointSupport C x.val ↔ b ∈ pointSupport C x.val) :
    rowDeficit C {h,g} x = 0 ∧
      degree (star C x.val) h = 3 ∧ degree (star C x.val) g = 3 := by
  have he := SupportObstruction.intersections_eq_of_agree
    (pointSupport C h) (pointSupport C g) (pointSupport C x.val) ha hb hag
  rw [pointSupport_inter,pointSupport_inter] at he
  have ht := rowDeficit_add hpair x
  simp only [card_pair hne,sum_pair hne] at ht
  have hz : rowDeficit C {h,g} x = 0 := by omega
  exact ⟨hz,zero_deficit_intersections hne hpair x hz⟩

/-- Uniformity counts the two exceptional blocks on all actual points. The
restricted equality partition supplies every premise of the finite obstruction. -/
theorem two_high_impossible {C : Family α}
    (hv : Fintype.card α = 18) (hC : IsCover C 10 3) (hb : C.card = 11)
    (hpair : ∀ x y, x ≠ y → 3 ≤ degree (star C x) y)
    {h g : α} (hne : h ≠ g) (hh : degree C h = 7) (hg : degree C g = 7)
    (hlow : ∀ x, x ≠ h → x ≠ g → degree C x = 6) : False := by
  classical
  have hlo : ∀ x, x ∉ ({h,g} : Finset α) → degree C x = 6 := by
    intro x hx
    have hx' : x ≠ h ∧ x ≠ g := by simpa using hx
    exact hlow x hx'.1 hx'.2
  have hm := high_pair_eq_six hv hC hb hpair hne hh hg hlo
  have hl : Fintype.card (Outside ({h,g} : Finset α)) = 16 := by
    rw [outside_card,hv,card_pair hne]
  have hbc : Fintype.card C = 11 := by simpa using hb
  have ht : (∑ x : Outside ({h,g} : Finset α), rowDeficit C {h,g} x) = 18 := by
    have he := two_high_deficit_total hv hC.1 hpair hne hh hg
    omega
  let R := rowIncidence C {h,g}
  let E := rowExcess C {h,g}
  let δ := rowDeficit C {h,g}
  have hs := rowExcess_symm C {h,g}
  have hn := rowExcess_nonneg (H := {h,g}) hpair
  have hz := rowExcess_diag C {h,g}
  have hr := row_balance hv hC.1 hlo hpair
  have hgr := row_gram hlo
  obtain ⟨e,hzero,hthree,hcross,_,_,heq⟩ :=
    core_pairing R E δ hl hbc hs hn hz hr ht hgr
  let P (i : Fin 5) := pointSupport C (e (.inl (i,false))).val
  let Q (i : Fin 6) := pointSupport C (e (.inr i)).val
  have hPs (i : Fin 5) (b : Bool) : pointSupport C (e (.inl (i,b))).val = P i := by
    cases b with
    | false => rfl
    | true =>
      ext B
      have he := heq i B
      change (if (e (.inl (i,false))).val ∈ B.val then (1 : ℝ) else 0) =
        (if (e (.inl (i,true))).val ∈ B.val then 1 else 0) at he
      simp only [pointSupport,P,mem_filter,mem_univ,true_and]
      split_ifs at he <;> simp_all
  have hP (i : Fin 5) : (P i).card = 6 := by
    rw [pointSupport_card]; exact hlo _ (e (.inl (i,false))).property
  have hPHG (i : Fin 5) : (P i ∩ pointSupport C h).card = 3 ∧
      (P i ∩ pointSupport C g).card = 3 := by
    simpa only [P,pointSupport_inter] using
      zero_deficit_intersections hne hpair (e (.inl (i,false))) (hzero i false)
  have hQ (i : Fin 6) : (Q i ∩ pointSupport C h).card +
      (Q i ∩ pointSupport C g).card = 9 := by
    have hd := rowDeficit_add hpair (e (.inr i))
    change δ (e (.inr i)) + _ = _ at hd
    rw [hthree i] at hd
    simpa only [Q,pointSupport_inter,card_pair hne,sum_pair hne] using hd.symm
  have hPP (i j : Fin 5) (hij : i ≠ j) : (P i ∩ P j).card = 3 := by
    have hne' : e (.inl (i,false)) ≠ e (.inl (j,false)) := by
      intro he; have he' := e.injective he; simp_all
    have he := hcross i j hij false false
    change rowExcess C {h,g} _ _ = 0 at he
    simp only [rowExcess,if_neg hne'] at he
    have hc : (degree (star C (e (.inl (i,false))).val)
        (e (.inl (j,false))).val : ℝ) = 3 := by linarith
    simpa only [P,pointSupport_inter] using (show degree
      (star C (e (.inl (i,false))).val) (e (.inl (j,false))).val = 3 by exact_mod_cast hc)
  have hcol (B : C) : (if B ∈ pointSupport C h then 1 else 0) +
      (if B ∈ pointSupport C g then 1 else 0) +
      2 * (∑ i, if B ∈ P i then 1 else 0) +
      (∑ i, if B ∈ Q i then 1 else 0) = (10 : ℕ) := by
    have he : (∑ x : Outside ({h,g} : Finset α),
        if B ∈ pointSupport C x.val then 1 else 0) =
        2 * (∑ i, if B ∈ P i then 1 else 0) +
          (∑ i, if B ∈ Q i then 1 else 0) := by
      rw [← e.sum_comp]
      simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,hPs]
      simp only [← two_mul,← mul_sum,Q]
    have ht := sum_outside ({h,g} : Finset α) (fun x => if x ∈ B.val then (1 : ℕ) else 0)
    have hB : (∑ x : α, if x ∈ B.val then 1 else 0) = (10 : ℕ) := by
      simpa [← sum_filter] using hC.1 B.val B.property
    simp only [pointSupport,mem_filter,mem_univ,true_and] at he ⊢
    rw [sum_pair hne,hB] at ht
    omega
  have hH : (pointSupport C h).card = 7 := by rw [pointSupport_card,hh]
  have hG : (pointSupport C g).card = 7 := by rw [pointSupport_card,hg]
  have hHG : (pointSupport C h ∩ pointSupport C g).card = 6 := by rw [pointSupport_inter,hm]
  obtain ⟨i,j,hij,hempty⟩ := SupportObstruction.paired_support_obstruction
    (pointSupport C h) (pointSupport C g) P Q hbc hH hG hHG hP
    (fun i => (hPHG i).1) (fun i => (hPHG i).2) hQ hPP hcol
  let x := e (.inl (i,false))
  let y := e (.inl (j,false))
  have hx : x.val ≠ h := (show x.val ≠ h ∧ x.val ≠ g by simpa using x.property).1
  have hy : y.val ≠ h := (show y.val ≠ h ∧ y.val ≠ g by simpa using y.property).1
  have hxy : x.val ≠ y.val := by
    intro he
    have he' := e.injective (show x = y from Subtype.ext he)
    simp_all [x,y]
  apply SupportObstruction.uncovered_triple (fun B : C => B.val) h x.val y.val
    hx.symm hy.symm hxy hempty
  intro T hT
  obtain ⟨B,hBC,hTB⟩ := hC.2 T hT
  exact ⟨⟨B,hBC⟩,hTB⟩

end CoveringDesigns.C18_10_3
