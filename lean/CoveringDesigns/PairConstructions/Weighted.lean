import CoveringDesigns.PairConstructions.Projective
import CoveringDesigns.AffineConstructions.Construction
import CoveringDesigns.TwoKMinusTwo.Expansion
import CoveringDesigns.PointReduction.Family

/-! Classical weighted projective replication, retaining twins and deduplicating
only block images. The endpoint is an ordinary family on arbitrary labels. -/
namespace CoveringDesigns.PairConstructions
open Finset ProjectiveHyperplanes

/-- Weight one projective line by r and all other points by u, then restrict
and pad. The only prime-power premise is in this construction theorem. -/
theorem weighted_projective {α : Type*} [Fintype α] {q u r : ℕ}
    (hq : IsPrimePow q) (hq2 : 2 ≤ q) (hr : 1 ≤ r) (hru : r ≤ u)
    (hv : Fintype.card α = q*(q*u+r)) :
    ∃ C : Family α, IsCover C (q*u+r) 2 ∧ C.card ≤ q*q+q+1 := by
  classical
  obtain ⟨F,hF,hfin,hcard⟩ := AffineConstructions.exists_field hq
  letI := hF
  letI := hfin
  let P := Point F 3
  let D := Direction F 3
  have : Finite (Module.Dual F (Fin 3 → F)) := Module.finite_of_finite F
  letI : Fintype P := Fintype.ofFinite _
  letI : Fintype D := Fintype.ofFinite _
  have hg2 : G q 2 = q+1 := by simp [G,AffineSchoenheim.geom,sum_range_succ,Nat.add_comm]
  have hg3 : G q 3 = q*q+q+1 := by
    simp [G,AffineSchoenheim.geom,sum_range_succ,pow_two]
    ring
  have hp : Fintype.card P = q*q+q+1 := by
    rw [← Nat.card_eq_fintype_card,point_card,hcard,hg3]
  have hd : Fintype.card D = q*q+q+1 := by
    rw [← Nat.card_eq_fintype_card,direction_card,hcard,hg3]
  have hs (d : D) : (hyperplane d).card = q+1 := by rw [hyperplane_card,hcard,hg2]
  haveI : Nonempty D := Fintype.card_pos_iff.mp (by rw [hd]; omega)
  let d₀ : D := Classical.choice inferInstance
  let L := hyperplane d₀
  let w : P → ℕ := fun x => if x ∈ L then r else u
  have weight_sum (S : Finset P) : (∑ x ∈ S, w x) =
      (S.filter (· ∈ L)).card*r + (S.filter (· ∉ L)).card*u := by
    simp [w,sum_ite]
    rfl
  have total : (∑ x, w x) = q*(q*u+r)+r := by
    have hc := card_filter_add_card_filter_not (s := (univ : Finset P)) (p := (· ∈ L))
    have hl : (univ.filter (· ∈ L)).card = q+1 := by simpa [L] using hs d₀
    have hn : (univ.filter (fun x : P => x ∉ L)).card = q*q := by
      rw [hl,card_univ,hp] at hc
      omega
    rw [weight_sum,hl,hn]
    ring
  have size (d : D) : (∑ x ∈ hyperplane d, w x) ≤ q*u+r := by
    by_cases he : d = d₀
    · subst d
      have hw : (∑ x ∈ L, w x) = (q+1)*r := by
        change (∑ x ∈ L, if x ∈ L then r else u) = _
        rw [sum_congr rfl (fun x hx => if_pos hx)]
        simpa only [sum_const,nsmul_eq_mul,Nat.cast_id] using congrArg (fun n => n*r) (hs d₀)
      change (∑ x ∈ L, w x) ≤ _
      rw [hw]
      nlinarith [Nat.mul_le_mul_left q hru]
    · have hc := card_filter_add_card_filter_not (s := hyperplane d) (p := (· ∈ L))
      have hl : ((hyperplane d).filter (· ∈ L)).card = 1 := by
        simpa only [filter_mem_eq_inter,L] using projective_line_intersection d d₀ he
      have hn : ((hyperplane d).filter (· ∉ L)).card = q := by
        rw [hl,hs] at hc
        omega
      rw [weight_sum,hl,hn]
      omega
  obtain ⟨C,hC,hb⟩ := TwoKMinusTwo.weighted_expansion w (fun d : D => hyperplane d)
    (k := q*u+r) (t := 2) (by rw [total]; nlinarith) size
    (fun S hS => hyperplanes_cover S hS)
  have hh : Fintype.card (Σ x : P, Fin (w x)) = q*(q*u+r)+r := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using total
  obtain ⟨E,hE,he⟩ := PointReduction.family_reduce_points (β := α) hC
    (by rw [hv]; nlinarith) (by rw [hh,hv]; omega)
  exact ⟨E,hE,he.trans (by simpa [hd] using hb)⟩

end CoveringDesigns.PairConstructions
