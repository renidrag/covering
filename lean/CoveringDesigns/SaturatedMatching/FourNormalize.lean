import CoveringDesigns.SaturatedMatching.Relabel
import CoveringDesigns.SaturatedMatching.FourNormalized
import Mathlib.Data.Fintype.EquivFin

/-! Symbolic normalization from two groups of remaining-block signatures.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset
variable {α ι M : Type*} [Fintype α] [Fintype ι] [Fintype M]
  [DecidableEq α] [DecidableEq ι] [DecidableEq M]
variable {B : ι → Finset α} {P : Pattern (M := M) B}

namespace Remaining
variable (R : Remaining P) (H : FourCompatibility P)
include H

/-- Number the two signature classes, retaining a bijection of actual edges. -/
theorem grouped_indices :
    ∃ r : Fin 4 ≃ M,
      R.signature (r 0) = R.signature (r 1) ∧
      R.signature (r 2) = R.signature (r 3) ∧
      Disjoint (R.signature (r 0)) (R.signature (r 2)) := by
  classical
  obtain ⟨hc,hfib⟩ := R.two_groups H
  obtain ⟨J,K,hJK,hS⟩ := card_eq_two.mp hc
  have hJ : J ∈ univ.image R.signature := by rw [hS]; simp
  have hK : K ∈ univ.image R.signature := by rw [hS]; simp
  obtain ⟨f,g,hfg,hfgS⟩ := card_eq_two.mp (hfib J hJ)
  obtain ⟨h,i,hhi,hhiS⟩ := card_eq_two.mp (hfib K hK)
  have hf : R.signature f = J :=
    (mem_filter.mp (show f ∈ univ.filter (fun x => R.signature x = J) by rw [hfgS]; simp)).2
  have hg : R.signature g = J :=
    (mem_filter.mp (show g ∈ univ.filter (fun x => R.signature x = J) by rw [hfgS]; simp)).2
  have hh : R.signature h = K :=
    (mem_filter.mp (show h ∈ univ.filter (fun x => R.signature x = K) by rw [hhiS]; simp)).2
  have hi : R.signature i = K :=
    (mem_filter.mp (show i ∈ univ.filter (fun x => R.signature x = K) by rw [hhiS]; simp)).2
  have hfh : f ≠ h := by intro he; exact hJK (hf.symm.trans (he ▸ hh))
  have hfi : f ≠ i := by intro he; exact hJK (hf.symm.trans (he ▸ hi))
  have hgh : g ≠ h := by intro he; exact hJK (hg.symm.trans (he ▸ hh))
  have hgi : g ≠ i := by intro he; exact hJK (hg.symm.trans (he ▸ hi))
  let v : Fin 4 → M := ![f,g,h,i]
  have hinj : Function.Injective v := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [v]
  let r := Equiv.ofBijective v
    ((Fintype.bijective_iff_injective_and_card v).mpr ⟨hinj,by simp [H.pairs]⟩)
  refine ⟨r,by simpa [r,v] using hf.trans hg.symm,
    by simpa [r,v] using hh.trans hi.symm,?_⟩
  change Disjoint (R.signature f) (R.signature h)
  exact (R.signatures_compatible H f h hfh).resolve_left
    (by rw [hf,hh]; exact hJK)

/-- Disjoint free signatures force opposite correlations in the other rows. -/
theorem disjoint_correlations (e h f g : M)
    (hfg : f ≠ g) (heh : e ≠ h)
    (hrest : (univ : Finset M) \ {f,g} = {e,h})
    (hd : Disjoint (R.signature f) (R.signature g)) :
    (P.sign e f == P.sign e g) ≠ (P.sign h f == P.sign h g) := by
  intro heq
  let c := !(P.sign e f == P.sign e g)
  have hem : (true == P.sign e f) ≠ (c == P.sign e g) := by
    cases ha : P.sign e f <;> cases hb : P.sign e g <;> simp [c,ha,hb]
  have hhm : (true == P.sign h f) ≠ (c == P.sign h g) := by
    cases ha : P.sign e f <;> cases hb : P.sign e g <;>
      cases hc : P.sign h f <;> cases hd : P.sign h g <;> simp_all [c]
  have hi := R.equal_of_missing e h f g true c hfg heh hrest hem hhm
    (H.floor f g hfg true c)
  apply disjoint_left.mp hd (show R.index (f,true) ∈ R.signature f by simp [signature])
  rw [hi]
  cases c <;> simp [signature]

end Remaining

variable {P : Pattern (M := Fin 4) B}

/-- Aligned plus labels in each signature class give four opposite entries. -/
theorem aligned_signs (R : Remaining P) (H : FourCompatibility P)
    (h01 : R.index (0,true) = R.index (1,true))
    (h23 : R.index (2,true) = R.index (3,true)) :
    P.sign 2 0 ≠ P.sign 2 1 ∧ P.sign 3 0 ≠ P.sign 3 1 ∧
    P.sign 0 2 ≠ P.sign 0 3 ∧ P.sign 1 2 ≠ P.sign 1 3 := by
  have aux (e h f g : Fin 4)
      (heh : e ≠ h) (hef : e ≠ f) (heg : e ≠ g)
      (hhf : h ≠ f) (hhg : h ≠ g) (hfg : f ≠ g)
      (hi : R.index (f,true) = R.index (g,true)) :
      P.sign e f ≠ P.sign e g := by
    have hx := R.shared_free_separated e h f g true true hfg heh
      (four_rest H.pairs heh hef heg hhf hhg hfg) H.saturated (H.floor f g hfg)
      (fun b c hc => hc.elim (H.cross e f g hef heg hfg b c)
        (H.cross h f g hhf hhg hfg b c)) hi
    simpa using hx
  exact ⟨aux 2 3 0 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h01,
    aux 3 2 0 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h01,
    aux 0 1 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h23,
    aux 1 0 2 3 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) h23⟩

/-- Once four row orientations are fixed, three cross-class equations
determine the four remaining entries from one bit. -/
theorem normalized_from_aligned (R : Remaining P) (H : FourCompatibility P)
    (h01 : R.index (0,true) = R.index (1,true))
    (h23 : R.index (2,true) = R.index (3,true))
    (hd : Disjoint (R.signature 0) (R.signature 2))
    (h13 : R.signature 1 = R.signature 0)
    (h32 : R.signature 3 = R.signature 2)
    (hr : P.sign 0 2 = true ∧ P.sign 1 2 = true ∧
      P.sign 2 0 = true ∧ P.sign 3 0 = true) :
    let b := P.sign 1 0
    ∀ e f, e ≠ f →
      (P.relabel (Equiv.refl _) ![b,b,true,true] ![true,true,b,b]).sign e f =
        normalizedSigns e f := by
  obtain ⟨h20,h30,h02,h12⟩ := aligned_signs R H h01 h23
  have h21 : P.sign 2 1 = false := by cases h : P.sign 2 1 <;> simp_all
  have h31 : P.sign 3 1 = false := by cases h : P.sign 3 1 <;> simp_all
  have h03 : P.sign 0 3 = false := by cases h : P.sign 0 3 <;> simp_all
  have h13' : P.sign 1 3 = false := by cases h : P.sign 1 3 <;> simp_all
  have hc02 := R.disjoint_correlations H 1 3 0 2 (by decide) (by decide)
    (four_rest H.pairs (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) hd
  have hc03 := R.disjoint_correlations H 1 2 0 3 (by decide) (by decide)
    (four_rest H.pairs (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) (by rwa [h32])
  have hc12 := R.disjoint_correlations H 0 3 1 2 (by decide) (by decide)
    (four_rest H.pairs (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) (by rwa [h13])
  have h32' : P.sign 3 2 = !(P.sign 1 0) := by
    cases hb : P.sign 1 0 <;> cases hh : P.sign 3 2 <;> simp_all
  have h23' : P.sign 2 3 = P.sign 1 0 := by
    cases hb : P.sign 1 0 <;> cases hh : P.sign 2 3 <;> simp_all
  have h01' : P.sign 0 1 = !(P.sign 1 0) := by
    cases hb : P.sign 1 0 <;> cases hh : P.sign 0 1 <;> simp_all
  dsimp only
  intro e f hef
  fin_cases e <;> fin_cases f <;>
    simp_all [Pattern.relabel,normalizedSigns]

end CoveringDesigns.SaturatedMatching
