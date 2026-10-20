import CoveringDesigns.SaturatedMatching.FourSignatures

/-! Exactly two groups of two remaining-block signatures.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset
variable {α ι M : Type*} [Fintype α] [Fintype ι] [Fintype M]
  [DecidableEq α] [DecidableEq ι] [DecidableEq M]
variable {B : ι → Finset α}

structure FourCompatibility (P : Pattern (M := M) B) : Prop where
  pairs : Fintype.card M = 4
  occurrences : Fintype.card ι = 13
  degree : ∀ f b, indexedDegree B (P.point (f,b)) = 6
  saturated : ∀ f, indexedSubsetDegree B {P.point (f,true),P.point (f,false)} = 2
  floor : ∀ f g, f ≠ g → ∀ b c,
    3 ≤ indexedSubsetDegree B {P.point (f,b),P.point (g,c)}
  cross : ∀ e f g, e ≠ f → e ≠ g → f ≠ g → ∀ b c,
    (b == P.sign e f) ≠ (c == P.sign e g) →
      indexedSubsetDegree B {P.point (f,b),P.point (g,c)} = 3

theorem four_rest (hM : Fintype.card M = 4) {e h f g : M}
    (heh : e ≠ h) (hef : e ≠ f) (heg : e ≠ g)
    (hhf : h ≠ f) (hhg : h ≠ g) (hfg : f ≠ g) :
    (univ : Finset M) \ {f,g} = {e,h} := by
  have hsub : ({e,h} : Finset M) ⊆ univ \ {f,g} := by
    simp [insert_subset_iff,hef,heg,hhf,hhg]
  apply (eq_of_subset_of_card_le hsub _).symm
  rw [card_sdiff_of_subset (subset_univ _),card_univ,hM,card_pair hfg,card_pair heh]

namespace Remaining
variable {P : Pattern (M := M) B} (R : Remaining P) (H : FourCompatibility P)
include H

theorem signatures_compatible (f g : M) (hfg : f ≠ g) :
    R.signature f = R.signature g ∨ Disjoint (R.signature f) (R.signature g) := by
  classical
  have hc : ((univ : Finset M) \ {f,g}).card = 2 := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,H.pairs,card_pair hfg]
  obtain ⟨e,h,heh,hrest⟩ := card_eq_two.mp hc
  have he : e ∈ (univ : Finset M) \ {f,g} := by rw [hrest]; simp
  have hh : h ∈ (univ : Finset M) \ {f,g} := by rw [hrest]; simp
  have hef : e ≠ f := by intro hn; exact (mem_sdiff.mp he).2 (by simp [hn])
  have heg : e ≠ g := by intro hn; exact (mem_sdiff.mp he).2 (by simp [hn])
  have hhf : h ≠ f := by intro hn; exact (mem_sdiff.mp hh).2 (by simp [hn])
  have hhg : h ≠ g := by intro hn; exact (mem_sdiff.mp hh).2 (by simp [hn])
  apply R.signatures_equal_or_disjoint e h f g hfg heh hrest (H.floor f g hfg)
  intro b c heither
  rcases heither with he | hh
  · exact H.cross e f g hef heg hfg b c he
  · exact H.cross h f g hhf hhg hfg b c hh

/-- Three distinct matching edges cannot share one remaining occurrence:
their endpoint signs in the fourth supporting partition would be pairwise
opposite. -/
theorem no_three_share {f g h : M} (hfg : f ≠ g) (hfh : f ≠ h) (hgh : g ≠ h)
    (b c d : Bool) (hfg' : R.index (f,b) = R.index (g,c))
    (hfh' : R.index (f,b) = R.index (h,d)) : False := by
  classical
  have hc : ((univ : Finset M) \ {f,g,h}).card = 1 := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,H.pairs]
    simp [hfg,hfh,hgh]
  obtain ⟨e,he⟩ := card_pos.mp (show 0 < ((univ : Finset M) \ {f,g,h}).card by omega)
  have hef : e ≠ f := by intro hn; exact (mem_sdiff.mp he).2 (by simp [hn])
  have heg : e ≠ g := by intro hn; exact (mem_sdiff.mp he).2 (by simp [hn])
  have heh : e ≠ h := by intro hn; exact (mem_sdiff.mp he).2 (by simp [hn])
  have opposite (u v w : M) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
      (heu : e ≠ u) (hev : e ≠ v) (hew : e ≠ w) (a b : Bool)
      (hab : R.index (u,a) = R.index (v,b)) :
      (a == P.sign e u) ≠ (b == P.sign e v) := by
    apply R.shared_free_separated e w u v a b huv hew
      (four_rest H.pairs hew heu hev huw.symm hvw.symm huv)
      H.saturated (H.floor u v huv) _ hab
    intro a b hcross
    rcases hcross with he | hw
    · exact H.cross e u v heu hev huv a b he
    · exact H.cross w u v huw.symm hvw.symm huv a b hw
  have h1 := opposite f g h hfg hfh hgh hef heg heh b c hfg'
  have h2 := opposite f h g hfh hfg hgh.symm hef heh heg b d hfh'
  have h3 := opposite g h f hgh hfg.symm hfh.symm heg heh hef c d (hfg'.symm.trans hfh')
  cases (b == P.sign e f) <;> cases (c == P.sign e g) <;>
    cases (d == P.sign e h) <;> simp_all <;> tauto

theorem signature_fibre_le_two (J : Finset ι) :
    (univ.filter (fun f => R.signature f = J)).card ≤ 2 := by
  classical
  by_contra hn
  obtain ⟨f,g,h,hf,hg,hh,hfg,hfh,hgh⟩ := two_lt_card_iff.mp (show
    2 < (univ.filter (fun f => R.signature f = J)).card by omega)
  have hfgJ : R.signature f = R.signature g :=
    (mem_filter.mp hf).2.trans (mem_filter.mp hg).2.symm
  have hfhJ : R.signature f = R.signature h :=
    (mem_filter.mp hf).2.trans (mem_filter.mp hh).2.symm
  have choose_label (g : M) (he : R.signature f = R.signature g) :
      ∃ c : Bool, R.index (f,true) = R.index (g,c) := by
    have hm : R.index (f,true) ∈ R.signature g := by rw [← he]; simp [signature]
    rcases mem_insert.mp hm with hm | hm
    · exact ⟨true,hm⟩
    · exact ⟨false,mem_singleton.mp hm⟩
  obtain ⟨c,hc⟩ := choose_label g hfgJ
  obtain ⟨d,hd⟩ := choose_label h hfhJ
  exact R.no_three_share H hfg hfh hgh true c d hc hd

/-- The four two-element signatures form exactly two classes of size two. -/
theorem two_groups :
    (univ.image R.signature).card = 2 ∧
    ∀ J ∈ univ.image R.signature, (univ.filter (fun f => R.signature f = J)).card = 2 := by
  classical
  let S := univ.image R.signature
  have hdis : (S : Set (Finset ι)).PairwiseDisjoint (fun J => J) := by
    intro J hJ K hK hne
    obtain ⟨f,_,rfl⟩ := mem_image.mp hJ
    obtain ⟨g,_,rfl⟩ := mem_image.mp hK
    have hfg : f ≠ g := by intro he; subst g; exact hne rfl
    exact (R.signatures_compatible H f g hfg).resolve_left hne
  have hsub : S.biUnion (fun J => J) ⊆ P.free := by
    intro i hi
    obtain ⟨J,hJ,hi⟩ := mem_biUnion.mp hi
    obtain ⟨f,_,rfl⟩ := mem_image.mp hJ
    rcases mem_insert.mp hi with hi | hi
    · exact hi ▸ R.mem _
    · exact mem_singleton.mp hi ▸ R.mem _
  have hc := card_le_card hsub
  rw [card_biUnion hdis] at hc
  have hs : ∑ J ∈ S, J.card = S.card*2 := by
    calc
      _ = ∑ _J ∈ S, 2 := sum_congr rfl (by
        intro J hJ
        obtain ⟨f,_,rfl⟩ := mem_image.mp hJ
        exact R.signature_card H.saturated f)
      _ = _ := by simp
  rw [hs] at hc
  have hfree := P.free_card
  rw [H.pairs,H.occurrences] at hfree
  have hS : S.card ≤ 2 := by omega
  have hp := card_eq_sum_card_image R.signature (univ : Finset M)
  have hf := sum_le_sum (s := S) (fun J _ => R.signature_fibre_le_two H J)
  simp only [sum_const,Nat.nsmul_eq_mul] at hf
  change Fintype.card M = ∑ J ∈ S, (univ.filter (fun f => R.signature f = J)).card at hp
  rw [H.pairs] at hp
  have hS2 : S.card = 2 := by omega
  refine ⟨hS2,?_⟩
  intro J hJ
  have hJle := R.signature_fibre_le_two H J
  have he := sum_erase_add (s := S)
    (f := fun K => (univ.filter (fun f => R.signature f = K)).card) hJ
  have hsle := sum_le_sum (s := S.erase J) (fun K _ => R.signature_fibre_le_two H K)
  simp only [sum_const,Nat.nsmul_eq_mul] at hsle
  have hJS : J ∈ S := hJ
  have hErase : (S.erase J).card = 1 := by rw [card_erase_of_mem hJS,hS2]
  rw [hErase] at hsle
  omega

end Remaining
end CoveringDesigns.SaturatedMatching
