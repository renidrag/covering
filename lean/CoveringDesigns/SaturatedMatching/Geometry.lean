import CoveringDesigns.TwoKMinusTwo.Capacity
import CoveringDesigns.C20_11_3.SaturatedLoss

/-! Forced actual supporting blocks and shared incidence.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset C20_11_3
variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
variable {C : Family α} {p q z : α} {B D : Finset α}

/-- A named containing block has an actual complementary partner. -/
theorem saturated_partner_of_mem (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hpq : p ≠ q)
    (hsat : degree (star C p) q = 2)
    (hBC : B ∈ C) (hpB : p ∈ B) (hqB : q ∈ B) :
    ∃ D ∈ C, D ≠ B ∧ B ∪ D = univ ∧ B ∩ D = {p,q} := by
  obtain ⟨U,hUC,V,hVC,hUV,hstar,hunion,hinter⟩ :=
    TwoKMinusTwo.saturated_pair_blocks hv hk hC hpq hsat
  have hB : B ∈ star (star C p) q :=
    mem_filter.mpr ⟨mem_filter.mpr ⟨hBC,hpB⟩,hqB⟩
  rw [hstar] at hB
  rcases mem_insert.mp hB with hBU | hBV
  · subst U
    exact ⟨V,hVC,Ne.symm hUV,hunion,hinter⟩
  · have hBV : B = V := mem_singleton.mp hBV
    subst V
    exact ⟨U,hUC,hUV,by simpa [union_comm] using hunion,
      by simpa [inter_comm] using hinter⟩

/-- The second saturated partner forces the opposite residual side plus
the new pair, as an actual block of the original family. -/
theorem second_partner_block (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hpq : p ≠ q) (hBC : B ∈ C)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p,q})
    (hz : z ∈ B \ {p,q}) (hsat : degree (star C q) z = 2) :
    (D \ {p,q}) ∪ {q,z} ∈ onlyBlocks C q p := by
  have hzB := (mem_sdiff.mp hz).1
  have hzpair := (mem_sdiff.mp hz).2
  have hzq : z ≠ q := by intro h; exact hzpair (by simp [h])
  have hzp : z ≠ p := by intro h; exact hzpair (by simp [h])
  have hqB : q ∈ B := inter_subset_left (by rw [hinter]; simp)
  obtain ⟨E,hEC,_,hBEunion,hBEinter⟩ :=
    saturated_partner_of_mem hv hk hC (Ne.symm hzq) hsat hBC hqB hzB
  have hE : E = (D \ {p,q}) ∪ {q,z} := by
    rw [other_block_eq_complement hBEunion hBEinter,
      saturated_residual_complement hunion hinter]
  have hqE : q ∈ E := by rw [hE]; simp
  have hpE : p ∉ E := by rw [hE]; simp [hpq, Ne.symm hzp]
  rw [← hE]
  exact mem_onlyBlocks.mpr ⟨hEC,hqE,hpE⟩

/-- The forced block has trace product k-2. -/
theorem second_partner_traces_left (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hpq : p ≠ q) (hBC : B ∈ C) (hDC : D ∈ C)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p,q})
    (hz : z ∈ B \ {p,q}) (hsat : degree (star C q) z = 2) :
    ∃ E ∈ onlyBlocks C q p,
      ((B \ {p,q}) ∩ E).card = 1 ∧ ((D \ {p,q}) ∩ E).card = k-2 := by
  let E := (D \ {p,q}) ∪ {q,z}
  have hEC := second_partner_block hv hk hC hpq hBC hunion hinter hz hsat
  obtain ⟨hdis,_,hD,_⟩ := TwoKMinusTwo.saturated_residual_geometry hpq
    (hC.1 B hBC) (hC.1 D hDC) hunion hinter
  have hleft : (B \ {p,q}) ∩ E = {z} := by
    ext x
    simp only [mem_inter, mem_singleton]
    constructor
    · rintro ⟨hxB,hxE⟩
      rcases mem_union.mp hxE with hxD | hxqz
      · exact (disjoint_left.mp hdis hxB hxD).elim
      · rcases mem_insert.mp hxqz with hxq | hxz
        · subst x; exact ((mem_sdiff.mp hxB).2 (by simp)).elim
        · exact mem_singleton.mp hxz
    · intro he
      subst x
      exact ⟨hz,by simp [E]⟩
  have hright : (D \ {p,q}) ∩ E = D \ {p,q} := inter_eq_left.mpr (subset_union_left)
  exact ⟨E,hEC,by rw [hleft,card_singleton],by rw [hright,hD]⟩

theorem second_partner_trace (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hpq : p ≠ q) (hBC : B ∈ C) (hDC : D ∈ C)
    (hunion : B ∪ D = univ) (hinter : B ∩ D = {p,q})
    (hz : z ∈ (B \ {p,q}) ∪ (D \ {p,q}))
    (hsat : degree (star C q) z = 2) :
    ∃ E ∈ onlyBlocks C q p,
      ((B \ {p,q}) ∩ E).card * ((D \ {p,q}) ∩ E).card = k-2 := by
  rcases mem_union.mp hz with hzB | hzD
  · obtain ⟨E,hE,hl,hr⟩ := second_partner_traces_left hv hk hC hpq hBC hDC
      hunion hinter hzB hsat
    exact ⟨E,hE,by rw [hl,hr,one_mul]⟩
  · obtain ⟨E,hE,hl,hr⟩ := second_partner_traces_left hv hk hC hpq hDC hBC
      (by simpa [union_comm] using hunion) (by simpa [inter_comm] using hinter) hzD hsat
    exact ⟨E,hE,by rw [hl,hr,mul_one]⟩

theorem intersection_le_pred {A E : Finset α} (hA : A.card = k)
    (hp : p ∈ A) (hpE : p ∉ E) : (A ∩ E).card ≤ k-1 := by
  have hsub : A ∩ E ⊆ A.erase p := by
    intro z hz
    obtain ⟨hzA,hzE⟩ := mem_inter.mp hz
    exact mem_erase.mpr ⟨by intro he; subst z; exact hpE hzE,hzA⟩
  have hh := card_le_card hsub
  rwa [card_erase_of_mem hp,hA] at hh

theorem shared_intersection_sum {A : Finset α}
    (hA : A.card = k) (hpA : p ∈ A) (hqA : q ∉ A)
    (hpoint : ∀ z, z ≠ p → z ≠ q → 2 ≤ degree (onlyBlocks C q p) z) :
    2*(k-1) ≤ ∑ E ∈ onlyBlocks C q p, (A ∩ E).card := by
  rw [intersection_sum]
  have hc : (A.erase p).card = k-1 := by rw [card_erase_of_mem hpA,hA]
  calc
    2*(k-1) = ∑ z ∈ A.erase p, 2 := by simp [hc,Nat.mul_comm]
    _ ≤ ∑ z ∈ A.erase p, degree (onlyBlocks C q p) z := by
      apply sum_le_sum
      intro z hz
      obtain ⟨hzp,hzA⟩ := mem_erase.mp hz
      exact hpoint z hzp (by intro h; subst z; exact hqA hzA)
    _ ≤ ∑ z ∈ A, degree (onlyBlocks C q p) z :=
      sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (by intros; exact Nat.zero_le _)

end CoveringDesigns.SaturatedMatching
