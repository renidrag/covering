import CoveringDesigns.Foundations.SupportDifferences

/-! A finite-incidence obstruction with doubled paired supports. The column
margin counts actual points, not representatives of equal supports. Occurrence
indices need not have distinct block values. No matrix assumptions are used. -/
namespace CoveringDesigns.SupportObstruction
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Separate the common high support from its two exceptional indices. -/
theorem exceptional_count (H G S : Finset ι) {a b : ι}
    (ha : H \ G = {a}) (hb : G \ H = {b}) :
    (S ∩ H).card + (S ∩ G).card =
      2 * (S ∩ H ∩ G).card + (if a ∈ S then 1 else 0) +
        (if b ∈ S then 1 else 0) := by
  have h1 := card_sdiff_add_card_inter (S ∩ H) G
  have h2 := card_sdiff_add_card_inter (S ∩ G) H
  have he1 : (S ∩ H) \ G = S ∩ {a} := by
    rw [← ha]; ext i; simp only [mem_sdiff,mem_inter]; tauto
  have he2 : (S ∩ G) \ H = S ∩ {b} := by
    rw [← hb]; ext i; simp only [mem_sdiff,mem_inter]; tauto
  have he3 : S ∩ G ∩ H = S ∩ H ∩ G := by
    ext i; simp only [mem_inter]; tauto
  rw [he1] at h1
  rw [he2,he3] at h2
  by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S <;>
    simp [haS,hbS] at h1 h2 ⊢ <;> omega

/-- Five doubled supports and six single supports with column margin ten
force two different paired classes whose intersection misses the high support.
The doubling is essential: a column counts both distinct points in each pair. -/
theorem paired_support_obstruction (H G : Finset ι)
    (P : Fin 5 → Finset ι) (Q : Fin 6 → Finset ι)
    (hc : Fintype.card ι = 11)
    (hH : H.card = 7) (hG : G.card = 7) (hHG : (H ∩ G).card = 6)
    (hP : ∀ i, (P i).card = 6)
    (hPH : ∀ i, (P i ∩ H).card = 3) (hPG : ∀ i, (P i ∩ G).card = 3)
    (hPQ : ∀ i, (Q i ∩ H).card + (Q i ∩ G).card = 9)
    (hcross : ∀ i j, i ≠ j → (P i ∩ P j).card = 3)
    (hcol : ∀ c, (if c ∈ H then 1 else 0) + (if c ∈ G then 1 else 0) +
      2 * (∑ i, if c ∈ P i then 1 else 0) + (∑ i, if c ∈ Q i then 1 else 0) = 10) :
    ∃ i j, i ≠ j ∧ H ∩ P i ∩ P j = ∅ := by
  obtain ⟨a,b,hab,ha,hb,haH,haG,hbG,hbH,hA⟩ :=
    single_differences H G 6 hH hG hHG
  have hag (i : Fin 5) : a ∈ P i ↔ b ∈ P i := by
    have he := exceptional_count H G (P i) ha hb
    rw [hPH,hPG] at he
    by_cases haP : a ∈ P i <;> by_cases hbP : b ∈ P i <;> simp_all <;> omega
  have hq (i : Fin 6) :
      (if a ∈ Q i then 1 else 0) + (if b ∈ Q i then 1 else 0) = (1 : ℕ) := by
    have he := exceptional_count H G (Q i) ha hb
    rw [hPQ] at he
    by_cases haQ : a ∈ Q i <;> by_cases hbQ : b ∈ Q i <;> simp_all <;> omega
  have hp : (∑ i : Fin 5, if a ∈ P i then 1 else 0) = (3 : ℕ) := by
    have hca := hcol a
    have hcb := hcol b
    simp only [haH,haG,hbG,hbH,ite_true,ite_false] at hca hcb
    have he : (∑ i : Fin 5, if b ∈ P i then 1 else 0) =
        ∑ i : Fin 5, if a ∈ P i then 1 else 0 := by simp_rw [hag]
    have hqs : (∑ i : Fin 6, if a ∈ Q i then 1 else 0) +
        (∑ i : Fin 6, if b ∈ Q i then 1 else 0) = (6 : ℕ) := by
      rw [← sum_add_distrib]; simp_rw [hq]; simp
    omega
  let Z := univ.filter (fun i : Fin 5 => a ∉ P i)
  have hz : Z.card = 2 := by
    have hh := card_filter_add_card_filter_not (s := (univ : Finset (Fin 5)))
      (fun i => a ∈ P i)
    have hp' : (univ.filter (fun i : Fin 5 => a ∈ P i)).card = 3 := by
      simpa only [card_eq_sum_ones,sum_filter] using hp
    simp only [card_univ,Fintype.card_fin] at hh
    change _ + Z.card = 5 at hh
    omega
  obtain ⟨i,j,hij,hZ⟩ := card_eq_two.mp hz
  have hiZ : i ∈ Z := by rw [hZ]; simp
  have hjZ : j ∈ Z := by rw [hZ]; simp
  have hi : a ∉ P i := (mem_filter.mp hiZ).2
  have hj : a ∉ P j := (mem_filter.mp hjZ).2
  have hib : b ∉ P i := fun h => hi ((hag i).mpr h)
  have hjb : b ∉ P j := fun h => hj ((hag j).mpr h)
  have hsub : P i ∪ P j ⊆ univ \ {a,b} := by
    intro c hc
    have hca : c ≠ a := by intro he; subst c; simp_all
    have hcb : c ≠ b := by intro he; subst c; simp_all
    simp [hca,hcb]
  have hunion : P i ∪ P j = univ \ {a,b} := by
    apply eq_of_subset_of_card_le hsub
    have he := card_union_add_card_inter (P i) (P j)
    rw [hP,hP,hcross i j hij] at he
    rw [card_sdiff_of_subset (subset_univ _),card_univ,hc,card_pair hab]
    omega
  refine ⟨i,j,hij,empty_of_intersection_bound univ {a,b} H (P i) (P j)
    (subset_univ _) hunion ?_⟩
  rw [inter_comm H (P i),inter_comm H (P j),hPH,hPH,hA,hH]

end CoveringDesigns.SupportObstruction
