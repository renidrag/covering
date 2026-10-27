import CoveringDesigns.PairEquality.Groups

/-! Füredi's augmented-independence argument, in the original coordinate space. -/

namespace CoveringDesigns.PairEquality.Internal
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem augmented_bound {q : ℕ} (hq : 0 < q)
    {H G : Finset (Finset I)}
    (hsize : ∀ E ∈ H, E.card = q+1)
    (hgsize : ∀ C ∈ G, C.card = q)
    (hdisj : ∀ C ∈ G, ∀ D ∈ G, C ≠ D → Disjoint C D)
    (htrans : ∀ E ∈ H, ∀ C ∈ G, (E ∩ C).card = 1)
    (hli : LinearIndependent ℝ (fun E : H => indicator E.val))
    (hk : G.card < q+1) : H.card + G.card ≤ Fintype.card I := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let v : H ⊕ G → I → ℝ := Sum.elim (fun E => indicator E.val) (fun C => indicator C.val)
  have hi : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hr (S : Finset I) :
        (∑ E : H, c (.inl E) * ((S ∩ E.val).card : ℝ)) +
        (∑ C : G, c (.inr C) * ((S ∩ C.val).card : ℝ)) = 0 := by
      have he := congrArg (fun z : I → ℝ => ∑ x ∈ S, z x) hc
      simp only [sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,sum_const_zero] at he
      rw [sum_comm] at he
      have ht (i : H ⊕ G) : (∑ x ∈ S, c i * v i x) =
          c i * ((S ∩ Sum.elim Subtype.val Subtype.val i).card : ℝ) := by
        rw [← mul_sum]
        cases i <;> simp [v,indicator, ← sum_filter,filter_mem_eq_inter]
      simp_rw [ht] at he
      simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using he
    let B := ∑ E : H, c (.inl E)
    let A := ∑ C : G, c (.inr C)
    have hC (C : G) : B + (q : ℝ) * c (.inr C) = 0 := by
      have he := hr C.val
      have ht (E : H) : (C.val ∩ E.val).card = 1 := by
        rw [inter_comm]
        exact htrans E.val E.property C.val C.property
      have hd (D : G) : (C.val ∩ D.val).card = if D = C then q else 0 := by
        by_cases he : D = C
        · subst D
          simp [hgsize C.val C.property]
        · rw [ite_eq_right he,disjoint_iff_inter_eq_empty.mp
            (hdisj C.val C.property D.val D.property
              (fun h => he (Subtype.ext h.symm))),card_empty]
      simp_rw [ht,hd] at he
      simpa [B,mul_comm,mul_ite] using he
    have hu : (q+1 : ℝ)*B + (q : ℝ)*A = 0 := by
      have he := hr univ
      simp only [univ_inter] at he
      simp_rw [hsize _ (Subtype.mem _),hgsize _ (Subtype.mem _)] at he
      simp only [Nat.cast_add,Nat.cast_one,← sum_mul] at he
      simpa only [B,A,mul_comm] using he
    have hg : (G.card : ℝ)*B + (q : ℝ)*A = 0 := by
      have he := congrArg (fun f : G → ℝ => ∑ C, f C) (funext hC)
      simpa [sum_add_distrib,← mul_sum,A] using he
    have hB : B = 0 := by
      have hkr : (G.card : ℝ) < q+1 := by exact_mod_cast hk
      nlinarith
    have hzero (C : G) : c (.inr C) = 0 := by
      have he := hC C
      rw [hB,zero_add] at he
      exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hqR)
    have he : (∑ E : H, c (.inl E) • indicator E.val) = 0 := by
      simpa [v,Fintype.sum_sum_type,hzero] using hc
    cases j with
    | inl E => exact Fintype.linearIndependent_iff.mp hli _ he E
    | inr C => exact hzero C
  simpa using hi.fintype_card_le_finrank

/-- One minimum-degree coordinate forces minimum degree at every coordinate.
The proof adds group indicators to the independent support indicators. -/
theorem degree_q_everywhere {q : ℕ} (hq : 0 < q)
    {H : Finset (Finset I)} {w : Finset I → ℝ} (h : PositiveUnitLoads q H w)
    (hli : LinearIndependent ℝ (fun E : H => indicator E.val))
    (hex : ∃ x, degree H x = q) : H.card = q*q ∧ ∀ x, degree H x = q := by
  classical
  let Q := univ.filter (fun x => degree H x = q)
  let G := Q.image (starGroup H)
  have hQ : Q.Nonempty := by
    obtain ⟨x,hx⟩ := hex
    exact ⟨x,by simp [Q,hx]⟩
  have hG : G.Nonempty := hQ.image _
  have hgsize (C : Finset I) (hC : C ∈ G) : C.card = q := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hC
    exact starGroup_card h (mem_filter.mp hx).2
  have hdisj (C : Finset I) (hC : C ∈ G) (D : Finset I) (hD : D ∈ G)
      (hCD : C ≠ D) : Disjoint C D := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hC
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hD
    exact (starGroup_equal_or_disjoint h (mem_filter.mp hx).2
      (mem_filter.mp hy).2).resolve_left hCD
  have htrans (E : Finset I) (hE : E ∈ H) (C : Finset I) (hC : C ∈ G) :
      (E ∩ C).card = 1 := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hC
    exact starGroup_transversal h (mem_filter.mp hx).2 hE
  have hQcard : Q.card ≤ q * G.card := by
    have hsub : Q ⊆ G.biUnion id := by
      intro x hx
      exact mem_biUnion.mpr ⟨starGroup H x,mem_image.mpr ⟨x,hx,rfl⟩,by simp⟩
    calc
      Q.card ≤ (G.biUnion id).card := card_le_card hsub
      _ ≤ ∑ C ∈ G, C.card := card_biUnion_le
      _ = q * G.card := by rw [sum_congr rfl hgsize]; simp [Nat.mul_comm]
  have hupper : H.card ≤ Fintype.card I := by simpa using hli.fintype_card_le_finrank
  let d := Fintype.card I - H.card
  have hd : H.card + d = Fintype.card I := Nat.add_sub_of_le hupper
  have hdq : d ≤ q := by have := h.card_lower; rw [h.coordinates] at hd; nlinarith
  have hcount : (q+1) * Fintype.card I ≤ (q+1) * H.card + Q.card := by
    have hl (x : I) : q+1 ≤ degree H x + if x ∈ Q then 1 else 0 := by
      have hx := h.degree_lower x
      by_cases he : degree H x = q <;> simp [Q,he] <;> omega
    have he := sum_le_sum (fun x (_ : x ∈ (univ : Finset I)) => hl x)
    simp only [sum_add_distrib] at he
    rw [degree_sum, sum_congr rfl h.uniform] at he
    simpa [← sum_filter,Nat.mul_comm,Nat.add_mul,Nat.mul_add] using he
  have hmin : d+1 ≤ G.card := by
    have hp : 0 < G.card := card_pos.mpr hG
    by_contra hn
    have hg : G.card ≤ d := by omega
    nlinarith
  have hdeq : d = q := by
    by_contra hn
    have hlt : d < q := by omega
    obtain ⟨K,hK,hKcard⟩ := exists_subset_card_eq hmin
    have he := augmented_bound hq h.uniform (fun C hC => hgsize C (hK hC))
      (fun C hC D hD => hdisj C (hK hC) D (hK hD))
      (fun E hE C hC => htrans E hE C (hK hC)) hli (by omega : K.card < q+1)
    omega
  have hH : H.card = q*q := by rw [hdeq,h.coordinates] at hd; nlinarith
  refine ⟨hH,?_⟩
  have hs : (∑ _x : I, q) = ∑ x, degree H x := by
    rw [degree_sum,sum_congr rfl h.uniform]
    simp [hH,h.coordinates]
    ring
  intro x
  exact ((sum_eq_sum_iff_of_le (fun x _ => h.degree_lower x)).mp hs x (mem_univ _)).symm

end CoveringDesigns.PairEquality.Internal
