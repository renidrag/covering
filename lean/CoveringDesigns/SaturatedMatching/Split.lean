import CoveringDesigns.SaturatedMatching.Geometry
import CoveringDesigns.SaturatedMatching.Counting

/-! Actual saturated splits, their exact loss budget, and refined capacity.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset C20_11_3 TwoKMinusTwo
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Two actual supporting blocks of a distinct saturated point pair. -/
structure Split (C : Family α) (p q : α) (k : ℕ) where
  left : Finset α
  right : Finset α
  distinct : left ≠ right
  left_mem : left ∈ C
  right_mem : right ∈ C
  left_card : left.card = k
  right_card : right.card = k
  endpoints : p ≠ q
  star_eq : star (star C p) q = {left,right}
  union_eq : left ∪ right = univ
  inter_eq : left ∩ right = {p,q}

namespace Split
variable {C : Family α} {p q : α} {k : ℕ}

theorem exists_of_saturated (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hpq : p ≠ q) (hs : degree (star C p) q = 2) :
    Nonempty (Split C p q k) := by
  obtain ⟨B,hBC,D,hDC,hBD,hstar,hunion,hinter⟩ :=
    TwoKMinusTwo.saturated_pair_blocks hv hk hC hpq hs
  exact ⟨⟨B,D,hBD,hBC,hDC,hC.1 B hBC,hC.1 D hDC,hpq,hstar,hunion,hinter⟩⟩

variable (s : Split C p q k)
def X : Finset α := s.left \ {p,q}
def Y : Finset α := s.right \ {p,q}
def P (_s : Split C p q k) : Family α := onlyBlocks C p q
def Q (_s : Split C p q k) : Family α := onlyBlocks C q p
def N (_s : Split C p q k) : Family α := neitherBlocks C p q
def weight (A : Finset α) : ℕ := (s.X ∩ A).card * (s.Y ∩ A).card
def cap (_s : Split C p q k) (A : Finset α) : ℕ :=
  if p ∈ A ∧ q ∈ A then 0 else
    if p ∈ A ∨ q ∈ A then capacity (k-1) else capacity k
def crosses : Finset (α × α) :=
  (s.X ×ˢ s.Y).filter (fun z => degree (star C z.1) z.2 = 2)
def loss : ℕ := ∑ A ∈ C, (s.cap A - s.weight A)
def excess : ℕ := ∑ z ∈ s.X ×ˢ s.Y, (degree (star C z.1) z.2 - 3)

include s

theorem saturated : degree (star C p) q = 2 := by
  change (star (star C p) q).card = 2
  rw [s.star_eq, card_pair s.distinct]

theorem geometry :
    Disjoint s.X s.Y ∧ s.X.card = k-2 ∧ s.Y.card = k-2 ∧
      s.X ∪ s.Y = univ \ {p,q} :=
  TwoKMinusTwo.saturated_residual_geometry s.endpoints s.left_card s.right_card
    s.union_eq s.inter_eq

theorem weight_left : s.weight s.left = 0 := by
  have he : s.Y ∩ s.left = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact residual_not_mem_other (B := s.right) (D := s.left)
      (by simpa [inter_comm] using s.inter_eq) (mem_inter.mp hz).1 (mem_inter.mp hz).2
  simp [weight,he]

theorem weight_right : s.weight s.right = 0 := by
  have he : s.X ∩ s.right = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact residual_not_mem_other s.inter_eq (mem_inter.mp hz).1 (mem_inter.mp hz).2
  simp [weight,he]

theorem cap_P {A : Finset α} (hA : A ∈ s.P) : s.cap A = capacity (k-1) := by
  obtain ⟨_,hp,hq⟩ := mem_onlyBlocks.mp hA
  simp [cap,hp,hq]
theorem cap_Q {A : Finset α} (hA : A ∈ s.Q) : s.cap A = capacity (k-1) := by
  obtain ⟨_,hq,hp⟩ := mem_onlyBlocks.mp hA
  simp [cap,hp,hq]
theorem cap_N {A : Finset α} (hA : A ∈ s.N) : s.cap A = capacity k := by
  obtain ⟨_,hp,hq⟩ := mem_neitherBlocks.mp hA
  simp [cap,hp,hq]

theorem capacity_bound (hC : IsCover C k 3) : ∀ A ∈ C, s.weight A ≤ s.cap A := by
  intro A hA
  by_cases hp : p ∈ A <;> by_cases hq : q ∈ A
  · have ha : A ∈ star (star C p) q := by simp [star,hA,hp,hq]
    rw [s.star_eq] at ha
    rcases mem_insert.mp ha with he | he
    · subst A; rw [s.weight_left]; exact Nat.zero_le _
    · have he := mem_singleton.mp he
      subst A; rw [s.weight_right]; exact Nat.zero_le _
  · simp only [cap,hp,hq,and_false,ite_false,or_false,ite_true]
    exact endpoint_trace_capacity s.geometry.1 s.geometry.2.2.2 (hC.1 A hA) hp hq
  · simp only [cap,hp,hq,false_and,ite_false,false_or,ite_true]
    exact endpoint_trace_capacity s.geometry.1
      (by simpa [pair_comm] using s.geometry.2.2.2) (hC.1 A hA) hq hp
  · simp only [cap,hp,hq,false_and,ite_false,false_or]
    exact cross_capacity _ _ _ s.geometry.1 (hC.1 A hA).le

theorem cap_sum :
    ∑ A ∈ C, s.cap A =
      capacity (k-1)*(s.P.card+s.Q.card) + capacity k*s.N.card := by
  rw [endpoint_sum_partition]
  have hp : ∑ A ∈ onlyBlocks C p q, s.cap A = s.P.card*capacity (k-1) := by
    calc
      _ = ∑ _A ∈ s.P, capacity (k-1) := sum_congr rfl (fun _ ha => s.cap_P ha)
      _ = _ := by simp
  have hq : ∑ A ∈ onlyBlocks C q p, s.cap A = s.Q.card*capacity (k-1) := by
    calc
      _ = ∑ _A ∈ s.Q, capacity (k-1) := sum_congr rfl (fun _ ha => s.cap_Q ha)
      _ = _ := by simp
  have hn : ∑ A ∈ neitherBlocks C p q, s.cap A = s.N.card*capacity k := by
    calc
      _ = ∑ _A ∈ s.N, capacity k := sum_congr rfl (fun _ ha => s.cap_N ha)
      _ = _ := by simp
  have hz : ∑ A ∈ star (star C p) q, s.cap A = 0 := by
    apply sum_eq_zero
    intro A hA
    obtain ⟨hAp,hqA⟩ := mem_filter.mp hA
    have hpA := (mem_filter.mp hAp).2
    simp [cap,hpA,hqA]
  rw [hp,hq,hn,hz]
  ring

theorem parts : C.card = s.P.card+s.Q.card+s.N.card+2 := by
  have hh := endpoint_card_partition C p q
  rw [s.saturated] at hh
  exact hh

theorem assignment (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) :
    ∃ f : α × α → Finset α × Finset α,
      (∀ z ∈ s.crosses, (f z).1 ∈ s.P ∧ (f z).2 ∈ s.Q ∧
        (f z).1 ∩ (f z).2 = {z.1,z.2}) ∧
      Set.InjOn f s.crosses :=
  exists_cross_assignment hv hk hC s.star_eq s.inter_eq s.geometry.1

theorem cross_card_le (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) : s.crosses.card ≤ s.P.card*s.Q.card := by
  obtain ⟨f,hf,hi⟩ := s.assignment hv hk hC
  exact assignment_card_le f (fun z hz => ⟨(hf z hz).1,(hf z hz).2.1⟩) hi

theorem exact_budget (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) :
    s.loss+s.excess+3*(k-2)*(k-2) =
      capacity (k-1)*(s.P.card+s.Q.card)+capacity k*s.N.card+s.crosses.card := by
  have hh := cross_loss_identity (s.X ×ˢ s.Y) C
    (fun z => degree (star C z.1) z.2) s.weight s.cap
    (by
      intro z hz
      obtain ⟨hx,hy⟩ := mem_product.mp hz
      exact pair_ge_two hv hk hC (by
        intro he
        exact disjoint_left.mp s.geometry.1 hx (he.symm ▸ hy)))
    (s.capacity_bound hC)
    (by rw [sum_product]; exact cross_pair_degree_sum C s.X s.Y)
  rw [s.cap_sum,card_product,s.geometry.2.1,s.geometry.2.2.1] at hh
  simpa only [loss,excess,crosses,Nat.mul_assoc] using hh

theorem loss_at (hC : IsCover C k 3) {A : Finset α} (hA : A ∈ C) :
    s.cap A - s.weight A ≤ s.loss :=
  single_le_sum (f := fun A => s.cap A - s.weight A) (fun _ _ => Nat.zero_le _) hA

/-- No second mate forces two remaining endpoint incidences at every
residual point. This is derived before refined assignment capacity. -/
theorem residual_degree_two (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3)
    (hnotsecond : ∀ z, z ≠ p → z ≠ q → degree (star C q) z ≠ 2) :
    ∀ z, z ≠ p → z ≠ q → 2 ≤ degree s.Q z := by
  intro z hzp hzq
  have hz : z ∈ s.X ∪ s.Y := by rw [s.geometry.2.2.2]; simp [hzp,hzq]
  have hf := pair_ge_two hv hk hC hzq.symm
  have hn := hnotsecond z hzp hzq
  rcases mem_union.mp hz with hzX | hzY
  · have he := residual_pair_eq s.star_eq (mem_sdiff.mp hzX).1
      (residual_not_mem_other s.inter_eq hzX)
    change degree (star C q) z = degree s.Q z + 1 at he
    omega
  · have he := residual_pair_eq
      (B := s.right) (D := s.left) (by simpa [pair_comm] using s.star_eq)
      (mem_sdiff.mp hzY).1
      (residual_not_mem_other (B := s.right) (D := s.left)
        (by simpa [inter_comm] using s.inter_eq) hzY)
    change degree (star C q) z = degree s.Q z + 1 at he
    omega

/-- Refined shared-block inequality from actual covering geometry; the
assignment and its fibre injectivity are derived, not hypothesised. -/
theorem refined_bound (hv : Fintype.card α = 2*k-2) (hk : 3 ≤ k)
    (hC : IsCover C k 3) (hQ : 2 ≤ s.Q.card)
    (hnotsecond : ∀ z, z ≠ p → z ≠ q → degree (star C q) z ≠ 2) :
    (k-3)*s.crosses.card ≤ s.P.card*((s.Q.card-2)*(k-1)) := by
  obtain ⟨f,hf,hi⟩ := s.assignment hv hk hC
  apply assignment_total_bound f (fun A E => (A ∩ E).card) hk hQ
    (fun z hz => ⟨(hf z hz).1,(hf z hz).2.1⟩) hi
  · intro A hA
    obtain ⟨hAC,hpA,hqA⟩ := mem_onlyBlocks.mp hA
    exact SaturatedMatching.shared_intersection_sum (hC.1 A hAC) hpA hqA
      (s.residual_degree_two hv hk hC hnotsecond)
  · intro z hz
    rw [(hf z hz).2.2]
    apply card_pair
    obtain ⟨hx,hy⟩ := mem_product.mp (mem_filter.mp hz).1
    intro he
    exact disjoint_left.mp s.geometry.1 hx (he.symm ▸ hy)
  · intro A hA E hE
    obtain ⟨hAC,hpA,_⟩ := mem_onlyBlocks.mp hA
    exact intersection_le_pred (hC.1 A hAC) hpA (mem_onlyBlocks.mp hE).2.2

/-- Exchange the endpoint labels while retaining both actual occurrences. -/
def swap : Split C q p k where
  left := s.left
  right := s.right
  distinct := s.distinct
  left_mem := s.left_mem
  right_mem := s.right_mem
  left_card := s.left_card
  right_card := s.right_card
  endpoints := s.endpoints.symm
  star_eq := by simpa [star,filter_filter,and_comm] using s.star_eq
  union_eq := s.union_eq
  inter_eq := by simpa [pair_comm] using s.inter_eq

@[simp] theorem swap_P : s.swap.P = s.Q := rfl
@[simp] theorem swap_Q : s.swap.Q = s.P := rfl
@[simp] theorem swap_crosses : s.swap.crosses = s.crosses := by
  simp only [crosses,X,Y,swap,pair_comm q p]

end Split
end CoveringDesigns.SaturatedMatching
