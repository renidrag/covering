import CoveringDesigns.SaturatedMatching.Separation
import CoveringDesigns.SaturatedMatching.Four
import CoveringDesigns.SaturatedMatching.Five
import CoveringDesigns.C62_32_3

/-! The ordinary covering adapter constructs its matching and supporting
occurrences from actual saturated pairs. Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset TwoKMinusTwo C20_11_3
variable {α M : Type*} [Fintype α] [DecidableEq α] [Fintype M] [DecidableEq M]
variable {C : Family α}

theorem family_degree (C : Family α) (x : α) :
    indexedDegree (fun A : C => A.val) x = degree C x := by
  classical
  simp only [indexedDegree,degree,star,card_eq_sum_ones,sum_filter]
  exact sum_coe_sort C (fun A => if x ∈ A then (1 : ℕ) else 0)

namespace Split
variable {p q : α} {k : ℕ} (s : Split C p q k)
include s
theorem endpoints_left : p ∈ s.left ∧ q ∈ s.left := by
  constructor <;> apply inter_subset_left <;> rw [s.inter_eq] <;> simp
theorem endpoints_right : p ∈ s.right ∧ q ∈ s.right := by
  constructor <;> apply inter_subset_right <;> rw [s.inter_eq] <;> simp
theorem complementary (x : α) (hp : x ≠ p) (hq : x ≠ q) :
    x ∈ s.left ↔ x ∉ s.right := by
  have hu : x ∈ s.left ∪ s.right := by rw [s.union_eq]; simp
  have hi : x ∉ s.left ∩ s.right := by rw [s.inter_eq]; simp [hp,hq]
  simp only [mem_union,mem_inter] at hu hi
  tauto
end Split

/-- A complete matching of saturated edges, with chosen actual splits.
The covering adapter derives every field; this is not a final cover premise. -/
structure CoverMatching (C : Family α) where
  point : M × Bool → α
  injective : Function.Injective point
  split : ∀ e, Split C (point (e,true)) (point (e,false)) 31
  complete : ∀ x y, x ≠ y → degree (star C x) y = 2 →
    ∃ e, {x,y} = ({point (e,true),point (e,false)} : Finset α)

namespace CoverMatching
variable (T : CoverMatching (M := M) C)

theorem point_ne {e f : M} (hef : e ≠ f) (b c : Bool) :
    T.point (e,b) ≠ T.point (f,c) := by
  intro he
  exact hef (congrArg Prod.fst (T.injective he))

def block (z : M × Bool) : C :=
  if z.2 then ⟨(T.split z.1).left,(T.split z.1).left_mem⟩
    else ⟨(T.split z.1).right,(T.split z.1).right_mem⟩

theorem own_mem (e : M) (a b : Bool) : T.point (e,b) ∈ (T.block (e,a)).val := by
  cases a <;> cases b <;>
    first | exact (T.split e).endpoints_right.1 | exact (T.split e).endpoints_right.2
          | exact (T.split e).endpoints_left.1 | exact (T.split e).endpoints_left.2

theorem block_injective (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) : Function.Injective T.block := by
  rintro ⟨e,a⟩ ⟨f,b⟩ he
  have heval := congrArg Subtype.val he
  by_cases hef : e = f
  · subst f
    cases a <;> cases b <;> simp only [block,Bool.false_eq_true,↓reduceIte] at heval ⊢
    · exact ((T.split e).distinct heval.symm).elim
    · exact ((T.split e).distinct heval).elim
  · have hp := T.own_mem f b true
    have hq := T.own_mem f b false
    rw [← heval] at hp hq
    exact ((T.split e).no_shared_support hv hC hb
      ⟨T.point_ne (Ne.symm hef) _ _,T.point_ne (Ne.symm hef) _ _⟩
      ⟨T.point_ne (Ne.symm hef) _ _,T.point_ne (Ne.symm hef) _ _⟩
      (T.split f).endpoints (T.split f).saturated (T.block (e,a)).property
      (T.own_mem e a true) (T.own_mem e a false) ⟨hp,hq⟩).elim

noncomputable def pattern (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) :
    Pattern (M := M) (fun A : C => A.val) := by
  classical
  refine ⟨T.point,T.injective,T.block,T.block_injective hv hC hb,
    (fun e f => decide (T.point (f,true) ∈ (T.split e).left)),?_,?_⟩
  · intro e a f b
    by_cases hef : e = f
    · subst f; simp only [true_or,eq_self_iff_true,iff_true]; exact T.own_mem e a b
    have hx := (T.split e).separates hv hC hb
      ⟨T.point_ne (Ne.symm hef) _ _,T.point_ne (Ne.symm hef) _ _⟩
      ⟨T.point_ne (Ne.symm hef) _ _,T.point_ne (Ne.symm hef) _ _⟩
      (T.split f).endpoints (T.split f).saturated
    have comp (b : Bool) := (T.split e).complementary (T.point (f,b))
      (T.point_ne (Ne.symm hef) _ _) (T.point_ne (Ne.symm hef) _ _)
    have hop : T.point (f,false) ∈ (T.split e).left ↔
        T.point (f,true) ∉ (T.split e).left := by
      rcases hx with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · have ht := (mem_sdiff.mp h1).1
        have hf := (mem_sdiff.mp h2).1
        have hn := (comp false).not.mpr (not_not.mpr hf)
        simp [ht,hn]
      · have ht := (mem_sdiff.mp h1).1
        have hf := (mem_sdiff.mp h2).1
        have hn := (comp true).not.mpr (not_not.mpr ht)
        simp [hf,hn]
    cases a <;> cases b <;> simp only [block,↓reduceIte,hef,false_or] <;>
      simp_all <;> tauto
  · intro x hx e
    exact (T.split e).complementary x (hx e true) (hx e false)

theorem endpoint_degree (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13) (f : M) (b : Bool) :
    indexedDegree (fun A : C => A.val) (T.point (f,b)) = 6 := by
  obtain ⟨_,_,_,hp,hq,_⟩ := (T.split f).surviving_counts
    (by simpa using hv) (Or.inl rfl) hC hb
  rw [family_degree]
  cases b <;> assumption

theorem pair_floor (hv : Fintype.card α = 60)
    (hC : IsCover C 31 3) (hb : C.card = 13)
    (x : α) (f : M) (b : Bool)
    (hx : x ≠ T.point (f,b)) (hy : x ≠ T.point (f,!b)) :
    3 ≤ indexedSubsetDegree (fun A : C => A.val) {x,T.point (f,b)} := by
  rw [family_pair]
  have hl := pair_ge_two (k := 31) (by simpa using hv) (by omega) hC hx
  have hs : degree (star C (T.point (f,!b))) (T.point (f,b)) = 2 := by
    cases b
    · exact (T.split f).saturated
    · simpa only [Bool.not_true,pair_degree_comm] using (T.split f).saturated
  have hn : degree (star C x) (T.point (f,b)) ≠ 2 := by
    intro he
    apply hy
    have hne : T.point (f,!b) ≠ T.point (f,b) := by
      cases b
      · exact (T.split f).endpoints
      · exact (T.split f).endpoints.symm
    exact saturated_matching hv hC hb hne hs x hx (by rwa [pair_degree_comm])
  omega

end CoverMatching
end CoveringDesigns.SaturatedMatching
