import CoveringDesigns.MulticoverLargeDefect
import CoveringDesigns.Foundations.StandardAxioms

/-! Full public contracts, expanded occurrence coverage and transitive axiom guards. -/
namespace CoveringDesigns.MulticoverLargeDefect
open Finset HigherIncidence MulticoverIncidence LargeDefect
universe u w

#print Multicover.IsCover
#print Multicover.CoverLower
#print MulticoverIncidence.Parameters
#print MulticoverIncidence.SmallerBounds
#print HigherIncidence.coefficient
#print HigherIncidence.defect
#print MulticoverLargeDefect.natExcess
#print LargeDefect.alpha
#print LargeDefect.beta
#print LargeDefect.ratio
#print MulticoverLargeDefect.value
#print MulticoverLargeDefect.bound

-- Selection
#check (natExcess_cast : ∀ {α : Type u} {ι : Type w} [DecidableEq α] [Fintype ι] {B : ι → Finset α} {b : ℕ → ℕ} {s : ℕ}
    (_hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    {X Y : Finset α} (_hX : X.card=s) (_hY : Y.card=s),
  (natExcess B b X Y : ℤ) = excess B b X Y)

#check (natExcess_sum_cast : ∀ {α : Type u} {ι : Type w} [DecidableEq α] [Fintype ι] {B : ι → Finset α} {b : ℕ → ℕ} {s : ℕ}
    (_hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    {X : Finset α} (_hX : X.card=s) (S : Finset (Finset α))
    (_hS : ∀ Y ∈ S, Y.card=s),
  ((∑ Y ∈ S, natExcess B b X Y : ℕ) : ℤ) = ∑ Y ∈ S, excess B b X Y)

#check (natExcess_degree : ∀ {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {b : ℕ → ℕ} {k s : ℕ}
    (_hu : Multicover.Uniform B k)
    (_hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    {X : Finset α} (_hX : X.card=s),
  ((∑ Y ∈ subsets α s, natExcess B b X Y : ℕ) : ℤ) =
      ((indexedSubsetDegree B X : ℤ)-b s)*((k.choose s : ℤ)-1)+
        defect (Fintype.card α) k s b)

#check (independent_card_le : ∀ {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {b : ℕ → ℕ} {s a : ℕ}
    (_hac : (a : ℤ) ≤ coefficient s b s)
    (_hc : ∀ j < s, 0 ≤ coefficient s b j)
    (_hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (S : Finset (Finset α)) (_hS : ∀ X ∈ S, X.card=s)
    (_hdeg : ∀ X ∈ S, ∑ Y ∈ S, natExcess B b X Y < a),
  S.card ≤ Fintype.card ι)

#check (potential_bound : ∀ {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {b : ℕ → ℕ} {s a : ℕ}
    (_ha : 0 < a) (_hac : (a : ℤ) ≤ coefficient s b s)
    (_hc : ∀ j < s, 0 ≤ coefficient s b j)
    (_hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z),
  (∑ X ∈ subsets α s,
      CaroTuza.f a ((∑ Y ∈ subsets α s, natExcess B b X Y : ℕ) : ℝ)) ≤ Fintype.card ι)

#check (selection_bound : ∀ {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {b : ℕ → ℕ} {k s : ℕ}
    (_hu : Multicover.Uniform B k) (_hK : 0 < k.choose s)
    (_hc : ∀ j < s, 0 ≤ coefficient s b j)
    (_hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (_ha : 1 ≤ coefficient s b s)
    (_had : coefficient s b s ≤ defect (Fintype.card α) k s b),
  alpha (coefficient s b s) (defect (Fintype.card α) k s b) *
        ((subsets α s).filter (indexedSubsetDegree B · = b s)).card +
      beta (k.choose s) (coefficient s b s) (defect (Fintype.card α) k s b) *
        ((subsets α s).filter (indexedSubsetDegree B · = b s+1)).card ≤ Fintype.card ι)

-- Counting
#check (incidence_bound : ∀ {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {k s m : ℕ}
    (_hu : Multicover.Uniform B k)
    (_hb : ∀ X : Finset α, X.card=s → m ≤ indexedSubsetDegree B X),
  (Fintype.card α).choose s*m ≤ k.choose s*Fintype.card ι)

#check (two_level_bound : ∀ {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {k s m : ℕ} {A D : ℝ}
    (_hu : Multicover.Uniform B k) (_hD : 0 ≤ D) (_hAD : 2*D ≤ A)
    (_hb : ∀ X : Finset α, X.card=s → m ≤ indexedSubsetDegree B X)
    (_hr : A*((subsets α s).filter (indexedSubsetDegree B · = m)).card +
      D*((subsets α s).filter (indexedSubsetDegree B · = m+1)).card ≤ Fintype.card ι),
  ((Fintype.card α).choose s : ℝ)*((m : ℝ)*(A-D)+A) ≤
      (Fintype.card ι : ℝ)*((k.choose s : ℝ)*(A-D)+1))

#check (two_level_ceiling : ∀ {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {k s m : ℕ} {A D : ℝ}
    (_hu : Multicover.Uniform B k) (_hD : 0 ≤ D) (_hAD : 2*D ≤ A)
    (_hb : ∀ X : Finset α, X.card=s → m ≤ indexedSubsetDegree B X)
    (_hr : A*((subsets α s).filter (indexedSubsetDegree B · = m)).card +
      D*((subsets α s).filter (indexedSubsetDegree B · = m+1)).card ≤ Fintype.card ι),
  ⌈((Fintype.card α).choose s : ℝ)*((m : ℝ)*(A-D)+A) /
      ((k.choose s : ℝ)*(A-D)+1)⌉₊ ≤ Fintype.card ι)

-- LowerBound
#check (bound_denominator_pos : ∀ {v k s : ℕ} {b : ℕ → ℕ}
    (_hK : 0 < k.choose s) (_ha : 0 ≤ coefficient s b s) (_hd : 0 ≤ defect v k s b),
  0 < (k.choose s : ℝ) *
      (alpha (coefficient s b s) (defect v k s b) -
        beta (k.choose s) (coefficient s b s) (defect v k s b)) + 1)

#check (bound_le_iff : ∀ {v k s n : ℕ} {b : ℕ → ℕ}
    (_hK : 0 < k.choose s) (_ha : 0 ≤ coefficient s b s) (_hd : 0 ≤ defect v k s b),
  bound v k s b ≤ n ↔
      (v.choose s : ℝ) * ((b s : ℝ) *
        (alpha (coefficient s b s) (defect v k s b) -
          beta (k.choose s) (coefficient s b s) (defect v k s b)) +
        alpha (coefficient s b s) (defect v k s b)) ≤
      (n : ℝ) * ((k.choose s : ℝ) *
        (alpha (coefficient s b s) (defect v k s b) -
          beta (k.choose s) (coefficient s b s) (defect v k s b)) + 1))

#check (value_nonneg : ∀ {v k s : ℕ} {b : ℕ → ℕ}
    (_hK : 0 < k.choose s) (_ha : 0 ≤ coefficient s b s) (_hd : 0 ≤ defect v k s b),
  0 ≤ value v k s b)

#check (lower_bound_of_multiplicities : ∀ {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {k s : ℕ} {b : ℕ → ℕ}
    (_hu : Multicover.Uniform B k)
    (_hc : ∀ j < s, 0 ≤ coefficient s b j)
    (_hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (_hmK : b s < k.choose s) (_ham : coefficient s b s < b s)
    (_ha : 1 ≤ coefficient s b s)
    (_had : coefficient s b s ≤ defect (Fintype.card α) k s b),
  bound (Fintype.card α) k s b ≤ Fintype.card ι)

#check (lower_bound : ∀ {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {lam v k t s : ℕ} {b : ℕ → ℕ}
    (_hp : MulticoverIncidence.Parameters lam v k t s b)
    (_hb : MulticoverIncidence.SmallerBounds.{u,w} lam v k t s b)
    (_hn : Fintype.card α=v) (_h : Multicover.IsCover B k t lam)
    (_hmK : b s < k.choose s) (_ha : 1 ≤ coefficient s b s)
    (_had : coefficient s b s ≤ defect v k s b),
  bound v k s b ≤ Fintype.card ι)

#check (lower_bound_inequality : ∀ {α : Type u} {ι : Type w} [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α} {lam v k t s : ℕ} {b : ℕ → ℕ}
    (_hp : MulticoverIncidence.Parameters lam v k t s b)
    (_hb : MulticoverIncidence.SmallerBounds.{u,w} lam v k t s b)
    (_hn : Fintype.card α=v) (_h : Multicover.IsCover B k t lam)
    (_hmK : b s < k.choose s) (_ha : 1 ≤ coefficient s b s)
    (_had : coefficient s b s ≤ defect v k s b),
  (v.choose s : ℝ) * ((b s : ℝ) *
      (alpha (coefficient s b s) (defect v k s b) -
        beta (k.choose s) (coefficient s b s) (defect v k s b)) +
      alpha (coefficient s b s) (defect v k s b)) ≤
    (Fintype.card ι : ℝ) * ((k.choose s : ℝ) *
      (alpha (coefficient s b s) (defect v k s b) -
        beta (k.choose s) (coefficient s b s) (defect v k s b)) + 1))

-- Family
#check (family_hypotheses_iff : ∀ {v k t s : ℕ} {b : ℕ → ℕ},
  (MulticoverIncidence.Parameters 1 v k t s b ∧
      MulticoverIncidence.SmallerBounds.{u,u} 1 v k t s b) ↔
    (HigherIncidence.Parameters v k t s b ∧ HigherIncidence.SmallerBounds.{u} v k t s b))

#check (value_eq_ordinary : ∀ (v k s : ℕ) (b : ℕ → ℕ),
  value v k s b = LargeDefect.value v k s b)

#check (bound_eq_ordinary : ∀ (v k s : ℕ) (b : ℕ → ℕ),
  bound v k s b = LargeDefect.bound v k s b)

#check (family_lower_bound : ∀ {α : Type u} [Fintype α] [DecidableEq α]
    {C : Family α} {v k t s : ℕ} {b : ℕ → ℕ}
    (_hp : HigherIncidence.Parameters v k t s b)
    (_hb : HigherIncidence.SmallerBounds.{u} v k t s b)
    (_hn : Fintype.card α=v) (_h : CoveringDesigns.IsCover C k t)
    (_hmK : b s < k.choose s) (_ha : 1 ≤ coefficient s b s)
    (_had : coefficient s b s ≤ defect v k s b),
  LargeDefect.bound v k s b ≤ C.card)

-- Examples
namespace Examples
#check (seeds5_values : seeds5 1=3 ∧ seeds5 2=2)

#check (parameters5 : MulticoverIncidence.Parameters 2 5 4 2 1 seeds5)

#check (smaller_bounds5 : MulticoverIncidence.SmallerBounds.{u,w} 2 5 4 2 1 seeds5)

#check (data5 : coefficient 1 seeds5 1=1 ∧ defect 5 4 1 seeds5=1 ∧
    (5 : ℕ).choose 1=5 ∧ (4 : ℕ).choose 1=4 ∧
    Multicover.bound 2 5 4 2=4)

#check (value5 : MulticoverLargeDefect.value 5 4 1 seeds5=35/11)

#check (bound5 : MulticoverLargeDefect.bound 5 4 1 seeds5=4)

#check (covering5 : ∀ {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α}
    (_hn : Fintype.card α=5) (_h : Multicover.IsCover B 4 2 2),
  4 ≤ Fintype.card ι)

#check (seeds10_values : seeds10 2=10 ∧ seeds10 3=5 ∧ seeds10 4=2)

#check (parameters10 : MulticoverIncidence.Parameters 2 10 6 4 2 seeds10)

#check (smaller_bounds10 : MulticoverIncidence.SmallerBounds.{u,w} 2 10 6 4 2 seeds10)

#check (data10 : coefficient 2 seeds10 2=2 ∧ defect 10 6 2 seeds10=4 ∧
    (10 : ℕ).choose 2=45 ∧ (6 : ℕ).choose 2=15 ∧
    Multicover.bound 2 10 6 4=30)

#check (value10 : MulticoverLargeDefect.value 10 6 2 seeds10=4293/164)

#check (bound10 : MulticoverLargeDefect.bound 10 6 2 seeds10=27)

#check (covering10 : ∀ {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α}
    (_hn : Fintype.card α=10) (_h : Multicover.IsCover B 6 4 2),
  27 ≤ Fintype.card ι)

#check (seeds11_values : seeds11 2=14 ∧ seeds11 3=6 ∧ seeds11 4=2)

#check (parameters11 : MulticoverIncidence.Parameters 2 11 6 4 2 seeds11)

#check (smaller_bounds11 : MulticoverIncidence.SmallerBounds.{u,w} 2 11 6 4 2 seeds11)

#check (data11 : coefficient 2 seeds11 2=4 ∧ defect 11 6 2 seeds11=16 ∧
    (11 : ℕ).choose 2=55 ∧ (6 : ℕ).choose 2=15 ∧
    Multicover.bound 2 11 6 4=52)

#check (value11 : MulticoverLargeDefect.value 11 6 2 seeds11=62425/2104)

#check (bound11 : MulticoverLargeDefect.bound 11 6 2 seeds11=30)

#check (covering11 : ∀ {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α}
    (_hn : Fintype.card α=11) (_h : Multicover.IsCover B 6 4 2),
  30 ≤ Fintype.card ι)

#check (counting_branches : defect 10 6 2 seeds10+2 ≤ ((6 : ℕ).choose 2 : ℤ) ∧
    ((6 : ℕ).choose 2 : ℤ) ≤ defect 11 6 2 seeds11+1)

#check (coefficient_boundary : ∀ {K : ℕ} {a d : ℝ} (_hK : 0 < K)
    (_ha : 0 ≤ a) (_hd : 0 ≤ d) (_he : d+2=(K : ℝ)),
  2*beta K a d=alpha a d)

#check (adjacent_fallback : ∀ {K : ℕ} {a d : ℝ} (_hK : 0 < K)
    (_ha : 0 ≤ a) (_hd : 0 ≤ d) (_he : d+1=(K : ℝ)),
  alpha a d < 2*beta K a d ∧ alpha a d*K=(a+1)/2)

#check (empty_selection : ∀ {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α}
    {b : ℕ → ℕ} {s a : ℕ} (_hac : (a : ℤ) ≤ coefficient s b s)
    (_hc : ∀ j < s, 0 ≤ coefficient s b j)
    (_hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z),
  (∅ : Finset (Finset α)).card ≤ Fintype.card ι)

#check (empty_low_classes : ∀ {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι] {B : ι → Finset α}
    {b : ℕ → ℕ} {k s : ℕ} (_hu : Multicover.Uniform B k) (_hK : 0 < k.choose s)
    (_hc : ∀ j < s, 0 ≤ coefficient s b j)
    (_hb : ∀ Z : Finset α, s ≤ Z.card → Z.card ≤ 2*s → b Z.card ≤ indexedSubsetDegree B Z)
    (_ha : 1 ≤ coefficient s b s)
    (_had : coefficient s b s ≤ defect (Fintype.card α) k s b)
    (_h0 : ((subsets α s).filter (indexedSubsetDegree B · = b s))=∅)
    (_h1 : ((subsets α s).filter (indexedSubsetDegree B · = b s+1))=∅),
  (0 : ℝ) ≤ Fintype.card ι)

#check (boundary_link : ∀ {α : Type u} {ι : Type w} [DecidableEq α] [Fintype ι]
    {B : ι → Finset α} {k s lam : ℕ} (_h : Multicover.IsCover B k (2*s) lam)
    {X : Finset α} (_hx : X.card=2*s),
  Multicover.IsCover (Multicover.subsetLink B X) (k-2*s) 0 lam ∧
      lam ≤ Fintype.card {i // X ⊆ B i})

#check (repeated_columns : repeatedBlocks 0 = repeatedBlocks 1)

#check (repeated_cover : Multicover.IsCover repeatedBlocks 2 2 2)

#check (repeated_excess : natExcess repeatedBlocks (fun _ => 1) {0} {1}=2)

#check (repeated_gram : ∀ (X Y : subsets (Fin 2) 1),
  (incidence repeatedBlocks (subsets (Fin 2) 1) *
      (incidence repeatedBlocks (subsets (Fin 2) 1)).transpose) X Y = 3)

end Examples

end CoveringDesigns.MulticoverLargeDefect

namespace CoveringDesigns.AuditMulticoverLargeDefect
open Finset HigherIncidence LargeDefect
universe u w

/-- The full source contract, expanding all occurrence-indexed covering conditions,
including those in the universally quantified residual hypotheses. -/
theorem lower_bound_explicit {α : Type u} {ι : Type w}
    [Fintype α] [DecidableEq α] [Fintype ι]
    {B : ι → Finset α} {lam v k t s : ℕ} {b : ℕ → ℕ}
    (hlam : 1 ≤ lam) (hs : 1 ≤ s) (hst : 2*s ≤ t) (htk : t < k) (hkv : k < v)
    (hpos : ∀ i, s ≤ i → i ≤ 2*s → 0 < b i)
    (hseed : Multicover.bound lam (v-2*s) (k-2*s) (t-2*s) ≤ b (2*s))
    (hstep : ∀ i, s ≤ i → i < 2*s →
      Schoenheim.ceilDiv ((v-i)*b (i+1)) (k-i) ≤ b i)
    (hcoeff : ∀ j, j ≤ s → 0 ≤ coefficient s b j)
    (hsmall : ∀ i, s ≤ i → i ≤ 2*s →
      ∀ {β : Type u} {κ : Type w} [Fintype β] [DecidableEq β] [Fintype κ]
        {D : κ → Finset β}, Fintype.card β=v-i →
        (∀ z, (D z).card=k-i) →
        (∀ T : Finset β, T.card=t-i →
          lam ≤ ((univ : Finset κ).filter (fun z => T ⊆ D z)).card) →
        b i ≤ Fintype.card κ)
    (hn : Fintype.card α=v) (hu : ∀ z, (B z).card=k)
    (hc : ∀ T : Finset α, T.card=t →
      lam ≤ ((univ : Finset ι).filter (fun z => T ⊆ B z)).card)
    (hmK : b s < k.choose s) (ha : 1 ≤ coefficient s b s)
    (had : coefficient s b s ≤ defect v k s b) :
    let A : ℝ := ((coefficient s b s : ℝ)+1)/(2*((defect v k s b : ℝ)+1))
    let D : ℝ := ((coefficient s b s : ℝ)+1)/(2*((defect v k s b : ℝ)+k.choose s))
    0 < (k.choose s : ℝ)*(A-D)+1 ∧
      (v.choose s : ℝ)*((b s : ℝ)*(A-D)+A) ≤
        (Fintype.card ι : ℝ)*((k.choose s : ℝ)*(A-D)+1) ∧
      ⌈(v.choose s : ℝ)*((b s : ℝ)*(A-D)+A)/
        ((k.choose s : ℝ)*(A-D)+1)⌉₊ ≤ Fintype.card ι := by
  have hp : MulticoverIncidence.Parameters lam v k t s b :=
    ⟨hlam, hs, hst, htk, hkv, hpos, hseed, hstep, hcoeff⟩
  have hb : MulticoverIncidence.SmallerBounds.{u,w} lam v k t s b := by
    intro i hlo hhi β κ _ _ _ D hcard hcover
    exact hsmall i hlo hhi hcard hcover.1 hcover.2
  exact ⟨MulticoverLargeDefect.bound_denominator_pos (by omega) (by omega) (by omega),
    MulticoverLargeDefect.lower_bound_inequality hp hb hn ⟨hu, hc⟩ hmK ha had,
    MulticoverLargeDefect.lower_bound hp hb hn ⟨hu, hc⟩ hmK ha had⟩

end CoveringDesigns.AuditMulticoverLargeDefect

#guard_standard_axioms
  CoveringDesigns.MulticoverLargeDefect.natExcess_cast
  CoveringDesigns.MulticoverLargeDefect.natExcess_sum_cast
  CoveringDesigns.MulticoverLargeDefect.natExcess_degree
  CoveringDesigns.MulticoverLargeDefect.independent_card_le
  CoveringDesigns.MulticoverLargeDefect.potential_bound
  CoveringDesigns.MulticoverLargeDefect.selection_bound
  CoveringDesigns.MulticoverLargeDefect.incidence_bound
  CoveringDesigns.MulticoverLargeDefect.two_level_bound
  CoveringDesigns.MulticoverLargeDefect.two_level_ceiling
  CoveringDesigns.MulticoverLargeDefect.bound_denominator_pos
  CoveringDesigns.MulticoverLargeDefect.bound_le_iff
  CoveringDesigns.MulticoverLargeDefect.value_nonneg
  CoveringDesigns.MulticoverLargeDefect.lower_bound_of_multiplicities
  CoveringDesigns.MulticoverLargeDefect.lower_bound
  CoveringDesigns.MulticoverLargeDefect.lower_bound_inequality
  CoveringDesigns.MulticoverLargeDefect.family_hypotheses_iff
  CoveringDesigns.MulticoverLargeDefect.value_eq_ordinary
  CoveringDesigns.MulticoverLargeDefect.bound_eq_ordinary
  CoveringDesigns.MulticoverLargeDefect.family_lower_bound
  CoveringDesigns.MulticoverLargeDefect.Examples.seeds5_values
  CoveringDesigns.MulticoverLargeDefect.Examples.parameters5
  CoveringDesigns.MulticoverLargeDefect.Examples.smaller_bounds5
  CoveringDesigns.MulticoverLargeDefect.Examples.data5
  CoveringDesigns.MulticoverLargeDefect.Examples.value5
  CoveringDesigns.MulticoverLargeDefect.Examples.bound5
  CoveringDesigns.MulticoverLargeDefect.Examples.covering5
  CoveringDesigns.MulticoverLargeDefect.Examples.seeds10_values
  CoveringDesigns.MulticoverLargeDefect.Examples.parameters10
  CoveringDesigns.MulticoverLargeDefect.Examples.smaller_bounds10
  CoveringDesigns.MulticoverLargeDefect.Examples.data10
  CoveringDesigns.MulticoverLargeDefect.Examples.value10
  CoveringDesigns.MulticoverLargeDefect.Examples.bound10
  CoveringDesigns.MulticoverLargeDefect.Examples.covering10
  CoveringDesigns.MulticoverLargeDefect.Examples.seeds11_values
  CoveringDesigns.MulticoverLargeDefect.Examples.parameters11
  CoveringDesigns.MulticoverLargeDefect.Examples.smaller_bounds11
  CoveringDesigns.MulticoverLargeDefect.Examples.data11
  CoveringDesigns.MulticoverLargeDefect.Examples.value11
  CoveringDesigns.MulticoverLargeDefect.Examples.bound11
  CoveringDesigns.MulticoverLargeDefect.Examples.covering11
  CoveringDesigns.MulticoverLargeDefect.Examples.counting_branches
  CoveringDesigns.MulticoverLargeDefect.Examples.coefficient_boundary
  CoveringDesigns.MulticoverLargeDefect.Examples.adjacent_fallback
  CoveringDesigns.MulticoverLargeDefect.Examples.empty_selection
  CoveringDesigns.MulticoverLargeDefect.Examples.empty_low_classes
  CoveringDesigns.MulticoverLargeDefect.Examples.boundary_link
  CoveringDesigns.MulticoverLargeDefect.Examples.repeated_columns
  CoveringDesigns.MulticoverLargeDefect.Examples.repeated_cover
  CoveringDesigns.MulticoverLargeDefect.Examples.repeated_excess
  CoveringDesigns.MulticoverLargeDefect.Examples.repeated_gram
  CoveringDesigns.AuditMulticoverLargeDefect.lower_bound_explicit

#print axioms CoveringDesigns.MulticoverLargeDefect.natExcess_cast
#print axioms CoveringDesigns.MulticoverLargeDefect.natExcess_sum_cast
#print axioms CoveringDesigns.MulticoverLargeDefect.natExcess_degree
#print axioms CoveringDesigns.MulticoverLargeDefect.independent_card_le
#print axioms CoveringDesigns.MulticoverLargeDefect.potential_bound
#print axioms CoveringDesigns.MulticoverLargeDefect.selection_bound
#print axioms CoveringDesigns.MulticoverLargeDefect.incidence_bound
#print axioms CoveringDesigns.MulticoverLargeDefect.two_level_bound
#print axioms CoveringDesigns.MulticoverLargeDefect.two_level_ceiling
#print axioms CoveringDesigns.MulticoverLargeDefect.bound_denominator_pos
#print axioms CoveringDesigns.MulticoverLargeDefect.bound_le_iff
#print axioms CoveringDesigns.MulticoverLargeDefect.value_nonneg
#print axioms CoveringDesigns.MulticoverLargeDefect.lower_bound_of_multiplicities
#print axioms CoveringDesigns.MulticoverLargeDefect.lower_bound
#print axioms CoveringDesigns.MulticoverLargeDefect.lower_bound_inequality
#print axioms CoveringDesigns.MulticoverLargeDefect.family_hypotheses_iff
#print axioms CoveringDesigns.MulticoverLargeDefect.value_eq_ordinary
#print axioms CoveringDesigns.MulticoverLargeDefect.bound_eq_ordinary
#print axioms CoveringDesigns.MulticoverLargeDefect.family_lower_bound
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.seeds5_values
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.parameters5
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.smaller_bounds5
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.data5
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.value5
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.bound5
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.covering5
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.seeds10_values
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.parameters10
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.smaller_bounds10
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.data10
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.value10
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.bound10
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.covering10
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.seeds11_values
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.parameters11
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.smaller_bounds11
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.data11
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.value11
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.bound11
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.covering11
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.counting_branches
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.coefficient_boundary
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.adjacent_fallback
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.empty_selection
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.empty_low_classes
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.boundary_link
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.repeated_columns
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.repeated_cover
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.repeated_excess
#print axioms CoveringDesigns.MulticoverLargeDefect.Examples.repeated_gram
#print axioms CoveringDesigns.AuditMulticoverLargeDefect.lower_bound_explicit
