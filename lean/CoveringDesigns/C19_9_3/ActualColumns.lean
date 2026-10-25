import CoveringDesigns.C19_9_3.ActualAffine
import CoveringDesigns.C19_9_3.ColumnForms

/-! The remaining columns, expressed on one actual affine configuration. -/
namespace CoveringDesigns.C19_9_3
open Finset SevenBlock
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

def AffineConfiguration.planeColumn {B : I → Finset V} (F : AffineConfiguration B) (x : V) :=
  univ.filter fun p => x ∈ B (F.planes p)

def AffineConfiguration.emptyColumn {B : I → Finset V} (F : AffineConfiguration B) (x : V) :=
  univ.filter fun b => x ∈ B (F.empty b)

private noncomputable def AffineConfiguration.occurrenceEquiv {B : I → Finset V}
    (F : AffineConfiguration B) : PlanePosition ⊕ Bool ≃ I :=
  Equiv.ofBijective (Sum.elim F.planes F.empty) ⟨by
    intro u v he
    cases u with
    | inl p => cases v with
      | inl q => exact congrArg Sum.inl (F.planes.injective he)
      | inr b => exact False.elim (F.disjoint p b he)
    | inr b => cases v with
      | inl p => exact False.elim (F.disjoint p b he.symm)
      | inr c => exact congrArg Sum.inr (F.empty.injective he),by
    intro i
    rcases F.partition i with ⟨p,rfl⟩ | ⟨b,rfl⟩
    · exact ⟨Sum.inl p,rfl⟩
    · exact ⟨Sum.inr b,rfl⟩⟩

private theorem AffineConfiguration.column_size {B : I → Finset V} (F : AffineConfiguration B) (x : V) :
    (F.planeColumn x).card + (F.emptyColumn x).card = indexedDegree B x := by
  have he := Fintype.sum_equiv F.occurrenceEquiv
    (fun s => if x ∈ B (F.occurrenceEquiv s) then 1 else 0)
    (fun i => if x ∈ B i then 1 else 0) (by intro s; rfl)
  rw [Fintype.sum_sum_type] at he
  have hleft (p : PlanePosition) : F.occurrenceEquiv (Sum.inl p) = F.planes p := rfl
  have hright (b : Bool) : F.occurrenceEquiv (Sum.inr b) = F.empty b := rfl
  simpa only [AffineConfiguration.planeColumn,AffineConfiguration.emptyColumn,
    card_eq_sum_ones,sum_filter,indexedDegree,hleft,hright] using he

private theorem AffineConfiguration.column_value {B : I → Finset V} (F : AffineConfiguration B)
    (m : ↥(minimumPoints B)) (x : V) :
    columnValue (F.planeColumn x) (F.points m) = indexedSubsetDegree B {m.val,x} := by
  let emb : Fin 7 ↪ I :=
    ⟨fun n => F.planes (n,orientation n (F.points m)),by
      intro n k he
      exact congrArg Prod.fst (F.planes.injective he)⟩
  have heq : (columnDirections (F.planeColumn x) (F.points m)).map emb =
      univ.filter fun i => ({m.val,x} : Finset V) ⊆ B i := by
    ext i
    constructor
    · intro hi
      obtain ⟨n,hn,rfl⟩ := mem_map.mp hi
      have hmx : m.val ∈ B (F.planes (n,orientation n (F.points m))) :=
        (F.incidence _ m).mpr (by simp [affinePlane])
      have hxx : x ∈ B (F.planes (n,orientation n (F.points m))) := by
        simpa only [columnDirections,AffineConfiguration.planeColumn,mem_filter,mem_univ,true_and] using hn
      exact mem_filter.mpr ⟨mem_univ _,insert_subset_iff.mpr ⟨hmx,singleton_subset_iff.mpr hxx⟩⟩
    · intro hi
      have hmx : m.val ∈ B i := (mem_filter.mp hi).2 (by simp)
      have hxx : x ∈ B i := (mem_filter.mp hi).2 (by simp)
      rcases F.partition i with ⟨⟨n,b⟩,rfl⟩ | ⟨b,rfl⟩
      · have hb : orientation n (F.points m) = b := by
          simpa only [affinePlane,mem_filter,mem_univ,true_and] using (F.incidence (n,b) m).mp hmx
        refine mem_map.mpr ⟨n,?_,?_⟩
        · simpa only [columnDirections,AffineConfiguration.planeColumn,mem_filter,mem_univ,true_and,hb] using hxx
        · change F.planes (n,orientation n (F.points m)) = F.planes (n,b)
          rw [hb]
      · exact False.elim (F.avoidance b m hmx)
  change (columnDirections (F.planeColumn x) (F.points m)).card = _
  rw [← card_map (f := emb),heq]
  rfl

private theorem AffineConfiguration.column_meets_lines {B : I → Finset V}
    (F : AffineConfiguration B) (h : Multicover.IsCover B 9 3 1)
    (x : V) (hx : x ∉ minimumPoints B) (a : Fin 8) (l : Fin 7) :
    (columnDirections (F.planeColumn x) a ∩ line l).Nonempty := by
  obtain ⟨b,hab,hline⟩ := affine_root_all_lines a l
  let m := F.points.symm a
  let n := F.points.symm b
  have hmn : m.val ≠ n.val := fun he => hab (F.points.symm.injective (Subtype.ext he))
  have hmx : m.val ≠ x := fun he => hx (he ▸ m.property)
  have hnx : n.val ≠ x := fun he => hx (he ▸ n.property)
  obtain ⟨i,hi⟩ := (Multicover.covers_one_iff B 3).mp h.2 {m.val,n.val,x}
    (by simp [hmn,hmx,hnx])
  have hm : m.val ∈ B i := hi (by simp)
  have hn : n.val ∈ B i := hi (by simp)
  have hxx : x ∈ B i := hi (by simp)
  rcases F.partition i with ⟨⟨k,c⟩,rfl⟩ | ⟨c,rfl⟩
  · have hma : orientation k a = c := by
      simpa only [affinePlane,mem_filter,mem_univ,true_and,m,Equiv.apply_symm_apply] using (F.incidence _ m).mp hm
    have hnb : orientation k b = c := by
      simpa only [affinePlane,mem_filter,mem_univ,true_and,n,Equiv.apply_symm_apply] using (F.incidence _ n).mp hn
    refine ⟨k,mem_inter.mpr ⟨?_,?_⟩⟩
    · simpa only [columnDirections,AffineConfiguration.planeColumn,mem_filter,mem_univ,true_and,hma] using hxx
    · rw [← hline]
      exact mem_filter.mpr ⟨mem_univ _,hma.trans hnb.symm⟩
  · exact False.elim (F.avoidance c m hm)

private theorem three_transversal_is_line : ∀ S ∈ (univ : Finset (Fin 7)).powersetCard 3,
    (∀ l : Fin 7, (S ∩ line l).Nonempty) → ∃ l, S = line l := by
  decide +kernel

/-- Every actual nonminimum column has precisely one of the three reviewed
forms. The local Fano premises come from actual parent triple coverage. -/
theorem actual_column_forms {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (F : AffineConfiguration B) (x : V) (hx : x ∉ minimumPoints B) :
    ((F.emptyColumn x).card = 2 ∧ ∃ l, F.planeColumn x = completeDirections (line l)) ∨
    ((F.emptyColumn x).card = 1 ∧ ∃ l n b, n ∉ line l ∧
      F.planeColumn x = insert (n,b) (completeDirections (line l))) ∨
    ((F.emptyColumn x).card = 0 ∧ ∃ D, D.card = 4 ∧ (∃ l, line l ⊆ D) ∧
      F.planeColumn x = completeDirections D) := by
  apply column_forms
  · exact (card_le_card (filter_subset _ _)).trans_eq (by simp)
  · rw [F.column_size,nonminimum_degree hv h hi x hx]
  · intro a
    let m := F.points.symm a
    have hmx : m.val ≠ x := fun he => hx (he ▸ m.property)
    rw [← F.points.apply_symm_apply a,F.column_value]
    exact ⟨pair_floor hv h (card_pair hmx),minimum_pair_le_four hv h m.val x
      ((mem_minimumPoints B m.val).mp m.property) hmx⟩
  · intro a ha
    exact three_transversal_is_line _ (mem_powersetCard_univ.mpr ha) (F.column_meets_lines h x hx a)
  · intro a _
    exact F.column_meets_lines h x hx a

/-- Each affine occurrence contains five nonminimum points. -/
theorem affine_nonminimum_row {B : I → Finset V} (hv : Fintype.card V = 19)
    (h : Multicover.IsCover B 9 3 1) (hi : Fintype.card I = 16)
    (F : AffineConfiguration B) (p : PlanePosition) :
    (B (F.planes p) \ minimumPoints B).card = 5 := by
  obtain ⟨a,ha⟩ := card_pos.mp (show 0 < (affinePlane p).card by rw [affine_plane_card]; decide)
  let m := F.points.symm a
  have hm : m.val ∈ B (F.planes p) := (F.incidence p m).mpr (by simpa only [m,Equiv.apply_symm_apply] using ha)
  have hfour := minimum_trace_four hv h hi (F.planes p) m.val m.property hm
  have hc := card_sdiff_add_card_inter (B (F.planes p)) (minimumPoints B)
  rw [hfour,h.1] at hc
  omega

/-- Each avoiding occurrence contains nine nonminimum points. -/
theorem empty_nonminimum_row {B : I → Finset V} (h : Multicover.Uniform B 9)
    (F : AffineConfiguration B) (b : Bool) :
    (B (F.empty b) \ minimumPoints B).card = 9 := by
  have he : B (F.empty b) \ minimumPoints B = B (F.empty b) := by
    apply sdiff_eq_left.mpr
    apply disjoint_left.mpr
    intro x hx hxM
    exact F.avoidance b ⟨x,hxM⟩ hx
  rw [he,h]

#guard_standard_axioms actual_column_forms affine_nonminimum_row empty_nonminimum_row
end CoveringDesigns.C19_9_3
