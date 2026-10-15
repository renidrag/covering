import CoveringDesigns.C12_6_3.Structural.Templates
import CoveringDesigns.Foundations.StandardAxioms
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/-! Rooted coordinates for the ordinary GPPT core. Only identities of the
single twelve-point Figure 1 template are checked by finite kernel reduction.
No completions or covering families are enumerated. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace CoveringDesigns.C13Structural

open Finset GPPTStructural

/-- Three companions and four pairs of outside points. -/
abbrev TracePoint := Fin 3 ⊕ (Fin 4 × Bool)

/-- The root together with the eleven points remaining after its deletion. -/
abbrev RootedPoint := Option TracePoint

/-- The three perfect matchings on four vertices, with an oriented edge. -/
def half (m : Fin 3) (b : Bool) : Finset (Fin 4) :=
  if b then ![{2, 3}, {1, 3}, {1, 2}] m
  else ![{0, 1}, {0, 2}, {0, 3}] m

def companions : Finset TracePoint := univ.image Sum.inl

def transverse (b : Bool) : Finset TracePoint :=
  univ.image (fun v : Fin 4 => Sum.inr (v, b))

/-- A five-point trace of a full row through the root. -/
def commonTrace (m : Fin 3) (b : Bool) : Finset TracePoint :=
  insert (Sum.inl m) (((half m b).product univ).image Sum.inr)

/-- A six-point full row avoiding the root. -/
def privateTrace (m : Fin 3) (b : Bool) : Finset TracePoint :=
  ((univ.erase m).image Sum.inl) ∪
    ((half m b).image (fun v => Sum.inr (v, false))) ∪
    ((half m (!b)).image (fun v => Sum.inr (v, true)))

def commonTraceFamily : Family TracePoint :=
  univ.image (fun i : Fin 3 × Bool => commonTrace i.1 i.2)

def privateTraceFamily : Family TracePoint :=
  univ.image (fun i : Fin 3 × Bool => privateTrace i.1 i.2)

def liftTrace (S : Finset TracePoint) : Finset RootedPoint :=
  S.image some

def rootedIncidentCore : Family RootedPoint :=
  commonTraceFamily.image (fun S => insert none (liftTrace S))

def rootedPrivateCore : Family RootedPoint :=
  privateTraceFamily.image liftTrace

def rootedCore : Family RootedPoint := rootedIncidentCore ∪ rootedPrivateCore

def rootedSpine (i : Fin 3) : Finset RootedPoint :=
  ![insert none (liftTrace companions), liftTrace (transverse false),
    liftTrace (transverse true)] i

private def encodeRooted : RootedPoint → Fin 12
  | none => 0
  | some (Sum.inl m) => ⟨m.val + 1, by omega⟩
  | some (Sum.inr (v, b)) =>
      if b then ⟨v.val + 8, by omega⟩ else ⟨v.val + 4, by omega⟩

private def decodeRooted (x : Fin 12) : RootedPoint :=
  if h0 : x.val = 0 then none
  else if h1 : x.val < 4 then some (Sum.inl ⟨x.val - 1, by omega⟩)
  else if h2 : x.val < 8 then some (Sum.inr (⟨x.val - 4, by omega⟩, false))
  else some (Sum.inr (⟨x.val - 8, by omega⟩, true))

/-- Identify these coordinates with the point labels of GPPT Figure 1. -/
def rootedLabel : RootedPoint ≃ Fin 12 where
  toFun := encodeRooted
  invFun := decodeRooted
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[simp] theorem rootedLabel_none : rootedLabel none = 0 := rfl

@[simp] theorem rootedLabel_companion (m : Fin 3) :
    rootedLabel (some (Sum.inl m)) = ⟨m.val + 1, by omega⟩ := rfl

@[simp] theorem rootedLabel_spouse (v : Fin 4) (b : Bool) :
    rootedLabel (some (Sum.inr (v, b))) =
      if b then ⟨v.val + 8, by omega⟩ else ⟨v.val + 4, by omega⟩ := rfl

theorem half_card : ∀ m b, (half m b).card = 2 := by decide +kernel

theorem half_complement : ∀ m b, half m (!b) = univ \ half m b := by
  decide +kernel

theorem commonTrace_card : ∀ m b, (commonTrace m b).card = 5 := by
  decide +kernel

theorem privateTrace_card : ∀ m b, (privateTrace m b).card = 6 := by
  decide +kernel

theorem commonTrace_injective :
    Function.Injective (fun i : Fin 3 × Bool => commonTrace i.1 i.2) := by
  decide +kernel

theorem privateTrace_injective :
    Function.Injective (fun i : Fin 3 × Bool => privateTrace i.1 i.2) := by
  decide +kernel

theorem commonTraceFamily_card : commonTraceFamily.card = 6 := by decide +kernel

theorem privateTraceFamily_card : privateTraceFamily.card = 6 := by decide +kernel

theorem rootedCore_eq_figure1 : relabel rootedLabel rootedCore = core := by
  decide +kernel

theorem rootedSpine_eq_figure1 :
    ∀ i, (rootedSpine i).map rootedLabel.toEmbedding = spine i := by
  decide +kernel

theorem rooted_core_through_root :
    star rootedCore none = rootedIncidentCore := by decide +kernel

theorem rooted_core_avoiding_root :
    rootedCore.filter (fun B => none ∉ B) = rootedPrivateCore := by decide +kernel


/-! Move an arbitrary point of the fixed Figure 1 template to zero.
The maps swap its spine with spine zero, then translate the two first
four-point spines by the same vector in F₂². This preserves the even parity
condition. The displayed tables are these twelve prescribed maps, not the
result of searching for permutations or coverings. -/

private def rootMoveTable : Fin 12 → Fin 12 → Fin 12 :=
  ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  ![1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11],
  ![2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11],
  ![3, 2, 1, 0, 7, 6, 5, 4, 8, 9, 10, 11],
  ![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11],
  ![5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11],
  ![6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11],
  ![7, 6, 5, 4, 3, 2, 1, 0, 8, 9, 10, 11],
  ![8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3],
  ![8, 9, 10, 11, 5, 4, 7, 6, 1, 0, 3, 2],
  ![8, 9, 10, 11, 6, 7, 4, 5, 2, 3, 0, 1],
  ![8, 9, 10, 11, 7, 6, 5, 4, 3, 2, 1, 0]]

private def rootMoveInverseTable : Fin 12 → Fin 12 → Fin 12 :=
  ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
  ![1, 0, 3, 2, 5, 4, 7, 6, 8, 9, 10, 11],
  ![2, 3, 0, 1, 6, 7, 4, 5, 8, 9, 10, 11],
  ![3, 2, 1, 0, 7, 6, 5, 4, 8, 9, 10, 11],
  ![4, 5, 6, 7, 0, 1, 2, 3, 8, 9, 10, 11],
  ![5, 4, 7, 6, 1, 0, 3, 2, 8, 9, 10, 11],
  ![6, 7, 4, 5, 2, 3, 0, 1, 8, 9, 10, 11],
  ![7, 6, 5, 4, 3, 2, 1, 0, 8, 9, 10, 11],
  ![8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3],
  ![9, 8, 11, 10, 5, 4, 7, 6, 0, 1, 2, 3],
  ![10, 11, 8, 9, 6, 7, 4, 5, 0, 1, 2, 3],
  ![11, 10, 9, 8, 7, 6, 5, 4, 0, 1, 2, 3]]

def rootMove (q : Fin 12) : Equiv.Perm (Fin 12) where
  toFun := rootMoveTable q
  invFun := rootMoveInverseTable q
  left_inv := (show ∀ q x, rootMoveInverseTable q (rootMoveTable q x) = x by
    decide +kernel) q
  right_inv := (show ∀ q x, rootMoveTable q (rootMoveInverseTable q x) = x by
    decide +kernel) q

def rootMoveSpines (q : Fin 12) : Equiv.Perm (Fin 3) :=
  Equiv.swap ⟨q.val / 4, by omega⟩ 0

theorem rootMove_root : ∀ q, rootMove q q = 0 := by decide +kernel

theorem rootMove_core : ∀ q, relabel (rootMove q) core = core := by
  decide +kernel

theorem rootMove_spines : ∀ q i,
    (spine i).map (rootMove q).toEmbedding = spine (rootMoveSpines q i) := by
  decide +kernel

/-- Any automorphism of the partial template carries arbitrary completions
onto completions; no choice of the six added points is restricted. -/
theorem templateCompletion_relabel {C : Family (Fin 12)}
    (hC : IsTemplateCompletion C) (e : Equiv.Perm (Fin 12))
    (s : Equiv.Perm (Fin 3))
    (hcore : relabel e core = core)
    (hspine : ∀ i, (spine i).map e.toEmbedding = spine (s i)) :
    IsTemplateCompletion (relabel e C) := by
  obtain ⟨B, hB, rfl⟩ := (isTemplateCompletion_iff_extensions C).mp hC
  apply (isTemplateCompletion_iff_extensions _).mpr
  refine ⟨fun j => (B (s.symm j)).map e.toEmbedding, ?_, ?_⟩
  · intro j
    constructor
    · have hs := (map_subset_map (f := e.toEmbedding)).mpr (hB (s.symm j)).1
      simpa only [hspine, s.apply_symm_apply] using hs
    · simpa using (hB (s.symm j)).2
  · have hh := relabel_completion_blocks e core (fun _ => ∅) B
    simp only [map_empty, empty_union] at hh
    rw [hh, hcore]
    apply congrArg (fun F : Family (Fin 12) => core ∪ F)
    ext D
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨s i, by simp⟩
    · rintro ⟨j, rfl⟩
      exact ⟨s.symm j, rfl⟩

/-- Normalize an ordinary minimum covering at any chosen point.
The existential additions remain completely arbitrary. -/
theorem ordinary_root_normalize {C : Family (Fin 12)}
    (hC : IsomorphicTemplateCompletion C) (q : Fin 12) :
    ∃ e : Equiv.Perm (Fin 12), e q = 0 ∧
      IsTemplateCompletion (relabel e C) := by
  obtain ⟨D, hD, f, hf⟩ := hC
  refine ⟨f.trans (rootMove (f q)), rootMove_root (f q), ?_⟩
  rw [← relabel_trans, hf]
  exact templateCompletion_relabel hD (rootMove (f q))
    (rootMoveSpines (f q)) (rootMove_core (f q)) (rootMove_spines (f q))

/-- A rooted ordinary link consists of the fixed parity core and three
arbitrary six-point extensions of its spines. This frame uses an equivalence
from the abstract root/companion/spouse coordinates to the actual points. -/
structure OrdinaryRootedFrame {α : Type*} [DecidableEq α]
    (C : Family α) (q : α) where
  label : RootedPoint ≃ α
  root_eq : label none = q
  completed : Fin 3 → Finset RootedPoint
  spine_subset : ∀ i, rootedSpine i ⊆ completed i
  completed_card : ∀ i, (completed i).card = 6
  family_eq : relabel label (rootedCore ∪ univ.image completed) = C


/-- Relabelling a family with a finite list of additional rows. -/
theorem relabel_union_image {α β ι : Type*}
    [DecidableEq α] [DecidableEq β] [Fintype ι]
    (e : α ≃ β) (K : Family α) (B : ι → Finset α) :
    relabel e (K ∪ univ.image B) =
      relabel e K ∪ univ.image (fun i => (B i).map e.toEmbedding) := by
  unfold relabel
  rw [map_union]
  apply congrArg (fun F : Family β => K.map _ ∪ F)
  rw [map_eq_image, image_image]
  rfl

/-- Extract the root/companion/spouse frame from any ordinary link. -/
theorem ordinary_rooted_frame {C : Family (Fin 12)}
    (hC : IsomorphicTemplateCompletion C) (q : Fin 12) :
    Nonempty (OrdinaryRootedFrame C q) := by
  obtain ⟨e, he, hN⟩ := ordinary_root_normalize hC q
  obtain ⟨B, hB, hfamily⟩ := (isTemplateCompletion_iff_extensions _).mp hN
  let B' : Fin 3 → Finset RootedPoint := fun i =>
    (B i).map rootedLabel.symm.toEmbedding
  have hBmap (i : Fin 3) : (B' i).map rootedLabel.toEmbedding = B i := by
    ext x
    simp only [B', mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]
  have hr : relabel rootedLabel (rootedCore ∪ univ.image B') = relabel e C := by
    rw [relabel_union_image, rootedCore_eq_figure1]
    simp only [hBmap]
    exact hfamily.symm
  refine ⟨{
    label := rootedLabel.trans e.symm
    root_eq := ?_
    completed := B'
    spine_subset := ?_
    completed_card := ?_
    family_eq := ?_ }⟩
  · change e.symm (rootedLabel none) = q
    rw [rootedLabel_none, ← he, e.symm_apply_apply]
  · intro i
    apply (map_subset_map (f := rootedLabel.toEmbedding)).mp
    rw [rootedSpine_eq_figure1, hBmap]
    exact (hB i).1
  · intro i
    simpa only [B', card_map] using (hB i).2
  · rw [← relabel_trans, hr, relabel_symm_relabel]

/-- The same coordinates on any point type already identified with a
Figure 1 completion. In particular this applies directly to actual links. -/
theorem ordinary_rooted_frame_of_isomorphic_template
    {α : Type*} [DecidableEq α] {C : Family α}
    (hC : ∃ D : Family (Fin 12), GPPTStructural.IsTemplateCompletion D ∧ Isomorphic C D)
    (q : α) : Nonempty (OrdinaryRootedFrame C q) := by
  obtain ⟨D, hD, e, he⟩ := hC
  have hD' : GPPTStructural.IsomorphicTemplateCompletion D :=
    ⟨D, hD, Equiv.refl _, relabel_refl D⟩
  obtain ⟨F⟩ := ordinary_rooted_frame hD' (e q)
  refine ⟨{
    label := F.label.trans e.symm
    root_eq := ?_
    completed := F.completed
    spine_subset := F.spine_subset
    completed_card := F.completed_card
    family_eq := ?_ }⟩
  · change e.symm (F.label none) = q
    rw [F.root_eq, e.symm_apply_apply]
  · rw [← relabel_trans, F.family_eq, ← he, relabel_symm_relabel]

namespace OrdinaryRootedFrame

variable {α : Type*} [DecidableEq α]
  {C : Family α} {q : α} (F : OrdinaryRootedFrame C q)

theorem core_subset : relabel F.label rootedCore ⊆ C := by
  have h : relabel F.label rootedCore ⊆
      relabel F.label (rootedCore ∪ univ.image F.completed) :=
    map_subset_map.mpr subset_union_left
  exact h.trans F.family_eq.subset

theorem core_mem {B : Finset RootedPoint} (hB : B ∈ rootedCore) :
    B.map F.label.toEmbedding ∈ C :=
  F.core_subset ((mem_relabel _ _ _).mpr hB)

theorem common_mem (m : Fin 3) (b : Bool) :
    (insert none (liftTrace (commonTrace m b))).map F.label.toEmbedding ∈ C := by
  apply F.core_mem
  apply mem_union_left
  apply mem_image.mpr
  refine ⟨commonTrace m b, ?_, rfl⟩
  exact mem_image.mpr ⟨(m, b), mem_univ _, rfl⟩

theorem private_mem (m : Fin 3) (b : Bool) :
    (liftTrace (privateTrace m b)).map F.label.toEmbedding ∈ C := by
  apply F.core_mem
  apply mem_union_right
  apply mem_image.mpr
  refine ⟨privateTrace m b, ?_, rfl⟩
  exact mem_image.mpr ⟨(m, b), mem_univ _, rfl⟩

theorem completed_mem (i : Fin 3) :
    (F.completed i).map F.label.toEmbedding ∈ C := by
  apply F.family_eq.subset
  apply (mem_relabel _ _ _).mpr
  exact mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)

end OrdinaryRootedFrame

#guard_standard_axioms commonTrace_card privateTrace_card commonTrace_injective
  privateTrace_injective rootedCore_eq_figure1 rootedSpine_eq_figure1
  rootMove_core rootMove_spines templateCompletion_relabel ordinary_root_normalize
  ordinary_rooted_frame ordinary_rooted_frame_of_isomorphic_template OrdinaryRootedFrame.common_mem OrdinaryRootedFrame.private_mem

end CoveringDesigns.C13Structural
