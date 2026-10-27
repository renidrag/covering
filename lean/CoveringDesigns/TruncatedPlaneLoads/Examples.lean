import CoveringDesigns.TruncatedPlaneLoads.Actual
import Mathlib.Data.Fin.VecNotation

/-! Kernel-checked boundary cases, using the retained order-four positive control. -/

namespace CoveringDesigns.TruncatedPlaneLoads.Examples
open Finset

-- BEGIN RETAINED ORDER-FOUR CORE
def coreEdge : Fin 16 → Finset (Fin 20) :=
  ![{0, 4, 8, 12, 16},
    {0, 5, 10, 15, 17},
    {0, 6, 11, 13, 18},
    {0, 7, 9, 14, 19},
    {1, 4, 11, 14, 17},
    {1, 5, 9, 13, 16},
    {1, 6, 8, 15, 19},
    {1, 7, 10, 12, 18},
    {2, 4, 9, 15, 18},
    {2, 5, 11, 12, 19},
    {2, 6, 10, 14, 16},
    {2, 7, 8, 13, 17},
    {3, 4, 10, 13, 19},
    {3, 5, 8, 14, 18},
    {3, 6, 9, 12, 17},
    {3, 7, 11, 15, 16}]
-- END RETAINED ORDER-FOUR CORE

def group4 (x : Fin 20) : Fin 5 := ⟨x.val / 4, by omega⟩
def core4 : Finset (Finset (Fin 20)) := univ.image coreEdge

private theorem transversals4 : ∀ i : Fin 16, ∀ g : Fin 5,
    ((coreEdge i).filter (group4 · = g)).card = 1 := by decide

private theorem intersections4 : ∀ i j : Fin 16, i ≠ j →
    (coreEdge i ∩ coreEdge j).card = 1 := by decide

def plane4 : Plane 4 (Fin 20) (Fin 5) where
  group := group4
  core := core4
  groups_card := rfl
  group_card := by decide
  transversal := by
    intro E hE i
    obtain ⟨j,_,rfl⟩ := mem_image.mp hE
    exact transversals4 j i
  degree := by decide
  codegree := by decide
  intersection := by
    intro E hE F hF hEF
    obtain ⟨i,_,rfl⟩ := mem_image.mp hE
    obtain ⟨j,_,rfl⟩ := mem_image.mp hF
    exact intersections4 i j (fun h => hEF (congrArg coreEdge h))

theorem pure4 : NatAdmissible plane4 plane4.core (fun _ => 1) 4 := by
  exact integer_converse plane4 (by decide) (by decide : 0 < 1) (Or.inl ⟨rfl,fun _ _ => rfl⟩)

def multiplicity4 (S : Finset (Fin 20)) : ℕ :=
  if S ∈ plane4.core then (if (0 : Fin 20) ∈ S then 1 else 2) else 1

theorem extended4 : NatAdmissible plane4 (plane4.extension 0) multiplicity4 8 := by
  apply integer_converse plane4 (t := 2) (by decide) (by decide)
  refine Or.inr ⟨0,1,by decide,by decide,fun S => plane4.mem_extension 0 S,?_,?_⟩
  · intro i hi
    simp [multiplicity4,plane4.extra_not_core (by decide)]
  · intro E hE
    simp [multiplicity4,hE]

theorem pure_counts :
    Fintype.card (Point plane4.core (fun _ => 1)) = 16 ∧
    (expandedFamily plane4.core (fun _ => 1)).card = 20 ∧
    IsCover (expandedFamily plane4.core (fun _ => 1)) 4 2 :=
  ⟨point_card pure4,expanded_family_card (by decide) pure4,expanded_family_cover pure4⟩

theorem extended_counts :
    Fintype.card (Point (plane4.extension 0) multiplicity4) = 32 ∧
    (expandedFamily (plane4.extension 0) multiplicity4).card = 20 ∧
    Multicover.IsCover (block (plane4.extension 0) multiplicity4) 8 2 1 ∧
    IsCover (expandedFamily (plane4.extension 0) multiplicity4) 8 2 :=
  ⟨point_card extended4,expanded_family_card (by decide) extended4,
    expanded_cover extended4,expanded_family_cover extended4⟩

theorem two_coordinate_intersection :
    plane4.extra 1 0 ∈ plane4.extension 0 ∧ coreEdge 0 ∈ plane4.core ∧
    (plane4.extra 1 0 ∩ coreEdge 0).card = 2 := by
  refine ⟨?_,?_,?_⟩
  · rw [plane4.mem_extension]
    exact Or.inr ⟨1,by decide,rfl⟩
  · exact mem_image.mpr ⟨0,mem_univ _,rfl⟩
  · decide

theorem unit_case {H : Finset (Finset (Fin 20))} {m : Finset (Fin 20) → ℕ}
    (h : NatAdmissible plane4 H m 4) : H = plane4.core ∧ ∀ E ∈ plane4.core, m E = 1 :=
  unit_load_pure plane4 (by decide) h

theorem relabelled_extended : ∃ C : Family (Fin 32), C.card = 20 ∧ IsCover C 8 2 :=
  expanded_on (by decide) extended4 rfl

theorem permuted_occurrences :
    Multicover.IsCover (block (plane4.extension 0) multiplicity4 ∘ Equiv.swap (0 : Fin 20) 19) 8 2 1 :=
  (expanded_reindex extended4 (Equiv.swap 0 19)).2

/-- Two distinct actual points legitimately have the same occupied support. -/
theorem twins_exist : ∃ p r : Point (plane4.extension 0) multiplicity4,
    p ≠ r ∧ p.1 = r.1 := by
  have he : coreEdge 4 ∈ plane4.extension 0 := by
    rw [plane4.mem_extension]
    exact Or.inl (mem_image.mpr ⟨4,mem_univ _,rfl⟩)
  have hm : multiplicity4 (coreEdge 4) = 2 := by decide
  let S : plane4.extension 0 := ⟨coreEdge 4,he⟩
  let p : Point (plane4.extension 0) multiplicity4 := ⟨S,⟨0,by simpa [S,hm]⟩⟩
  let r : Point (plane4.extension 0) multiplicity4 := ⟨S,⟨1,by simpa [S,hm]⟩⟩
  refine ⟨p,r,?_,rfl⟩
  intro h
  have hh := congrArg (fun z : Point (plane4.extension 0) multiplicity4 => z.2.val) h
  change (0 : ℕ) = 1 at hh
  omega

end CoveringDesigns.TruncatedPlaneLoads.Examples
