import CoveringDesigns.SaturatedMatching.FourNormalize

/-! The four-pair small-intersection theorem, with no normalization premise.
Formalisation: Rob Gardiner with AI assistance. -/
namespace CoveringDesigns.SaturatedMatching
open Finset
variable {α ι M : Type*} [Fintype α] [Fintype ι] [Fintype M]
  [DecidableEq α] [DecidableEq ι] [DecidableEq M]
variable {B : ι → Finset α} (P : Pattern (M := M) B)

/-- Four actual mutually separating pairs with the stated incidence
compatibility have a supporting intersection of size four. Block sizes and
the number of unmatched points are unrestricted. -/
theorem four_pair_small_intersection (H : FourCompatibility P)
    (hpair : ∀ x f b, x ≠ P.point (f,b) → x ≠ P.point (f,!b) →
      3 ≤ indexedSubsetDegree B {x,P.point (f,b)}) :
    ∃ e f : M, e ≠ f ∧ ∃ a b : Bool,
      (B (P.block (e,a)) ∩ B (P.block (f,b))).card = 4 := by
  classical
  obtain ⟨R⟩ := Remaining.exists_of_four P H.pairs H.degree
  obtain ⟨r,h01,h23,hd⟩ := R.grouped_indices H
  have pick (f g : M) (he : R.signature f = R.signature g) :
      ∃ b : Bool, R.index (f,true) = R.index (g,b) := by
    have hm : R.index (f,true) ∈ R.signature g := by
      rw [← he]; simp [Remaining.signature]
    rcases mem_insert.mp hm with hm | hm
    · exact ⟨true,hm⟩
    · exact ⟨false,mem_singleton.mp hm⟩
  obtain ⟨b,hb⟩ := pick (r 0) (r 1) h01
  obtain ⟨d,hd'⟩ := pick (r 2) (r 3) h23
  let p : Fin 4 → Bool := ![true,b,true,d]
  let P₀ := P.relabel r p (fun _ => true)
  let R₀ := R.relabel r p (fun _ => true)
  let H₀ := H.relabel r p (fun _ => true)
  have ha : R₀.index (0,true) = R₀.index (1,true) := by
    simpa [R₀,Remaining.relabel,Pattern.labels,p] using hb
  have hb' : R₀.index (2,true) = R₀.index (3,true) := by
    simpa [R₀,Remaining.relabel,Pattern.labels,p] using hd'
  have hsa : R₀.signature 1 = R₀.signature 0 := by
    simpa only [R₀,Remaining.relabel_signature] using h01.symm
  have hsb : R₀.signature 3 = R₀.signature 2 := by
    simpa only [R₀,Remaining.relabel_signature] using h23.symm
  have hsd : Disjoint (R₀.signature 0) (R₀.signature 2) := by
    simpa only [R₀,Remaining.relabel_signature] using hd
  let q : Fin 4 → Bool := ![P₀.sign 0 2,P₀.sign 1 2,P₀.sign 2 0,P₀.sign 3 0]
  let P₁ := P₀.relabel (Equiv.refl _) (fun _ => true) q
  let R₁ := R₀.relabel (Equiv.refl _) (fun _ => true) q
  let H₁ := H₀.relabel (Equiv.refl _) (fun _ => true) q
  have ha' : R₁.index (0,true) = R₁.index (1,true) := by
    simpa [R₁,Remaining.relabel,Pattern.labels] using ha
  have hb'' : R₁.index (2,true) = R₁.index (3,true) := by
    simpa [R₁,Remaining.relabel,Pattern.labels] using hb'
  have hsa' : R₁.signature 1 = R₁.signature 0 := by
    simpa only [R₁,Remaining.relabel_signature,Equiv.refl_apply] using hsa
  have hsb' : R₁.signature 3 = R₁.signature 2 := by
    simpa only [R₁,Remaining.relabel_signature,Equiv.refl_apply] using hsb
  have hsd' : Disjoint (R₁.signature 0) (R₁.signature 2) := by
    simpa only [R₁,Remaining.relabel_signature,Equiv.refl_apply] using hsd
  have hr : P₁.sign 0 2 = true ∧ P₁.sign 1 2 = true ∧
      P₁.sign 2 0 = true ∧ P₁.sign 3 0 = true := by
    simp [P₁,Pattern.relabel,q]
  let c := P₁.sign 1 0
  let P₂ := P₁.relabel (Equiv.refl _) ![c,c,true,true] ![true,true,c,c]
  have hs : ∀ e f, e ≠ f → P₂.sign e f = normalizedSigns e f :=
    normalized_from_aligned R₁ H₁ ha' hb'' hsd' hsa' hsb' hr
  have hp₀ := P.relabel_pair_floor r p (fun _ => true) hpair
  have hp₁ := P₀.relabel_pair_floor (Equiv.refl _) (fun _ => true) q hp₀
  have hp₂ := P₁.relabel_pair_floor (Equiv.refl _) ![c,c,true,true] ![true,true,c,c] hp₁
  have hc := normalized_small_intersection P₂ hs
    (P₁.relabel_degree (Equiv.refl _) _ _ H₁.degree) hp₂
  refine ⟨r 0,r 1,fun he => (by decide : (0 : Fin 4) ≠ 1) (r.injective he),
    q 0,q 1,?_⟩
  simpa [P₂,P₁,P₀,Pattern.relabel,Pattern.labels] using hc

end CoveringDesigns.SaturatedMatching
