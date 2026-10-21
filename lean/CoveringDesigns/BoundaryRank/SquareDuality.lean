import CoveringDesigns.TwoKMinusTwoEquality.Matrix
import CoveringDesigns.Foundations.SupportObstruction

/-! Square constant-Gram duality and the universal eleven-column obstruction.
No particular matrix, classification or diagnostic data is used. -/
namespace CoveringDesigns.BoundaryRank
open Finset Matrix
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Constant row Gram and row margin give invertibility, the same column
margin and the same column Gram. Binary entries are unnecessary here. -/
theorem square_duality (U : Matrix κ κ ℝ) (r lam : ℝ)
    (hlam : 0 ≤ lam) (hlt : lam < r) (hb : 0 < Fintype.card κ)
    (hrow : ∀ i, ∑ j, U i j = r)
    (hgram : U * U.transpose =
      Matrix.diagonal (fun _ => r-lam) + Matrix.of (fun _ _ => lam)) :
    U.det ≠ 0 ∧ U⁻¹ * U = 1 ∧ U * U⁻¹ = 1 ∧
    (∀ j, ∑ i, U i j = r) ∧
    U.transpose * U = Matrix.diagonal (fun _ => r-lam) +
      Matrix.of (fun _ _ => lam) := by
  have hpd : (U * U.transpose).PosDef := by
    rw [hgram]
    exact (Matrix.PosDef.diagonal (fun _ => sub_pos.mpr hlt)).add_posSemidef
      (TwoKMinusTwoEquality.constant_posSemidef lam hlam)
  have hdet : U.det ≠ 0 := by
    intro hz
    have hp := hpd.det_pos
    rw [Matrix.det_mul, Matrix.det_transpose, hz] at hp
    norm_num at hp
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet
  have hcol := (TwoKMinusTwoEquality.square_parameters U r lam hlam hlt hb hrow hgram).1
  refine ⟨hdet, U.nonsing_inv_mul hu, U.mul_nonsing_inv hu, hcol, ?_⟩
  apply Matrix.mul_right_injective_of_inv U⁻¹ U (U.nonsing_inv_mul hu)
  dsimp only
  rw [← Matrix.mul_assoc, hgram]
  rw [Matrix.add_mul, Matrix.mul_add]
  apply congrArg₂ (· + ·)
  · ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  · ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [← mul_sum, ← sum_mul, hcol, hrow]
    ring

noncomputable def binarySupport (f : κ → ℝ) : Finset κ :=
  univ.filter (fun j => f j = 1)

theorem binary_sum (f : κ → ℝ) (hf : ∀ j, f j = 0 ∨ f j = 1) :
    ∑ j, f j = ((binarySupport f).card : ℝ) := by
  classical
  simp only [binarySupport, card_eq_sum_ones, sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply sum_congr rfl
  intro j _
  rcases hf j with hj | hj <;> simp [hj]

theorem binary_dot (f g : κ → ℝ)
    (hf : ∀ j, f j = 0 ∨ f j = 1) (hg : ∀ j, g j = 0 ∨ g j = 1) :
    (∑ j, f j * g j) = ((binarySupport f ∩ binarySupport g).card : ℝ) := by
  classical
  have he : binarySupport f ∩ binarySupport g =
      univ.filter (fun j => f j = 1 ∧ g j = 1) := by
    ext j
    simp [binarySupport]
  rw [he]
  simp only [card_eq_sum_ones, sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply sum_congr rfl
  intro j _
  rcases hf j with hj | hj <;> rcases hg j with hk | hk <;> simp [hj,hk]

/-- The two zero rows are determined just by the two Gram identities.
They are distinct actual row indices, with supports uniting to the complement. -/
theorem two_zero_rows (U : Matrix κ κ ℝ) (hc : Fintype.card κ = 11)
    (hbin : ∀ i j, U i j = 0 ∨ U i j = 1)
    (hrow : ∀ i, ∑ j, U i j = 6)
    (hgram : U * U.transpose = Matrix.diagonal (fun _ => (3 : ℝ)) +
      Matrix.of (fun _ _ => (3 : ℝ))) {a b : κ} (hab : a ≠ b) :
    (univ.filter (fun i => U i a = 0 ∧ U i b = 0)).card = 2 ∧
    ∃ x y, x ≠ y ∧ U x a = 0 ∧ U x b = 0 ∧ U y a = 0 ∧ U y b = 0 ∧
      binarySupport (U x) ∪ binarySupport (U y) = univ \ {a,b} := by
  classical
  obtain ⟨_,_,_,hcol,hdual⟩ := square_duality U 6 3 (by norm_num) (by norm_num)
    (by omega) hrow (by norm_num; exact hgram)
  have hcs (j : κ) : (binarySupport (fun i => U i j)).card = 6 := by
    have he := binary_sum (fun i => U i j) (fun i => hbin i j)
    rw [hcol] at he
    exact_mod_cast he.symm
  have hci : (binarySupport (fun i => U i a) ∩ binarySupport (fun i => U i b)).card = 3 := by
    have he := binary_dot (fun i => U i a) (fun i => U i b)
      (fun i => hbin i a) (fun i => hbin i b)
    have hd := congr_fun (congr_fun hdual a) b
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hd
    rw [he] at hd
    simp [hab] at hd
    exact_mod_cast hd
  let Z := univ.filter (fun i => U i a = 0 ∧ U i b = 0)
  have hZ : Z = univ \ (binarySupport (fun i => U i a) ∪ binarySupport (fun i => U i b)) := by
    ext i
    rcases hbin i a with ha | ha <;> rcases hbin i b with hb | hb <;>
      simp [Z,binarySupport,ha,hb]
  have hZcard : Z.card = 2 := by
    have hi := card_union_add_card_inter (binarySupport (fun i => U i a))
      (binarySupport (fun i => U i b))
    rw [hcs,hcs,hci] at hi
    rw [hZ,card_sdiff_of_subset (subset_univ _),card_univ,hc]
    omega
  obtain ⟨x,y,hxy,hxyZ⟩ := card_eq_two.mp hZcard
  have hx : U x a = 0 ∧ U x b = 0 := by
    have hm : x ∈ Z := by rw [hxyZ]; simp
    exact (mem_filter.mp hm).2
  have hy : U y a = 0 ∧ U y b = 0 := by
    have hm : y ∈ Z := by rw [hxyZ]; simp
    exact (mem_filter.mp hm).2
  have hrs (i : κ) : (binarySupport (U i)).card = 6 := by
    have he := binary_sum (U i) (hbin i)
    rw [hrow] at he
    exact_mod_cast he.symm
  have hri : (binarySupport (U x) ∩ binarySupport (U y)).card = 3 := by
    have he := binary_dot (U x) (U y) (hbin x) (hbin y)
    have hd := congr_fun (congr_fun hgram x) y
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at hd
    rw [he] at hd
    simp [hxy] at hd
    exact_mod_cast hd
  have hsub : binarySupport (U x) ∪ binarySupport (U y) ⊆ univ \ {a,b} := by
    intro i hi
    have ha : i ≠ a := by
      intro hi'; subst i
      simpa [binarySupport,hx.1,hy.1] using hi
    have hb : i ≠ b := by
      intro hi'; subst i
      simpa [binarySupport,hx.2,hy.2] using hi
    simp [ha,hb]
  refine ⟨hZcard,x,y,hxy,hx.1,hx.2,hy.1,hy.2,eq_of_subset_of_card_le hsub ?_⟩
  have hi := card_union_add_card_inter (binarySupport (U x)) (binarySupport (U y))
  rw [hrs,hrs,hri] at hi
  rw [card_sdiff_of_subset (subset_univ _),card_univ,hc,card_pair hab]
  omega

/-- Minimal exceptional-support obstruction. Only the 00 rows need a bound;
there is no second seven-support or design-classification premise. -/
theorem exceptional_support (U : Matrix κ κ ℝ) (hc : Fintype.card κ = 11)
    (hbin : ∀ i j, U i j = 0 ∨ U i j = 1)
    (hrow : ∀ i, ∑ j, U i j = 6)
    (hgram : U * U.transpose = Matrix.diagonal (fun _ => (3 : ℝ)) +
      Matrix.of (fun _ _ => (3 : ℝ)))
    {a b : κ} (hab : a ≠ b) (H : Finset κ) (hH : H.card = 7)
    (hA : (H ∩ {a,b}).card = 1)
    (hbound : ∀ i, U i a = 0 → U i b = 0 → (H ∩ binarySupport (U i)).card ≤ 3) :
    ∃ x y, x ≠ y ∧ ((H ∩ binarySupport (U x)) ∩ binarySupport (U y)) = ∅ := by
  obtain ⟨_,x,y,hxy,hxa,hxb,hya,hyb,hunion⟩ := two_zero_rows U hc hbin hrow hgram hab
  refine ⟨x,y,hxy,SupportObstruction.empty_of_intersection_bound univ {a,b} H
    (binarySupport (U x)) (binarySupport (U y)) (subset_univ _) hunion ?_⟩
  have hx := hbound x hxa hxb
  have hy := hbound y hya hyb
  omega

end CoveringDesigns.BoundaryRank
