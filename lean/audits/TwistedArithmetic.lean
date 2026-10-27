import CoveringDesigns.TwistedArithmetic

/-! Complete expected public types and transitive foundational axioms. -/
universe u_1 u_2 u_3

namespace CoveringDesigns.AuditTwistedArithmetic
/-- Nonexistence from only the small actual twisted-incidence contract. -/
theorem no_twisted_explicit {I : Type*} [Fintype I] [DecidableEq I]
    (H : Finset (Finset I)) (hn : Fintype.card I = 20) (hc : H.card = 20)
    (hu : ∀ E ∈ H, E.card = 5) (hd : ∀ x, (H.filter (x ∈ ·)).card = 5)
    (hi : ∀ E ∈ H, ∀ F ∈ H, E ≠ F → (E ∩ F).Nonempty) : False := by
  exact TwistedArithmetic.no_twisted_four ⟨hn,hc,hu,hd,hi⟩
#guard_standard_axioms no_twisted_explicit
#print axioms no_twisted_explicit
end CoveringDesigns.AuditTwistedArithmetic


#check (@CoveringDesigns.TwistedArithmetic.pairedGram :
{R : Type u_1} → [DecidableEq R] → ℚ → Matrix (R ⊕ R) (R ⊕ R) ℚ)
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.pairedGram
#print axioms CoveringDesigns.TwistedArithmetic.pairedGram

#check (@CoveringDesigns.TwistedArithmetic.instFintypeMateRepresentatives :
{I : Type u_1} → [inst : Fintype I] → (f : I → I) → Fintype (CoveringDesigns.TwistedArithmetic.MateRepresentatives f))
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.instFintypeMateRepresentatives
#print axioms CoveringDesigns.TwistedArithmetic.instFintypeMateRepresentatives

#check (@CoveringDesigns.TwistedArithmetic.pairedGram_apply :
∀ {R : Type u_1} [Fintype R] [inst : DecidableEq R] (a : ℚ) (x y : R ⊕ R),
  CoveringDesigns.TwistedArithmetic.pairedGram a x y = (if x = y then a else 0) + 1 + if y = x.swap then 1 else 0)
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.pairedGram_apply
#print axioms CoveringDesigns.TwistedArithmetic.pairedGram_apply

#check (@CoveringDesigns.TwistedArithmetic.pairedGram_det :
∀ {R : Type u_1} [inst : Fintype R] [inst_1 : DecidableEq R] (a : ℚ),
  a + 1 ≠ 0 →
    (CoveringDesigns.TwistedArithmetic.pairedGram a).det =
      (a - 1) ^ Fintype.card R * (a + 1) ^ Fintype.card R * (1 + 2 * ↑(Fintype.card R) / (a + 1)))
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.pairedGram_det
#print axioms CoveringDesigns.TwistedArithmetic.pairedGram_det

#check (@CoveringDesigns.TwistedArithmetic.MateRepresentatives :
{I : Type u_1} → [Fintype I] → (I → I) → Type (max 0 u_1))
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.MateRepresentatives
#print axioms CoveringDesigns.TwistedArithmetic.MateRepresentatives

#check (@CoveringDesigns.TwistedArithmetic.mateEquiv :
{I : Type u_1} →
  [inst : Fintype I] →
    (f : I → I) →
      Function.Involutive f →
        (∀ (x : I), f x ≠ x) →
          CoveringDesigns.TwistedArithmetic.MateRepresentatives f ⊕
              CoveringDesigns.TwistedArithmetic.MateRepresentatives f ≃
            I)
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.mateEquiv
#print axioms CoveringDesigns.TwistedArithmetic.mateEquiv

#check (@CoveringDesigns.TwistedArithmetic.mateEquiv_swap :
∀ {I : Type u_1} [inst : Fintype I] (f : I → I) (hi : Function.Involutive f) (hn : ∀ (x : I), f x ≠ x)
  (z :
    CoveringDesigns.TwistedArithmetic.MateRepresentatives f ⊕ CoveringDesigns.TwistedArithmetic.MateRepresentatives f),
  (CoveringDesigns.TwistedArithmetic.mateEquiv f hi hn) z.swap =
    f ((CoveringDesigns.TwistedArithmetic.mateEquiv f hi hn) z))
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.mateEquiv_swap
#print axioms CoveringDesigns.TwistedArithmetic.mateEquiv_swap

#check (@CoveringDesigns.TwistedArithmetic.mateRepresentatives_card :
∀ {I : Type u_1} [inst : Fintype I] (f : I → I),
  Function.Involutive f →
    (∀ (x : I), f x ≠ x) → 2 * Fintype.card (CoveringDesigns.TwistedArithmetic.MateRepresentatives f) = Fintype.card I)
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.mateRepresentatives_card
#print axioms CoveringDesigns.TwistedArithmetic.mateRepresentatives_card

#check (@CoveringDesigns.TwistedArithmetic.incidence :
{I : Type u_1} → [DecidableEq I] → (H : Finset (Finset I)) → Matrix I ↥H ℤ)
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.incidence
#print axioms CoveringDesigns.TwistedArithmetic.incidence

#check (@CoveringDesigns.TwistedArithmetic.incidence_gram :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {H : Finset (Finset I)} {q : ℕ}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane q H) (x y : I),
  (CoveringDesigns.TwistedArithmetic.incidence H * (CoveringDesigns.TwistedArithmetic.incidence H).transpose) x y =
    (if x = y then ↑q else 0) + 1 + if y = T.coordinateMate x then 1 else 0)
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.incidence_gram
#print axioms CoveringDesigns.TwistedArithmetic.incidence_gram

#check (@CoveringDesigns.TwistedArithmetic.squareIncidence :
{I : Type u_1} →
  [inst : Fintype I] →
    [inst_1 : DecidableEq I] →
      {H : Finset (Finset I)} → {q : ℕ} → CoveringDesigns.PairEquality.IsTwistedPlane q H → Matrix I I ℤ)
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.squareIncidence
#print axioms CoveringDesigns.TwistedArithmetic.squareIncidence

#check (@CoveringDesigns.TwistedArithmetic.order_four_determinant :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {H : Finset (Finset I)}
  (T : CoveringDesigns.PairEquality.IsTwistedPlane 4 H),
  (CoveringDesigns.TwistedArithmetic.squareIncidence T).det ^ 2 = 3 ^ 10 * 5 ^ 11)
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.order_four_determinant
#print axioms CoveringDesigns.TwistedArithmetic.order_four_determinant

#check (@CoveringDesigns.TwistedArithmetic.no_twisted_four :
∀ {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] {H : Finset (Finset I)},
  CoveringDesigns.PairEquality.IsTwistedPlane 4 H → False)
#guard_standard_axioms CoveringDesigns.TwistedArithmetic.no_twisted_four
#print axioms CoveringDesigns.TwistedArithmetic.no_twisted_four
