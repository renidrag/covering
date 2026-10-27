import CoveringDesigns.PairEquality.Twisted

/-! Natural multiplicity equations; independent of determinant arguments. -/
namespace CoveringDesigns.PairDivisibility
open Finset PairEquality
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {q k : ℕ} {H : Finset (Finset I)}

private theorem total_multiplicity (T : IsTwistedPlane q H) (m : Finset I → ℕ)
    (hl : ∀ x, (∑ E ∈ H, if x ∈ E then m E else 0) = k) :
    (∑ E ∈ H, m E) = q*k := by
  have he : (∑ x : I, ∑ E ∈ H, if x ∈ E then m E else 0) =
      (q+1) * ∑ E ∈ H, m E := by
    rw [sum_comm,mul_sum]
    apply sum_congr rfl
    intro E hE
    rw [← sum_filter]
    simp [T.uniform E hE]
  simp only [hl,sum_const,card_univ,nsmul_eq_mul,T.coordinates] at he
  nlinarith

/-- The historical support-mate equation uses the original natural weights. -/
theorem twisted_mate_equation (T : IsTwistedPlane q H) (m : Finset I → ℕ)
    (hl : ∀ x, (∑ E ∈ H, if x ∈ E then m E else 0) = k) (E : H) :
    q*m E.val + m (T.supportMate E).val = k := by
  have he : (∑ F ∈ H, m F * (E.val ∩ F).card) = (q+1)*k := by
    have hs := congrArg (fun f : I → ℕ => ∑ x ∈ E.val, f x) (funext hl)
    rw [sum_comm] at hs
    have term (F : Finset I) : (∑ x ∈ E.val, if x ∈ F then m F else 0) =
        m F * (E.val ∩ F).card := by
      rw [← sum_filter]
      simp [filter_mem_eq_inter,mul_comm]
    simpa [term,T.uniform E.val E.property] using hs
  have term (F : Finset I) (hF : F ∈ H) : m F * (E.val ∩ F).card =
      m F + (if F = E.val then q*m E.val else 0) +
        (if F = (T.supportMate E).val then m (T.supportMate E).val else 0) := by
    by_cases hf : F = E.val
    · subst F
      have hn : E.val ≠ (T.supportMate E).val := fun h =>
        T.supportMate_ne E (Subtype.ext h.symm)
      simp [T.uniform E.val E.property,hn]
      ring
    · have hs : E ≠ (⟨F,hF⟩ : H) := fun h => hf (congrArg Subtype.val h).symm
      rw [T.support_intersection E ⟨F,hF⟩ hs]
      by_cases hm : F = (T.supportMate E).val
      · have hh : (⟨F,hF⟩ : H) = T.supportMate E := Subtype.ext hm
        simp [hm,T.supportMate_ne E]
        omega
      · have hh : (⟨F,hF⟩ : H) ≠ T.supportMate E := fun h => hm (congrArg Subtype.val h)
        simp [hf,hm,hh]
  rw [sum_congr rfl term,sum_add_distrib,sum_add_distrib,
    sum_ite_eq',if_pos E.property,sum_ite_eq',if_pos (T.supportMate E).property,
    total_multiplicity T m hl] at he
  nlinarith

theorem twisted_multiplicity (hq : 4 ≤ q) (T : IsTwistedPlane q H)
    (m : Finset I → ℕ) (hl : ∀ x, (∑ E ∈ H, if x ∈ E then m E else 0) = k)
    (E : H) : (q+1)*m E.val = k := by
  have he := twisted_mate_equation T m hl E
  have hf := twisted_mate_equation T m hl (T.supportMate E)
  rw [T.supportMate_involutive E] at hf
  have hm : m E.val = m (T.supportMate E).val := by
    rcases lt_trichotomy (m E.val) (m (T.supportMate E).val) with h|h|h
    · nlinarith
    · exact h
    · nlinarith
  rw [← hm] at he
  nlinarith

end CoveringDesigns.PairDivisibility
