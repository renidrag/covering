import CoveringDesigns.TwoKMinusTwo.Arithmetic

/-! Scalar capacity exclusions, proved on infinite parameter ranges.
Formalisation: Rob Gardiner, with AI assistance. -/
namespace CoveringDesigns.TwoKMinusCGeneral
open TwoKMinusTwo

theorem link_capacity_strict {c k : ℕ} (hc : 2 ≤ c) (hk : 8*c ≤ k+7) :
    3*capacity (k-1) < (k-c)*(k-c) := by
  have hck : c ≤ k := by omega
  have hk1 : 1 ≤ k := by omega
  have hf : 4*capacity (k-1) ≤ (k-1)*(k-1) := by
    simpa [capacity, Nat.mul_comm] using Nat.div_mul_le_self ((k-1)*(k-1)) 4
  have he : k-c+c=k := Nat.sub_add_cancel hck
  have he1 : k-1+1=k := Nat.sub_add_cancel hk1
  have hshift : 0 ≤ (k : ℤ)+7-8*c := by omega
  have hprod := mul_nonneg hshift (show (0 : ℤ) ≤ 8*((c : ℤ)-1) by omega)
  have hsq := sq_nonneg ((k : ℤ)+7-8*c)
  have hpos : 0 < ((c : ℤ)-1)^2 := by nlinarith
  have hstrict : 3*((k : ℤ)-1)^2 < 4*((k : ℤ)-c)^2 := by nlinarith
  have hfZ : 4*(capacity (k-1) : ℤ) ≤ ((k : ℤ)-1)^2 := by
    exact_mod_cast (show 4*capacity (k-1) ≤ (k-1)^2 by nlinarith)
  have hz : 3*(capacity (k-1) : ℤ) < ((k : ℤ)-c)^2 := by linarith
  have hs : ((k-c : ℕ) : ℤ) = (k : ℤ)-c := by omega
  rw [← hs] at hz
  simpa only [pow_two] using (show 3*capacity (k-1) < (k-c)^2 by exact_mod_cast hz)

theorem capacity_uniform_impossible {c k : ℕ} (hc : 2 ≤ c) (hk : 25*c ≤ k)
    (hs : 3*(k-c)*(k-c) ≤ 11*capacity k+30*capacity c) : False := by
  have hfk : 4*capacity k ≤ k*k := by
    simpa [capacity, Nat.mul_comm] using Nat.div_mul_le_self (k*k) 4
  have hfc : 4*capacity c ≤ c*c := by
    simpa [capacity, Nat.mul_comm] using Nat.div_mul_le_self (c*c) 4
  have hsub : k-c+c=k := Nat.sub_add_cancel (by omega)
  have hprod := Nat.mul_le_mul_left (26*c) hk
  nlinarith [sq_nonneg ((k : ℤ)-25*c)]

theorem endpoint_budget_three {u w r : ℕ} (hu : 4 ≤ u) (hw : 4 ≤ w)
    (hs : u+w ≤ 11) (hr : 28 ≤ r) : 2*u*w+8*r ≤ r*(u+w)+32 := by
  have hp := mul_nonneg (show (0 : ℤ) ≤ (u : ℤ)-4 by omega)
    (show (0 : ℤ) ≤ (r : ℤ)-2*w by omega)
  have hq := mul_nonneg (show (0 : ℤ) ≤ (w : ℤ)-4 by omega)
    (show (0 : ℤ) ≤ (r : ℤ)-8 by omega)
  have hz : 2*(u : ℤ)*w+8*r ≤ (r : ℤ)*(u+w)+32 := by nlinarith
  exact_mod_cast hz

theorem capacity_three_impossible {k : ℕ} (hk : 57 ≤ k)
    (hs : 3*(k-3)*(k-3)+8*(k/2) ≤ 11*capacity k+32) : False := by
  have hm := Nat.mod_lt k (by decide : 0 < 2)
  have he := Nat.mod_add_div k 2
  rcases (show k%2=0 ∨ k%2=1 by omega) with h | h
  · have hr : 29 ≤ k/2 := by omega
    have hp : k = 2*(k/2) := by omega
    rw [hp, capacity_even] at hs
    have hd : 2*(k/2)/2=k/2 := by omega
    rw [hd] at hs
    have ht : 2*(k/2)-3+3=2*(k/2) := by omega
    nlinarith [sq_nonneg ((k/2 : ℕ) : ℤ)]
  · have hr : 28 ≤ k/2 := by omega
    have hp : k = 2*(k/2)+1 := by omega
    rw [hp, capacity_odd] at hs
    have hd : (2*(k/2)+1)/2=k/2 := by omega
    rw [hd] at hs
    have ht : (2*(k/2)+1)-3+2=2*(k/2) := by omega
    nlinarith [sq_nonneg ((k/2 : ℕ) : ℤ)]

end CoveringDesigns.TwoKMinusCGeneral
