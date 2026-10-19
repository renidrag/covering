import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.ModEq

/-! Universal integer capacities; no parameter enumeration. -/
namespace CoveringDesigns.TwoKMinusTwo

def capacity (k : ℕ) : ℕ := k*k/4

theorem product_le_capacity {a b k : ℕ} (h : a+b ≤ k) : a*b ≤ capacity k := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr
  have hs : (a : ℤ) + b ≤ k := by exact_mod_cast h
  have hab : (a : ℤ)*b*4 ≤ (k : ℤ)*k := by
    nlinarith [sq_nonneg ((a : ℤ)-(b : ℤ)), sq_nonneg ((k : ℤ)-(a+b))]
  exact_mod_cast hab

theorem capacity_even (r : ℕ) : capacity (2*r) = r*r := by
  unfold capacity
  have h : 2*r*(2*r) = r*r*4 := by ring
  rw [h, Nat.mul_div_cancel]
  decide

theorem capacity_odd (r : ℕ) : capacity (2*r+1) = r*(r+1) := by
  unfold capacity
  have h : (2*r+1)*(2*r+1) = 1 + r*(r+1)*4 := by ring
  rw [h, Nat.add_mul_div_right]
  · omega
  · decide

theorem capacity_step {k : ℕ} (hk : 1 ≤ k) :
    capacity k = capacity (k-1) + k/2 := by
  have hm := Nat.mod_lt k (by decide : 0 < 2)
  have he := Nat.mod_add_div k 2
  rcases (show k%2=0 ∨ k%2=1 by omega) with h | h
  · have hk' : k = 2*(k/2) := by omega
    have hr : 1 ≤ k/2 := by omega
    have hp : k-1 = 2*(k/2-1)+1 := by omega
    rw [hp, capacity_odd, hk', capacity_even]
    have hd : 2*(k/2)/2 = k/2 := by omega
    rw [hd]
    nlinarith [Nat.sub_add_cancel hr]
  · have hk' : k = 2*(k/2)+1 := by omega
    have hp : k-1 = 2*(k/2) := by omega
    rw [hp, capacity_even, hk', capacity_odd]
    have hd : (2*(k/2)+1)/2 = k/2 := by omega
    rw [hd]
    ring

theorem link_capacity_strict {k : ℕ} (hk : 9 ≤ k) :
    3*capacity (k-1) < (k-2)*(k-2) := by
  have hm := Nat.mod_lt k (by decide : 0 < 2)
  have he := Nat.mod_add_div k 2
  rcases (show k%2=0 ∨ k%2=1 by omega) with h | h
  · have hr : 5 ≤ k/2 := by omega
    have hp : k-1 = 2*(k/2-1)+1 := by omega
    rw [hp, capacity_odd]
    have hz : k/2-1+1 = k/2 := by omega
    rw [hz]
    have hs : k-2 = 2*(k/2-1) := by omega
    rw [hs]
    nlinarith
  · have hr : 4 ≤ k/2 := by omega
    have hp : k-1 = 2*(k/2) := by omega
    rw [hp, capacity_even]
    have hs : k-2+1 = 2*(k/2) := by omega
    nlinarith [sq_nonneg (k/2-4 : ℤ)]

theorem endpoint_budget {u w r : ℕ} (hu : 4 ≤ u) (hw : 4 ≤ w)
    (hur : u ≤ r) (hwr : w ≤ r) : u*w+8*r ≤ r*(u+w)+16 := by
  have huZ : (4 : ℤ) ≤ u := by exact_mod_cast hu
  have hwZ : (4 : ℤ) ≤ w := by exact_mod_cast hw
  have hwrZ : (w : ℤ) ≤ r := by exact_mod_cast hwr
  have hrZ : (4 : ℤ) ≤ r := by omega
  have hp := mul_nonneg (sub_nonneg.mpr huZ) (sub_nonneg.mpr hwrZ)
  have hq := mul_nonneg (sub_nonneg.mpr hrZ) (sub_nonneg.mpr hwZ)
  have hz : (u : ℤ)*w+8*r ≤ (r : ℤ)*(u+w)+16 := by nlinarith
  exact_mod_cast hz

theorem capacity_twelve_impossible {k : ℕ} (hk : 17 ≤ k)
    (hs : 3*(k-2)*(k-2)+8*(k/2) ≤ 10*capacity k+16) : False := by
  have hm := Nat.mod_lt k (by decide : 0 < 2)
  have he := Nat.mod_add_div k 2
  rcases (show k%2=0 ∨ k%2=1 by omega) with h | h
  · have hr : 9 ≤ k/2 := by omega
    have hp : k = 2*(k/2) := by omega
    rw [hp, capacity_even] at hs
    have hd : 2*(k/2)/2=k/2 := by omega
    rw [hd] at hs
    have ht : 2*(k/2)-2+2=2*(k/2) := by omega
    nlinarith
  · have hr : 8 ≤ k/2 := by omega
    have hp : k = 2*(k/2)+1 := by omega
    rw [hp, capacity_odd] at hs
    have hd : (2*(k/2)+1)/2=k/2 := by omega
    rw [hd] at hs
    have ht : (2*(k/2)+1)-2+1=2*(k/2) := by omega
    nlinarith

theorem capacity_thirteen_impossible {k : ℕ} (hk : 33 ≤ k)
    (hs : 3*(k-2)*(k-2)+8*(k/2) ≤ 11*capacity k+16) : False := by
  have hm := Nat.mod_lt k (by decide : 0 < 2)
  have he := Nat.mod_add_div k 2
  rcases (show k%2=0 ∨ k%2=1 by omega) with h | h
  · have hr : 17 ≤ k/2 := by omega
    have hp : k = 2*(k/2) := by omega
    rw [hp, capacity_even] at hs
    have hd : 2*(k/2)/2=k/2 := by omega
    rw [hd] at hs
    have ht : 2*(k/2)-2+2=2*(k/2) := by omega
    nlinarith
  · have hr : 16 ≤ k/2 := by omega
    have hp : k = 2*(k/2)+1 := by omega
    rw [hp, capacity_odd] at hs
    have hd : (2*(k/2)+1)/2=k/2 := by omega
    rw [hd] at hs
    have ht : (2*(k/2)+1)-2+1=2*(k/2) := by omega
    nlinarith

end CoveringDesigns.TwoKMinusTwo
