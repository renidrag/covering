import CoveringDesigns.Qk_K_2.Determinant
import CoveringDesigns.PairDivisibility

namespace CoveringDesigns.Qk_K_2
open PairEquality PairDivisibility

/-- Integer interval check, entirely reduced and proved in the kernel. -/
theorem nonsquare_seven (d : ℤ) : d^2 ≠ (6 : ℤ)^28 * 8^29 := by
  intro h
  have he : |d|^2 = (950264780777977979756873143073558390802688770048 : ℤ) := by simpa using h
  have hp : 0 ≤ |d| := abs_nonneg d
  by_cases hb : |d| ≤ 974815254690845500084678
  · nlinarith
  · have hb' : 974815254690845500084679 ≤ |d| := by omega
    nlinarith

theorem no_twisted_seven {I : Type*} [Fintype I] [DecidableEq I]
    {H : Finset (Finset I)} (T : IsTwistedPlane 7 H) : False :=
  exclude_twisted (by decide) nonsquare_seven T

/-- Integer interval check, entirely reduced and proved in the kernel. -/
theorem nonsquare_nine (d : ℤ) : d^2 ≠ (8 : ℤ)^45 * 10^46 := by
  intro h
  have he : |d|^2 = (435561429658801233233119497512663310663680000000000000000000000000000000000000000000000 : ℤ) := by simpa using h
  have hp : 0 ≤ |d| := abs_nonneg d
  by_cases hb : |d| ≤ 20870108520532451539759314890004013390213242
  · nlinarith
  · have hb' : 20870108520532451539759314890004013390213243 ≤ |d| := by omega
    nlinarith

theorem no_twisted_nine {I : Type*} [Fintype I] [DecidableEq I]
    {H : Finset (Finset I)} (T : IsTwistedPlane 9 H) : False :=
  exclude_twisted (by decide) nonsquare_nine T

/-- A supplied exclusion, independent of field existence, improves the indexed floor. -/
theorem indexed_exclusion {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] {q k : ℕ} {B : I → Finset X}
    (hq : 4 ≤ q) (hk : q ≤ k) (hv : Fintype.card X = q*k)
    (hB : Multicover.IsCover B k 2 1) (hnd : ¬ q ∣ k)
    (hn : ∀ {H : Finset (Finset I)}, IsTwistedPlane q H → False) : q*(q+1)+1 ≤ Fintype.card I := by
  have hf := incidence_floor hq hk hv hB
  have he : Fintype.card I ≠ q*(q+1) := by
    intro hi
    have T := (twisted_of_not_dvd hq hk hv hi hB hnd).1
    exact hn T
  omega

end CoveringDesigns.Qk_K_2
