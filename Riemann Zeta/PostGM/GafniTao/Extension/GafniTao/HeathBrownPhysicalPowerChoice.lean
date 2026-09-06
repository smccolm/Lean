import GafniTao.HeathBrownPowerChoice

/-!
# Physical form of the Heath--Brown power choice

The asymptotic notation `tau = log B / log N` is avoided here.  Its exact
content on the source window `2 ≤ tau ≤ 4` is the pair of inequalities
`N^2 ≤ B ≤ N^4`.  The selected power is two or three according as
`B ≤ N^3`, and the finite dyadic colouring factor is retained explicitly.
-/

namespace GafniTao

noncomputable section

/-- Physical two-or-three choice, equivalent to `heathBrownLowPower` after
passing to logarithmic scales. -/
def heathBrownPhysicalLowPower (N : Nat) (B : Real) : Nat :=
  if B ≤ (N : Real) ^ 3 then 2 else 3

theorem heathBrownPhysicalLowPower_eq_two_or_three (N : Nat) (B : Real) :
    heathBrownPhysicalLowPower N B = 2 ∨
      heathBrownPhysicalLowPower N B = 3 := by
  by_cases h : B ≤ (N : Real) ^ 3
  · left
    simp [heathBrownPhysicalLowPower, h]
  · right
    simp [heathBrownPhysicalLowPower, h]

theorem heathBrownPhysicalLowPower_pos (N : Nat) (B : Real) :
    0 < heathBrownPhysicalLowPower N B := by
  rcases heathBrownPhysicalLowPower_eq_two_or_three N B with h | h <;>
    simp [h]

/-- The energy-producing powered length starts below the physical height. -/
theorem heathBrownPhysicalLowPower_base_le_height
    {N : Nat} {B : Real} (hLower : (N : Real) ^ 2 ≤ B) :
    (N : Real) ^ heathBrownPhysicalLowPower N B ≤ B := by
  by_cases h : B ≤ (N : Real) ^ 3
  · simpa [heathBrownPhysicalLowPower, h] using hLower
  · have hThree : (N : Real) ^ 3 < B := lt_of_not_ge h
    simpa [heathBrownPhysicalLowPower, h] using hThree.le

/-- The physical height is below the companion `(p+1)`-st power. -/
theorem heathBrownPhysicalLowPower_height_le_companion
    {N : Nat} {B : Real} (hUpper : B ≤ (N : Real) ^ 4) :
    B ≤ (N : Real) ^ (heathBrownPhysicalLowPower N B + 1) := by
  by_cases h : B ≤ (N : Real) ^ 3
  · simp only [heathBrownPhysicalLowPower, if_pos h, Nat.reduceAdd]
    exact h
  · simp only [heathBrownPhysicalLowPower, if_neg h, Nat.reduceAdd]
    exact hUpper

/-- Exact polynomial form of the upper powered-scale bound
`tau/p ≤ 3/2`. -/
theorem heathBrownPhysicalLowPower_height_sq_le_base_cube
    {N : Nat} {B : Real} (hN : 1 ≤ N)
    (hLower : (N : Real) ^ 2 ≤ B) (hUpper : B ≤ (N : Real) ^ 4) :
    B ^ 2 ≤
      ((N : Real) ^ heathBrownPhysicalLowPower N B) ^ 3 := by
  have hNReal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNNonneg : (0 : Real) ≤ N := zero_le_one.trans hNReal
  have hBNonneg : 0 ≤ B := (pow_nonneg hNNonneg 2).trans hLower
  by_cases h : B ≤ (N : Real) ^ 3
  · have hsq := pow_le_pow_left₀ hBNonneg h 2
    simpa [heathBrownPhysicalLowPower, h, ← pow_mul] using hsq
  · have hsq := pow_le_pow_left₀ hBNonneg hUpper 2
    have hEightNine : (N : Real) ^ 8 ≤ (N : Real) ^ 9 :=
      pow_le_pow_right₀ hNReal (by omega)
    have : B ^ 2 ≤ (N : Real) ^ 9 := by
      calc
        B ^ 2 ≤ ((N : Real) ^ 4) ^ 2 := hsq
        _ = (N : Real) ^ 8 := by rw [← pow_mul]
        _ ≤ (N : Real) ^ 9 := hEightNine
    simpa [heathBrownPhysicalLowPower, h, ← pow_mul] using this

/-- Every dyadic block selected from the `p`-th power fits in the explicit
ambient height `8B`; this is where the finite colouring factor enters. -/
theorem heathBrownPhysicalLowPower_selected_length_le
    {N r : Nat} {B : Real} (hLower : (N : Real) ^ 2 ≤ B)
    (hr : r < heathBrownPhysicalLowPower N B) :
    (2 ^ r * N ^ heathBrownPhysicalLowPower N B : Nat) ≤
      Nat.floor (8 * B) := by
  have hBNonneg : 0 ≤ B := by
    have hNNonneg : (0 : Real) ≤ N := by positivity
    exact (pow_nonneg hNNonneg 2).trans hLower
  have hBase := heathBrownPhysicalLowPower_base_le_height hLower
  have hpCases := heathBrownPhysicalLowPower_eq_two_or_three N B
  have hTwoR : ((2 ^ r : Nat) : Real) ≤ 8 := by
    rcases hpCases with hp | hp
    · have : r < 2 := by simpa [hp] using hr
      interval_cases r <;> norm_num
    · have : r < 3 := by simpa [hp] using hr
      interval_cases r <;> norm_num
  apply Nat.le_floor
  push_cast
  have hTwoRReal : (2 : Real) ^ r ≤ 8 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hTwoR
  exact mul_le_mul hTwoRReal hBase (pow_nonneg (by positivity) _)
    (by norm_num)

#print axioms heathBrownPhysicalLowPower_base_le_height
#print axioms heathBrownPhysicalLowPower_height_le_companion
#print axioms heathBrownPhysicalLowPower_height_sq_le_base_cube
#print axioms heathBrownPhysicalLowPower_selected_length_le

end

end GafniTao
