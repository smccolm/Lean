import GafniTao.HeathBrownExponentRelation

/-!
# The two-or-three power choice in the low Heath--Brown cells

For a physical logarithmic scale `tau` in `[2,4]`, the source chooses the
power `p=2` on `[2,3]` and `p=3` on `(3,4]`.  The `p`-th powered scale then
lies in `[1,3/2]`, while the companion `(p+1)`-st scale is at most one.
-/

namespace GafniTao

/-- The literal power selected in the low/middle Heath--Brown argument. -/
noncomputable def heathBrownLowPower (tau : Real) : Nat :=
  if tau ≤ 3 then 2 else 3

theorem heathBrownLowPower_eq_two_or_three (tau : Real) :
    heathBrownLowPower tau = 2 ∨ heathBrownLowPower tau = 3 := by
  by_cases h : tau ≤ 3
  · left
    simp [heathBrownLowPower, h]
  · right
    simp [heathBrownLowPower, h]

theorem heathBrownLowPower_pos (tau : Real) :
    0 < heathBrownLowPower tau := by
  rcases heathBrownLowPower_eq_two_or_three tau with h | h <;> simp [h]

/-- Exact source scale window for the energy-producing `p`-th power. -/
theorem heathBrownLowPower_scale_window
    {tau : Real} (htauLower : 2 ≤ tau) (htauUpper : tau ≤ 4) :
    1 ≤ tau / (heathBrownLowPower tau : Real) ∧
      tau / (heathBrownLowPower tau : Real) ≤ 3 / 2 := by
  by_cases h : tau ≤ 3
  · simp only [heathBrownLowPower, if_pos h, Nat.cast_ofNat]
    constructor <;> norm_num <;> linarith
  · have htauThree : 3 < tau := lt_of_not_ge h
    simp only [heathBrownLowPower, if_neg h, Nat.cast_ofNat]
    constructor <;> norm_num <;> linarith

/-- The companion `(p+1)`-st power lies in the ordinary mean-value range. -/
theorem heathBrownLowPower_companion_scale
    {tau : Real} (htauUpper : tau ≤ 4) :
    tau / ((heathBrownLowPower tau + 1 : Nat) : Real) ≤ 1 := by
  by_cases h : tau ≤ 3
  · simp only [heathBrownLowPower, if_pos h, Nat.reduceAdd, Nat.cast_ofNat]
    exact (div_le_one (by norm_num : (0 : Real) < 3)).2 h
  · simp only [heathBrownLowPower, if_neg h, Nat.reduceAdd, Nat.cast_ofNat]
    exact (div_le_one (by norm_num : (0 : Real) < 4)).2 htauUpper

/-- The selected power and its companion are both positive. -/
theorem heathBrownLowPower_companion_pos (tau : Real) :
    0 < heathBrownLowPower tau + 1 := by
  omega

#print axioms heathBrownLowPower_scale_window
#print axioms heathBrownLowPower_companion_scale

end GafniTao
