import GafniTao.HeathBrownEP1LargeAlgebra

/-!
# Selecting the derivative order in Heath--Brown's large EP1 range

The source strips are consecutive but are not aligned with integer values of
`tau`.  This file makes the floor choice explicit and proves all endpoint
relations, including the boundary `tau = 13/3`.
-/

namespace GafniTao

noncomputable section

def heathBrownEP1LargeOrder (tau : ℝ) : ℕ :=
  let m := Nat.floor tau
  if tau < heathBrownEP1StripUpper (m + 1) then m + 1 else m + 2

theorem heathBrownEP1StripLower_succ_le
    {m : ℕ} (hm : 1 ≤ m) :
    heathBrownEP1StripLower (m + 1) ≤ m := by
  have hmPos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmReal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmOnePos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  unfold heathBrownEP1StripLower
  push_cast
  rw [div_le_iff₀ hmOnePos]
  ring_nf
  nlinarith

theorem heathBrownEP1StripLower_succ_succ_eq_upper_succ
    (m : ℕ) :
    heathBrownEP1StripLower (m + 2) =
      heathBrownEP1StripUpper (m + 1) := by
  unfold heathBrownEP1StripLower heathBrownEP1StripUpper
  push_cast
  ring

theorem heathBrownEP1_cast_succ_le_stripUpper_succ_succ
    (m : ℕ) :
    (m : ℝ) + 1 ≤ heathBrownEP1StripUpper (m + 2) := by
  unfold heathBrownEP1StripUpper
  rw [le_div_iff₀ (by positivity :
    (0 : ℝ) < ((m + 2 : ℕ) : ℝ) + 1)]
  push_cast
  nlinarith

theorem heathBrownEP1StripUpper_five :
    heathBrownEP1StripUpper 5 = (13 / 3 : ℝ) := by
  unfold heathBrownEP1StripUpper
  norm_num

/-- Every `tau ≥ 13/3` lies in the exact source strip selected by
`heathBrownEP1LargeOrder`; the selected order is at least six. -/
theorem heathBrownEP1LargeOrder_mem_strip
    {tau : ℝ} (htau : 13 / 3 ≤ tau) :
    6 ≤ heathBrownEP1LargeOrder tau ∧
      heathBrownEP1StripLower (heathBrownEP1LargeOrder tau) ≤ tau ∧
      tau ≤ heathBrownEP1StripUpper (heathBrownEP1LargeOrder tau) := by
  have htauNonneg : 0 ≤ tau := by linarith
  let m : ℕ := Nat.floor tau
  have hmLower : (m : ℝ) ≤ tau := by
    dsimp only [m]
    exact Nat.floor_le htauNonneg
  have hmUpper : tau < (m : ℝ) + 1 := by
    dsimp only [m]
    exact Nat.lt_floor_add_one tau
  have hmFour : 4 ≤ m := by
    dsimp only [m]
    apply Nat.le_floor
    exact_mod_cast (show (4 : ℝ) ≤ tau by linarith)
  unfold heathBrownEP1LargeOrder
  dsimp only
  change
    6 ≤ (if tau < heathBrownEP1StripUpper (m + 1) then m + 1 else m + 2) ∧
      heathBrownEP1StripLower
          (if tau < heathBrownEP1StripUpper (m + 1) then m + 1 else m + 2) ≤ tau ∧
      tau ≤ heathBrownEP1StripUpper
          (if tau < heathBrownEP1StripUpper (m + 1) then m + 1 else m + 2)
  split_ifs with hbranch
  · have hmFive : 5 ≤ m := by
      by_contra hnot
      have hmEq : m = 4 := by omega
      rw [hmEq] at hbranch
      norm_num [heathBrownEP1StripUpper_five] at hbranch
      linarith
    constructor
    · omega
    constructor
    · exact (heathBrownEP1StripLower_succ_le (show 1 ≤ m by omega)).trans
        hmLower
    · exact hbranch.le
  · constructor
    · omega
    constructor
    · rw [heathBrownEP1StripLower_succ_succ_eq_upper_succ]
      exact le_of_not_gt hbranch
    · exact hmUpper.le.trans
        (heathBrownEP1_cast_succ_le_stripUpper_succ_succ m)

#print axioms heathBrownEP1LargeOrder_mem_strip

end

end GafniTao
