import Mathlib.Tactic

namespace HuxleyChartedLengthScratch

/-- The actual chart-selection mass loss forces enough selected windows
in every full original-family block. Both logarithmic budgets are kept. -/
private theorem charted_selected_blocks
    {b B c C n nSource nSelected : ℕ}
    (hc : 0 < c) (hbB : b ≤ B) (hcC : c ≤ C) (hn : 0 < n)
    (hselection : nSource ≤ 6+c*(105+17*nSelected))
    (hblocks : (6+C*(105+544*B))*n ≤ nSource) :
    32*b*n ≤ nSelected := by
  have hbudget : 6+c*(105+544*b) ≤ 6+C*(105+544*B) := by gcongr
  have hlower := (Nat.mul_le_mul_right n hbudget).trans hblocks
  have hoffset : 6+105*c ≤ (6+105*c)*n := Nat.le_mul_of_pos_right _ hn
  have hmul : c*(17*(32*b*n)) ≤ c*(17*nSelected) := by
    nlinarith only [hlower,hselection,hoffset]
  have hh := Nat.le_of_mul_le_mul_left hmul hc
  exact Nat.le_of_mul_le_mul_left hh (by decide : 0 < (17:ℕ))

/-- The chart and height-label budgets cancel from the physical unit
length. They remain in the original-family block size, not in Lunit. -/
private theorem charted_selected_source_length
    {b B c C n nSource nSelected : ℕ} {κ Cphys : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hbB : b ≤ B) (hcC : c ≤ C) (hn : 0 < n)
    (hκ : 0 < κ) (hCphys : 0 < Cphys)
    (hselection : nSource ≤ 6+c*(105+17*nSelected))
    (hblocks : (6+C*(105+544*B))*n ≤ nSource) :
    (2*κ/Cphys)*(n:ℝ) ≤ κ/(16*(b:ℝ)*Cphys)*(nSelected:ℝ) := by
  have hmass : (32:ℝ)*(b:ℝ)*(n:ℝ) ≤ (nSelected:ℝ) := by
    exact_mod_cast charted_selected_blocks hc hbB hcC hn hselection hblocks
  have hbreal : (0:ℝ) < b := Nat.cast_pos.mpr hb
  calc
    _ = κ/(16*(b:ℝ)*Cphys)*((32:ℝ)*(b:ℝ)*(n:ℝ)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

#print axioms charted_selected_blocks
#print axioms charted_selected_source_length


/-- Integer blocks of the ORIGINAL family control the selected length
and its actual cardinality; the selected family is not substituted for it. -/
private theorem charted_actual_block_normalization
    {b B c C nSource nSelected : ℕ} {κ Cphys : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hbB : b ≤ B) (hcC : c ≤ C)
    (hκ : 0 < κ) (hCphys : 0 < Cphys)
    (hselection : nSource ≤ 6+c*(105+17*nSelected))
    (hlong : 6+C*(105+544*B) ≤ nSource) :
    let m0 := 6+C*(105+544*B)
    let n := nSource/m0
    0 < n ∧ m0*n ≤ nSource ∧ nSource ≤ 2*m0*n ∧
      (2*κ/Cphys)*(n:ℝ) ≤ κ/(16*(b:ℝ)*Cphys)*(nSelected:ℝ) := by
  intro m0 n
  have hm0 : 0 < m0 := by dsimp only [m0]; omega
  have hn : 0 < n := Nat.div_pos hlong hm0
  have hlower : m0*n ≤ nSource := Nat.mul_div_le nSource m0
  have hupper : nSource ≤ 2*m0*n := by
    have he := Nat.div_add_mod nSource m0
    have hr := Nat.mod_lt nSource hm0
    have hm : m0 ≤ m0*n := Nat.le_mul_of_pos_right m0 hn
    change m0*n+nSource % m0=nSource at he
    nlinarith only [he,hr,hm]
  exact ⟨hn,hlower,hupper,
    charted_selected_source_length hb hc hbB hcC hn hκ hCphys hselection hlower⟩

#print axioms charted_actual_block_normalization

end HuxleyChartedLengthScratch
