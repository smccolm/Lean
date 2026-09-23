import TaoTrudgianYang2025.SargosQuarticRadiusBudget

/-! Logarithmic bounds for every rounded frequency length in the quartic source expansion. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosQuarticSharpLengths_log_budget {C N α γ l b η : ℝ}
    (hC : 0 ≤ C) (hN : 1 ≤ N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hη : 0 < η) (hl : 1 ≤ l) (hb : b ≤ 2) (hflat : l+4*η < b) :
    let L := sargosQuarticSupportLower N α γ l η
    let U := sargosQuarticSupportUpper N α γ b η
    let A := sargosQuarticPlateauLower N α γ l η
    let B := sargosQuarticPlateauUpper N α γ b η
    let R := sargosQuarticSharpRadius C N α γ l b η
    let G := Real.log (C+24)+3*Real.log (α*N^2+1)
    Real.log ((B-A-1).toNat : ℝ) ≤ G ∧
      Real.log ((L+(R : ℤ)).toNat : ℝ) ≤ G ∧
      Real.log (((R : ℤ)-U).toNat : ℝ) ≤ G := by
  intro L U A B R G
  have hK : 1 ≤ C+24 := by linarith
  have hT : 0 ≤ α*N^2 := by positivity
  have hf := sargosQuarticSharpFarLengths_le_polynomial hC hN hα hγ hη hl hb hflat
  have hi := sargosQuarticSharpInnerLength_le_polynomial hC hN hα hγ hη hl hb hflat
  exact ⟨log_nat_le_polynomial_budget hK hT hi,
    log_nat_le_polynomial_budget hK hT hf.1,
    log_nat_le_polynomial_budget hK hT hf.2⟩

end TaoTrudgianYang2025

