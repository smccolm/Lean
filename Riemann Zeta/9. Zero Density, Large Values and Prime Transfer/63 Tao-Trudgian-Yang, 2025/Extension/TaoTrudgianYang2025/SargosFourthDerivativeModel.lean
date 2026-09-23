import TaoTrudgianYang2025.SargosWithinDerivativeCalculus

/-! The actual fourth derivative is a normalized approximate model on the closed interval. -/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosFourthDerivativeModel (F : ℝ → ℝ) (σ : ℝ) (u : ℝ) : ℝ :=
  (modelPhaseJetCoefficient σ 4)⁻¹*iteratedDerivWithin 4 F phaseInterval u

theorem sargosFourthDerivativeModel_contDiffOn {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (σ : ℝ) :
    ContDiffOn ℝ ∞ (sargosFourthDerivativeModel F σ) phaseInterval :=
  contDiffOn_const.mul (sargos_contDiffOn_iteratedDerivWithin hF uniqueDiffOn_phaseInterval 4)

theorem sargosFourthDerivativeModel_iteratedDerivWithin (F : ℝ → ℝ) (σ : ℝ)
    (p : ℕ) (u : ℝ) :
    iteratedDerivWithin (p+1) (sargosFourthDerivativeModel F σ) phaseInterval u =
      (modelPhaseJetCoefficient σ 4)⁻¹*iteratedDerivWithin (p+5) F phaseInterval u := by
  unfold sargosFourthDerivativeModel
  rw [iteratedDerivWithin_const_mul_field,
    sargos_iteratedDerivWithin_comp_order]

theorem sargos_modelPhase_shift_four {σ : ℝ} (hσ : 0 < σ)
    (p : ℕ) {u : ℝ} (hu : u ∈ phaseInterval) :
    (modelPhaseJetCoefficient σ 4)⁻¹*iteratedDerivWithin (p+4) (modelPhase σ) phaseInterval u =
      iteratedDerivWithin p (modelPhase (σ+4)) phaseInterval u := by
  have hD : modelPhaseJetCoefficient σ 4 ≠ 0 := (modelPhaseJetCoefficient_pos hσ 4).ne'
  rw [iteratedDerivWithin_modelPhase σ (p+4) hu,
    iteratedDerivWithin_modelPhase (σ+4) p hu,sargos_descPochhammer_shift_four hσ.le]
  push_cast
  rw [show -σ-((p:ℝ)+4) = -(σ+4)-(p:ℝ) by ring]
  field_simp

theorem sargosFourthDerivativeModel_error {F : ℝ → ℝ} {σ : ℝ}
    (hσ : 0 < σ) (p : ℕ) {u : ℝ} (hu : u ∈ phaseInterval) :
    modelPhaseErrorAt (sargosFourthDerivativeModel F σ) (σ+4) p u =
      (modelPhaseJetCoefficient σ 4)⁻¹*modelPhaseErrorAt F σ (p+4) u := by
  rw [modelPhaseErrorAt,sargosFourthDerivativeModel_iteratedDerivWithin,
    ← sargos_modelPhase_shift_four hσ p hu,← mul_sub]
  congr 1

theorem sargosFourthDerivativeModel_approximate {F : ℝ → ℝ} {σ δ : ℝ} {P : ℕ}
    (hσ : 0 < σ) (hF : IsApproximateModelPhaseFunction F σ (P+4) δ) :
    IsApproximateModelPhaseFunction (sargosFourthDerivativeModel F σ) (σ+4) P
      (δ/modelPhaseJetCoefficient σ 4) := by
  refine ⟨sargosFourthDerivativeModel_contDiffOn hF.1 σ,?_⟩
  intro p hp u
  rw [sargosFourthDerivativeModel_error hσ p u.property,norm_mul,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (modelPhaseJetCoefficient_pos hσ 4))]
  have h := mul_le_mul_of_nonneg_left (hF.2 (p+4) (by omega) u)
    (inv_nonneg.mpr (modelPhaseJetCoefficient_pos hσ 4).le)
  simpa only [div_eq_mul_inv,mul_comm] using h

end TaoTrudgianYang2025
