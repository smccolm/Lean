import Dubon2026.SourceIntegralSlashCuspSubgroup
import Dubon2026.SourceGammaOneFourierLinear
import Dubon2026.SourceGammaOneModularStretchCoefficients
import Dubon2026.SourceGammaOneCuspAuxiliaryForm

/-! DUB-17/18 -> original Gamma1 degree/genus -> reduced field action
-> uniform level-power slash integrality. The actual arbitrary-cusp
chart is a Gamma1(M^2) modular form. Native translated holomorphy,
boundedness, principal-congruence periods and coefficient uniqueness
give its exact width-one expansion from the original width-M series. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open Function UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Pointwise

theorem cusp_strictPeriod (M : ℕ) (β : SL(2, ℤ)) :
    (M : ℝ) ∈ (ConjAct.toConjAct (β : GL (Fin 2) ℝ)⁻¹ •
      (Gamma1 M : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  apply GammaOne.CuspAuxiliary.natCast_mem_strictPeriods_conj M _ β
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem hasSum_cusp (f : ModularForm (Gamma1 M) k) (β : SL(2, ℤ)) (τ : ℍ) :
    HasSum (fun n : ℕ => (qExpansion (M : ℝ)
      ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))).coeff n •
        Periodic.qParam (M : ℝ) τ ^ n)
      (((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) τ) := by
  let F := ModularForm.translate f (β : GL (Fin 2) ℝ)
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)
  letI : Fact (IsCusp OnePoint.infty
      (ConjAct.toConjAct (β : GL (Fin 2) ℝ)⁻¹ •
        (Gamma1 M : Subgroup (GL (Fin 2) ℝ)))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods hM (cusp_strictPeriod M β)⟩
  exact hasSum_qExpansion hM
    (SlashInvariantFormClass.periodic_comp_ofComplex F (cusp_strictPeriod M β))
    F.holo' (ModularFormClass.bdd_at_infty F) τ

/-- The actual arbitrary-cusp chart at level M squared. -/
def cuspChart (f : ModularForm (Gamma1 M) k) (β : SL(2, ℤ)) :
    ModularForm (Gamma1 (M ^ 2)) k :=
  ModularNormPolynomial.restrict (Gamma1_sq_le_conj_cusp M β)
    (ModularForm.translate f ((β : GL (Fin 2) ℝ) * levelRaiseMatrix M))

theorem coe_cuspChart (f : ModularForm (Gamma1 M) k) (β : SL(2, ℤ)) :
    (⇑(cuspChart f β) : ℍ → ℂ) =
      (⇑f : ℍ → ℂ) ∣[k] ((β : GL (Fin 2) ℝ) * levelRaiseMatrix M) := rfl

theorem slash_levelRaise_apply (M : ℕ) [NeZero M] (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] levelRaiseMatrix M) τ =
      (M : ℂ) ^ (k - 1) * f (levelRaiseMatrix M • τ) := by
  rw [ModularForm.slash_apply, σ_levelRaiseMatrix, ContinuousAlgEquiv.refl_apply,
    abs_levelRaiseMatrix_det_val, denom_levelRaiseMatrix, one_zpow, mul_one,
    Complex.ofReal_natCast]
  ring

theorem cuspChart_apply (f : ModularForm (Gamma1 M) k) (β : SL(2, ℤ)) (τ : ℍ) :
    cuspChart f β τ = (M : ℂ) ^ (k - 1) *
      ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ)) (levelRaiseMatrix M • τ) := by
  rw [coe_cuspChart, SlashAction.slash_mul, slash_levelRaise_apply]

theorem qParam_levelRaise_smul (M : ℕ) [NeZero M] (τ : ℍ) :
    Periodic.qParam (M : ℝ) ((levelRaiseMatrix M • τ : ℍ) : ℂ) =
      Periodic.qParam 1 τ := by
  rw [coe_levelRaiseMatrix_smul]
  simp only [Periodic.qParam, Complex.ofReal_natCast, Complex.ofReal_one, div_one]
  congr 1
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne M)]

theorem coeff_qExpansion_cuspChart (f : ModularForm (Gamma1 M) k)
    (β : SL(2, ℤ)) (n : ℕ) :
    (qExpansion 1 (cuspChart f β)).coeff n = (M : ℂ) ^ (k - 1) *
      (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))).coeff n := by
  have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ =>
      ((M : ℂ) ^ (k - 1) *
        (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (β : GL (Fin 2) ℝ))).coeff m) •
          Periodic.qParam 1 τ ^ m) (cuspChart f β τ) := by
    intro τ
    have hs := (hasSum_cusp f β (levelRaiseMatrix M • τ)).mul_left ((M : ℂ) ^ (k - 1))
    rw [qParam_levelRaise_smul, ← cuspChart_apply] at hs
    convert hs using 1
    funext m
    simp only [smul_eq_mul]
    ring
  exact (ModularFormClass.qExpansion_coeff_unique one_pos
    (SourceFricke.gammaOne_one_mem_strictPeriods (M ^ 2)) hsum n).symm

end
end Dubon2026.SourceFunctionField.IntegralSlash
