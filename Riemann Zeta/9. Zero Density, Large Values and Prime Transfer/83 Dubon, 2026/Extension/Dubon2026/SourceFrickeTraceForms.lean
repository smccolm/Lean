import Dubon2026.SourceFrickeTraceSubgroup
import Dubon2026.SourceModularNormPolynomial
import Dubon2026.SourceIntegralTraceModularForm
import Dubon2026.SourceGammaOneFourierLinear

/-! DUB-17/18 -> original Gamma1 degree/genus -> level-power slash
integrality -> trace application. Construct the two actual forms on
the S-conjugate subgroup and identify their Fourier coefficients.
Native subgroup restriction, triangular Hecke slash, strict periods,
coefficient uniqueness and even-weight negation replace duplicate
infrastructure. No coefficient identity is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_fricke_coeff. -/
namespace Dubon2026.SourceFunctionField.IntegralFricke
noncomputable section
open UpperHalfPlane CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Pointwise
local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
variable {N : ℕ} [NeZero N] {k w : ℤ}

/-- The actual diagonal transform obtained from Fricke followed by inverse S. -/
def g₀ (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  frickeMatrix N * ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹

/-- The input modular form translated to the trace subgroup. -/
def Gform (f : ModularForm Γ₁(N) k) :
    ModularForm ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
  ModularNormPolynomial.restrict (GammaS_le_conj_g₀ N) (ModularForm.translate f (g₀ N))

theorem coe_Gform (f : ModularForm Γ₁(N) k) :
    (⇑(Gform f) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] g₀ N := rfl

/-- The constructed peaked auxiliary translated to the same trace subgroup. -/
def Thetaform (ϑ : ModularForm Γ₁(N) w) :
    ModularForm ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w :=
  ModularNormPolynomial.restrict (GammaS_le_conjS N)
    (ModularForm.translate ϑ ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))

omit [NeZero N] in
theorem coe_Thetaform (ϑ : ModularForm Γ₁(N) w) :
    (⇑(Thetaform ϑ) : ℍ → ℂ) =
      (⇑ϑ : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) := rfl

theorem g₀_eq_diagonal : g₀ N = heckeTriangularMatrix 1 N 0 := by
  rw [g₀, mul_inv_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, frickeMatrix_val,
    heckeTriangularMatrix_val]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.S]

theorem qParam_diagonal_smul (τ : ℍ) :
    Periodic.qParam 1 ((heckeTriangularMatrix 1 N 0 • τ : ℍ) : ℂ) =
      Periodic.qParam (N : ℝ) τ := by
  rw [heckeTriangularMatrix_smul]
  simp only [Periodic.qParam]
  congr 1
  simp [heckeUpperPoint, coe_levelRaiseMatrix_smul]
  ring

theorem coeff_qExpansion_Gform (f : ModularForm Γ₁(N) k) (n : ℕ) :
    (qExpansion (N : ℝ) (⇑(Gform f) : ℍ → ℂ)).coeff n =
      ((N : ℂ))⁻¹ * (qExpansion 1 (⇑f : ℍ → ℂ)).coeff n := by
  let c : ℕ → ℂ := fun n => ((N : ℂ))⁻¹ * (qExpansion 1 (⇑f : ℍ → ℂ)).coeff n
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam (N : ℝ) τ ^ m) (Gform f τ) := by
    intro τ
    have h1 := hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f (SourceFricke.gammaOne_one_mem_strictPeriods N))
      f.holo' (ModularFormClass.bdd_at_infty f) (heckeTriangularMatrix 1 N 0 • τ)
    have h2 := h1.mul_left ((N : ℂ))⁻¹
    have happ : (Gform f : ℍ → ℂ) τ =
        ((N : ℂ))⁻¹ * f (heckeTriangularMatrix 1 N 0 • τ) := by
      rw [coe_Gform, g₀_eq_diagonal, heckeTriangular_slash_apply, heckeTriangularMatrix_smul]
      simp
    rw [happ]
    convert h2 using 1
    ext m
    rw [qParam_diagonal_smul]
    simp only [c, smul_eq_mul]
    ring
  exact (ModularFormClass.qExpansion_coeff_unique (Nat.cast_pos.mpr (NeZero.pos N))
    (natCast_mem_strictPeriods_GammaS N) hsum n).symm

theorem Gform_slash_S (f : ModularForm Γ₁(N) k) :
    (⇑(Gform f) : ℍ → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (⇑f : ℍ → ℂ) ∣[k] frickeMatrix N := by
  rw [coe_Gform, ← SlashAction.slash_mul, g₀, inv_mul_cancel_right]

omit [NeZero N] in
theorem Thetaform_slash_S (hw : Even w) (ϑ : ModularForm Γ₁(N) w) :
    (⇑(Thetaform ϑ) : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (⇑ϑ : ℍ → ℂ) := by
  have hmul : ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ((ModularGroup.S * ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) :=
    (map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) ModularGroup.S ModularGroup.S).symm
  rw [coe_Thetaform, ← SlashAction.slash_mul, hmul, SourceSL2Cocycle.S_mul_S]
  change (⇑ϑ : ℍ → ℂ) ∣[w] (-1 : SL(2, ℤ)) = _
  rw [IntegralTrace.slash_neg_even hw, SlashAction.slash_one]

omit [NeZero N] in
theorem Thetaform_slash (ϑ : ModularForm Γ₁(N) w) (β : SL(2, ℤ)) :
    (⇑(Thetaform ϑ) : ℍ → ℂ) ∣[w] (β : GL (Fin 2) ℝ) =
      (⇑ϑ : ℍ → ℂ) ∣[w] ((ModularGroup.S * β : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [coe_Thetaform, ← SlashAction.slash_mul]
  exact congrArg (fun γ : GL (Fin 2) ℝ => (⇑ϑ : ℍ → ℂ) ∣[w] γ)
    (map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) ModularGroup.S β).symm

end
end Dubon2026.SourceFunctionField.IntegralFricke
