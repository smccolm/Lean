import Dubon2026.SourceSiegelNormalizedProduct

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> exact integral Siegel expansion.
Consume the actual residue reindexing and actual polynomial products to
identify their analytic limit with the normalized literal Siegel function.
The stabilized finite-product coefficients then supply its exact HasSum;
integrality and the level-cleared leading inverse are proved separately.
The native Taylor route replaces the source candidate's formal product W.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion
noncomputable section
open Complex Polynomial Filter Topology
open scoped Real

/-- The actual stabilized finite-product coefficients of the normalized Siegel factor. -/
def coef (N r : ℕ) (s : ℤ) (m : ℕ) : ℂ :=
  (if r = 0 then 1 - zeta N s else 1) * stableCoeff (Pc N r (zeta N s) (zeta N s)⁻¹) m

theorem hasSum_coef (N : ℕ) (hN : 0 < N) (r : ℕ) (hr : r < N) (s : ℤ) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => coef N r s m * qN N τ ^ m)
      (siegelFun N r s (τ : ℂ) /
        (-cexp (π * I * (s : ℂ) * (((r : ℤ) : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
          cexp (2 * π * I * (6 * ((r : ℤ) : ℂ) ^ 2 - 6 * ((r : ℤ) : ℂ) * (N : ℂ) + (N : ℂ) ^ 2) * (τ : ℂ) /
            (12 * (N : ℂ) ^ 2)))) := by
  rw [siegelFun_div_eq N hN r hr s τ, ← polynomial_product_eq_streams N r hr _ _ (norm_qN_lt_one N hN τ)]
  simp_rw [coef, mul_assoc]
  exact (hasSum_stableCoeff (Pc N r (zeta N s) (zeta N s)⁻¹)
    (Pc_coeff_zero N r _ _) 3 (by norm_num)
    (Pc_norm_bound N r (norm_zeta N s).le (norm_zeta_inv N s).le)
    (norm_qN_lt_one N hN τ)).mul_left _

theorem isIntegral_coef (N : ℕ) (hN : 0 < N) (r : ℕ) (s : ℤ) (m : ℕ) : IsIntegral ℤ (coef N r s m) := by
  unfold coef
  refine IsIntegral.mul ?_ (isIntegral_stableCoeff N r (isIntegral_zeta N hN s) (isIntegral_zeta_inv N hN s) m)
  split_ifs
  · exact isIntegral_one.sub (isIntegral_zeta N hN s)
  · exact isIntegral_one

theorem coef_zero (N r : ℕ) (s : ℤ) : coef N r s 0 = if r = 0 then 1 - zeta N s else 1 := by
  rw [coef, stableCoeff_zero,
    mul_one]

theorem isIntegral_N_mul_inv_coef_zero (N : ℕ) (hN : 0 < N) (r : ℕ) (s : ℤ)
    (hs : r = 0 → ¬ (N : ℤ) ∣ s) : IsIntegral ℤ ((N : ℂ) * (coef N r s 0)⁻¹) := by
  rw [coef_zero]
  split_ifs with h
  · exact isIntegral_N_mul_inv_one_sub N (zeta N s) (isIntegral_zeta N hN s) (zeta_pow N hN s)
      (zeta_ne_one N hN s (hs h))
  · rw [inv_one, mul_one]
    have hN1 : IsIntegral ℤ ((N : ℤ) : ℂ) := isIntegral_algebraMap
    exact_mod_cast hN1


end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion
