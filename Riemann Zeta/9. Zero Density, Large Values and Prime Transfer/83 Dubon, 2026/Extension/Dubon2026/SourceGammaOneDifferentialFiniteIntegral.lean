import Dubon2026.SourceJEulerPolynomial
import Dubon2026.SourceGammaOneRatioClosure
import Dubon2026.SourceModularQuotientIntegral

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> all-weight arithmetic
association -> finite Gamma1 character realization -> Picard/H1 comparison ->
regular differential/cusp comparison. The exact q-Euler normalization and
the existing modular norm theorem prove the finite-coordinate integral
bound for an actual weight-two cusp form. No integral equation is assumed.
Selected source: anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_mul_thetaL_eq_qExpansion_of_finiteIndex. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane ModularForm SourceDifferential
open scoped MatrixGroups

theorem isIntegral_cusp_differential_finite_expression
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) (Y : LaurentSeries ℂ)
    (hY : Y * qEuler ℂ (jqModC ℂ) = (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ)) :
    IsIntegral (Algebra.adjoin ℂ ({jqModC ℂ} : Set (LaurentSeries ℂ)))
      (Y ^ 6 * (jqModC ℂ) ^ 4 * (jqModC ℂ - 1728) ^ 3) := by
  let A := Algebra.adjoin ℂ ({jqModC ℂ} : Set (LaurentSeries ℂ))
  let fm : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2 := f
  let f6 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 :=
    (fm.pow 6).mcast (by norm_num)
  have hf6 : (qExpansion 1 (f6 : ℍ → ℂ) : LaurentSeries ℂ) =
      (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ) ^ 6 := by
    dsimp only [f6]
    rw [ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos (hper hT), PowerSeries.coe_pow]
    rfl
  have hI := isIntegral_modular_quotient (hper hT) 1 (k := 12) (by norm_num) f6
  rw [pow_one, hf6, ← jqModC_eq_modular_quotient] at hI
  obtain ⟨c, hc, he⟩ := ModularQDerivative.exists_qEuler_jqModC_power_six
  let C := algebraMap ℂ (LaurentSeries ℂ) c
  have hC : C ≠ 0 := by
    intro hz
    apply hc
    apply (algebraMap ℂ (LaurentSeries ℂ)).injective
    simpa only [map_zero] using hz
  have hs : IsIntegral A (C⁻¹ ^ 6) := by
    have hm : C⁻¹ ^ 6 ∈ A := by
      change (algebraMap ℂ (LaurentSeries ℂ) c)⁻¹ ^ 6 ∈ A
      rw [← map_inv₀, ← map_pow]
      exact A.algebraMap_mem _
    change IsIntegral A (algebraMap A (LaurentSeries ℂ) ⟨C⁻¹ ^ 6, hm⟩)
    exact isIntegral_algebraMap
  have hprod : (Y ^ 6 * (jqModC ℂ) ^ 4 * (jqModC ℂ - 1728) ^ 3) *
      (C ^ 6 * (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ)) =
        (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ) ^ 6 := by
    calc
      _ = Y ^ 6 * qEuler ℂ (jqModC ℂ) ^ 6 := by rw [he]; dsimp [C]; ring
      _ = (Y * qEuler ℂ (jqModC ℂ)) ^ 6 := (mul_pow _ _ _).symm
      _ = _ := by rw [hY]
  have hEq : Y ^ 6 * (jqModC ℂ) ^ 4 * (jqModC ℂ - 1728) ^ 3 =
      C⁻¹ ^ 6 * ((qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ) ^ 6 /
        (qExpansion 1 ModularForm.discriminant : LaurentSeries ℂ)) := by
    rw [← hprod]
    field_simp [hC, discriminant_expansion_ne_zero]
  rw [hEq]
  exact hs.mul hI

end
end Dubon2026.SourceFunctionField.GammaOne
