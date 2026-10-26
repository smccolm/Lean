import Dubon2026.SourceLaurentIntegralDescent
import Dubon2026.SourceGammaOneDifferentialFiniteIntegral
import Dubon2026.SourceGammaOneDifferentialCuspIntegral
import Dubon2026.SourceOriginalQuotientIntegral

/-! DUB-17/18 -> actual Gamma1 regular differential/cusp comparison.
Descend both proved complex integral equations to the actual Laurent
subfield containing the original j. The coefficient embedding, q-Euler
compatibility and subfield transport are proved explicitly. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceDifferential
open scoped MatrixGroups

theorem coeffMap_qEuler_natural {K L : Type*} [Field K] [Field L]
    (σ : K →+* L) (x : LaurentSeries K) :
    coeffMap σ (qEuler K x) = qEuler L (coeffMap σ x) := by
  ext n
  simp only [coeffMap_coeff, qEuler_coeff, map_mul, map_intCast]

theorem integral_subfield_of_integral_coeffMap
    {K L : Type*} [Field K] [Field L] (σ : K →+* L)
    (E : IntermediateField K (LaurentSeries K)) (j x : E)
    (hi : IsIntegral (Algebra.adjoin L ({coeffMap σ (j : LaurentSeries K)} :
      Set (LaurentSeries L))) (coeffMap σ (x : LaurentSeries K))) :
    IsIntegral (Algebra.adjoin K ({j} : Set E)) x :=
  isIntegral_adjoin_subfield E j.2 x.2
    (isIntegral_adjoin_of_isIntegral_coeffMap σ _ _ hi)

theorem differential_integral_expressions_of_matching_expansion
    {K : Type*} [Field K] (σ : K →+* ℂ)
    (E : IntermediateField K (LaurentSeries K)) (j : E)
    (hj : (j : LaurentSeries K) = jqModC K)
    (M : ℕ) [NeZero M] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    [Γ.FiniteIndex] (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2) (y : E)
    (hy : coeffMap σ ((y : LaurentSeries K) * qEuler K (jqModC K)) =
      (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ)) :
    IsIntegral (Algebra.adjoin K ({j} : Set E))
        (y ^ 6 * j ^ 4 * (j - algebraMap K E 1728) ^ 3) ∧
      IsIntegral (Algebra.adjoin K ({j⁻¹} : Set E))
        (y ^ (2 * M) * j ^ (M + 1) * (j - algebraMap K E 1728) ^ M) := by
  have hmapj : coeffMap σ (jqModC K) = jqModC ℂ := map_jqModC σ
  have hY : coeffMap σ (y : LaurentSeries K) * qEuler ℂ (jqModC ℂ) =
      (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ) := by
    rw [map_mul, coeffMap_qEuler_natural, hmapj] at hy
    exact hy
  have hjm : coeffMap σ (E.val j) = jqModC ℂ := by
    change coeffMap σ (j : LaurentSeries K) = jqModC ℂ
    rw [hj, hmapj]
  have hu : coeffMap σ (E.val (y ^ 6 * j ^ 4 * (j - algebraMap K E 1728) ^ 3)) =
      coeffMap σ (y : LaurentSeries K) ^ 6 * (jqModC ℂ) ^ 4 *
        (jqModC ℂ - 1728) ^ 3 := by
    simp only [map_mul, map_pow, map_sub, map_ofNat]
    rw [hjm]
    rfl
  have hv : coeffMap σ (E.val (y ^ (2 * M) * j ^ (M + 1) *
      (j - algebraMap K E 1728) ^ M)) =
      coeffMap σ (y : LaurentSeries K) ^ (2 * M) * (jqModC ℂ) ^ (M + 1) *
        (jqModC ℂ - 1728) ^ M := by
    simp only [map_mul, map_pow, map_sub, map_ofNat]
    rw [hjm]
    rfl
  have hjinv : coeffMap σ (E.val j⁻¹) = (jqModC ℂ)⁻¹ := by
    rw [map_inv₀, map_inv₀, hjm]
  constructor
  · apply integral_subfield_of_integral_coeffMap σ E j
    change IsIntegral (Algebra.adjoin ℂ ({coeffMap σ (E.val j)} : Set (LaurentSeries ℂ)))
      (coeffMap σ (E.val (y ^ 6 * j ^ 4 * (j - algebraMap K E 1728) ^ 3)))
    rw [hjm, hu]
    exact isIntegral_cusp_differential_finite_expression hT f
      (coeffMap σ (y : LaurentSeries K)) hY
  · apply integral_subfield_of_integral_coeffMap σ E j⁻¹
    change IsIntegral (Algebra.adjoin ℂ ({coeffMap σ (E.val j⁻¹)} : Set (LaurentSeries ℂ)))
      (coeffMap σ (E.val (y ^ (2 * M) * j ^ (M + 1) *
        (j - algebraMap K E 1728) ^ M)))
    rw [hjinv, hv]
    exact isIntegral_cusp_differential_cusp_expression M hΓ hT f
      (coeffMap σ (y : LaurentSeries K)) hY

end
end Dubon2026.SourceFunctionField.GammaOne
