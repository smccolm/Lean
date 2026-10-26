import Dubon2026.SourceGammaOneDifferentialIntegralDescent
import Dubon2026.SourceCurveRegularIntegralCriterion
import Dubon2026.SourceGammaOneCurveGeometry

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> all-weight arithmetic
association -> original finite Gamma1 character realization -> actual
Picard/H1 and diamond comparison -> regular differential/cusp comparison.
For the actual integral-ratio field, a differential whose expansion is
that of an actual cusp form is regular at every place. Both integral
equations and all local differential prerequisites are proved inputs.
Algebraic realization of an arbitrary cusp form and the converse remain
separate obligations. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceDifferential SourceCurve KaehlerDifferential
open scoped MatrixGroups

theorem regular_of_diffQExp_matches_cusp
    {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (σ : K →+* ℂ) (M : ℕ) [NeZero M]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Γ.FiniteIndex]
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2)
    (ω : Ω[functionFieldOver Γ K⁄K])
    (hω : coeffMap σ (diffQExp (functionFieldOver Γ K) ω) =
      (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ)) :
    ω ∈ regularDifferentials K (functionFieldOver Γ K) := by
  let E := functionFieldOver Γ K
  let j : E := jCoordinateOver Γ K
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  letI := finiteDimensional_jCoordinateOver hT K
  letI := functionFieldOver_isCurveOver Γ K hT
  have hD : D K E j ≠ 0 := D_jCoordinateOver_ne_zero Γ K
  have hj : (j : LaurentSeries K) = jqModC K := coeffEmb_jq K
  obtain ⟨y, hyω⟩ := RegularDifferentialsComparison.exists_smul_eq hD ω
  have hθ : coeffMap σ ((y : LaurentSeries K) * qEuler K (jqModC K)) =
      (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ) := by
    rw [← hyω, diffQExp_smul_D] at hω
    rwa [hj] at hω
  obtain ⟨hfinite, hcusp⟩ :=
    differential_integral_expressions_of_matching_expansion σ E j hj M hΓ hT f y hθ
  rw [← hyω]
  exact regular_smul_D_of_two_integral_expressions j y hD M hfinite hcusp

theorem gamma1_regular_of_diffQExp_matches_cusp
    {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (σ : K →+* ℂ) (M : ℕ) [NeZero M]
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (ω : Ω[functionFieldOver (CongruenceSubgroup.Gamma1 M) K⁄K])
    (hω : coeffMap σ (diffQExp (functionFieldOver (CongruenceSubgroup.Gamma1 M) K) ω) =
      (qExpansion 1 (f : ℍ → ℂ) : LaurentSeries ℂ)) :
    ω ∈ regularDifferentials K (functionFieldOver (CongruenceSubgroup.Gamma1 M) K) := by
  apply regular_of_diffQExp_matches_cusp σ M ?_ ?_ f ω hω
  · intro A hA
    rw [CongruenceSubgroup.Gamma_mem] at hA
    rw [CongruenceSubgroup.Gamma1_mem]
    exact ⟨hA.1, hA.2.2.2, hA.2.2.1⟩
  · simp [CongruenceSubgroup.Gamma1_mem, ModularGroup.T]

end
end Dubon2026.SourceFunctionField.GammaOne
