import Dubon2026.SourceGammaOneCuspDifferentialCoefficient
import Dubon2026.SourceGammaOneDifferentialRegularity
import Dubon2026.SourceGammaOneScalarExtension

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison. Every actual
weight-two cusp form with coefficients in the specified embedded field is
the exact expansion of a differential in the original integral-ratio field.
Construct y D(j) from the proved coefficient y, then apply the already proved
regularity theorem. No matching differential or integral equation is assumed.
The converse, Hecke/diamond comparison and arithmetic realization remain. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceDifferential SourceCurve KaehlerDifferential CongruenceSubgroup
open scoped ModularForm MatrixGroups

theorem exists_gammaOne_differential_of_coefficients
    {K : Type*} [Field K] [Algebra ℚ K] (σ : K →+* ℂ) (N : ℕ) [NeZero N]
    (f : CuspForm (Gamma1 N) 2)
    (hf : ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ σ.range) :
    ∃ ω : Ω[functionFieldOver (Gamma1 N) K⁄K],
      coeffMap σ (diffQExp (functionFieldOver (Gamma1 N) K) ω) =
        (qExpansion 1 f : LaurentSeries ℂ) := by
  classical
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  choose c hc using hf
  let y : PowerSeries K := PowerSeries.mk c
  have hy : y.map σ = qExpansion 1 f := by
    apply PowerSeries.ext
    intro n
    simpa only [y, PowerSeries.coeff_map, PowerSeries.coeff_mk] using hc n
  obtain ⟨a, ha⟩ := exists_cusp_differential_coefficient_of_coeffMap σ N f y hy
  let F := functionFieldOver (Gamma1 N) K
  letI : Algebra K F := F.toSubalgebra.algebra
  have hm : (a : LaurentSeries K) ∈ F := by
    rw [show F = qExpFunctionFieldC K (Gamma1 N) from
      functionFieldOver_eq_qExpFunctionFieldC (Gamma1 N) K]
    exact a.property
  let b : F := ⟨a, hm⟩
  have he := congrArg (coeffMap σ) (diffQExp_smul_D F b (jCoordinateOver (Gamma1 N) K))
  refine ⟨_, he.trans ?_⟩
  change coeffMap σ ((a : LaurentSeries K) * qEuler K (coeffEmb K jq)) = _
  rw [coeffEmb_jq, ha, coeffMap_ofPowerSeries, hy]

theorem exists_gammaOne_regular_differential_of_coefficients
    {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (σ : K →+* ℂ) (N : ℕ) [NeZero N]
    (f : CuspForm (Gamma1 N) 2)
    (hf : ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ σ.range) :
    ∃ ω : Ω[functionFieldOver (Gamma1 N) K⁄K],
      ω ∈ regularDifferentials K (functionFieldOver (Gamma1 N) K) ∧
      coeffMap σ (diffQExp (functionFieldOver (Gamma1 N) K) ω) =
        (qExpansion 1 f : LaurentSeries ℂ) := by
  obtain ⟨ω, hω⟩ := exists_gammaOne_differential_of_coefficients σ N f hf
  exact ⟨ω, gamma1_regular_of_diffQExp_matches_cusp σ N f ω hω, hω⟩

end
end Dubon2026.SourceFunctionField.GammaOne
