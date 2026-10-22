import Dubon2026.SourceOriginalRegularCuspGerms
import Dubon2026.SourceOriginalNumericalGenus
import Dubon2026.SourceWeightTwoPeriodDimension

/-! DUB-17/18 -> original parabolic Hecke realization -> period surjectivity.
The actual regular-differential germ map is injective and its range lies
in the native cusp-form germ range. Original Riemann--Roch and the proved
numerical genus therefore give the missing cusp-form dimension lower bound.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve

theorem original_weight_two_cusp_finite (N : ℕ) [NeZero N] :
    Module.Finite ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
  letI := sourceWeightTwoParabolic_finite N
  letI := Module.Finite.of_injective (sourceWeightTwoParabolicPeriodPair N)
    (sourceWeightTwoParabolicPeriodPair_injective N)
  exact Module.Finite.of_injective
    (LinearMap.inl ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)
      (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) LinearMap.inl_injective

theorem finrank_original_regularDifferentials_le_cuspForms (N : ℕ) [NeZero N] :
    Module.finrank ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) ≤
      Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
  letI := original_weight_two_cusp_finite N
  have h := Submodule.finrank_mono (original_regular_differential_germ_range_le N I)
  rw [LinearMap.finrank_range_of_inj (originalRegularDifferentialGerm_injective N I)] at h
  exact h.trans (originalCuspFormGerm N I).finrank_range_le

theorem genusFormula_le_finrank_cuspForms (N : ℕ) [NeZero N] :
    SourceLevelProjective.genusFormula N ≤
      (Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) : ℚ) := by
  rw [← finrank_original_regularDifferentials_eq_genusFormula N]
  exact_mod_cast finrank_original_regularDifferentials_le_cuspForms N

end
end Dubon2026.SourceFunctionField
