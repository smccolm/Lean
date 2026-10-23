import Dubon2026.SourceOriginalPeriodSurjectivity

/-! DUB-17/18 -> original Picard-period Hecke comparison -> identifying
regular-differential periods with actual weight-two cusp periods. The
proved equal dimensions and injective regular germ map turn the existing
range inclusion into equality. No further analytic continuation theorem
or new normalization is needed to obtain the actual linear equivalence.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve
variable (N : ℕ) [NeZero N]

theorem finrank_original_regularDifferentials_eq_cuspForms :
    Module.finrank ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) =
      Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
  exact_mod_cast (finrank_original_regularDifferentials_eq_genusFormula N).trans
    (sourceWeightTwo_cusp_dimension_eq_genusFormula N).symm

theorem original_regular_differential_germ_range_eq (τ : ℍ) :
    (originalRegularDifferentialGerm N τ).range = (originalCuspFormGerm N τ).range := by
  letI := finite_original_regularDifferentials N ℂ
  letI := original_weight_two_cusp_finite N
  apply Submodule.eq_of_le_of_finrank_le (original_regular_differential_germ_range_le N τ)
  rw [LinearMap.finrank_range_of_inj (originalRegularDifferentialGerm_injective N τ),
    finrank_original_regularDifferentials_eq_cuspForms]
  exact (originalCuspFormGerm N τ).finrank_range_le

theorem originalCuspFormGerm_injective (τ : ℍ) :
    Function.Injective (originalCuspFormGerm N τ) := by
  letI := original_weight_two_cusp_finite N
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  have h := (originalCuspFormGerm N τ).finrank_range_add_finrank_ker
  rw [← original_regular_differential_germ_range_eq,
    LinearMap.finrank_range_of_inj (originalRegularDifferentialGerm_injective N τ),
    finrank_original_regularDifferentials_eq_cuspForms] at h
  omega

/-- The actual original regular differentials identified with native cusp forms by their germs. -/
def originalRegularCuspEquiv :
    regularDifferentials ℂ (modularFunctionFieldOver N ℂ) ≃ₗ[ℂ]
      CuspForm (CongruenceSubgroup.Gamma0 N) 2 :=
  (LinearEquiv.ofInjective (originalRegularDifferentialGerm N I)
    (originalRegularDifferentialGerm_injective N I)).trans
      ((LinearEquiv.ofEq _ _ (original_regular_differential_germ_range_eq N I)).trans
        (LinearEquiv.ofInjective (originalCuspFormGerm N I) (originalCuspFormGerm_injective N I)).symm)

theorem originalRegularCuspEquiv_germ_at_I
    (ω : regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    originalCuspFormGerm N I (originalRegularCuspEquiv N ω) =
      originalRegularDifferentialGerm N I ω := by
  have h := (LinearEquiv.ofInjective (originalCuspFormGerm N I)
    (originalCuspFormGerm_injective N I)).apply_symm_apply
      ((LinearEquiv.ofEq _ _ (original_regular_differential_germ_range_eq N I))
        ((LinearEquiv.ofInjective (originalRegularDifferentialGerm N I)
          (originalRegularDifferentialGerm_injective N I)) ω))
  exact congrArg Subtype.val h

end
end Dubon2026.SourceFunctionField
