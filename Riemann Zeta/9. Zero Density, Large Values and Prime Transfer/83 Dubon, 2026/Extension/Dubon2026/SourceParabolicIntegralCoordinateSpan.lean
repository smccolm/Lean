import Dubon2026.SourceParabolicUniformDenominator
import Dubon2026.SourceComplexBinaryCocycleSpan

/-! DUB17/18 -> original all-weight association -> original parabolic
Hecke character -> integral span of the source period class. A rational
coordinate with its actual whole-cusp-stabilizer witnesses lies in the
complex span of integral parabolic cocycles. The integer coefficient
composition proof is reused verbatim from SourceComplexBinaryCocycleSpan. -/
namespace Dubon2026
noncomputable section
open MvPolynomial Matrix.SpecialLinearGroup CongruenceSubgroup groupCohomology

private theorem integer_coefficient_composition (Q w : ℕ)
    (z : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep ℤ Q w)) :
    sourceBinaryCocyclesChange (algebraMap ℚ ℂ) Q w
        (sourceBinaryCocyclesChange (Int.castRingHom ℚ) Q w z) =
      sourceBinaryCocyclesChange (Int.castRingHom ℂ) Q w z := by
  apply groupCohomology.cocycles₁_ext
  intro g
  apply Subtype.ext
  ext m
  rw [sourceBinaryCocyclesChange_apply, coeff_map,
    sourceBinaryCocyclesChange_apply, coeff_map,
    sourceBinaryCocyclesChange_apply, coeff_map]
  exact map_intCast (algebraMap ℚ ℂ) _

theorem sourceRationalCuspBinaryCocycle_mem_integralParabolic_span
    (Q w : ℕ) [NeZero Q]
    (c : cocycles₁ (sourceBinaryCoefficientRep ℚ Q w))
    (hc : ∀ β : OnePoint ℚ, ∃ v : sourceBinaryCoefficientRep ℚ Q w,
      ∀ γ : Gamma0 Q, mapGL ℚ γ.val • β = β →
        c γ = (sourceBinaryCoefficientRep ℚ Q w).ρ γ v - v) :
    sourceBinaryCocyclesChange (algebraMap ℚ ℂ) Q w c ∈
      Submodule.span ℂ (sourceBinaryCocyclesChange (Int.castRingHom ℂ) Q w ''
        (sourceParabolicCocycles (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q w) :
          Set (cocycles₁ (sourceBinaryCoefficientRep ℤ Q w)))) := by
  obtain ⟨d, z, hd, hz, hp⟩ := sourceRationalBinaryCocycle_parabolic_integerMultiple Q w c hc
  have hmem := Submodule.subset_span (R := ℂ)
    (show sourceBinaryCocyclesChange (Int.castRingHom ℂ) Q w z ∈
      sourceBinaryCocyclesChange (Int.castRingHom ℂ) Q w ''
        (sourceParabolicCocycles (Gamma0 Q) (sourceBinaryCoefficientRep ℤ Q w) :
          Set (cocycles₁ (sourceBinaryCoefficientRep ℤ Q w))) from ⟨z, hp, rfl⟩)
  rw [← integer_coefficient_composition, hz, map_smulₛₗ] at hmem
  have h := Submodule.smul_mem _ (algebraMap ℚ ℂ (d : ℚ))⁻¹ hmem
  rw [smul_smul, inv_mul_cancel₀ ((map_ne_zero (algebraMap ℚ ℂ)).mpr
    (Int.cast_ne_zero.mpr hd)), one_smul] at h
  exact h

end
end Dubon2026
