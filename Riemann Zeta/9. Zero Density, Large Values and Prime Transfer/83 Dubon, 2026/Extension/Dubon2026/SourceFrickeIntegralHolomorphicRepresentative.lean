import Dubon2026.SourceFrickeClearedLaurentMonic
import Dubon2026.SourceHolomorphicMonicQuotient
import Dubon2026.SourceIntegralCoordinateMonic
import Dubon2026.SourceFrickeFractionPeriodicity

/-! DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
character realization -> differential/cusp comparison -> rational Fourier
spanning. Recover an actual holomorphic cyclotomic Fricke fraction for each
integral Laurent summand. The cleared monic relation supplies the local
boundedness needed by the existing removable-singularity theorem; neither
holomorphic realization nor periodicity is assumed. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold MatrixGroups ModularForm

theorem exists_holomorphic_cyclotomic_fraction_of_integral_laurent
    {N : ℕ} [NeZero N] {X : LaurentSeries ℂ}
    (hX : X ∈ ConstantDescent.RSet (kN N) {jqNModC ℂ N} (frickeLaurentGenerators N)) :
    ∃ (F a b : ℍ → ℂ),
      a ∈ cyclotomicLevelRing N ∧ b ∈ cyclotomicLevelRing N ∧ b ≠ 0 ∧
      MDiff F ∧ F * b = a ∧ CuspTaylor.Represents X (cuspFunction N F) ∧
      Function.Periodic (F ∘ ofComplex) N := by
  obtain ⟨a, b, A, B, ha, hb, hb0, hB0, hAr, hBr, hXeq⟩ :=
    exists_cyclotomic_function_fraction_of_laurent_field hX.1
  obtain ⟨d, p, hmonic⟩ := exists_coordinate_monic_relation hX.2
  rw [hXeq] at hmonic
  have hclear := cleared_cyclotomic_relation_of_laurent ha hb hAr hBr d p
    (cleared_monic_relation_of_div hB0 hmonic)
  obtain ⟨F, hF, hFa⟩ := exists_mdifferentiable_quotient_of_monic
    (cyclotomicLevelRing_holomorphic ha) (cyclotomicLevelRing_holomorphic hb) hb0
    (fun k _ => cyclotomicLevelRing_holomorphic (cyclotomic_polynomial_jf_mem N (p k))) hclear
  refine ⟨F, a, b, ha, hb, hb0, hF, hFa, ?_, periodic_cyclotomic_fraction ha hb hb0 hF hFa⟩
  rw [hXeq]
  exact hAr.cusp_of_mul_eq hBr hB0 hFa

end
end Dubon2026.SourceFricke