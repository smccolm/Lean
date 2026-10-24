import Dubon2026.SourceOriginalConormDimension
import Dubon2026.SourceOriginalNumericalGenus
import Dubon2026.SourceCurvePositiveDivisorStabilization

/-! DUB-17/18 -> modular good reduction -> genus equality. The actual
arithmetic-to-complex conorm preserves divisor degree and divisor-space
dimension. The existing positive-divisor stabilization therefore identifies
the two genera, and the proved complex numerical formula gives the arithmetic
formula. No genus-invariance premise or new general extension theory is used. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]

private theorem originalGenus_eq_maximum
    (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
    {γ : ℤ} {D₀ : Divisor L (modularFunctionFieldOver N L)}
    (h : RiemannGenusReachedAt γ D₀) : (originalGenus N L : ℤ) = γ := by
  haveI := hasPrincipalDivisors_original N L
  haveI := finite_original_place_residue N L
  haveI := finite_original_lSpace N L 0
  have he := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [original_ell_zero N L, map_zero] at he
  rw [originalGenus_eq_zero_index]
  omega

theorem originalGenus_arithmetic_eq_complex : originalGenus N Qbar = originalGenus N ℂ := by
  haveI := hasPrincipalDivisors_original N Qbar
  haveI := hasPrincipalDivisors_original N ℂ
  haveI := finite_original_place_residue N Qbar
  haveI := finite_original_place_residue N ℂ
  haveI := finite_original_lSpace N Qbar 0
  haveI := finite_original_lSpace N ℂ 0
  obtain ⟨γQ, DQ, hQ⟩ := original_degree_dimension_maximum N Qbar
  obtain ⟨γC, DC, hC⟩ := original_degree_dimension_maximum N ℂ
  let P := (exists_original_poleDivisorPackage N Qbar).some
  have hp : 0 < Divisor.degree P.B := by rw [P.degB_eq]; exact_mod_cast P.hn_pos
  obtain ⟨mq, hq⟩ := hQ.exists_forall_degree_nsmul_sub_ell_eq hp
  have hpc : 0 < Divisor.degree (OriginalConstantField.conorm N P.B) := by
    rw [OriginalConstantField.degree_conorm]
    exact hp
  obtain ⟨mc, hc⟩ := hC.exists_forall_degree_nsmul_sub_ell_eq hpc
  have hqm := hq (max mq mc) (le_max_left _ _)
  have hcm := hc (max mq mc) (le_max_right _ _)
  have hmap : OriginalConstantField.conorm N (max mq mc • P.B) =
      max mq mc • OriginalConstantField.conorm N P.B := by rw [map_nsmul]
  rw [← hmap, OriginalConstantField.degree_conorm, OriginalConstantField.ell_conorm] at hcm
  have heQ := originalGenus_eq_maximum N Qbar hQ
  have heC := originalGenus_eq_maximum N ℂ hC
  omega

theorem originalGenus_arithmetic_eq_genusFormula :
    (originalGenus N Qbar : ℚ) = SourceLevelProjective.genusFormula N := by
  rw [originalGenus_arithmetic_eq_complex, originalGenus_eq_genusFormula]

end
end Dubon2026.SourceFunctionField
