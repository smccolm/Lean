import Dubon2026.SourceOriginalAnalyticDivisorMoving
import Dubon2026.SourceOriginalHeckeAbelQuotient

/-! DUB-17/18 -> full original Picard-period Hecke compatibility.
Every degree-zero finite analytic divisor is the literal integer sum of
analytic point differences. Additivity extends the already proved genuine
Hecke quotient identity to these divisors, with no representative or
point-compatibility input supplied by the caller.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_analytic_divisor_eq_sum_differences (c : ℍ →₀ ℤ)
    (hc : c.sum (fun _ n => n) = 0) (τ₀ : ℍ) :
    Finsupp.mapDomain (originalAnalyticPlace N) c =
      ∑ τ ∈ c.support, c τ •
        (Finsupp.single (originalAnalyticPlace N τ) (1 : ℤ) -
          Finsupp.single (originalAnalyticPlace N τ₀) (1 : ℤ)) := by
  classical
  have hz : ∑ τ ∈ c.support, c τ = 0 := hc
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hz, zero_smul, sub_zero]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

theorem originalPeriodQuotientHecke_analytic_divisor
    (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (c : ℍ →₀ ℤ) (hc : c.sum (fun _ n => n) = 0) :
    originalPeriodQuotientHecke N ell b
        ((pathPeriodLattice N (fun i => (b i).val)).mkQ
          (abelJacobiDiv N (fun i => (b i).val) P₀
            (Finsupp.mapDomain (originalAnalyticPlace N) c))) =
      letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
      (pathPeriodLattice N (fun i => (b i).val)).mkQ
        (abelJacobiDiv N (fun i => (b i).val) P₀
          (originalHeckeDivisor ℂ N ell.val (Finsupp.mapDomain (originalAnalyticPlace N) c))) := by
  classical
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  rw [original_analytic_divisor_eq_sum_differences N c hc I]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro τ _
  rw [originalPeriodQuotientHecke_analytic_abel_difference]

end
end Dubon2026.SourceFunctionField.OriginalChart
