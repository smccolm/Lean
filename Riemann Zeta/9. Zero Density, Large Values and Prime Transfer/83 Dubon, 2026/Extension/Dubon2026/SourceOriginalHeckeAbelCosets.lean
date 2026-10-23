import Dubon2026.SourceOriginalAnalyticAbelPeriods
import Dubon2026.SourceOriginalHeckeAnalyticDivisor

/-! DUB-17/18 -> original Picard-period Hecke comparison -> the actual
Hecke image of analytic point differences. Combine the proved literal
divisor correspondence, including ramification multiplicities, with the
actual Abel/path-period comparison. The result is the genuine quotient
coset sum of normalized cusp primitive differences in the original
period quotient. Identification with the analytic Hecke matrix remains
a distinct next obligation.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup KaehlerDifferential
open scoped MatrixGroups
variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

private local instance : Fintype (Gamma0 N ⧸ heckeUpperSubgroup N ℓ) :=
  sourceHeckeUpperFintype N ℓ

theorem originalHecke_abel_analytic_difference_cosets {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ)) (τ₀ τ₁ : ℍ) :
    (pathPeriodLattice N (fun i => (b i).val)).mkQ
      (abelJacobiDiv N (fun i => (b i).val) P₀
        (originalHeckeDivisor ℂ N ℓ
          (Finsupp.single (originalAnalyticPlace N τ₁) 1 -
            Finsupp.single (originalAnalyticPlace N τ₀) 1))) =
      ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ℓ,
        (pathPeriodLattice N (fun i => (b i).val)).mkQ
          (fun i => sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i))
              (originalHeckeCosetPoint N ℓ τ₁ q) -
            sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i))
              (originalHeckeCosetPoint N ℓ τ₀ q)) := by
  rw [map_sub, originalHeckeDivisor_single_analytic_cosets,
    originalHeckeDivisor_single_analytic_cosets, ← Finset.sum_sub_distrib, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact abelJacobiDiv_analytic_difference N b P₀
    (originalHeckeCosetPoint N ℓ τ₀ q) (originalHeckeCosetPoint N ℓ τ₁ q)

end
end Dubon2026.SourceFunctionField.OriginalChart
