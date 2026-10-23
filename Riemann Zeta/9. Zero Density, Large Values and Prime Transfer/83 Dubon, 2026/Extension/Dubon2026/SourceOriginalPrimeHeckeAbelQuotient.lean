import Dubon2026.SourceOriginalPrimePeriodLattice
import Dubon2026.SourceOriginalHeckeAnalyticDivisors

/-! DUB-17/18 -> rank-two full Hecke algebra realization -> all-prime
Picard-period compatibility. Combine the proved all-prime primitive trace
and invariant lattice with the existing finite integer decomposition into
analytic point differences. Every prime is included, with no
coprimality-to-level premise.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ
private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalPrimePeriodQuotientHecke_analytic_abel_difference
    (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ)) (τ₀ τ₁ : ℍ) :
    originalPrimePeriodQuotientHecke N ell b
        ((pathPeriodLattice N (fun i => (b i).val)).mkQ
          (abelJacobiDiv N (fun i => (b i).val) P₀
            (Finsupp.single (originalAnalyticPlace N τ₁) 1 -
              Finsupp.single (originalAnalyticPlace N τ₀) 1))) =
      (pathPeriodLattice N (fun i => (b i).val)).mkQ
        (abelJacobiDiv N (fun i => (b i).val) P₀
          (originalHeckeDivisor ℂ N ell.val
            (Finsupp.single (originalAnalyticPlace N τ₁) 1 -
              Finsupp.single (originalAnalyticPlace N τ₀) 1))) := by
  letI : Fact ell.val.Prime := ⟨ell.property⟩
  rw [abelJacobiDiv_analytic_difference, originalPrimePeriodQuotientHecke_mk,
    originalPrimePeriodHecke_primitive_difference]
  exact (originalHecke_abel_analytic_difference_all N ell.val b P₀ τ₀ τ₁).symm
theorem originalPrimePeriodQuotientHecke_analytic_divisor
    (ell : Nat.Primes) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (c : ℍ →₀ ℤ) (hc : c.sum (fun _ n => n) = 0) :
    originalPrimePeriodQuotientHecke N ell b
        ((pathPeriodLattice N (fun i => (b i).val)).mkQ
          (abelJacobiDiv N (fun i => (b i).val) P₀
            (Finsupp.mapDomain (originalAnalyticPlace N) c))) =
      letI : NeZero ell.val := ⟨ell.property.ne_zero⟩
      (pathPeriodLattice N (fun i => (b i).val)).mkQ
        (abelJacobiDiv N (fun i => (b i).val) P₀
          (originalHeckeDivisor ℂ N ell.val (Finsupp.mapDomain (originalAnalyticPlace N) c))) := by
  classical
  letI : NeZero ell.val := ⟨ell.property.ne_zero⟩
  rw [original_analytic_divisor_eq_sum_differences N c hc I]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro τ _
  rw [originalPrimePeriodQuotientHecke_analytic_abel_difference]

end
end Dubon2026.SourceFunctionField.OriginalChart
