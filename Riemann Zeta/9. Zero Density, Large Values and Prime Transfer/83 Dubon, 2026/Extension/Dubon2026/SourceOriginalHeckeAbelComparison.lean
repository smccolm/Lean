import Dubon2026.SourceOriginalHeckeAbelCosets
import Dubon2026.SourceOriginalHeckePrimitiveTrace

/-! DUB-17/18 -> original Picard-period Hecke comparison -> the actual
good-prime Abel comparison on analytic point differences. The literal
Picard correspondence and the actual analytic Hecke transform give the
same element of the original period quotient. Both the ramification
multiplicities and the primitive normalization have been discharged.
Extension to all divisor classes and lattice compatibility remain required.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup KaehlerDifferential
open scoped MatrixGroups
variable (N p : ℕ) [NeZero N] [Fact p.Prime]

private local instance : Fintype (Gamma0 N ⧸ heckeUpperSubgroup N p) :=
  sourceHeckeUpperFintype N p

theorem originalHecke_abel_analytic_difference (hpN : Nat.Coprime p N) {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ)) (τ₀ τ₁ : ℍ) :
    (pathPeriodLattice N (fun i => (b i).val)).mkQ
      (abelJacobiDiv N (fun i => (b i).val) P₀
        (originalHeckeDivisor ℂ N p
          (Finsupp.single (originalAnalyticPlace N τ₁) 1 -
            Finsupp.single (originalAnalyticPlace N τ₀) 1))) =
      (pathPeriodLattice N (fun i => (b i).val)).mkQ
        (fun i => sourceWeightTwoPrimitive 1 (cuspHeckePrime (p := p) Fact.out (originalRegularCuspEquiv N (b i))) τ₁ -
          sourceWeightTwoPrimitive 1 (cuspHeckePrime (p := p) Fact.out (originalRegularCuspEquiv N (b i))) τ₀) := by
  rw [originalHecke_abel_analytic_difference_cosets, ← map_sum]
  congr 1
  funext i
  simp only [Finset.sum_apply]
  exact originalHeckePrimitiveTrace_difference N p Fact.out hpN
    (originalRegularCuspEquiv N (b i)) τ₀ τ₁

end
end Dubon2026.SourceFunctionField.OriginalChart
