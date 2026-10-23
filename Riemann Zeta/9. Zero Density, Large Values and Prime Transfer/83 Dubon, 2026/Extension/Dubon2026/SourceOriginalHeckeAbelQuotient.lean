import Dubon2026.SourceOriginalPeriodHeckeLattice
import Dubon2026.SourceOriginalHeckeAbelComparison
import Dubon2026.SourceOriginalPathIntegralLinearCombination

/-! DUB-17/18 -> original Jacobian Tate Hecke realization -> actual
Picard-period compatibility. Identify the genuine dual Hecke operator
with integration of transformed original differentials. The proved
analytic divisor comparison then becomes an equality of the two actual
endomorphisms on analytic point differences. Moving divisor classes away
from cusps remains the next step.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup KaehlerDifferential
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

private local instance {N : ℕ} (ell : sourceBinaryHeckePrime N) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

theorem originalPeriodHecke_pathIntegral (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    {P Q : Place ℂ (modularFunctionFieldOver N ℂ)} (γ : Path P Q) :
    originalPeriodHecke N ell b (fun i => pathIntegral N (b i).val γ) =
      fun i => pathIntegral N (originalRegularHecke N ell (b i)).val γ := by
  funext i
  change b.constr ℂ (fun j => pathIntegral N (b j).val γ)
    (originalRegularHecke N ell (b i)) = _
  rw [Module.Basis.constr_apply_fintype]
  have he := congrArg Subtype.val (b.sum_repr (originalRegularHecke N ell (b i)))
  simp only [Submodule.coe_sum, Submodule.coe_smul] at he
  rw [← he, pathIntegral_sum_smul N _ _ (fun j => (b j).property)]
  rfl

theorem originalPeriodHecke_primitive_difference (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    (τ₀ τ₁ : ℍ) :
    originalPeriodHecke N ell b
        (fun i => sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) τ₁ -
          sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) τ₀) =
      fun i => sourceWeightTwoPrimitive 1
          (cuspHeckePrime ell.property.1 (originalRegularCuspEquiv N (b i))) τ₁ -
        sourceWeightTwoPrimitive 1
          (cuspHeckePrime ell.property.1 (originalRegularCuspEquiv N (b i))) τ₀ := by
  let γ : Path τ₀ τ₁ := PathConnectedSpace.somePath τ₀ τ₁
  have he := originalPeriodHecke_pathIntegral N ell b
    (γ.map (originalAnalyticPlace_continuous N))
  simpa only [original_pathIntegral_eq_cusp_primitive, originalRegularHecke_cusp] using he

theorem originalPeriodQuotientHecke_analytic_abel_difference
    (ell : sourceBinaryHeckePrime N) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ)) (τ₀ τ₁ : ℍ) :
    originalPeriodQuotientHecke N ell b
        ((pathPeriodLattice N (fun i => (b i).val)).mkQ
          (abelJacobiDiv N (fun i => (b i).val) P₀
            (Finsupp.single (originalAnalyticPlace N τ₁) 1 -
              Finsupp.single (originalAnalyticPlace N τ₀) 1))) =
      (pathPeriodLattice N (fun i => (b i).val)).mkQ
        (abelJacobiDiv N (fun i => (b i).val) P₀
          (originalHeckeDivisor ℂ N ell.val
            (Finsupp.single (originalAnalyticPlace N τ₁) 1 -
              Finsupp.single (originalAnalyticPlace N τ₀) 1))) := by
  letI : Fact ell.val.Prime := ⟨ell.property.1⟩
  rw [abelJacobiDiv_analytic_difference, originalPeriodQuotientHecke_mk,
    originalPeriodHecke_primitive_difference]
  exact (originalHecke_abel_analytic_difference N ell.val ell.property.2 b P₀ τ₀ τ₁).symm

end
end Dubon2026.SourceFunctionField.OriginalChart
