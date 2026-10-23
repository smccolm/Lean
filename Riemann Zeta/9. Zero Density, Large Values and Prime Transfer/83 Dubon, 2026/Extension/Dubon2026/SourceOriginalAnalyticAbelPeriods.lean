import Dubon2026.SourceOriginalCuspPathIntegral
import Dubon2026.SourceOriginalAbelJacobiPeriods

/-! DUB-17/18 -> original Picard-period Hecke comparison -> the Abel map
of analytic point divisors. The proved actual path-integral comparison
identifies the Abel difference modulo the actual loop-period lattice,
for an arbitrary original base place. Native path connectedness of the
upper half-plane supplies the path; no analytic path is assumed.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

theorem abelJacobiVec_sub_cusp_primitive_mem {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ)) (τ₀ τ₁ : ℍ) :
    abelJacobiVec N (fun i => (b i).val) P₀ (originalAnalyticPlace N τ₁) -
      abelJacobiVec N (fun i => (b i).val) P₀ (originalAnalyticPlace N τ₀) -
      (fun i => sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) τ₁ -
        sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) τ₀) ∈
      pathPeriodLattice N (fun i => (b i).val) := by
  let γ : Path τ₀ τ₁ := PathConnectedSpace.somePath τ₀ τ₁
  have hm := abelJacobiVec_sub_mem N (fun i => (b i).val) (fun i => (b i).property)
    ((originalPath N P₀ (originalAnalyticPlace N τ₀)).trans
      (γ.map (originalAnalyticPlace_continuous N)))
  convert hm using 1
  funext i
  simp only [Pi.sub_apply, pathIntegral_trans N (b i).property,
    original_pathIntegral_eq_cusp_primitive, abelJacobiVec]
  ring

theorem abelJacobiDiv_analytic_difference {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ)) (τ₀ τ₁ : ℍ) :
    (pathPeriodLattice N (fun i => (b i).val)).mkQ
      (abelJacobiDiv N (fun i => (b i).val) P₀
        (Finsupp.single (originalAnalyticPlace N τ₁) 1 -
          Finsupp.single (originalAnalyticPlace N τ₀) 1)) =
      (pathPeriodLattice N (fun i => (b i).val)).mkQ
        (fun i => sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) τ₁ -
          sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) τ₀) := by
  rw [map_sub, abelJacobiDiv_single, abelJacobiDiv_single, one_smul, one_smul]
  exact (Submodule.Quotient.eq _).mpr (abelJacobiVec_sub_cusp_primitive_mem N b P₀ τ₀ τ₁)

end
end Dubon2026.SourceFunctionField.OriginalChart
