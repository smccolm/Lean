import Dubon2026.SourceOriginalCuspPathIntegral
import Dubon2026.SourceWeightTwoPeriods
import Dubon2026.SourceOriginalAbelJacobiPeriods
import Dubon2026.SourceOriginalEdgePathIntegral
import Dubon2026.SourceOriginalAnalyticOrbitSeparation

/-! DUB-17/18 -> original Picard-period Hecke comparison -> identifying
the actual path lattice with the native modular periods. Use the already
proved scalar cusp-period character, including its orientation and its
normalized Eichler primitive. Each modular period is an actual original
loop period. The reverse inclusion remains a separate obligation.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup KaehlerDifferential
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

theorem original_cusp_primitive_period (f : CuspForm (Gamma0 N) 2)
    (γ : Gamma0 N) (τ : ℍ) :
    sourceWeightTwoPrimitive 1 f (γ.val • τ) = sourceWeightTwoPrimitive 1 f τ +
      sourceWeightTwoPeriodValue (Gamma0 N) f γ := by
  simpa only [strictWidthInfty_Gamma0] using
    sourceWeightTwoPrimitive_period (Gamma0 N) f γ τ

/-- Integer span of the actual scalar modular periods in original regular-differential coordinates. -/
def originalCuspPeriodLattice {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    Submodule ℤ (Fin n → ℂ) :=
  Submodule.span ℤ (Set.range fun γ : Gamma0 N =>
    fun i => sourceWeightTwoPeriodValue (Gamma0 N) (originalRegularCuspEquiv N (b i)) γ)

theorem original_cusp_period_mem_pathPeriodLattice {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) (γ : Gamma0 N) :
    (fun i => sourceWeightTwoPeriodValue (Gamma0 N) (originalRegularCuspEquiv N (b i)) γ) ∈
      pathPeriodLattice N (fun i => (b i).val) := by
  let δ : Path I (γ.val • I) := PathConnectedSpace.somePath I (γ.val • I)
  have hP : originalAnalyticPlace N I = originalAnalyticPlace N (γ.val • I) :=
    (originalAnalyticPlace_smul N γ I).symm
  have hm := mem_pathPeriodLattice_of_loop N (fun i => (b i).val)
    ((δ.map (originalAnalyticPlace_continuous N)).cast rfl hP)
  convert hm using 1
  funext i
  rw [CellGeometry.OriginalEdgePaths.pathIntegral_cast,
    original_pathIntegral_eq_cusp_primitive, original_cusp_primitive_period]
  ring

theorem originalCuspPeriodLattice_le_pathPeriodLattice {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    originalCuspPeriodLattice N b ≤ pathPeriodLattice N (fun i => (b i).val) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨γ, rfl⟩
  exact original_cusp_period_mem_pathPeriodLattice N b γ

end
end Dubon2026.SourceFunctionField.OriginalChart
