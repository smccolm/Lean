import Dubon2026.SourceOriginalWeilCoverAbelConverse
import Dubon2026.SourceOriginalWeilCoverJacobiInversionAssembled
import Dubon2026.SourceCurvePicardDivisionFromAbel

/-! DUB-17/18 -> auxiliary point division. Divide the actual Abel vector by n,
realize it with the proved cover Jacobi inversion, and apply the proved cover
Abel converse to the resulting integer-period difference. The actual Picard
quotient then supplies n-division of the specified degree-zero class. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)


theorem cover_degree_zero_class_has_division (P₀ : Place ℂ EE)
    (D : Divisor.degZero (K := ℂ) (F := EE)) :
    ∃ y : Pic0 ℂ EE, n • y = Pic0.mk D := by
  let b := coverRegularBasis N n radicand
  let η : Fin (Module.finrank ℂ (regularDifferentials ℂ EE)) → Ω[EE⁄ℂ] := fun i => b i
  let AJ := abelJacobiDiv N n radicand baseDivisor hRadicand hOrders η P₀
  let Λ := pathPeriodLattice N n radicand baseDivisor hRadicand hOrders η
  exact Pic0.exists_nsmul_mk_of_abel_data n (NeZero.ne n) AJ Λ
    (exists_cover_jacobi_divisor N n radicand baseDivisor hRadicand hOrders P₀)
    (fun B hB0 hB => cover_isPrincipal_of_abelJacobi_mem N n radicand baseDivisor hRadicand hOrders
      b P₀ B hB0 hB) D

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
