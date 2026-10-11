import Dubon2026.LocalGeometricFiniteFlatCohomology
import Dubon2026.FirstOrderAdditionFiniteFlatModel
import Dubon2026.FirstOrderScalingFiniteFlatModel
import Dubon2026.FirstOrderCoefficientClassOperations

/-! # The genuine local geometric finite-flat condition is a cohomology subspace -/

namespace Dubon2026
noncomputable section
open Matrix

variable {R F K ι k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [Field k] [Finite k]
  [TopologicalSpace k] [IsTopologicalRing k]

/-- The original local geometric set is a genuine linear submodule. Closure comes
from actual finite-flat models under compatible coefficient addition, epsilon scaling,
and the constant lift of a supplied genuine residual model. -/
def localGeometricFiniteFlatCohomologySubmodule
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K (Multiplicative (ι → k))
      (matrixUnderlyingGroupAction ρ)) :
    Submodule k (ContinuousMatrixAdjointH1 ρ hρ) where
  carrier := localGeometricFiniteFlatCohomologyCondition R F K ρ hρ
  zero_mem' := by
    exact ⟨firstOrderLiftFromCocycle ρ 0,
      firstOrderLiftFromCocycle_continuous ρ hρ 0 continuous_const,
      matrixFirstOrderZero_finiteFlatScheme ρ m, continuousMatrixFirstOrderClass_zero ρ hρ⟩
  add_mem' := by
    rintro x y ⟨τ, hτ, ht, hx⟩ ⟨υ, hυ, hu, hy⟩
    refine ⟨matrixFirstOrderSum ρ τ υ, matrixFirstOrderSum_continuous ρ hρ τ υ hτ hυ,
      matrixFirstOrderSum_finiteFlatScheme ρ τ υ ht hu, ?_⟩
    rw [continuousMatrixFirstOrderClass_sum ρ hρ τ υ hτ hυ, hx, hy]
  smul_mem' := by
    rintro c x ⟨τ, hτ, ht, hx⟩
    refine ⟨matrixFirstOrderScale ρ c τ, matrixFirstOrderScale_continuous ρ hρ c τ hτ,
      matrixFirstOrderScale_finiteFlatScheme ρ c τ ht, ?_⟩
    rw [continuousMatrixFirstOrderClass_scale ρ hρ c τ hτ, hx]

/-- A genuine model of the residual local representation proves that the original
geometric condition is the membership predicate of a unique actual cohomology
submodule. The statement requires no irreducibility or assumed linear closure. -/
theorem localGeometricFiniteFlatCohomologySubmodule_existsUnique
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (m : FiniteFreeHopfPointModel.{0,0,0,0,0} R F K (Multiplicative (ι → k))
      (matrixUnderlyingGroupAction ρ)) :
    ∃! S : Submodule k (ContinuousMatrixAdjointH1 ρ hρ),
      ∀ x, x ∈ S ↔ x ∈ localGeometricFiniteFlatCohomologyCondition R F K ρ hρ := by
  refine ⟨localGeometricFiniteFlatCohomologySubmodule ρ hρ m, fun _ => Iff.rfl, ?_⟩
  intro S hS
  apply Submodule.ext
  intro x
  exact hS x

end
end Dubon2026
