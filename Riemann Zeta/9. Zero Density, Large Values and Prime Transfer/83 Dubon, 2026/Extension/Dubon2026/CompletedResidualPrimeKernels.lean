import Dubon2026.IdealPowerMatrixKernels
import Dubon2026.CompletedResidualFiniteQuotients
import Dubon2026.CompletedResidualField
import Mathlib.Algebra.CharP.Defs

/-! # The genuine prime-power matrix kernels of the original completed residual ring -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- The genuine residue characteristic belongs to the true maximal ideal of the original completion. -/
theorem residualRepresentationCompletion_prime_mem
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) [CharP (IsLocalRing.ResidueField O) p] :
    (p : ResidualRepresentationCompletion ρ) ∈
      IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) := by
  rw [← completedResidualRepresentationEvaluation_ker ρ]
  change completedResidualRepresentationEvaluation ρ
    (p : ResidualRepresentationCompletion ρ) = 0
  rw [map_natCast, CharP.cast_eq_zero]

/-- The literal residual matrix kernel at each actual maximal-power quotient is a p-group for the original residue prime. -/
theorem residualRepresentationCompletion_powerKernel_isPGroup
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p] (n : ℕ) :
    IsPGroup p (MatrixCongruenceKernel (ι := ι)
      ((IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)).map
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n)))) :=
  idealPowerMatrixKernel_isPGroup
    (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)) hp
    (residualRepresentationCompletion_prime_mem ρ p) n

/-- Each actual matrix kernel at an original completed power quotient is finite when the original residue field is finite. -/
theorem residualRepresentationCompletion_powerKernel_finite
    [Finite (IsLocalRing.ResidueField O)]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (n : ℕ) :
    Finite (MatrixCongruenceKernel (ι := ι)
      ((IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)).map
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n)))) := by
  letI := residualRepresentationCompletion_finite_quotient ρ n
  infer_instance

end
end Dubon2026
