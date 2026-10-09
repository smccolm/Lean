import Dubon2026.MatrixCongruenceKernelImages
import Dubon2026.CompletedResidualPrimeKernels

/-! # The actual finite congruence images of the original completed residual matrix kernel -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι O : Type*} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]

/-- The literal image of the original completed residual matrix kernel in an actual maximal-power quotient. -/
abbrev CompletedResidualCongruenceImage
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (n : ℕ) :=
  (MatrixCongruenceKernel (ι := ι)
    (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ))).map
      (GeneralLinearGroup.map (n := ι) (R := ResidualRepresentationCompletion ρ)
        (S := ResidualRepresentationCompletion ρ ⧸
          IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n)
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ) ^ n)))

/-- Every genuine congruence image of the original completed residual matrix kernel is a p-group for its original residue prime. -/
theorem completedResidualCongruenceImage_isPGroup
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p] (n : ℕ) :
    IsPGroup p (CompletedResidualCongruenceImage ρ n) :=
  matrixCongruenceKernel_powerImage_isPGroup
    (IsLocalRing.maximalIdeal (ResidualRepresentationCompletion ρ)) hp
    (residualRepresentationCompletion_prime_mem ρ p) n

/-- Each literal original completed congruence image is finite when the original residue field is finite. -/
theorem completedResidualCongruenceImage_finite [Finite (IsLocalRing.ResidueField O)]
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (n : ℕ) :
    Finite (CompletedResidualCongruenceImage ρ n) := by
  letI := residualRepresentationCompletion_finite_quotient ρ n
  infer_instance

end
end Dubon2026
