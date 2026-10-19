import Dubon2026.CocycleKernelTranslateDetection
import Dubon2026.TraceZeroContinuousCharacterPairing

/-! The invariant functional required by DUB-17 dual Selmer detection is
the actual trace pairing with a commuting trace-zero matrix. The original
twisted trace-zero action is used in every dimension. A scalar residual
kernel element with trivial character acts trivially on these coefficients.
Existence of the residual elements and the nonzero trace pairing remains
the residual-image obligation. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι k : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field k]

/-- A commuting original trace-zero matrix is fixed by the actual
trace-zero adjoint action of the same group element. -/
theorem matrixTraceZeroAdjoint_fixed_of_commute
    (ρ : G →* GeneralLinearGroup ι k) (g : G)
    (M : matrixTraceZeroSubmodule ι k)
    (hM : (ρ g).val * M.val = M.val * (ρ g).val) :
    (matrixTraceZeroAdjointRep ρ).ρ g M = M := by
  apply Subtype.ext
  change (ρ g).val * M.val * (ρ g⁻¹).val = M.val
  rw [hM, mul_assoc, map_inv, Units.mul_inv, mul_one]

/-- The actual trace functional is fixed by the twisted adjoint action
when the character is trivial and the witness matrix commutes with the
original residual image. No independent functional-invariance premise remains. -/
theorem matrixTraceZero_traceFunctional_fixed
    (ρ : G →* GeneralLinearGroup ι k) (χ : G →* k) (g : G)
    (hχ : χ g = 1) (M : matrixTraceZeroSubmodule ι k)
    (hM : (ρ g).val * M.val = M.val * (ρ g).val)
    (X : matrixTraceZeroSubmodule ι k) :
    matrixTraceZeroTracePairing.flip M ((matrixTraceZeroCharacterRep ρ χ).ρ g X) =
      matrixTraceZeroTracePairing.flip M X := by
  have hfix := matrixTraceZeroAdjoint_fixed_of_commute ρ g M hM
  have he := matrixTraceZeroTracePairing_character_equivariant ρ χ g X M
  rw [hfix] at he
  change matrixTraceZeroTracePairing ((matrixTraceZeroCharacterRep ρ χ).ρ g X) M =
    χ g * matrixTraceZeroTracePairing X M at he
  rw [hχ, one_mul] at he
  exact he

/-- An actual scalar residual image acts trivially on the original
twisted trace-zero coefficients when its character value is one. -/
theorem matrixTraceZeroCharacterRep_eq_one_of_scalar
    (ρ : G →* GeneralLinearGroup ι k) (χ : G →* k) (τ : G)
    (hχ : χ τ = 1) (d : k) (hscalar : (ρ τ).val = d • (1 : Matrix ι ι k)) :
    (matrixTraceZeroCharacterRep ρ χ).ρ τ = 1 := by
  apply LinearMap.ext
  intro X
  have hcomm : (ρ τ).val * X.val = X.val * (ρ τ).val := by
    rw [hscalar, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hfix := matrixTraceZeroAdjoint_fixed_of_commute ρ τ X hcomm
  change χ τ • (matrixTraceZeroAdjointRep ρ).ρ τ X = X
  rw [hχ, one_smul, hfix]

/-- A nonzero actual trace pairing supplies a detecting element for the
same twisted trace-zero cocycle, with both candidate residual images retained. -/
theorem traceCocycle_exists_detecting_kernel_translate
    (ρ : G →* GeneralLinearGroup ι k) (χ : G →* k)
    (c : groupCohomology.cocycles₁ (matrixTraceZeroCharacterRep ρ χ))
    (H : Subgroup G) (g τ : G) (hg : g ∈ H) (hτ : τ ∈ H)
    (hχg : χ g = 1) (hχτ : χ τ = 1)
    (d : k) (hscalar : (ρ τ).val = d • (1 : Matrix ι ι k))
    (M : matrixTraceZeroSubmodule ι k)
    (hM : (ρ g).val * M.val = M.val * (ρ g).val)
    (hc : Matrix.trace ((c τ).val * M.val) ≠ 0) :
    ∃ σ : G, σ ∈ H ∧ (σ = g ∨ σ = τ * g) ∧
      c σ ∉ LinearMap.range ((matrixTraceZeroCharacterRep ρ χ).ρ σ - 1) := by
  apply cocycle_exists_detecting_of_kernel_functional (matrixTraceZeroCharacterRep ρ χ)
    c H g τ hg hτ (matrixTraceZeroCharacterRep_eq_one_of_scalar ρ χ τ hχτ d hscalar)
    (matrixTraceZeroTracePairing.flip M)
  · exact matrixTraceZero_traceFunctional_fixed ρ χ g hχg M hM
  · exact hc

end
end Dubon2026
