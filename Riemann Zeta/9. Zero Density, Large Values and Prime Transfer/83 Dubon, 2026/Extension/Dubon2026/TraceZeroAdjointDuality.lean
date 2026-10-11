import Dubon2026.FullAdjointTraceDuality
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Perfect trace duality on the actual trace-zero adjoint module -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]

/-- Restrict both arguments of the genuine trace pairing to the original
trace-zero coefficient submodule. -/
def matrixTraceZeroTracePairing :
    matrixTraceZeroSubmodule ι K →ₗ[K] Module.Dual K (matrixTraceZeroSubmodule ι K) :=
  ((matrixTraceZeroSubmodule ι K).subtype.dualMap).comp
    (fullMatrixTracePairing.comp (matrixTraceZeroSubmodule ι K).subtype)

/-- A trace-zero matrix pairs identically with a matrix and with its actual
trace-free part. This identity itself does not require invertible dimension. -/
theorem matrixTraceZero_traceFreePart_pairing
    (X : matrixTraceZeroSubmodule ι K) (Y : Matrix ι ι K) :
    Matrix.trace (X.val * matrixTraceFreePart Y) = Matrix.trace (X.val * Y) := by
  have hX : Matrix.trace X.val = 0 := X.property
  rw [matrixTraceFreePart, mul_sub, Matrix.mul_smul, mul_one,
    Matrix.trace_sub, Matrix.trace_smul, hX, smul_zero, sub_zero]

/-- The trace pairing on the actual trace-zero module is injective when the
matrix dimension is nonzero in the original coefficient field. -/
theorem matrixTraceZeroTracePairing_injective (hn : (Fintype.card ι : K) ≠ 0) :
    Function.Injective (matrixTraceZeroTracePairing (ι := ι) (K := K)) := by
  intro X Y h
  apply Subtype.ext
  apply fullMatrixTracePairing_bijective.1
  ext Z
  have hz := DFunLike.congr_fun h
    (⟨matrixTraceFreePart Z, matrixTraceFreePart_trace hn Z⟩ : matrixTraceZeroSubmodule ι K)
  change Matrix.trace (X.val * matrixTraceFreePart Z) =
    Matrix.trace (Y.val * matrixTraceFreePart Z) at hz
  exact (matrixTraceZero_traceFreePart_pairing X Z).symm.trans
    (hz.trans (matrixTraceZero_traceFreePart_pairing Y Z))

/-- Actual finite-dimensional linear algebra upgrades nondegeneracy to perfect
duality of the trace-zero module; no arithmetic duality is assumed or claimed. -/
theorem matrixTraceZeroTracePairing_bijective (hn : (Fintype.card ι : K) ≠ 0) :
    Function.Bijective (matrixTraceZeroTracePairing (ι := ι) (K := K)) := by
  have hi := matrixTraceZeroTracePairing_injective hn
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    Subspace.dual_finrank_eq.symm).mp hi⟩

/-- The restricted trace pairing intertwines the actual trace-zero adjoint and
the actual contragredient representation. -/
theorem matrixTraceZeroTracePairing_adjoint
    (ρ : G →* GeneralLinearGroup ι K) (g : G) (X : matrixTraceZeroSubmodule ι K) :
    matrixTraceZeroTracePairing (matrixTraceZeroAdjointRepresentation ρ g X) =
      (matrixTraceZeroAdjointRepresentation ρ).dual g (matrixTraceZeroTracePairing X) := by
  ext Y
  exact DFunLike.congr_fun (fullMatrixTracePairing_adjoint ρ g X.val) Y.val

/-- The original trace-zero adjoint is identified with its true linear dual
by the trace form when the characteristic does not divide the matrix dimension. -/
def matrixTraceZeroAdjointTraceDuality (hn : (Fintype.card ι : K) ≠ 0)
    (ρ : G →* GeneralLinearGroup ι K) :
    Representation.Equiv (matrixTraceZeroAdjointRepresentation ρ)
      (matrixTraceZeroAdjointRepresentation ρ).dual where
  toLinearEquiv := LinearEquiv.ofBijective matrixTraceZeroTracePairing
    (matrixTraceZeroTracePairing_bijective hn)
  isIntertwining' g := by
    apply LinearMap.ext
    intro X
    exact matrixTraceZeroTracePairing_adjoint ρ g X

end
end Dubon2026
