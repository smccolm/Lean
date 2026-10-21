import Dubon2026.PolarizedBlockContinuity
import Mathlib.LinearAlgebra.Matrix.Trace

/-! DUB-17/18 -> residual Galois association -> undo the weight-two
descent's exact cyclotomic factor. The original scalar centrality and
continuity theorems construct the actual rank-two character twist.
-/
namespace Dubon2026
noncomputable section
open Matrix
variable {G R : Type} [Group G] [CommRing R]

/-- The genuine scalar-character twist of a rank-two Galois representation. -/
def sourceGaloisCharacterTwist
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (χ : G →* Rˣ) :
    G →* GeneralLinearGroup (Fin 2) R where
  toFun g := GeneralLinearGroup.scalar (Fin 2) (χ g) * ρ g
  map_one' := by rw [map_one, map_one, map_one, one_mul]
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul]
    have hc := polarizedScalar_commute (χ h) (ρ g)
    calc
      _ = GeneralLinearGroup.scalar (Fin 2) (χ g) *
          (GeneralLinearGroup.scalar (Fin 2) (χ h) * ρ g) * ρ h := by
        simp only [mul_assoc]
      _ = _ := by rw [hc.eq]; simp only [mul_assoc]

/-- The new matrix is exactly the original matrix times the prescribed scalar. -/
theorem sourceGaloisCharacterTwist_val
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (χ : G →* Rˣ) (g : G) :
    (sourceGaloisCharacterTwist ρ χ g).val = (χ g : R) • (ρ g).val := by
  change Matrix.scalar (Fin 2) (χ g : R) * (ρ g).val = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

/-- The scalar-character twist preserves continuity in the original coefficient topology. -/
theorem sourceGaloisCharacterTwist_continuous
    [TopologicalSpace G] [TopologicalSpace R] [IsTopologicalRing R]
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (χ : G →* Rˣ)
    (hρ : Continuous ρ) (hχ : Continuous χ) :
    Continuous (sourceGaloisCharacterTwist ρ χ) :=
  (polarizedScalar_continuous.comp hχ).mul hρ

/-- Twisting multiplies the original Frobenius trace by the prescribed character. -/
theorem sourceGaloisCharacterTwist_trace
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (χ : G →* Rˣ) (g : G) :
    Matrix.trace (sourceGaloisCharacterTwist ρ χ g).val =
      (χ g : R) * Matrix.trace (ρ g).val := by
  rw [sourceGaloisCharacterTwist_val, Matrix.trace_smul, smul_eq_mul]

/-- The rank-two determinant acquires exactly the square of the character. -/
theorem sourceGaloisCharacterTwist_det
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (χ : G →* Rˣ) (g : G) :
    Matrix.det (sourceGaloisCharacterTwist ρ χ g).val =
      (χ g : R) ^ 2 * Matrix.det (ρ g).val := by
  rw [sourceGaloisCharacterTwist_val, Matrix.det_smul, Fintype.card_fin]

/-- Original inertia remains trivial when both the representation and the
twisting character kill it. -/
theorem sourceGaloisCharacterTwist_eq_one
    (ρ : G →* GeneralLinearGroup (Fin 2) R) (χ : G →* Rˣ) (g : G)
    (hρ : ρ g = 1) (hχ : χ g = 1) : sourceGaloisCharacterTwist ρ χ g = 1 := by
  change GeneralLinearGroup.scalar (Fin 2) (χ g) * ρ g = 1
  rw [hρ, hχ, map_one, one_mul]

end
end Dubon2026
