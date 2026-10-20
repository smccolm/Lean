import Dubon2026.IntegralWeightBorelOpenCell

/-! The generic open cell with an actual unitriangular second factor.
Removing its diagonal makes invariance under the opposite unipotent
subgroup sufficient for uniqueness. This supplies the invariant-line
interface for the required characteristic-zero irreducibility argument.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable (R : Type*) [CommRing R] (n : ℕ)

/-- The actual invertible diagonal part of an original Borel matrix. -/
def integralWeightBorelDiagonalMatrix (b : generalLinearBorel R n) :
    generalLinearBorel R n :=
  ⟨⟨Matrix.diagonal (fun i => (generalLinearBorelDiagonalUnit b i : R)),
    Matrix.diagonal (fun i => ((generalLinearBorelDiagonalUnit b i)⁻¹ : Rˣ)),
    by simp [Matrix.diagonal_mul_diagonal],
    by simp [Matrix.diagonal_mul_diagonal]⟩, Matrix.blockTriangular_diagonal _⟩

/-- The actual diagonal part preserves every original diagonal unit. -/
theorem integralWeightBorelDiagonalMatrix_diagonal (b : generalLinearBorel R n) (i : Fin n) :
    generalLinearBorelDiagonalUnit (integralWeightBorelDiagonalMatrix R n b) i =
      generalLinearBorelDiagonalUnit b i := by
  apply Units.ext
  exact Matrix.diagonal_apply_eq _ i

/-- The actual diagonal matrix is unchanged by transpose. -/
theorem integralWeightBorelDiagonalMatrix_transpose (b : generalLinearBorel R n) :
    integralWeightTranspose (integralWeightBorelDiagonalMatrix R n b).val =
      (integralWeightBorelDiagonalMatrix R n b).val := by
  apply Units.ext
  exact Matrix.diagonal_transpose _

/-- Dividing the original Borel matrix on the right by its actual diagonal leaves diagonal units equal to one. -/
theorem integralWeightBorel_unitriangular_diagonal (b : generalLinearBorel R n) (i : Fin n) :
    generalLinearBorelDiagonalUnit (b * (integralWeightBorelDiagonalMatrix R n b)⁻¹) i = 1 := by
  change generalLinearBorelDiagonal i (b * (integralWeightBorelDiagonalMatrix R n b)⁻¹) = 1
  rw [map_mul, map_inv]
  change generalLinearBorelDiagonalUnit b i *
    (generalLinearBorelDiagonalUnit (integralWeightBorelDiagonalMatrix R n b) i)⁻¹ = 1
  rw [integralWeightBorelDiagonalMatrix_diagonal, mul_inv_cancel]

/-- The original generic fraction-field matrix has an actual upper-Borel times lower-unitriangular factorization, with all minor hypotheses discharged. -/
theorem integralWeightGeneric_fraction_unitriangularCell [IsDomain R] :
    ∃ b c : generalLinearBorel (FractionRing (GeneralLinearRegularFunctions R n)) n,
      GeneralLinearGroup.map
        (algebraMap (GeneralLinearRegularFunctions R n)
          (FractionRing (GeneralLinearRegularFunctions R n)))
        (generalLinearRegularGeneric R n) = b.val * integralWeightTranspose c.val ∧
      ∀ i, generalLinearBorelDiagonalUnit c i = 1 := by
  obtain ⟨b, c, hc⟩ := integralWeightGeneric_fraction_openCell R n
  let d := integralWeightBorelDiagonalMatrix _ n c
  let u := c * d⁻¹
  refine ⟨b * d, u, ?_, integralWeightBorel_unitriangular_diagonal _ n c⟩
  have hcu : c.val = u.val * d.val := by
    change c.val = (c.val * d.val⁻¹) * d.val
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [hc, hcu, integralWeightTranspose_mul, integralWeightBorelDiagonalMatrix_transpose]
  exact (mul_assoc b.val d.val (integralWeightTranspose u.val)).symm

end
end Dubon2026
