import Dubon2026.IntegralWeightLeadingLU
import Dubon2026.IntegralWeightGenericMinors
import Dubon2026.IntegralDominantVectorTranspose

/-! The actual generic matrix lies in the upper-times-lower open cell.
The original all-algebra covariance can therefore determine a highest
regular function by one value. No Bruhat decomposition is assumed.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- Nonzero leading minors of the original inverse give an upper-times-lower factorization of the original invertible matrix. -/
theorem integralWeight_borel_openCell (g : GeneralLinearGroup (Fin n) K)
    (h : ∀ (k : ℕ) (hk : k ≤ n),
      ((g⁻¹).val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) :
    ∃ b c : generalLinearBorel K n, g = b.val * integralWeightTranspose c.val := by
  obtain ⟨L, U, hLU, hL, hU⟩ := integralWeight_exists_LU_of_leading n (g⁻¹).val h
  have hprod : L.det * U.det ≠ 0 := by
    rw [← Matrix.det_mul, ← hLU]
    exact (GeneralLinearGroup.det g⁻¹).ne_zero
  let l := GeneralLinearGroup.mkOfDetNeZero L (left_ne_zero_of_mul hprod)
  let u := GeneralLinearGroup.mkOfDetNeZero U (right_ne_zero_of_mul hprod)
  have hgl : g⁻¹ = l * u := Units.ext hLU
  have hlu : (l⁻¹).val.BlockTriangular OrderDual.toDual := by
    rw [GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hL
  have huu : (u⁻¹).val.BlockTriangular id := by
    rw [GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hU
  let b : generalLinearBorel K n := ⟨u⁻¹, huu⟩
  let c : generalLinearBorel K n := ⟨integralWeightTranspose l⁻¹, by
    intro i j hij
    exact hlu hij⟩
  refine ⟨b, c, ?_⟩
  change g = u⁻¹ * integralWeightTranspose (integralWeightTranspose l⁻¹)
  rw [integralWeightTranspose_involutive]
  simpa only [inv_inv, _root_.mul_inv_rev] using congrArg Inv.inv hgl

/-- The original generic matrix, faithfully embedded in its own coordinate fraction field, has the required actual Borel open-cell factorization. -/
theorem integralWeightGeneric_fraction_openCell (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) :
    ∃ b c : generalLinearBorel (FractionRing (GeneralLinearRegularFunctions R n)) n,
      GeneralLinearGroup.map
        (algebraMap (GeneralLinearRegularFunctions R n)
          (FractionRing (GeneralLinearRegularFunctions R n)))
        (generalLinearRegularGeneric R n) = b.val * integralWeightTranspose c.val := by
  apply integralWeight_borel_openCell
  intro k hk
  rw [← map_inv]
  exact integralWeightGenericInverse_fraction_leading_ne_zero R n k hk

end
end Dubon2026
