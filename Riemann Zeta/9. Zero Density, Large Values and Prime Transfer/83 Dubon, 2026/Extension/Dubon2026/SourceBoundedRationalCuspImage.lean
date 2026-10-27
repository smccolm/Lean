import Dubon2026.SourceBoundedRationalJAlgebra
import Dubon2026.SourceRationalCuspWeightIntegrality

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> bounded rational Fourier denominators. The original
rational Fourier cusp form supplies both the actual Fricke-field entry and
the rational monic relation. Their assembled Laurent normality consumer
therefore bounds every coefficient of its exact weight-lowering image by
one integer. No monic, fraction, or denominator-bound premise remains. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField CongruenceSubgroup
open scoped Manifold ModularForm MatrixGroups

theorem exists_bounded_rational_cuspWeightImage_laurent
    (N : ℕ) [NeZero N] (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m) (f : CuspForm (Gamma1 N) k)
    (y : PowerSeries ℚ) (hy : y.map (algebraMap ℚ ℂ) = qExpansion 1 f) :
    ∃ X : LaurentSeries ℚ,
      CuspTaylor.Represents (coeffMap (algebraMap ℚ ℂ) X)
        (cuspFunction N (cuspWeightImage (Gamma1 N) k a b m f)) ∧
      HasBoundedIntegralLaurentCoefficients X := by
  obtain ⟨X, hX, hi⟩ := exists_integral_rational_cuspWeightImage_laurent N k a b m hk f y hy
  refine ⟨X, hX, ?_⟩
  apply hasBoundedIntegralLaurentCoefficients_of_integral_j_of_frickeField N hi
  have hF := gammaOne_cuspWeightImage_mem_original_of_rational_series N k a b m hk f y hy
  apply mem_frickeLaurentFieldK_of_represents_frickeSpan (Submodule.subset_span hF)
  have he : coeffMap (algebraMap (kN N) ℂ) (coeffMap (algebraMap ℚ (kN N)) X) =
      coeffMap (algebraMap ℚ ℂ) X := by
    ext n
    simp only [coeffMap_coeff]
    rfl
  rw [he]
  exact hX

end
end Dubon2026.SourceFricke
