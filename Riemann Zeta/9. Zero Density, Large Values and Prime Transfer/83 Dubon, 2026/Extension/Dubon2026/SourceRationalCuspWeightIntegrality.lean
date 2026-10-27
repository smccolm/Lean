import Dubon2026.SourceRationalCuspWeightLaurent
import Dubon2026.SourceFrickeLaurentSpanDescent
import Dubon2026.SourceCuspWeightImageSpan

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> bounded rational Fourier denominators. Derive
original Fricke membership and a monic relation over rational j from the
original cusp form and its rational Fourier series. Neither original-field
membership nor an integral equation is an additional hypothesis. The exact
source weight balance is retained. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField CongruenceSubgroup
open scoped Manifold ModularForm MatrixGroups

theorem gammaOne_cuspWeightImage_mem_original_of_rational_series
    (N : ℕ) [NeZero N] (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m) (f : CuspForm (Gamma1 N) k)
    (y : PowerSeries ℚ) (hy : y.map (algebraMap ℚ ℂ) = qExpansion 1 f) :
    cuspWeightImage (Gamma1 N) k a b m f ∈ holomorphicCyclotomicFrickeFractions N := by
  obtain ⟨X, hX⟩ := exists_rational_cuspWeightImage_laurent N k a b m f y hy
  have hΓ : Gamma N ≤ Gamma1 N := by
    intro A hA
    simp_all [Gamma1_mem, Gamma_mem]
  apply holomorphicCyclotomicFrickeFractions_of_represents_frickeSpan
    (cuspWeightImage_mem_frickeSpan N (Gamma1 N) hΓ k a b m hk f)
    (X := coeffMap (algebraMap ℚ (kN N)) X)
  have he : coeffMap (algebraMap (kN N) ℂ) (coeffMap (algebraMap ℚ (kN N)) X) =
      coeffMap (algebraMap ℚ ℂ) X := by
    ext n
    simp only [coeffMap_coeff]
    rfl
  rw [he]
  exact hX

theorem exists_integral_rational_cuspWeightImage_laurent
    (N : ℕ) [NeZero N] (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m) (f : CuspForm (Gamma1 N) k)
    (y : PowerSeries ℚ) (hy : y.map (algebraMap ℚ ℂ) = qExpansion 1 f) :
    ∃ X : LaurentSeries ℚ,
      CuspTaylor.Represents (coeffMap (algebraMap ℚ ℂ) X)
        (cuspFunction N (cuspWeightImage (Gamma1 N) k a b m f)) ∧
      IsIntegral (Algebra.adjoin ℚ ({jqNModC ℚ N} : Set (LaurentSeries ℚ))) X := by
  obtain ⟨X, hX⟩ := exists_rational_cuspWeightImage_laurent N k a b m f y hy
  refine ⟨X, hX, ?_⟩
  have hF := gammaOne_cuspWeightImage_mem_original_of_rational_series N k a b m hk f y hy
  have he : coeffMap (algebraMap (kN N) ℂ) (coeffMap (algebraMap ℚ (kN N)) X) =
      coeffMap (algebraMap ℚ ℂ) X := by
    ext n
    simp only [coeffMap_coeff]
    rfl
  have hXK : CuspTaylor.Represents
      (coeffMap (algebraMap (kN N) ℂ) (coeffMap (algebraMap ℚ (kN N)) X))
      (cuspFunction N (cuspWeightImage (Gamma1 N) k a b m f)) := by
    rw [he]
    exact hX
  apply isIntegral_adjoin_of_isIntegral_coeffMap (algebraMap ℚ (kN N))
  have hj : coeffMap (algebraMap ℚ (kN N)) (jqNModC ℚ N) = jqNModC (kN N) N := by
    rw [jqNModC, coeffMap_qExpand, jqNModC]
    congr 1
    exact map_jqModC (algebraMap ℚ (kN N))
  rw [hj]
  exact isIntegral_laurent_holomorphic_fraction hF hXK

end
end Dubon2026.SourceFricke
