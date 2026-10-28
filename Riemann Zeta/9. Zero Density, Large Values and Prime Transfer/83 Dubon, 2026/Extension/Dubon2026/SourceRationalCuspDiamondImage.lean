import Dubon2026.SourceRationalDiamondFraction
import Dubon2026.SourceRationalCuspWeightIntegrality

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond Galois compatibility. Actual rational cusp forms discharge the
Fricke-fraction and rational-germ inputs of diamond descent. The existing
weight-lowering criterion supplies Gamma1 invariance. Normalized cusp
quotients will apply this to the original integral modular-ratio generators.
-/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField CongruenceSubgroup
open scoped MatrixGroups

theorem exists_rational_cuspWeightImage_diamond_laurent
    (N : ℕ) [NeZero N] (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m) (f : CuspForm (Gamma1 N) k)
    (y : PowerSeries ℚ) (hy : y.map (algebraMap ℚ ℂ) = qExpansion 1 f) (g : Gamma0 N) :
    ∃ X : LaurentSeries ℚ,
      CuspTaylor.Represents (coeffMap (algebraMap ℚ ℂ) X)
        (cuspFunction N (cuspWeightImage (Gamma1 N) k a b m f ∘ (g.val • ·))) := by
  have hF := gammaOne_cuspWeightImage_mem_original_of_rational_series N k a b m hk f y hy
  obtain ⟨X, hX⟩ := exists_rational_cuspWeightImage_laurent N k a b m f y hy
  have hinv := (CuspWeightCriterion.forward hk f
    (cuspWeightImage_mul_discriminant (Gamma1 N) k a b m f)).2.2.2
  exact exists_rational_laurent_diamond_fraction N hF hinv X hX g

end
end Dubon2026.SourceFricke
