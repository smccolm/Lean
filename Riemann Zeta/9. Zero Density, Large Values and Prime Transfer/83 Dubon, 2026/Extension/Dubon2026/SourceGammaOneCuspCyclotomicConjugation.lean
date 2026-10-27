import Dubon2026.SourceCyclotomicEllipticCoordinates
import Dubon2026.SourceCyclotomicConjugateCuspOrder
import Dubon2026.SourceCuspWeightImage

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> actual cusp forms under cyclotomic conjugation. Construct the
holomorphic conjugate of the original Fricke image, derive all four conditions
of the proved cusp-form characterization, and recover a cusp form of the same
weight and Gamma1 level. The original cyclotomic fraction algebra is retained. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField SourceFunctionField.CuspWeightCriterion
open ModularForm CongruenceSubgroup
open scoped Manifold MatrixGroups ModularForm

theorem exists_gammaOne_cuspWeightImage_cyclotomic_conjugate (N : ℕ) [NeZero N]
    (σ : kN N ≃ₐ[ℚ] kN N) (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m) (f : CuspForm (Gamma1 N) k)
    (hf : cuspWeightImage (Gamma1 N) k a b m f ∈ holomorphicCyclotomicFrickeFractions N) :
    ∃ f' : CuspForm (Gamma1 N) k,
      cuspWeightImage (Gamma1 N) k a b m f' ∈ holomorphicCyclotomicFrickeFractions N ∧
      CyclotomicConjugates σ (cuspWeightImage (Gamma1 N) k a b m f)
        (cuspWeightImage (Gamma1 N) k a b m f') := by
  obtain ⟨G, hG, hFG⟩ := exists_cyclotomicConjugates σ hf
  obtain ⟨h1, h2, h3, h4⟩ :=
    (CuspWeightCriterion.main (Gamma1 N) k a b m hk _ hf.1).mp
      ⟨f, cuspWeightImage_mul_discriminant (Gamma1 N) k a b m f⟩
  obtain ⟨f', hf'⟩ := (CuspWeightCriterion.main (Gamma1 N) k a b m hk G hG.1).mpr
    ⟨hFG.E4_divisibility hf hG m a h1, hFG.E6_divisibility hf hG m b h2,
      hFG.all_cusps hf hG m h3, hFG.gammaOne_invariant hf hG h4⟩
  have he : cuspWeightImage (Gamma1 N) k a b m f' = G := by
    funext τ
    change f' τ * (E₄ τ ^ a * E₆ τ ^ b) / discriminant τ ^ m = G τ
    rw [hf' τ, mul_div_cancel_right₀ _ (pow_ne_zero _ (discriminant_ne_zero τ))]
  exact ⟨f', he ▸ hG, he ▸ hFG⟩

end
end Dubon2026.SourceFricke
