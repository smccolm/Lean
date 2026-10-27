import Dubon2026.SourceEisensteinFactorCyclotomicLaurent
import Dubon2026.SourceCuspWeightImage
import Dubon2026.SourceFrickeHolomorphicIntegralSpan

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational cusp
spanning. An original cyclotomic Fricke image forces cyclotomic Fourier
coefficients of the original cusp form. Laurent division cancels the
actual Eisenstein weight factor, whose nonzero germ has already been proved. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField SourceFunctionField.CuspWeightCriterion
open scoped Manifold ModularForm MatrixGroups

theorem exists_cuspWeightImage_laurent {N : ℕ} [NeZero N]
    (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (a b m : ℕ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : cuspWeightImage Γ k a b m f ∈ holomorphicCyclotomicFrickeFractions N) :
    ∃ X : LaurentSeries (kN N),
      CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) X) (cuspFunction N f) := by
  obtain ⟨_, P, hP, Q, hQ, hQ0, he⟩ := hf
  obtain ⟨X, hX⟩ := exists_cyclotomic_fraction_represents hP hQ hQ0 he
  refine ⟨X * discriminantLaurentK N ^ m /
    (eisensteinLaurentK N 4 ^ a * eisensteinLaurentK N 6 ^ b), ?_⟩
  rw [map_div₀, map_mul, map_pow, coeffMap_discriminantLaurentK]
  apply (hX.cusp_mul ((represents_discriminant_width N).cusp_pow m)).cusp_of_mul_eq
    (represents_eisensteinFactorLaurentK N a b) (eisensteinFactorLaurentK_ne_zero N a b)
  funext τ
  exact cuspWeightImage_mul_discriminant Γ k a b m f τ

theorem cuspWeightImage_qExpansion_coeff_mem {N : ℕ} [NeZero N]
    (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (a b m : ℕ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hf : cuspWeightImage Γ k a b m f ∈ holomorphicCyclotomicFrickeFractions N)
    (hper : Function.Periodic ((f : ℍ → ℂ) ∘ ofComplex) N)
    (hbd : IsBoundedAtImInfty f) (n : ℕ) :
    (qExpansion N f).coeff n ∈ kN N := by
  obtain ⟨X, hX⟩ := exists_cuspWeightImage_laurent Γ k a b m f hf
  have hq := CuspTaylor.represents_qExpansion (by exact_mod_cast NeZero.pos N)
    hper f.holo' hbd
  have hc := congrArg (fun Y : LaurentSeries ℂ => Y.coeff (n : ℤ)) (hX.eq_series hq)
  dsimp only at hc
  rw [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] at hc
  rw [← hc]
  exact (X.coeff (n : ℤ)).property

end
end Dubon2026.SourceFricke
