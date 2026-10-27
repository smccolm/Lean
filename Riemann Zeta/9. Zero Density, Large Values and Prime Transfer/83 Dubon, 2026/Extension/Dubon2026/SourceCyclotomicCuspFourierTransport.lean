import Dubon2026.SourceGammaOneCuspCyclotomicConjugation
import Dubon2026.SourceEisensteinFactorCyclotomicLaurent

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> Fourier conjugation of the constructed cusp form. Rational
Eisenstein and discriminant expansions are fixed under every cyclotomic
embedding. Cancel their actual nonzero Laurent germs in the weight identity;
no weight-zero membership is asserted for the positive-weight Eisenstein factor. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass
open SourceFunctionField SourceFunctionField.CuspWeightCriterion
open scoped Manifold ModularForm MatrixGroups

theorem coeffMap_eisensteinLaurentK_ringHom (N : ℕ) [NeZero N] (φ : kN N →+* ℂ)
    {k : ℕ} (hk : 3 ≤ k) (heven : Even k) :
    coeffMap φ (eisensteinLaurentK N k) =
      (qExpansion N (E hk : ℍ → ℂ) : LaurentSeries ℂ) := by
  rw [eisensteinLaurentK, coeffMap_qExpand, coeffMap_ofPowerSeries]
  have he : ((eisensteinQSeries k).map (algebraMap ℚ (kN N))).map φ =
      (eisensteinQSeries k).map (algebraMap ℚ ℂ) := by
    ext n
    simp only [PowerSeries.coeff_map, eq_ratCast, map_ratCast]
  rw [he, eisensteinQSeries_map hk heven]
  exact (qExpansion_laurent_width _ N
    (periodic_comp_ofComplex (E hk) one_mem_strictPeriods_SL)
    (E hk).holo' (ModularFormClass.bdd_at_infty (E hk))).symm

theorem coeffMap_eisensteinFactorLaurentK_ringHom (N : ℕ) [NeZero N]
    (φ : kN N →+* ℂ) (a b : ℕ) :
    coeffMap φ (eisensteinLaurentK N 4 ^ a * eisensteinLaurentK N 6 ^ b) =
      coeffMap (algebraMap (kN N) ℂ)
        (eisensteinLaurentK N 4 ^ a * eisensteinLaurentK N 6 ^ b) := by
  simp only [map_mul, map_pow,
    coeffMap_eisensteinLaurentK_ringHom N φ (by norm_num : 3 ≤ 4) (by decide : Even 4),
    coeffMap_eisensteinLaurentK_ringHom N φ (by norm_num : 3 ≤ 6) (by decide : Even 6),
    coeffMap_eisensteinLaurentK N (by norm_num : 3 ≤ 4) (by decide : Even 4),
    coeffMap_eisensteinLaurentK N (by norm_num : 3 ≤ 6) (by decide : Even 6)]

theorem CyclotomicConjugates.cusp_forms {N : ℕ} [NeZero N]
    {σ : kN N ≃ₐ[ℚ] kN N} (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (a b m : ℕ)
    (f g : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hfg : CyclotomicConjugates σ (cuspWeightImage Γ k a b m f)
      (cuspWeightImage Γ k a b m g)) : CyclotomicConjugates σ f g := by
  obtain ⟨A, hA, hAG⟩ := hfg
  let X := A * discriminantLaurentK N ^ m /
    (eisensteinLaurentK N 4 ^ a * eisensteinLaurentK N 6 ^ b)
  refine ⟨X, ?_, ?_⟩
  · dsimp only [X]
    rw [map_div₀, map_mul, map_pow, coeffMap_discriminantLaurentK]
    apply (hA.cusp_mul ((represents_discriminant_width N).cusp_pow m)).cusp_of_mul_eq
      (represents_eisensteinFactorLaurentK N a b) (eisensteinFactorLaurentK_ne_zero N a b)
    funext τ
    exact cuspWeightImage_mul_discriminant Γ k a b m f τ
  · let φ := (algebraMap (kN N) ℂ).comp σ.toRingEquiv.toRingHom
    change CuspTaylor.Represents (coeffMap φ X) (cuspFunction N g)
    dsimp only [X]
    rw [map_div₀, map_mul, map_pow, coeffMap_discriminantLaurentK_ringHom,
      coeffMap_eisensteinFactorLaurentK_ringHom]
    apply (hAG.cusp_mul ((represents_discriminant_width N).cusp_pow m)).cusp_of_mul_eq
      (represents_eisensteinFactorLaurentK N a b) (eisensteinFactorLaurentK_ne_zero N a b)
    funext τ
    exact cuspWeightImage_mul_discriminant Γ k a b m g τ

end
end Dubon2026.SourceFricke
