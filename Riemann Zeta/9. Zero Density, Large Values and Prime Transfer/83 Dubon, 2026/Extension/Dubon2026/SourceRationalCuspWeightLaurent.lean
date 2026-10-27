import Dubon2026.SourceGammaOneFourierLinear

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> bounded rational Fourier denominators. Construct
the literal rational Laurent germ of the source weight-lowering image
directly from the original cusp Fourier series and the proved rational
Eisenstein and integral discriminant expansions. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField CongruenceSubgroup ModularForm
open SourceFunctionField.CuspWeightCriterion
open scoped Manifold ModularForm MatrixGroups

theorem represents_qExpand_rational_series (N : ℕ) [NeZero N]
    (F : ℍ → ℂ) (y : PowerSeries ℚ)
    (hy : y.map (algebraMap ℚ ℂ) = qExpansion 1 F)
    (hper : Function.Periodic (F ∘ ofComplex) 1) (hhol : MDiff F)
    (hbd : IsBoundedAtImInfty F) :
    CuspTaylor.Represents (coeffMap (algebraMap ℚ ℂ) (qExpand ℚ N y))
      (cuspFunction N F) := by
  rw [coeffMap_qExpand, coeffMap_ofPowerSeries, hy,
    ← qExpansion_laurent_width F N hper hhol hbd]
  exact CuspTaylor.represents_qExpansion (by exact_mod_cast NeZero.pos N)
    (by simpa using hper.nat_mul N) hhol hbd

theorem exists_rational_cuspWeightImage_laurent (N : ℕ) [NeZero N]
    (k : ℤ) (a b m : ℕ) (f : CuspForm (Gamma1 N) k)
    (y : PowerSeries ℚ) (hy : y.map (algebraMap ℚ ℂ) = qExpansion 1 f) :
    ∃ X : LaurentSeries ℚ, CuspTaylor.Represents (coeffMap (algebraMap ℚ ℂ) X)
      (cuspFunction N (cuspWeightImage (Gamma1 N) k a b m f)) := by
  have hp := gammaOne_one_mem_strictPeriods N
  letI : Fact (IsCusp OnePoint.infty ((Gamma1 N) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods zero_lt_one hp⟩
  have hf := represents_qExpand_rational_series N f y hy
    (SlashInvariantFormClass.periodic_comp_ofComplex f hp) f.holo'
    (ModularFormClass.bdd_at_infty f)
  have h4 := represents_qExpand_rational_series N E₄ (eisensteinQSeries 4)
    (eisensteinQSeries_map (by norm_num) (by decide))
    (SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL)
    E₄.holo' (ModularFormClass.bdd_at_infty E₄)
  have h6 := represents_qExpand_rational_series N E₆ (eisensteinQSeries 6)
    (eisensteinQSeries_map (by norm_num) (by decide))
    (SlashInvariantFormClass.periodic_comp_ofComplex E₆ one_mem_strictPeriods_SL)
    E₆.holo' (ModularFormClass.bdd_at_infty E₆)
  let D : PowerSeries ℚ := (PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom ℚ)
  have hD : D.map (algebraMap ℚ ℂ) = qExpansion 1 (⇑CuspForm.discriminant : ℍ → ℂ) := by
    rw [CuspForm.coe_discriminant, qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit]
    ext n
    simp only [D, PowerSeries.coeff_map, Int.coe_castRingHom, map_intCast]
  have hd := represents_qExpand_rational_series N CuspForm.discriminant D hD
    (SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL)
    CuspForm.discriminant.holo' (ModularFormClass.bdd_at_infty CuspForm.discriminant)
  refine ⟨qExpand ℚ N y * (qExpand ℚ N (eisensteinQSeries 4) ^ a *
    qExpand ℚ N (eisensteinQSeries 6) ^ b) / qExpand ℚ N D ^ m, ?_⟩
  rw [map_div₀, map_mul, map_mul, map_pow, map_pow, map_pow]
  exact (hf.cusp_mul ((h4.cusp_pow a).cusp_mul (h6.cusp_pow b))).cusp_div (hd.cusp_pow m)

end
end Dubon2026.SourceFricke
