import Dubon2026.SourceRationalCuspWeightCancellation
import Dubon2026.SourceBoundedRationalSeriesImage
import Dubon2026.SourceGammaOneRationalCuspSpan

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field. The original rational Fourier cusp form admits one
nonzero integer multiple with a literal integral Fourier expansion.
Combining this with actual rational Fourier spanning gives integral cusp
spanning, in particular in geometric weight two at every nonzero level.
The differential realization and arithmetic comparison remain downstream. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField CongruenceSubgroup
open scoped Manifold ModularForm MatrixGroups

theorem exists_gammaOne_integralQExp_int_multiple (N : ℕ) [NeZero N]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ Set.range ((↑) : ℚ → ℂ)) :
    ∃ d : ℤ, d ≠ 0 ∧ ∃ p : PowerSeries ℤ,
      GammaOne.IsIntegralQExp ((d : ℂ) • f) p := by
  classical
  choose c hc using hf
  let y : PowerSeries ℚ := PowerSeries.mk c
  have hy : y.map (algebraMap ℚ ℂ) = qExpansion 1 f := by
    apply PowerSeries.ext
    intro n
    simpa only [y, PowerSeries.coeff_map, PowerSeries.coeff_mk] using hc n
  have hb := gammaOne_rational_series_hasBoundedIntegralCoefficients N k a b m hk f y hy
  obtain ⟨d, p, hd, hp⟩ := hb.exists_integer_series
  refine ⟨d, hd, p, ?_⟩
  unfold GammaOne.IsIntegralQExp
  rw [ModularForm.qExpansion_smul zero_lt_one (gammaOne_one_mem_strictPeriods N) (d : ℂ) f,
    PowerSeries.smul_eq_C_mul, ← hy]
  have hm := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) hp
  apply PowerSeries.ext
  intro n
  have hn := congrArg (fun s : PowerSeries ℂ => s.coeff n) hm
  simpa only [PowerSeries.coeff_map, PowerSeries.coeff_C_mul, map_mul,
    Int.coe_castRingHom, map_intCast] using hn

theorem span_gammaOne_integral_cuspForms_eq_top (N : ℕ) [NeZero N]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m) :
    Submodule.span ℂ {f : CuspForm (Gamma1 N) k |
      ∃ p : PowerSeries ℤ, GammaOne.IsIntegralQExp f p} = ⊤ := by
  classical
  apply top_unique
  rw [← span_gammaOne_rational_cuspForms_eq_top N k a b m hk]
  apply Submodule.span_le.mpr
  intro f hf
  obtain ⟨d, hd, p, hp⟩ := exists_gammaOne_integralQExp_int_multiple N k a b m hk f hf
  have hdc : (d : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have hm : (d : ℂ) • f ∈ Submodule.span ℂ {g : CuspForm (Gamma1 N) k |
      ∃ p : PowerSeries ℤ, GammaOne.IsIntegralQExp g p} :=
    Submodule.subset_span ⟨p, hp⟩
  have hs := Submodule.smul_mem _ (d : ℂ)⁻¹ hm
  simpa only [inv_smul_smul₀ hdc] using hs

theorem span_gammaOne_weightTwo_integral_cuspForms_eq_top (N : ℕ) [NeZero N] :
    Submodule.span ℂ {f : CuspForm (Gamma1 N) 2 |
      ∃ p : PowerSeries ℤ, GammaOne.IsIntegralQExp f p} = ⊤ :=
  span_gammaOne_integral_cuspForms_eq_top N 2 1 1 1 (by norm_num)

end
end Dubon2026.SourceFricke
