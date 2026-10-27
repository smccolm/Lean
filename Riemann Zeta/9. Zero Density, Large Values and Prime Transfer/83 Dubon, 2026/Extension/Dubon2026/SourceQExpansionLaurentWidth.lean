import Dubon2026.SourceQExpansionPeriodWidth
import Dubon2026.SourceCuspLaurentFunctionIdentity
import Dubon2026.SourceAnalyticJTransformation
import Dubon2026.SourceLaurentReindex
import Dubon2026.SourceIntegralPowerSeriesFrobenius

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> Laurent coefficient descent. The existing width formula and
native power-series substitution identify the actual width-N expansions
with the original Laurent reindexing, including the literal j series. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass
open scoped Manifold ModularForm MatrixGroups

theorem qExpansion_eq_expand (f : ℍ → ℂ) {N : ℕ} (hN : N ≠ 0)
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbd : IsBoundedAtImInfty f) :
    qExpansion N f = (qExpansion 1 f).expand N hN := by
  ext n
  rw [SourceFricke.qExpansion_coeff_width f hN hper hhol hbd, PowerSeries.coeff_expand]

theorem qExpansion_laurent_width (f : ℍ → ℂ) (N : ℕ) [NeZero N]
    (hper : Function.Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbd : IsBoundedAtImInfty f) :
    (qExpansion N f : LaurentSeries ℂ) = qExpand ℂ N (qExpansion 1 f) := by
  rw [qExpansion_eq_expand f (NeZero.ne N) hper hhol hbd, qExpand_ofPowerSeries_eq_expand]

theorem represents_jqNModC (N : ℕ) [NeZero N] :
    CuspTaylor.Represents (jqNModC ℂ N) (cuspFunction N JMultiplicity.jf) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have h4p := periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL
  have hdp := periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL
  have h4 := CuspTaylor.represents_qExpansion hN (by simpa using h4p.nat_mul N)
    E₄.holo' (ModularFormClass.bdd_at_infty E₄)
  have hd := CuspTaylor.represents_qExpansion hN (by simpa using hdp.nat_mul N)
    CuspForm.discriminant.holo' (ModularFormClass.bdd_at_infty CuspForm.discriminant)
  have he : ((⇑E₄ : ℍ → ℂ) ^ 3 / ⇑CuspForm.discriminant) = JMultiplicity.jf := rfl
  rw [jqNModC, jqModC_eq_modular_quotient, ← CuspForm.coe_discriminant, map_div₀, map_pow,
    ← qExpansion_laurent_width _ N h4p E₄.holo' (ModularFormClass.bdd_at_infty E₄),
    ← qExpansion_laurent_width _ N hdp CuspForm.discriminant.holo'
      (ModularFormClass.bdd_at_infty CuspForm.discriminant)]
  exact he ▸ (h4.cusp_pow 3).cusp_div hd

end
end Dubon2026.SourceFunctionField