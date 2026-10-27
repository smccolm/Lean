import Dubon2026.SourceQExpansionPeriodWidth
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-! DUB-17/18 -> higher continuation -> arithmetic automorphy -> original
all-weight association -> finite Gamma1 character realization -> Picard/H1
and diamond comparison -> cusp differential realization -> rational Fourier
structure -> Fricke coefficient transport. Reuses the native Eisenstein
q-expansion and the existing sparse-series reindexing. No rationality or
analytic conjugation premise substitutes for a proof. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass
open scoped Manifold MatrixGroups ModularForm ArithmeticFunction.sigma

/-- The rational coefficient formula of the normalized Eisenstein series. -/
def eisensteinQSeries (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 1
    else -(2 * k / bernoulli k : ℚ) * (ArithmeticFunction.sigma (k - 1) n)

theorem eisensteinQSeries_map {k : ℕ} (hk : 3 ≤ k) (heven : Even k) :
    (eisensteinQSeries k).map (algebraMap ℚ ℂ) = qExpansion 1 (E hk) := by
  ext n
  rw [PowerSeries.coeff_map, eisensteinQSeries, PowerSeries.coeff_mk,
    EisensteinSeries.E_qExpansion_coeff hk heven]
  split_ifs <;> simp [Rat.cast_div]

/-- The width-N rational Fourier series of the actual product E4 E6. -/
def e4e6QSeries (N : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if N ∣ n then
    (eisensteinQSeries 4 * eisensteinQSeries 6).coeff (n / N) else 0

theorem periodic_E4E6 :
    Function.Periodic ((⇑E₄ * ⇑E₆ : ℍ → ℂ) ∘ ofComplex) 1 := by
  have h4 := periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL
  have h6 := periodic_comp_ofComplex E₆ one_mem_strictPeriods_SL
  intro τ
  have e4 := h4 τ
  have e6 := h6 τ
  simp only [Function.comp_apply, Pi.mul_apply, Complex.ofReal_one] at e4 e6 ⊢
  rw [e4, e6]

theorem e4e6QSeries_map {N : ℕ} (hN : N ≠ 0) :
    (e4e6QSeries N).map (algebraMap ℚ ℂ) =
      qExpansion N (⇑E₄ * ⇑E₆ : ℍ → ℂ) := by
  have he : (eisensteinQSeries 4 * eisensteinQSeries 6).map (algebraMap ℚ ℂ) =
      qExpansion 1 (⇑E₄ * ⇑E₆ : ℍ → ℂ) := by
    rw [map_mul, eisensteinQSeries_map (by norm_num) (by decide),
      eisensteinQSeries_map (by norm_num) (by decide)]
    exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL E₄ E₆).symm
  ext n
  rw [PowerSeries.coeff_map, e4e6QSeries, PowerSeries.coeff_mk,
    qExpansion_coeff_width _ hN periodic_E4E6 (E₄.holo'.mul E₆.holo')
      ((ModularFormClass.bdd_at_infty E₄).mul (ModularFormClass.bdd_at_infty E₆))]
  split_ifs
  · exact congrArg (PowerSeries.coeff (n / N)) he
  · simp

theorem analyticAt_cuspFunction_E4E6 {N : ℕ} (hN : N ≠ 0) :
    AnalyticAt ℂ (cuspFunction N (⇑E₄ * ⇑E₆ : ℍ → ℂ)) 0 := by
  exact analyticAt_cuspFunction_zero (by exact_mod_cast Nat.pos_of_ne_zero hN)
    (by simpa using periodic_E4E6.nat_mul N) (E₄.holo'.mul E₆.holo')
    ((ModularFormClass.bdd_at_infty E₄).mul (ModularFormClass.bdd_at_infty E₆))

end
end Dubon2026.SourceFricke
