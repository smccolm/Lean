import Dubon2026.TorusGridLog
import Mathlib.MeasureTheory.Group.Integral

/-! # Analytic products of genuine prime twists and their Haar logarithms -/

namespace Dubon2026

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The product probability is invariant under additive phase translations. -/
instance torusHaar_isAddHaarMeasure (N : ℕ) : Measure.IsAddHaarMeasure (torusHaar N) := by
  unfold torusHaar
  infer_instance

theorem integrable_translated_bohr_log (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (v : PrimeTorus N) :
    Integrable (fun z => Real.log ‖bohrOnTorus a N σ (z + v)‖) (torusHaar N) :=
  (measurePreserving_add_right (torusHaar N) v).integrable_comp_of_integrable
    (integrable_bohrOnTorus_log a N σ)

theorem integral_translated_bohr_log (a : ℕ → ℂ) (N : ℕ) (σ : ℝ) (v : PrimeTorus N) :
    (∫ z, Real.log ‖bohrOnTorus a N σ (z + v)‖ ∂torusHaar N) = haarLogPotential a N σ :=
  integral_add_right_eq_self (fun z => Real.log ‖bohrOnTorus a N σ z‖) v

theorem translated_bohr_ne_zero_ae {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) (v : PrimeTorus N) :
    ∀ᵐ z ∂torusHaar N, bohrOnTorus a N σ (z + v) ≠ 0 :=
  (measurePreserving_add_right (torusHaar N) v).quasiMeasurePreserving.ae
    (bohrOnTorus_ne_zero_ae hN ha σ)

/-- Product of finite Dirichlet polynomials with specified prime phases. -/
def twistProduct {ι : Type*} [Fintype ι] (a : ℕ → ℂ) (N : ℕ)
    (v : ι → PrimeTorus N) (s : ℂ) : ℂ :=
  ∏ i, dirichletSum (twistedCoefficients a N (v i)) N s

theorem analyticAt_twistProduct {ι : Type*} [Fintype ι] (a : ℕ → ℂ) (N : ℕ)
    (v : ι → PrimeTorus N) (s : ℂ) : AnalyticAt ℂ (twistProduct a N v) s := by
  change AnalyticAt ℂ (fun s => ∏ i, dirichletSum (twistedCoefficients a N (v i)) N s) s
  apply Finset.analyticAt_fun_prod
  exact fun i _ => analyticAt_dirichletSum (twistedCoefficients a N (v i)) N s

theorem twistProduct_vertical {ι : Type*} [Fintype ι] (a : ℕ → ℂ) (N : ℕ)
    (v : ι → PrimeTorus N) (σ t : ℝ) :
    twistProduct a N v ((σ : ℂ) + Complex.I * t) =
      ∏ i, bohrOnTorus a N σ (v i + primeTorusFlow N t) := by
  apply Finset.prod_congr rfl
  exact fun i _ => verticalFamily_eq_torus_translate a N σ (v i) t

theorem log_norm_translated_bohr_product_ae_eq {ι : Type*} [Fintype ι]
    {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) (v : ι → PrimeTorus N) :
    (fun z => Real.log ‖∏ i, bohrOnTorus a N σ (z + v i)‖) =ᵐ[torusHaar N]
      (fun z => ∑ i, Real.log ‖bohrOnTorus a N σ (z + v i)‖) := by
  have hne : ∀ᵐ z ∂torusHaar N, ∀ i, bohrOnTorus a N σ (z + v i) ≠ 0 :=
    ae_all_iff.mpr (fun i => translated_bohr_ne_zero_ae hN ha σ (v i))
  filter_upwards [hne] with z hz
  rw [norm_prod, Real.log_prod]
  exact fun i _ => norm_ne_zero_iff.mpr (hz i)

theorem integrable_log_norm_translated_bohr_product {ι : Type*} [Fintype ι]
    {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) (v : ι → PrimeTorus N) :
    Integrable (fun z => Real.log ‖∏ i, bohrOnTorus a N σ (z + v i)‖) (torusHaar N) :=
  (integrable_finsetSum _ (fun i _ => integrable_translated_bohr_log a N σ (v i))).congr
    (log_norm_translated_bohr_product_ae_eq hN ha σ v).symm

theorem integral_log_norm_translated_bohr_product {ι : Type*} [Fintype ι]
    {a : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) (ha : a 1 ≠ 0) (σ : ℝ) (v : ι → PrimeTorus N) :
    (∫ z, Real.log ‖∏ i, bohrOnTorus a N σ (z + v i)‖ ∂torusHaar N) =
      (Fintype.card ι : ℝ) * haarLogPotential a N σ := by
  classical
  calc
    _ = ∫ z, ∑ i, Real.log ‖bohrOnTorus a N σ (z + v i)‖ ∂torusHaar N :=
      integral_congr_ae (log_norm_translated_bohr_product_ae_eq hN ha σ v)
    _ = ∑ i, ∫ z, Real.log ‖bohrOnTorus a N σ (z + v i)‖ ∂torusHaar N :=
      integral_finsetSum _ (fun i _ => integrable_translated_bohr_log a N σ (v i))
    _ = _ := by simp only [integral_translated_bohr_log, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end

end Dubon2026
