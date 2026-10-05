import GuthMaynard.ZetaBounds
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The exact pole coefficient in zeta's logarithmic derivative

The nonnegative von Mangoldt series controls all imaginary parts. On the
real interval adjacent to one the actual pole-removed zeta function
supplies a bounded analytic remainder; larger real parts are monotone.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Set Filter ArithmeticFunction
open RiemannZeta.GuthMaynard
open scoped Topology

/-- On the real line the von Mangoldt Dirichlet-series terms are nonnegative real numbers. -/
theorem norm_mangoldt_term_eq_re (σ : ℝ) (n : ℕ) :
    ‖LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ : ℂ) n‖ =
      (LSeries.term (fun k => (vonMangoldt k : ℂ)) (σ : ℂ) n).re := by
  by_cases hn : n = 0
  · simp [hn]
  rw [LSeries.term_of_ne_zero hn]
  have he : (n : ℂ) ^ (σ : ℂ) = ((n : ℝ) ^ σ : ℝ) := by
    exact (Complex.ofReal_cpow (Nat.cast_nonneg n) σ).symm
  rw [he, ← ofReal_div, norm_real, Real.norm_eq_abs, ofReal_re]
  exact abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _))

/-- The Euler series bounds the full complex logarithmic derivative by a smaller real argument. -/
theorem norm_logDeriv_zeta_le_real {σ : ℝ} {s : ℂ} (hσ : 1 < σ) (hs : σ ≤ s.re) :
    ‖logDeriv riemannZeta s‖ ≤ -(logDeriv riemannZeta (σ : ℂ)).re := by
  let f : ℕ → ℂ := fun n => (vonMangoldt n : ℂ)
  have hreal : LSeriesSummable f (σ : ℂ) :=
    LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hcplx : LSeriesSummable f s := LSeriesSummable_vonMangoldt (lt_of_lt_of_le hσ hs)
  have hbound : ‖LSeries f s‖ ≤ (LSeries f (σ : ℂ)).re := by
    calc
      ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hcplx.norm
      _ ≤ ∑' n, ‖LSeries.term f (σ : ℂ) n‖ :=
        hcplx.norm.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re f (by simpa using hs)) hreal.norm
      _ = ∑' n, (LSeries.term f (σ : ℂ) n).re := by
        exact tsum_congr (norm_mangoldt_term_eq_re σ)
      _ = (LSeries f (σ : ℂ)).re := (Complex.re_tsum hreal).symm
  have hLs : LSeries f s = -logDeriv riemannZeta s := by
    simpa only [logDeriv_apply, neg_div, f] using
      LSeries_vonMangoldt_eq_deriv_riemannZeta_div (lt_of_lt_of_le hσ hs)
  have hLr : LSeries f (σ : ℂ) = -logDeriv riemannZeta (σ : ℂ) := by
    simpa only [logDeriv_apply, neg_div, f] using
      LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ : 1 < (σ : ℂ).re)
  simpa only [hLs, hLr, norm_neg, neg_re] using hbound

/-- Pole removal is nonvanishing on the whole closed real half-line. -/
theorem regularized_zeta_ne_zero_real {σ : ℝ} (hσ : 1 ≤ σ) :
    regularizedRiemannZeta (σ : ℂ) ≠ 0 := by
  by_cases h1 : σ = 1
  · subst σ
    simp [regularizedRiemannZeta]
  have hc1 : (σ : ℂ) ≠ 1 := by exact_mod_cast h1
  rw [regularizedRiemannZeta, Function.update_of_ne hc1]
  exact mul_ne_zero (sub_ne_zero.mpr hc1) (riemannZeta_ne_zero_of_one_le_re hσ)

/-- The logarithmic derivative of the actual pole-removed zeta is bounded on the compact real slab. -/
theorem exists_regularized_zeta_logDeriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc (1 : ℝ) 2,
      ‖logDeriv regularizedRiemannZeta (σ : ℂ)‖ ≤ C := by
  have hd : Differentiable ℂ regularizedRiemannZeta := differentiableAt_regularizedRiemannZeta
  have hdc : Continuous (deriv regularizedRiemannZeta) :=
    continuous_iff_continuousAt.mpr fun z => (hd.analyticAt z).deriv.continuousAt
  have hc : ContinuousOn (fun σ : ℝ => logDeriv regularizedRiemannZeta (σ : ℂ)) (Icc 1 2) := by
    apply (hdc.comp continuous_ofReal).continuousOn.div
      (hd.continuous.comp continuous_ofReal).continuousOn
    intro σ hσ
    exact regularized_zeta_ne_zero_real hσ.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨max C 0, le_max_right _ _, fun σ hσ => (hC σ hσ).trans (le_max_left _ _)⟩

/-- Logarithmic pole subtraction is an identity of actual derivatives. -/
theorem logDeriv_zeta_eq_regularized {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta s = logDeriv regularizedRiemannZeta s - 1 / (s - 1) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have he : regularizedRiemannZeta =ᶠ[𝓝 s] (fun z : ℂ => (z - 1) * riemannZeta z) := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    exact Function.update_of_ne hz _ _
  have hlog : logDeriv regularizedRiemannZeta s =
      logDeriv (fun z : ℂ => (z - 1) * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, he.deriv_eq, he.self_of_nhds]
  rw [logDeriv_mul (f := fun z : ℂ => z - 1) (g := riemannZeta)
    s (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_le_re hs.le)
    (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta hs1)] at hlog
  have hlin : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    simp [logDeriv_apply]
  rw [hlin] at hlog
  linear_combination -hlog

/-- Uniform pole growth with the exact coefficient one, for every imaginary part. -/
theorem exists_norm_logDeriv_zeta_le_pole :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 < s.re →
      ‖logDeriv riemannZeta s‖ ≤ 1 / (s.re - 1) + C := by
  obtain ⟨C₀, hC₀, hb⟩ := exists_regularized_zeta_logDeriv_bound
  refine ⟨max C₀ (-(logDeriv riemannZeta 2).re),
    hC₀.trans (le_max_left _ _), ?_⟩
  intro s hs
  by_cases hsmall : s.re ≤ 2
  · have hreal := norm_logDeriv_zeta_le_real hs (le_refl s.re)
    have he := logDeriv_zeta_eq_regularized (s := (s.re : ℂ)) (by simpa using hs)
    have hre := congrArg Complex.re he
    have hi : (1 / ((s.re : ℂ) - 1)).re = 1 / (s.re - 1) := by
      rw [← ofReal_one, ← ofReal_sub, ← ofReal_div, ofReal_re]
    simp only [sub_re, hi] at hre
    have hreg := hb s.re ⟨hs.le, hsmall⟩
    have hlow := (abs_le.mp (abs_re_le_norm
      (logDeriv regularizedRiemannZeta (s.re : ℂ)))).1
    linarith [le_max_left C₀ (-(logDeriv riemannZeta 2).re)]
  · have hlarge := norm_logDeriv_zeta_le_real (σ := 2) (s := s)
      (by norm_num) (by linarith)
    have hp : 0 ≤ 1 / (s.re - 1) := by positivity
    norm_num only [ofReal_ofNat] at hlarge
    linarith [le_max_right C₀ (-(logDeriv riemannZeta 2).re)]

end
end DongWangWangZhang2026
