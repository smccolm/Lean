import DongWangWangZhang2026.ZetaSum
import DongWangWangZhang2026.TwistSelection
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Chebyshev

/-!
# Transform of the actual summatory phase

The analytic mean-value argument uses a Laplace/Fourier transform of the
original floor-cutoff sum. We reuse Mathlib's Abel representation of L-series
and explicitly discharge measurability, growth and absolute convergence.
-/

namespace DongWangWangZhang2026

open Finset Filter MeasureTheory Complex
open scoped Topology FourierTransform ENNReal

noncomputable section

/-- Measurability includes the jumps at every integer cutoff. -/
theorem measurable_zetaSum (t : ℝ) : Measurable (fun x => zetaSum x t) :=
  (measurable_of_countable (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, zetaTerm t n)).comp
    Nat.measurable_floor

/-- Absolute convergence of the actual summatory integral on its right half-plane. -/
theorem integrableOn_zetaSum_cpow (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => zetaSum u t * (u : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => zetaSum u t * (u : ℂ) ^ (-(s + 1))) (volume.restrict (Set.Ioi 1)) := by
    apply ((measurable_zetaSum t).aestronglyMeasurable.restrict).mul
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro u hu
    exact (Complex.continuousAt_ofReal_cpow_const u (-(s + 1))
      (Or.inr (ne_of_gt (zero_lt_one.trans hu)))).continuousWithinAt
  apply (integrableOn_Ioi_rpow_of_lt (show -s.re < -1 by linarith) zero_lt_one).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  calc
    _ ≤ u * u ^ (-(s + 1)).re := mul_le_mul_of_nonneg_right
      (norm_zetaSum_le hu0.le t) (Real.rpow_nonneg hu0.le _)
    _ = u ^ (-s.re) := by
      nth_rw 1 [← Real.rpow_one u]
      rw [← Real.rpow_add hu0]
      congr 1
      simp

/-- Mathlib's L-series zero-index convention agrees with the actual phase series. -/
theorem LSeries_zetaTerm (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (zetaTerm t) s = riemannZeta (s - (t : ℂ) * I) := by
  rw [LSeries]
  simp_rw [LSeries.term_def₀ (zetaTerm_zero t), Complex.cpow_neg, ← div_eq_mul_inv]
  exact tsum_zetaTerm_div_cpow t hs

/-- Exact Mellin-side formula for the actual sum, not a smoothed proxy. -/
theorem integral_zetaSum_cpow (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Set.Ioi (1 : ℝ), zetaSum u t * (u : ℂ) ^ (-(s + 1))) =
      riemannZeta (s - (t : ℂ) * I) / s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, zetaTerm t k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    apply Asymptotics.isBigO_of_le
    intro n
    simpa only [Real.rpow_one, Real.norm_natCast, zetaSum, Nat.floor_natCast] using
      norm_zetaSum_le (Nat.cast_nonneg n) t
  have hS : LSeriesSummable (zetaTerm t) s := by
    simpa only [LSeriesSummable, funext (LSeries.term_def₀ (zetaTerm_zero t) s), Complex.cpow_neg,
      ← div_eq_mul_inv] using summable_zetaTerm_div_cpow t hs
  have h := LSeries_eq_mul_integral (zetaTerm t) zero_le_one hs hS hO
  rw [LSeries_zetaTerm t hs] at h
  apply (eq_div_iff (Complex.ne_zero_of_one_lt_re hs)).mpr
  simpa only [zetaSum, mul_comm] using h.symm

private theorem exp_image_Ioi_zero : Real.exp '' Set.Ioi (0 : ℝ) = Set.Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hu
  · intro hx
    exact ⟨Real.log x, Real.log_pos hx, Real.exp_log (zero_lt_one.trans hx)⟩

private theorem exp_cpow_jacobian (s : ℂ) (u : ℝ) :
    (Real.exp u : ℂ) * (Real.exp u : ℂ) ^ (-(s + 1)) = Complex.exp (-s * u) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  ring

/-- The logarithmic change of variables is proved at the actual cutoff, including its Jacobian. -/
theorem integral_zetaSum_exp (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Set.Ioi (0 : ℝ), zetaSum (Real.exp u) t * Complex.exp (-s * u)) =
      riemannZeta (s - (t : ℂ) * I) / s := by
  rw [← integral_zetaSum_cpow t hs, ← exp_image_Ioi_zero,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  dsimp only
  rw [abs_of_pos (Real.exp_pos u), Complex.real_smul, mul_left_comm,
    exp_cpow_jacobian]

/-- Absolute convergence is transported with the same Jacobian, not inferred from an identity
between totalized integrals. -/
theorem integrableOn_zetaSum_exp (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => zetaSum (Real.exp u) t * Complex.exp (-s * u)) (Set.Ioi 0) := by
  have h := integrableOn_zetaSum_cpow t hs
  rw [← exp_image_Ioi_zero, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
      Real.exp_injective.injOn] at h
  apply h.congr_fun _ measurableSet_Ioi
  intro u _
  dsimp only
  rw [abs_of_pos (Real.exp_pos u), Complex.real_smul, mul_left_comm,
    exp_cpow_jacobian]

/-- The full real-line Laplace integrand is absolutely integrable; the negative half-line
vanishes because the original sum is empty below one. -/
theorem integrable_zetaSum_exp (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun u : ℝ => zetaSum (Real.exp u) t * Complex.exp (-s * u)) := by
  have hpos := integrableOn_zetaSum_exp t hs
  have hneg : IntegrableOn (fun u : ℝ => zetaSum (Real.exp u) t * Complex.exp (-s * u))
      (Set.Iio 0) := by
    apply (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Set.Iio 0) volume).congr_fun
      _ measurableSet_Iio
    intro u hu
    dsimp only
    rw [zetaSum_eq_zero_of_lt_one (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hu),
      zero_mul]
  have hnonneg := (integrableOn_Ici_iff_integrableOn_Ioi).mpr hpos
  simpa only [Set.Iio_union_Ici, integrableOn_univ] using hneg.union hnonneg

/-- The full-line transform retains the exact shifted-zeta denominator and sign. -/
theorem integral_zetaSum_exp_univ (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∫ u : ℝ, zetaSum (Real.exp u) t * Complex.exp (-s * u)) =
      riemannZeta (s - (t : ℂ) * I) / s := by
  rw [← integral_zetaSum_exp t hs]
  have hzero : ∀ u ∈ Set.Iio (0 : ℝ),
      zetaSum (Real.exp u) t * Complex.exp (-s * u) = 0 := by
    intro u hu
    rw [zetaSum_eq_zero_of_lt_one (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hu),
      zero_mul]
  have h := integral_union_eq_left_of_forall (μ := volume)
    (s := Set.Ici (0 : ℝ)) measurableSet_Iio hzero
  rw [Set.Ici_union_Iio, setIntegral_univ, integral_Ici_eq_integral_Ioi] at h
  exact h

/-- The actual damped summatory phase used by the mean-value Fourier argument. -/
def dampedZetaSum (t σ u : ℝ) : ℂ := (Real.exp (-σ * u) : ℂ) * zetaSum (Real.exp u) t

theorem integrable_dampedZetaSum (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (dampedZetaSum t σ) := by
  apply (integrable_zetaSum_exp t (s := (σ : ℂ)) (by simpa using hσ)).congr
  filter_upwards with u
  simp only [dampedZetaSum, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp,
    mul_comm]

/-- Exact Fourier normalization: Mathlib's frequency `ξ` corresponds to ordinate `2πξ`.
No Gaussian smoothing, missing zero-index term or implicit residue is introduced. -/
theorem fourier_dampedZetaSum (t ξ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    𝓕 (dampedZetaSum t σ) ξ =
      riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  let s : ℂ := (σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I
  have hs : 1 < s.re := by simpa [s] using hσ
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_assoc (-2 * Real.pi)]
  have hkernel (u : ℝ) :
      Complex.exp ((-2 * Real.pi * (u * ξ) : ℝ) * I) * dampedZetaSum t σ u =
        zetaSum (Real.exp u) t * Complex.exp (-s * u) := by
    rw [dampedZetaSum, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 1
    congr 1
    dsimp [s]
    push_cast
    ring
  have hintegral : (∫ u : ℝ, Complex.exp ((-2 * Real.pi * (u * ξ) : ℝ) * I) •
      dampedZetaSum t σ u) = ∫ u : ℝ, zetaSum (Real.exp u) t * Complex.exp (-s * u) := by
    apply integral_congr_ae
    filter_upwards with u
    exact hkernel u
  rw [hintegral, integral_zetaSum_exp_univ t hs]
  dsimp [s]
  congr 2
  push_cast
  ring

/-- The source damping makes the actual summatory function globally bounded by one. -/
theorem norm_dampedZetaSum_le_one (t u : ℝ) {σ : ℝ} (hσ : 1 ≤ σ) :
    ‖dampedZetaSum t σ u‖ ≤ 1 := by
  by_cases hu : 0 ≤ u
  · rw [dampedZetaSum, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ Real.exp (-σ * u) * Real.exp u := mul_le_mul_of_nonneg_left
        (norm_zetaSum_le (Real.exp_pos _).le t) (Real.exp_pos _).le
      _ = Real.exp ((1 - σ) * u) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hu)
  · rw [dampedZetaSum, zetaSum_eq_zero_of_lt_one
      (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (lt_of_not_ge hu))]
    simp

/-- Genuine square integrability for the mean-value/Plancherel input. -/
theorem memLp_dampedZetaSum_two (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    MemLp (dampedZetaSum t σ) 2 := by
  have hf := integrable_dampedZetaSum t hσ
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply hf.norm.mono' (hf.aestronglyMeasurable.norm.pow 2)
  filter_upwards with u
  dsimp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := norm_dampedZetaSum_le_one t u hσ.le
  nlinarith [norm_nonneg (dampedZetaSum t σ u)]

/-- The integral Fourier transform agrees almost everywhere with Mathlib's `L²` transform
on the common `L¹ ∩ L²` domain. Smooth test functions identify the two actual transforms. -/
theorem fourier_toLp_ae_eq {f : ℝ → ℂ} (hf : Integrable f) (hf₂ : MemLp f 2) :
    (fun u => (𝓕 hf₂.toLp : Lp ℂ 2 volume) u) =ᵐ[volume] 𝓕 f := by
  have hcont : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 hf₂.toLp : Lp ℂ 2 volume)).locallyIntegrable (by norm_num))
      (hcont.locallyIntegrable (μ := volume))
  intro g hg hgc
  have hgc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg' := Complex.ofRealCLM.contDiff.comp hg
  let ψ : SchwartzMap ℝ ℂ := hgc'.toSchwartzMap hg'
  have hψ (u : ℝ) : ψ u = (g u : ℂ) := rfl
  have hdistribution := congrArg (fun D : TemperedDistribution ℝ ℂ => D ψ)
    (Lp.fourier_toTemperedDistribution_eq hf₂.toLp)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hdistribution
  have hpair : (∫ u : ℝ, (𝓕 ψ) u • f u) = ∫ u : ℝ, ψ u • (𝓕 f) u := by
    simpa using VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner ψ.integrable hf
  calc
    _ = ∫ u : ℝ, ψ u • (𝓕 hf₂.toLp : Lp ℂ 2 volume) u := by
      simp only [hψ, Complex.real_smul, smul_eq_mul]
    _ = ∫ u : ℝ, (𝓕 ψ) u • (hf₂.toLp : ℝ → ℂ) u := hdistribution.symm
    _ = ∫ u : ℝ, (𝓕 ψ) u • f u := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with u hu
      rw [hu]
    _ = ∫ u : ℝ, ψ u • (𝓕 f) u := hpair
    _ = _ := by simp only [hψ, Complex.real_smul, smul_eq_mul]

/-- The ordinary Fourier transform is genuinely square integrable on the `L¹ ∩ L²` domain. -/
theorem memLp_fourier_of_integrable_memLp_two {f : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) : MemLp (𝓕 f) 2 :=
  (memLp_congr_ae (fourier_toLp_ae_eq hf hf₂)).mp
    (Lp.memLp (𝓕 hf₂.toLp : Lp ℂ 2 volume))

/-- Plancherel for the actual integral Fourier transform, with both domain conditions explicit. -/
theorem integral_norm_sq_fourier_of_integrable_memLp_two {f : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : MemLp f 2) :
    (∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2) = ∫ u : ℝ, ‖f u‖ ^ 2 := by
  have hnorm (g : Lp ℂ 2 (volume : Measure ℝ)) : (∫ u : ℝ, ‖g u‖ ^ 2) = ‖g‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) g
    rw [L2.inner_def] at h
    simpa only [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow] using h
  calc
    _ = ∫ u : ℝ, ‖(𝓕 hf₂.toLp : Lp ℂ 2 volume) u‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [fourier_toLp_ae_eq hf hf₂] with u hu
      rw [hu]
    _ = ‖(𝓕 hf₂.toLp : Lp ℂ 2 volume)‖ ^ 2 := hnorm _
    _ = ‖hf₂.toLp‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ u : ℝ, ‖(hf₂.toLp : ℝ → ℂ) u‖ ^ 2 := (hnorm _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with u hu
      rw [hu]

/-- Actual summatory-phase Parseval identity, with the frequency scaling and damping retained. -/
theorem integral_zeta_quotient_sq_eq_sum_sq (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (∫ ξ : ℝ, ‖riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) =
        ∫ u : ℝ, Real.exp (-2 * σ * u) * ‖zetaSum (Real.exp u) t‖ ^ 2 := by
  simp_rw [← fourier_dampedZetaSum t _ hσ]
  rw [integral_norm_sq_fourier_of_integrable_memLp_two
    (integrable_dampedZetaSum t hσ) (memLp_dampedZetaSum_two t hσ)]
  apply integral_congr_ae
  filter_upwards with u
  rw [dampedZetaSum, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, ← Real.exp_nat_mul]
  congr 1
  congr 1
  push_cast
  ring

/-- Integrability of the exact spectral square in the preceding Parseval identity. -/
theorem integrable_zeta_quotient_sq (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun ξ : ℝ => ‖riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) := by
  simp_rw [← fourier_dampedZetaSum t _ hσ]
  have h := memLp_fourier_of_integrable_memLp_two
    (integrable_dampedZetaSum t hσ) (memLp_dampedZetaSum_two t hσ)
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

/-- The logarithmically weighted original sum in the mean-value argument. -/
def logZetaSum (x t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Real.log n : ℂ) * zetaTerm t n

theorem logZetaSum_eq_zero_of_lt_one {x : ℝ} (hx : x < 1) (t : ℝ) :
    logZetaSum x t = 0 := by
  simp [logZetaSum, Nat.floor_eq_zero.mpr hx]

theorem measurable_logZetaSum (t : ℝ) : Measurable (fun x => logZetaSum x t) :=
  (measurable_of_countable (fun N : ℕ =>
    ∑ n ∈ Finset.Icc 1 N, (Real.log n : ℂ) * zetaTerm t n)).comp Nat.measurable_floor

theorem norm_logZetaSum_le {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    ‖logZetaSum x t‖ ≤ x * Real.log x := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖(Real.log n : ℂ) * zetaTerm t n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log x := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [norm_mul, norm_zetaTerm t (Finset.mem_Icc.mp hn).1,
        Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hn1), mul_one]
      exact Real.log_le_log (zero_lt_one.trans_le hn1)
        ((by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ ⌊x⌋₊).trans (Nat.floor_le hx0))
    _ = (⌊x⌋₊ : ℝ) * Real.log x := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.floor_le hx0) (Real.log_nonneg hx)

/-- Arbitrarily small power loss, used only to justify convergence on the full half-plane. -/
theorem norm_logZetaSum_le_rpow {x ε : ℝ} (hx : 0 ≤ x) (hε : 0 < ε) (t : ℝ) :
    ‖logZetaSum x t‖ ≤ ε⁻¹ * x ^ (1 + ε) := by
  by_cases hx1 : 1 ≤ x
  · calc
      _ ≤ x * Real.log x := norm_logZetaSum_le hx1 t
      _ ≤ x * (x ^ ε / ε) := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx hε) hx
      _ = _ := by rw [Real.rpow_add (zero_lt_one.trans_le hx1), Real.rpow_one]; ring
  · rw [logZetaSum_eq_zero_of_lt_one (lt_of_not_ge hx1)]
    rw [norm_zero]
    positivity

theorem LSeries_logZetaTerm (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (Real.log n : ℂ) * zetaTerm t n) s =
      -deriv riemannZeta (s - (t : ℂ) * I) := by
  have hab : LSeries.abscissaOfAbsConv (zetaTerm t) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n hn =>
      (norm_zetaTerm t (Nat.pos_of_ne_zero hn)).le⟩
  have hs' : LSeries.abscissaOfAbsConv (zetaTerm t) < s.re :=
    hab.trans_lt (by exact_mod_cast hs)
  have heq : LSeries (zetaTerm t) =ᶠ[𝓝 s] fun z => riemannZeta (z - (t : ℂ) * I) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact LSeries_zetaTerm t hz
  have hd := heq.deriv_eq
  rw [LSeries_deriv hs', deriv_comp_sub_const] at hd
  have hlog : LSeries.logMul (zetaTerm t) =
      (fun n : ℕ => (Real.log n : ℂ) * zetaTerm t n) := by
    funext n
    rw [LSeries.logMul, ← Complex.natCast_log]
  rw [hlog] at hd
  exact neg_eq_iff_eq_neg.mp hd

/-- Abel's exact formula for the weighted original coefficients. -/
theorem integral_logZetaSum_cpow (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Set.Ioi (1 : ℝ), logZetaSum u t * (u : ℂ) ^ (-(s + 1))) =
      -deriv riemannZeta (s - (t : ℂ) * I) / s := by
  let ε := (s.re - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (Real.log k : ℂ) * zetaTerm t k)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 + ε)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨ε⁻¹, Filter.Eventually.of_forall fun n => ?_⟩
    simpa only [logZetaSum, Nat.floor_natCast,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using
        norm_logZetaSum_le_rpow (Nat.cast_nonneg n) hε t
  have hab : LSeries.abscissaOfAbsConv (zetaTerm t) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n hn =>
      (norm_zetaTerm t (Nat.pos_of_ne_zero hn)).le⟩
  have hs' : LSeries.abscissaOfAbsConv (zetaTerm t) < s.re :=
    hab.trans_lt (by exact_mod_cast hs)
  have hS : LSeriesSummable (fun n => (Real.log n : ℂ) * zetaTerm t n) s := by
    have hlog : LSeries.logMul (zetaTerm t) =
        (fun n : ℕ => (Real.log n : ℂ) * zetaTerm t n) := by
      funext n
      rw [LSeries.logMul, ← Complex.natCast_log]
    rw [← hlog]
    exact LSeriesSummable_logMul_of_lt_re hs'
  have h := LSeries_eq_mul_integral _ (show 0 ≤ 1 + ε by linarith)
    (show 1 + ε < s.re by dsimp [ε]; linarith) hS hO
  rw [LSeries_logZetaTerm t hs] at h
  apply (eq_div_iff (Complex.ne_zero_of_one_lt_re hs)).mpr
  simpa only [logZetaSum, mul_comm] using h.symm

theorem integrableOn_logZetaSum_cpow (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => logZetaSum u t * (u : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  let ε := (s.re - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => logZetaSum u t * (u : ℂ) ^ (-(s + 1))) (volume.restrict (Set.Ioi 1)) := by
    apply ((measurable_logZetaSum t).aestronglyMeasurable.restrict).mul
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro u hu
    exact (Complex.continuousAt_ofReal_cpow_const u (-(s + 1))
      (Or.inr (ne_of_gt (zero_lt_one.trans hu)))).continuousWithinAt
  apply ((integrableOn_Ioi_rpow_of_lt (show -1 - ε < -1 by linarith) zero_lt_one).const_mul
    ε⁻¹).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  calc
    _ ≤ (ε⁻¹ * u ^ (1 + ε)) * u ^ (-(s + 1)).re := mul_le_mul_of_nonneg_right
      (norm_logZetaSum_le_rpow hu0.le hε t) (Real.rpow_nonneg hu0.le _)
    _ = ε⁻¹ * u ^ (-1 - ε) := by
      rw [mul_assoc, ← Real.rpow_add hu0]
      congr 2
      simp only [neg_re, add_re, one_re]
      dsimp [ε]
      ring

theorem integral_logZetaSum_exp (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∫ u in Set.Ioi (0 : ℝ), logZetaSum (Real.exp u) t * Complex.exp (-s * u)) =
      -deriv riemannZeta (s - (t : ℂ) * I) / s := by
  rw [← integral_logZetaSum_cpow t hs, ← exp_image_Ioi_zero,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  dsimp only
  rw [abs_of_pos (Real.exp_pos u), Complex.real_smul, mul_left_comm, exp_cpow_jacobian]

theorem integrableOn_logZetaSum_exp (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun u : ℝ => logZetaSum (Real.exp u) t * Complex.exp (-s * u))
      (Set.Ioi 0) := by
  have h := integrableOn_logZetaSum_cpow t hs
  rw [← exp_image_Ioi_zero, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
      Real.exp_injective.injOn] at h
  apply h.congr_fun _ measurableSet_Ioi
  intro u _
  dsimp only
  rw [abs_of_pos (Real.exp_pos u), Complex.real_smul, mul_left_comm, exp_cpow_jacobian]

theorem integrable_logZetaSum_exp (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun u : ℝ => logZetaSum (Real.exp u) t * Complex.exp (-s * u)) := by
  have hpos := integrableOn_logZetaSum_exp t hs
  have hneg : IntegrableOn (fun u : ℝ => logZetaSum (Real.exp u) t * Complex.exp (-s * u))
      (Set.Iio 0) := by
    apply (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Set.Iio 0) volume).congr_fun
      _ measurableSet_Iio
    intro u hu
    dsimp only
    rw [logZetaSum_eq_zero_of_lt_one
      (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hu), zero_mul]
  have hnonneg := (integrableOn_Ici_iff_integrableOn_Ioi).mpr hpos
  simpa only [Set.Iio_union_Ici, integrableOn_univ] using hneg.union hnonneg

theorem integral_logZetaSum_exp_univ (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∫ u : ℝ, logZetaSum (Real.exp u) t * Complex.exp (-s * u)) =
      -deriv riemannZeta (s - (t : ℂ) * I) / s := by
  rw [← integral_logZetaSum_exp t hs]
  have hzero : ∀ u ∈ Set.Iio (0 : ℝ),
      logZetaSum (Real.exp u) t * Complex.exp (-s * u) = 0 := by
    intro u hu
    rw [logZetaSum_eq_zero_of_lt_one
      (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hu), zero_mul]
  have h := integral_union_eq_left_of_forall (μ := volume)
    (s := Set.Ici (0 : ℝ)) measurableSet_Iio hzero
  rw [Set.Ici_union_Iio, setIntegral_univ, integral_Ici_eq_integral_Ioi] at h
  exact h

/-- Actual weighted summatory function, with no smooth-number replacement. -/
def dampedLogZetaSum (t σ u : ℝ) : ℂ :=
  (Real.exp (-σ * u) : ℂ) * logZetaSum (Real.exp u) t

theorem integrable_dampedLogZetaSum (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (dampedLogZetaSum t σ) := by
  apply (integrable_logZetaSum_exp t (s := (σ : ℂ)) (by simpa using hσ)).congr
  filter_upwards with u
  simp only [dampedLogZetaSum, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp,
    mul_comm]

/-- The logarithmic coefficient corresponds to a negative zeta derivative. -/
theorem fourier_dampedLogZetaSum (t ξ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    𝓕 (dampedLogZetaSum t σ) ξ =
      -deriv riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  let s : ℂ := (σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I
  have hs : 1 < s.re := by simpa [s] using hσ
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_assoc (-2 * Real.pi)]
  have hkernel (u : ℝ) :
      Complex.exp ((-2 * Real.pi * (u * ξ) : ℝ) * I) * dampedLogZetaSum t σ u =
        logZetaSum (Real.exp u) t * Complex.exp (-s * u) := by
    rw [dampedLogZetaSum, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 1
    congr 1
    dsimp [s]
    push_cast
    ring
  have hintegral : (∫ u : ℝ, Complex.exp ((-2 * Real.pi * (u * ξ) : ℝ) * I) •
      dampedLogZetaSum t σ u) = ∫ u : ℝ, logZetaSum (Real.exp u) t * Complex.exp (-s * u) := by
    apply integral_congr_ae
    filter_upwards with u
    exact hkernel u
  rw [hintegral, integral_logZetaSum_exp_univ t hs]
  dsimp [s]
  congr 3
  push_cast
  ring

theorem norm_dampedLogZetaSum_le (t u : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    ‖dampedLogZetaSum t σ u‖ ≤ ((σ - 1) / 2)⁻¹ := by
  let ε := (σ - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  change ‖dampedLogZetaSum t σ u‖ ≤ ε⁻¹
  by_cases hu : 0 ≤ u
  · rw [dampedLogZetaSum, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ Real.exp (-σ * u) * (ε⁻¹ * (Real.exp u) ^ (1 + ε)) :=
        mul_le_mul_of_nonneg_left (norm_logZetaSum_le_rpow (Real.exp_pos u).le hε t)
          (Real.exp_pos _).le
      _ = ε⁻¹ * Real.exp (-ε * u) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_left_comm, ← Real.exp_add]
        congr 2
        dsimp [ε]
        ring
      _ ≤ ε⁻¹ * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le) hu))
          (inv_nonneg.mpr hε.le)
      _ = ε⁻¹ := mul_one _
  · rw [dampedLogZetaSum, logZetaSum_eq_zero_of_lt_one
      (by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (lt_of_not_ge hu))]
    simp only [mul_zero, norm_zero]
    positivity

theorem memLp_dampedLogZetaSum_two (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    MemLp (dampedLogZetaSum t σ) 2 := by
  have hf := integrable_dampedLogZetaSum t hσ
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply (hf.norm.const_mul (((σ - 1) / 2)⁻¹)).mono' (hf.aestronglyMeasurable.norm.pow 2)
  filter_upwards with u
  dsimp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (norm_dampedLogZetaSum_le t u hσ) (norm_nonneg _)

/-- Weighted mean-value Parseval, on the actual unsmoothed phase coefficients. -/
theorem integral_zeta_deriv_quotient_sq_eq_logSum_sq (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (∫ ξ : ℝ, ‖deriv riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) =
        ∫ u : ℝ, Real.exp (-2 * σ * u) * ‖logZetaSum (Real.exp u) t‖ ^ 2 := by
  have hnorm (ξ : ℝ) : ‖deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ =
          ‖𝓕 (dampedLogZetaSum t σ) ξ‖ := by
    rw [fourier_dampedLogZetaSum t ξ hσ, neg_div, norm_neg]
  simp_rw [hnorm]
  rw [integral_norm_sq_fourier_of_integrable_memLp_two
    (integrable_dampedLogZetaSum t hσ) (memLp_dampedLogZetaSum_two t hσ)]
  apply integral_congr_ae
  filter_upwards with u
  rw [dampedLogZetaSum, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, ← Real.exp_nat_mul]
  congr 1
  congr 1
  push_cast
  ring

theorem integrable_zeta_deriv_quotient_sq (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun ξ : ℝ => ‖deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) := by
  have h := memLp_fourier_of_integrable_memLp_two
    (integrable_dampedLogZetaSum t hσ) (memLp_dampedLogZetaSum_two t hσ)
  have hint := (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  simpa only [fourier_dampedLogZetaSum t _ hσ, neg_div, norm_neg] using hint

/-- Summatory Laplace formula for coefficients with a proved linear absolute mean.
The von Mangoldt consumer below supplies the bound from Chebyshev. -/
theorem summatory_LSeries_laplace {f : ℕ → ℂ} {C : ℝ}
    (hA : ∀ x : ℝ, 0 ≤ x → (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f n‖) ≤ C * x)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun u : ℝ => (∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, f n) *
      Complex.exp (-s * u)) ∧
    (∫ u : ℝ, (∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, f n) * Complex.exp (-s * u)) =
      LSeries f s / s := by
  let A : ℝ → ℂ := fun x => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n
  have hmeas : Measurable A :=
    (measurable_of_countable (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n)).comp Nat.measurable_floor
  have hnorm (x : ℝ) (hx : 0 ≤ x) : ‖A x‖ ≤ C * x := (norm_sum_le _ _).trans (hA x hx)
  have hzero (u : ℝ) (hu : u < 0) : A (Real.exp u) = 0 := by
    have he : Real.exp u < 1 := by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hu
    simp [A, Nat.floor_eq_zero.mpr he]
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖f k‖)
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨C, Filter.Eventually.of_forall fun n => ?_⟩
    simpa only [Nat.floor_natCast, Real.rpow_one, Real.norm_natCast,
      Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] using hA n (Nat.cast_nonneg n)
  have hcpow : IntegrableOn (fun x : ℝ => A x * (x : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
    have hm : AEStronglyMeasurable (fun x : ℝ => A x * (x : ℂ) ^ (-(s + 1)))
        (volume.restrict (Set.Ioi 1)) := by
      apply hmeas.aestronglyMeasurable.restrict.mul
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
      intro x hx
      exact (Complex.continuousAt_ofReal_cpow_const x (-(s + 1))
        (Or.inr (ne_of_gt (zero_lt_one.trans hx)))).continuousWithinAt
    apply ((integrableOn_Ioi_rpow_of_lt (show -s.re < -1 by linarith) zero_lt_one).const_mul C).mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    calc
      _ ≤ (C * x) * x ^ (-(s + 1)).re := mul_le_mul_of_nonneg_right
        (hnorm x hx0.le) (Real.rpow_nonneg hx0.le _)
      _ = C * x ^ (-s.re) := by
        rw [mul_assoc]
        nth_rw 1 [← Real.rpow_one x]
        rw [← Real.rpow_add hx0]
        congr 2
        simp
  have hexp : IntegrableOn (fun u : ℝ => A (Real.exp u) * Complex.exp (-s * u)) (Set.Ioi 0) := by
    rw [← exp_image_Ioi_zero, integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
        Real.exp_injective.injOn] at hcpow
    apply hcpow.congr_fun _ measurableSet_Ioi
    intro u _
    dsimp only
    rw [abs_of_pos (Real.exp_pos u), Complex.real_smul, mul_left_comm, exp_cpow_jacobian]
  have hneg : IntegrableOn (fun u : ℝ => A (Real.exp u) * Complex.exp (-s * u)) (Set.Iio 0) := by
    apply (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Set.Iio 0) volume).congr_fun
      _ measurableSet_Iio
    intro u hu
    dsimp only
    rw [hzero u hu, zero_mul]
  refine ⟨?_, ?_⟩
  · have hnonneg := (integrableOn_Ici_iff_integrableOn_Ioi).mpr hexp
    simpa only [Set.Iio_union_Ici, integrableOn_univ] using hneg.union hnonneg
  · have hrep := LSeries_eq_mul_integral' f zero_le_one hs hO
    have hpos : (∫ u in Set.Ioi (0 : ℝ), A (Real.exp u) * Complex.exp (-s * u)) =
        LSeries f s / s := by
      have hi : (∫ x in Set.Ioi (1 : ℝ), A x * (x : ℂ) ^ (-(s + 1))) = LSeries f s / s := by
        apply (eq_div_iff (Complex.ne_zero_of_one_lt_re hs)).mpr
        simpa only [A, mul_comm] using hrep.symm
      rw [← hi, ← exp_image_Ioi_zero,
        integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
          (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      dsimp only
      rw [abs_of_pos (Real.exp_pos u), Complex.real_smul, mul_left_comm, exp_cpow_jacobian]
    have h := integral_union_eq_left_of_forall (μ := volume)
      (s := Set.Ici (0 : ℝ)) measurableSet_Iio
        (fun u hu => show A (Real.exp u) * Complex.exp (-s * u) = 0 by rw [hzero u hu, zero_mul])
    rw [Set.Ici_union_Iio, setIntegral_univ, integral_Ici_eq_integral_Ioi] at h
    exact h.trans hpos

/-- A linear absolute coefficient mean gives the precise inverse-distance mean-square scale.
This is proved through the summatory function, not assumed as a spectral estimate. -/
theorem LSeries_quotient_mean_square_le {f : ℕ → ℂ} {C σ : ℝ} (hC : 0 ≤ C)
    (hA : ∀ x : ℝ, 0 ≤ x → (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖f n‖) ≤ C * x)
    (hσ : 1 < σ) :
    Integrable (fun ξ : ℝ => ‖LSeries f ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) /
      ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) ∧
    (∫ ξ : ℝ, ‖LSeries f ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) /
      ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) ≤ C ^ 2 / (2 * (σ - 1)) := by
  let A : ℝ → ℂ := fun x => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n
  let g : ℝ → ℂ := fun u => (Real.exp (-σ * u) : ℂ) * A (Real.exp u)
  have hg₁ : Integrable g := by
    apply (summatory_LSeries_laplace hA (s := (σ : ℂ)) (by simpa using hσ)).1.congr
    filter_upwards with u
    simp only [g, A, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp, mul_comm]
  have hzero (u : ℝ) (hu : u < 0) : g u = 0 := by
    have he : Real.exp u < 1 := by simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hu
    simp [g, A, Nat.floor_eq_zero.mpr he]
  have hdecay (u : ℝ) : ‖g u‖ ≤ C * Real.exp ((1 - σ) * u) := by
    dsimp only [g]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ Real.exp (-σ * u) * (C * Real.exp u) := mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (hA (Real.exp u) (Real.exp_pos _).le)) (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hbound (u : ℝ) : ‖g u‖ ≤ C := by
    by_cases hu : 0 ≤ u
    · exact (hdecay u).trans (by
        calc
          _ ≤ C * 1 := mul_le_mul_of_nonneg_left
            (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hu)) hC
          _ = C := mul_one _)
    · rw [hzero u (lt_of_not_ge hu), norm_zero]
      exact hC
  have hg₂ : MemLp g 2 := by
    apply (memLp_two_iff_integrable_sq_norm hg₁.aestronglyMeasurable).mpr
    apply (hg₁.norm.const_mul C).mono' (hg₁.aestronglyMeasurable.norm.pow 2)
    filter_upwards with u
    dsimp only [Pi.pow_apply]
    rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul_of_nonneg_right (hbound u) (norm_nonneg _)
  have hfourier (ξ : ℝ) : 𝓕 g ξ =
      LSeries f ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
    let s : ℂ := (σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I
    have hs : 1 < s.re := by simpa [s] using hσ
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [mul_assoc (-2 * Real.pi)]
    have hkernel (u : ℝ) :
        Complex.exp ((-2 * Real.pi * (u * ξ) : ℝ) * I) * g u =
          A (Real.exp u) * Complex.exp (-s * u) := by
      dsimp only [g]
      rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add, mul_comm]
      congr 1
      congr 1
      dsimp [s]
      push_cast
      ring
    calc
      _ = ∫ u : ℝ, A (Real.exp u) * Complex.exp (-s * u) := by
        apply integral_congr_ae
        filter_upwards with u
        exact hkernel u
      _ = LSeries f s / s := (summatory_LSeries_laplace hA hs).2
  have hF₂ := memLp_fourier_of_integrable_memLp_two hg₁ hg₂
  have hFint := (memLp_two_iff_integrable_sq_norm hF₂.aestronglyMeasurable).mp hF₂
  constructor
  · simpa only [hfourier] using hFint
  · simp_rw [← hfourier]
    rw [integral_norm_sq_fourier_of_integrable_memLp_two hg₁ hg₂]
    have hpos : (∫ u : ℝ, ‖g u‖ ^ 2) = ∫ u in Set.Ioi (0 : ℝ), ‖g u‖ ^ 2 := by
      have h := integral_union_eq_left_of_forall (μ := volume)
        (s := Set.Ici (0 : ℝ)) measurableSet_Iio
          (fun u hu => show ‖g u‖ ^ 2 = 0 by rw [hzero u hu, norm_zero, zero_pow (by norm_num)])
      rw [Set.Ici_union_Iio, setIntegral_univ, integral_Ici_eq_integral_Ioi] at h
      exact h
    rw [hpos]
    have ha : 2 * (1 - σ) < 0 := by linarith
    have hmain := (memLp_two_iff_integrable_sq_norm hg₁.aestronglyMeasurable).mp hg₂
    calc
      _ ≤ ∫ u in Set.Ioi (0 : ℝ), C ^ 2 * Real.exp ((2 * (1 - σ)) * u) := by
        apply setIntegral_mono_on hmain.integrableOn
          ((integrableOn_exp_mul_Ioi ha 0).const_mul (C ^ 2)) measurableSet_Ioi
        intro u _
        calc
          _ ≤ (C * Real.exp ((1 - σ) * u)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hdecay u) 2
          _ = _ := by rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
      _ = C ^ 2 / (2 * (σ - 1)) := by
        rw [integral_const_mul, integral_exp_mul_Ioi ha 0]
        simp only [mul_zero, Real.exp_zero]
        have hden : 2 * (1 - σ) = -(2 * (σ - 1)) := by ring
        rw [hden, neg_div_neg_eq]
        ring

/-- Exact coefficient series for the actual twisted von Mangoldt function. -/
theorem LSeries_twistedMangoldt (t : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * zetaTerm t n) s =
      -deriv riemannZeta (s - (t : ℂ) * I) / riemannZeta (s - (t : ℂ) * I) := by
  have hs' : 1 < (s - (t : ℂ) * I).re := by simpa using hs
  calc
    _ = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s - (t : ℂ) * I) := by
      unfold LSeries
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · simp [hn]
      · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
          mul_div_assoc, zetaTerm_div_cpow t hs]
        ring
    _ = _ := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs'

theorem sum_norm_twistedMangoldt_le (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ‖(ArithmeticFunction.vonMangoldt n : ℂ) * zetaTerm t n‖) ≤
      (Real.log 4 + 4) * x := by
  have hI (N : ℕ) : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  calc
    _ = Chebyshev.psi x := by
      rw [Chebyshev.psi, hI]
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, norm_zetaTerm t (Finset.mem_Icc.mp hn).1, Complex.norm_real,
        Real.norm_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg), mul_one]
    _ ≤ _ := Chebyshev.psi_le_const_mul_self hx

/-- Uniform logarithmic-derivative mean square, with actual twists and an explicit constant. -/
theorem zeta_logDeriv_quotient_mean_square_le (t : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Integrable (fun ξ : ℝ => ‖(-deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I)) /
          ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) ∧
    (∫ ξ : ℝ, ‖(-deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I)) /
          ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) ≤
            (Real.log 4 + 4) ^ 2 / (2 * (σ - 1)) := by
  have h := LSeries_quotient_mean_square_le
    (show 0 ≤ Real.log 4 + 4 by positivity) (fun x hx => sum_norm_twistedMangoldt_le t hx) hσ
  have harg (ξ : ℝ) : (σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I - (t : ℂ) * I =
      (σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I := by push_cast; ring
  have hL (ξ : ℝ) := LSeries_twistedMangoldt t
    (s := (σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I) (by simpa using hσ)
  simpa only [hL, harg] using h

/-- The near-frequency derivative integral is controlled by the actual local zeta maximum.
The logarithmic-derivative mean square is discharged by the von Mangoldt theorem above. -/
theorem zeta_deriv_near_frequency_le (t R M : ℝ) {σ : ℝ} (hσ : 1 < σ)
    (hmax : ∀ ξ ∈ Set.Icc (-R) R,
      ‖riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I)‖ ≤ M) :
    (∫ ξ in Set.Icc (-R) R, ‖deriv riemannZeta
      ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) ≤
          M ^ 2 * (Real.log 4 + 4) ^ 2 / (2 * (σ - 1)) := by
  let G : ℝ → ℝ := fun ξ => ‖(-deriv riemannZeta
    ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
      riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I)) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2
  have hG := zeta_logDeriv_quotient_mean_square_le t hσ
  have hpoint (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-R) R) :
      ‖deriv riemannZeta ((σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2 ≤ M ^ 2 * G ξ := by
    let z : ℂ := (σ : ℂ) + ((2 * Real.pi * ξ - t : ℝ) : ℂ) * I
    let s : ℂ := (σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I
    have hz : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simpa [z] using hσ)
    have hs : s ≠ 0 := Complex.ne_zero_of_one_lt_re (by simpa [s] using hσ)
    have hfactor : deriv riemannZeta z / s =
        -riemannZeta z * ((-deriv riemannZeta z / riemannZeta z) / s) := by
      field_simp [hz, hs]
    change ‖deriv riemannZeta z / s‖ ^ 2 ≤
      M ^ 2 * ‖(-deriv riemannZeta z / riemannZeta z) / s‖ ^ 2
    rw [hfactor, norm_mul, norm_neg, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hmax ξ hξ) 2) (sq_nonneg _)
  calc
    _ ≤ ∫ ξ in Set.Icc (-R) R, M ^ 2 * G ξ :=
      setIntegral_mono_on (integrable_zeta_deriv_quotient_sq t hσ).integrableOn
        (hG.1.const_mul (M ^ 2)).integrableOn measurableSet_Icc hpoint
    _ = M ^ 2 * ∫ ξ in Set.Icc (-R) R, G ξ := integral_const_mul _ _
    _ ≤ M ^ 2 * ∫ ξ : ℝ, G ξ := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hG.1 (Filter.Eventually.of_forall fun _ => sq_nonneg _)) (sq_nonneg M)
    _ ≤ M ^ 2 * ((Real.log 4 + 4) ^ 2 / (2 * (σ - 1))) :=
      mul_le_mul_of_nonneg_left hG.2 (sq_nonneg M)
    _ = _ := (mul_div_assoc _ _ _).symm

/-- The actual maximizing twist controls the near-frequency mean square at the source scale.
The center is selected from the original zeta function, not supplied as an analytic premise. -/
theorem exists_maximizingTwist_near_mean_square {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      (∫ ξ in Set.Icc (-(Real.log x / (2 * Real.pi))) (Real.log x / (2 * Real.pi)),
        ‖deriv riemannZeta (twistZetaPoint x t (2 * Real.pi * ξ)) /
          ((((1 + 1 / Real.log x : ℝ) : ℂ)) + ((2 * Real.pi * ξ : ℝ) : ℂ) * I)‖ ^ 2) ≤
            ‖riemannZeta (twistZetaPoint x t t₀)‖ ^ 2 * (Real.log 4 + 4) ^ 2 * Real.log x / 2 := by
  obtain ⟨t₀, ht₀, hmax⟩ := exists_maximizingTwist hx t
  refine ⟨t₀, ht₀, hmax, ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hσ : 1 < 1 + 1 / Real.log x := lt_add_of_pos_right 1 (one_div_pos.mpr hlog)
  have hp : 0 < 2 * Real.pi := by positivity
  have hnear := zeta_deriv_near_frequency_le t (Real.log x / (2 * Real.pi))
    ‖riemannZeta (twistZetaPoint x t t₀)‖ hσ (fun ξ hξ => by
      apply hmax
      rw [abs_mul, abs_of_pos hp]
      have habs : |ξ| ≤ Real.log x / (2 * Real.pi) := abs_le.mpr hξ
      have hb := (le_div_iff₀ hp).mp habs
      linarith)
  have hscale : ‖riemannZeta (twistZetaPoint x t t₀)‖ ^ 2 * (Real.log 4 + 4) ^ 2 /
      (2 * (1 + 1 / Real.log x - 1)) =
        ‖riemannZeta (twistZetaPoint x t t₀)‖ ^ 2 * (Real.log 4 + 4) ^ 2 * Real.log x / 2 := by
    field_simp
    ring
  rw [hscale] at hnear
  exact hnear

private theorem laplace_dilation (g : ℝ → ℂ) (s : ℂ) (b : ℝ)
    (hg : Integrable (fun u : ℝ => g u * Complex.exp (-s * u))) :
    Integrable (fun u : ℝ => (g u - (Real.exp b : ℂ) * g (u - b)) *
      Complex.exp (-s * u)) ∧
    (∫ u : ℝ, (g u - (Real.exp b : ℂ) * g (u - b)) * Complex.exp (-s * u)) =
      (∫ u : ℝ, g u * Complex.exp (-s * u)) * (1 - Complex.exp ((1 - s) * b)) := by
  let c : ℂ := Complex.exp ((1 - s) * b)
  have hshift := (hg.comp_sub_right b).const_mul c
  have heq (u : ℝ) :
      (g u - (Real.exp b : ℂ) * g (u - b)) * Complex.exp (-s * u) =
        g u * Complex.exp (-s * u) - c * (g (u - b) * Complex.exp (-s * (u - b : ℝ))) := by
    have hexp : (Real.exp b : ℂ) * Complex.exp (-s * u) =
        c * Complex.exp (-s * (u - b : ℝ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      dsimp only [c]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = g u * Complex.exp (-s * u) -
          g (u - b) * ((Real.exp b : ℂ) * Complex.exp (-s * u)) := by ring
      _ = _ := by rw [hexp]; ring
  simp_rw [heq]
  refine ⟨hg.sub hshift, ?_⟩
  rw [integral_sub hg hshift, integral_const_mul,
    integral_sub_right_eq_self (fun u : ℝ => g u * Complex.exp (-s * u)) b]
  dsimp only [c]
  ring

/-- The exact Laplace transform of the unnormalized difference corresponding
to two normalized zeta sums. The original cutoff functions are retained. -/
theorem laplace_zetaSum_dilation (t b : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun u : ℝ => (zetaSum (Real.exp u) t -
      (Real.exp b : ℂ) * zetaSum (Real.exp (u - b)) t) * Complex.exp (-s * u)) ∧
    (∫ u : ℝ, (zetaSum (Real.exp u) t -
      (Real.exp b : ℂ) * zetaSum (Real.exp (u - b)) t) * Complex.exp (-s * u)) =
        (riemannZeta (s - (t : ℂ) * I) / s) * (1 - Complex.exp ((1 - s) * b)) := by
  have h := laplace_dilation (fun u => zetaSum (Real.exp u) t) s b (integrable_zetaSum_exp t hs)
  rwa [integral_zetaSum_exp_univ t hs] at h

/-- The matching dilation transform for the logarithmically weighted original
coefficients, with the derivative sign and denominator unchanged. -/
theorem laplace_logZetaSum_dilation (t b : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun u : ℝ => (logZetaSum (Real.exp u) t -
      (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) t) * Complex.exp (-s * u)) ∧
    (∫ u : ℝ, (logZetaSum (Real.exp u) t -
      (Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) t) * Complex.exp (-s * u)) =
        (-deriv riemannZeta (s - (t : ℂ) * I) / s) *
          (1 - Complex.exp ((1 - s) * b)) := by
  have h := laplace_dilation (fun u => logZetaSum (Real.exp u) t) s b
    (integrable_logZetaSum_exp t hs)
  rwa [integral_logZetaSum_exp_univ t hs] at h

end
end DongWangWangZhang2026
