import RiemannZeta.GuthMaynard.DFIEquation29

open Complex
open Classical
open scoped FourierTransform SchwartzMap ContDiff

namespace RiemannZeta.GuthMaynard

theorem probe_arch_shift (q : ℕ) [NeZero q] (s : ℂ) (hs : s ≠ 0) :
    dfiPeriodicArchimedeanFactor q (s + 1) =
      (q : ℂ) / (2 * Real.pi : ℂ) * s * dfiPeriodicArchimedeanFactor q s := by
  unfold dfiPeriodicArchimedeanFactor
  rw [Complex.Gamma_add_one s hs]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [show s + 1 - 1 = s by ring]
  rw [show -(s + 1) = -s + (-1) by ring]
  rw [Complex.cpow_add _ _ hp]
  rw [Complex.cpow_neg_one]
  have hqpow : (q : ℂ) ^ s = (q : ℂ) ^ (s - 1) * (q : ℂ) := by
    calc
      (q : ℂ) ^ s = (q : ℂ) ^ ((s - 1) + 1) := by congr 1; ring
      _ = (q : ℂ) ^ (s - 1) * (q : ℂ) ^ (1 : ℂ) :=
        Complex.cpow_add _ _ hq
      _ = (q : ℂ) ^ (s - 1) * (q : ℂ) := by simp
  rw [hqpow]
  field_simp

theorem probe_plus_shift (q : ℕ) [NeZero q] (z : ℂ) (hz : z ≠ 1) :
    dfiVoronoiPlusMultiplier q (z - 1) =
      ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 * (1 - z) ^ 2 *
        dfiVoronoiPlusMultiplier q z := by
  have hs : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold dfiVoronoiPlusMultiplier
  rw [show 1 - (z - 1) = (1 - z) + 1 by ring]
  rw [probe_arch_shift q (1 - z) hs]
  ring

theorem probe_minus_shift (q : ℕ) [NeZero q] (z : ℂ) (hz : z ≠ 1) :
    dfiVoronoiMinusMultiplier q (z - 1) =
      -(((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 * (1 - z) ^ 2) *
        dfiVoronoiMinusMultiplier q z := by
  have hs : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold dfiVoronoiMinusMultiplier
  rw [show 1 - (z - 1) = (1 - z) + 1 by ring]
  rw [probe_arch_shift q (1 - z) hs]
  have hep : cexp (Real.pi * I * ((1 - z) + 1)) =
      -cexp (Real.pi * I * (1 - z)) := by
    rw [show Real.pi * I * ((1 - z) + 1) =
      Real.pi * I * (1 - z) + Real.pi * I by ring]
    exact Complex.exp_add_pi_mul_I _
  have hem : cexp (-Real.pi * I * ((1 - z) + 1)) =
      -cexp (-Real.pi * I * (1 - z)) := by
    rw [show -Real.pi * I * ((1 - z) + 1) =
      -Real.pi * I * (1 - z) - Real.pi * I by ring]
    exact Complex.exp_sub_pi_mul_I _
  rw [hep, hem]
  ring

noncomputable def probe_log_iterate_test
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) (k : ℕ) :
    DFIVoronoiTestFunction (dfiMellinLogDerivativeIterate σ k g) where
  lower := hg.lower
  upper := hg.upper
  lower_pos := hg.lower_pos
  lower_le_upper := hg.lower_le_upper
  smooth := contDiff_dfiMellinLogDerivativeIterate hg.smooth k
  support_subset := by
    intro x hx
    have hxt : x ∈ tsupport (dfiMellinLogDerivativeIterate σ k g) :=
      subset_tsupport _ hx
    have hxg : x ∈ tsupport g :=
      tsupport_dfiMellinLogDerivativeIterate_subset σ k g hxt
    exact closure_minimal hg.support_subset isClosed_Icc hxg

noncomputable def probe_log_operator_test
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ : ℝ) :
    DFIVoronoiTestFunction (dfiMellinLogOperator σ g) where
  lower := hg.lower
  upper := hg.upper
  lower_pos := hg.lower_pos
  lower_le_upper := hg.lower_le_upper
  smooth := contDiff_dfiMellinLogOperator hg.smooth
  support_subset := by
    intro x hx
    have hxt : x ∈ tsupport (dfiMellinLogOperator σ g) := subset_tsupport _ hx
    have hxg : x ∈ tsupport g := tsupport_dfiMellinLogOperator_subset σ g hxt
    exact closure_minimal hg.support_subset isClosed_Icc hxg

theorem probe_mellinConvergent_complex
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (z : ℂ) :
    MellinConvergent g z := by
  exact mellinConvergent_of_isBigO_rpow
    (hg.continuous.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
    (hg.isBigO_atTop (z.re + 1)) (by simp)
    (hg.isBigO_atZero (z.re - 1)) (by simp)

theorem probe_mellin_log_iterate_one_line
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ u : ℝ) :
    mellin (dfiMellinLogDerivativeIterate σ 1 g)
        ((σ : ℂ) + (u : ℂ) * I) =
      ((u : ℂ) * I) * mellin g ((σ : ℂ) + (u : ℂ) * I) := by
  let f : ℝ → ℂ := dfiVoronoiMellinKernel σ g
  let g₁ : ℝ → ℂ := dfiMellinLogDerivativeIterate σ 1 g
  have hg₁ : DFIVoronoiTestFunction g₁ := probe_log_iterate_test hg σ 1
  have hfInt : MeasureTheory.Integrable f :=
    (hg.contDiff_mellinKernel σ).continuous.integrable_of_hasCompactSupport
      (hg.hasCompactSupport_mellinKernel σ)
  have hfDiff : Differentiable ℝ f :=
    (hg.contDiff_mellinKernel σ).differentiable (by simp)
  have hderiv : deriv f = dfiVoronoiMellinKernel σ g₁ := by
    funext v
    simpa [f, g₁, dfiMellinLogDerivativeIterate,
      dfiVoronoiMellinKernel] using
      iteratedDeriv_dfiVoronoiMellinKernel hg.smooth 1 v
  have hfDerivInt : MeasureTheory.Integrable (deriv f) := by
    rw [hderiv]
    exact (hg₁.contDiff_mellinKernel σ).continuous.integrable_of_hasCompactSupport
      (hg₁.hasCompactSupport_mellinKernel σ)
  have hFourier := Real.fourier_deriv hfInt hfDiff hfDerivInt
  calc
    mellin g₁ ((σ : ℂ) + (u : ℂ) * I) =
        𝓕 (dfiVoronoiMellinKernelSchwartz hg₁ σ)
          (u / (2 * Real.pi)) := hg₁.mellin_eq_fourier_mellinKernel σ u
    _ = 𝓕 (deriv f) (u / (2 * Real.pi)) := by
      apply congrArg (fun h : ℝ → ℂ => 𝓕 h (u / (2 * Real.pi)))
      exact funext fun v => congrFun hderiv v |>.symm
    _ = ((2 * Real.pi : ℂ) * I * (u / (2 * Real.pi) : ℝ)) *
        𝓕 f (u / (2 * Real.pi)) := by
      rw [congr_fun hFourier (u / (2 * Real.pi))]
      simp [smul_eq_mul]
    _ = ((u : ℂ) * I) * mellin g ((σ : ℂ) + (u : ℂ) * I) := by
      have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      have hcoef : (2 * Real.pi : ℂ) * I * (u / (2 * Real.pi) : ℝ) =
          (u : ℂ) * I := by
        push_cast
        field_simp
      rw [hcoef]
      congr 1
      simpa [f] using (hg.mellin_eq_fourier_mellinKernel σ u).symm

theorem probe_mellin_log_operator_line
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (ρ σ u : ℝ) :
    mellin (dfiMellinLogOperator ρ g) ((σ : ℂ) + (u : ℂ) * I) =
      (((ρ - σ : ℝ) : ℂ) - (u : ℂ) * I) *
        mellin g ((σ : ℂ) + (u : ℂ) * I) := by
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I
  let Lσ : ℝ → ℂ := dfiMellinLogOperator σ g
  let g₁ : ℝ → ℂ := dfiMellinLogDerivativeIterate σ 1 g
  have hg₁ : DFIVoronoiTestFunction g₁ := probe_log_iterate_test hg σ 1
  have hLσ : DFIVoronoiTestFunction Lσ := probe_log_operator_test hg σ
  have hm₁ : mellin g₁ z = ((u : ℂ) * I) * mellin g z := by
    simpa [z, g₁] using probe_mellin_log_iterate_one_line hg σ u
  have hneg : mellin g₁ z = -mellin Lσ z := by
    have h := mellin_const_smul Lσ z (-1 : ℂ)
    simpa [g₁, Lσ, dfiMellinLogDerivativeIterate, smul_eq_mul] using h
  have hmLσ : mellin Lσ z = -((u : ℂ) * I) * mellin g z := by
    calc
      mellin Lσ z = -mellin g₁ z := by rw [hneg]; ring
      _ = -((u : ℂ) * I) * mellin g z := by rw [hm₁]; ring
  have hcg := hasMellin_const_smul (probe_mellinConvergent_complex hg z)
    ((ρ - σ : ℝ) : ℂ)
  have hadd := hasMellin_add hcg.1 (probe_mellinConvergent_complex hLσ z)
  have hfun : dfiMellinLogOperator ρ g =
      fun x => ((ρ - σ : ℝ) : ℂ) * g x + Lσ x := by
    funext x
    simp only [dfiMellinLogOperator, Lσ]
    push_cast
    ring
  rw [hfun]
  change mellin (fun x => ((ρ - σ : ℝ) : ℂ) * g x + Lσ x) z = _
  have hadd' : mellin (fun x => ((ρ - σ : ℝ) : ℂ) * g x + Lσ x) z =
      mellin (fun x => ((ρ - σ : ℝ) : ℂ) * g x) z + mellin Lσ z := by
    simpa only [smul_eq_mul] using hadd.2
  have hcg' : mellin (fun x => ((ρ - σ : ℝ) : ℂ) * g x) z =
      ((ρ - σ : ℝ) : ℂ) * mellin g z := by
    simpa only [smul_eq_mul] using hcg.2
  rw [hadd', hcg', hmLσ]
  change ((ρ - σ : ℝ) : ℂ) * mellin g z +
      -((u : ℂ) * I) * mellin g z =
    (((ρ - σ : ℝ) : ℂ) - (u : ℂ) * I) *
      mellin g ((σ : ℂ) + (u : ℂ) * I)
  change _ = (((ρ - σ : ℝ) : ℂ) - (u : ℂ) * I) * mellin g z
  ring

end RiemannZeta.GuthMaynard
