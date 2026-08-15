import RiemannZeta.GuthMaynard.DFIEquation24
import RiemannZeta.GuthMaynard.DFIBesselKernel
import RiemannZeta.GuthMaynard.DFIBesselTransformBridge
import RiemannZeta.GuthMaynard.DFIEquation28
import RiemannZeta.GuthMaynard.ArithmeticCoefficients
import RiemannZeta.GuthMaynard.GammaVerticalDecay
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DFI equation (29): effective dual-frequency truncation

This file proves the contour displacement and rapid frequency decay behind
the two inequalities in DFI equation (29).  The contour is moved one unit at
a time so that every horizontal side is controlled on a translated compact
Mellin strip.
-/

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology Interval
open Classical

namespace RiemannZeta.GuthMaynard

/-- Quantitative tail of a shifted real `p`-series.  This is the summation
lemma that turns the pointwise Mellin-contour decay in DFI (29) into an
effective dual-frequency truncation with an explicit power saving. -/
theorem tsum_nat_add_one_rpow_neg_le
    {L p : ℝ} (hL : 0 < L) (hp : 1 < p) :
    ∑' j : ℕ, (L + (j + 1 : ℕ)) ^ (-p) ≤ L ^ (1 - p) / (p - 1) := by
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact Real.rpow_nonneg (by positivity) _
  · intro N
    have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-p))
        (Set.Icc L (L + N)) := by
      exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
        (fun x hx ↦ hL.trans_le hx.1)
    have hsum :
        ∑ j ∈ Finset.range N, (L + (j + 1 : ℕ)) ^ (-p) ≤
          ∫ x in L..L + N, x ^ (-p) :=
      hanti.sum_le_integral
    have hzero_not_mem : (0 : ℝ) ∉ [[L, L + N]] := by
      rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg N))]
      exact fun hx ↦ hL.not_ge hx.1
    rw [integral_rpow
      (Or.inr ⟨by linarith, hzero_not_mem⟩)] at hsum
    calc
      ∑ j ∈ Finset.range N, (L + (j + 1 : ℕ)) ^ (-p) ≤
          (((L + N) ^ (-p + 1) - L ^ (-p + 1)) / (-p + 1)) := hsum
      _ = (L ^ (1 - p) - (L + N) ^ (1 - p)) / (p - 1) := by
        field_simp [show p - 1 ≠ 0 by linarith, show -p + 1 ≠ 0 by linarith]
        ring_nf
      _ ≤ L ^ (1 - p) / (p - 1) := by
        have hpow : 0 ≤ (L + N) ^ (1 - p) := Real.rpow_nonneg (by positivity) _
        have hden : 0 < p - 1 := by linarith
        apply (div_le_div_iff_of_pos_right hden).2
        linarith

private lemma dfiEquation29_zeroTendstoDiff
    (L₁ L₂ : ℂ) (f : ℝ → ℂ) (h : ∀ᶠ T in atTop, f T = 0)
    (h' : Tendsto f atTop (𝓝 (L₂ - L₁))) : L₁ = L₂ := by
  rw [← zero_add L₁, ← @eq_sub_iff_add_eq]
  exact tendsto_nhds_unique (EventuallyEq.tendsto h) h'

private lemma dfiEquation29_rectangle_tendsTo_vertical
    {σ σ' : ℝ} {f : ℂ → ℂ}
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I))
      atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I))
      atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    Tendsto (fun (T : ℝ) ↦ RectangleIntegral f (σ - I * T) (σ' + I * T))
      atTop (𝓝 (VerticalIntegral f σ' - VerticalIntegral f σ)) := by
  simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, sub_zero, add_re, add_zero, sub_im, mul_im,
    one_mul, zero_add, zero_sub, add_im]
  apply Tendsto.sub
  · rewrite [← zero_add (VerticalIntegral _ _), ← zero_sub_zero]
    apply Tendsto.add <| Tendsto.sub (hbot.comp tendsto_neg_atTop_atBot) htop
    exact (intervalIntegral_tendsto_integral hright
      tendsto_neg_atTop_atBot tendsto_id).const_smul I
  · exact (intervalIntegral_tendsto_integral hleft
      tendsto_neg_atTop_atBot tendsto_id).const_smul I

private lemma dfiEquation29_verticalIntegral_eq
    {σ σ' : ℝ} {f : ℂ → ℂ}
    (hf : HolomorphicOn f ([[σ, σ']] ×ℂ univ))
    (hbot : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I))
      atBot (𝓝 0))
    (htop : Tendsto (fun (y : ℝ) ↦ ∫ (x : ℝ) in σ..σ', f (x + y * I))
      atTop (𝓝 0))
    (hleft : Integrable (fun (y : ℝ) ↦ f (σ + y * I)))
    (hright : Integrable (fun (y : ℝ) ↦ f (σ' + y * I))) :
    VerticalIntegral f σ = VerticalIntegral f σ' := by
  refine dfiEquation29_zeroTendstoDiff _ _ _ (univ_mem' fun _ ↦ ?_)
    (dfiEquation29_rectangle_tendsTo_vertical hbot htop hleft hright)
  exact integral_boundary_rect_eq_zero_of_differentiableOn f _ _
    (hf.mono fun z hrect ↦ ⟨by simpa using hrect.1, trivial⟩)

noncomputable def dfiEquation29Multiplier (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) : ℂ → ℂ :=
  match branch with
  | .minusTerm => dfiVoronoiMinusMultiplier q
  | .plusTerm => dfiVoronoiPlusMultiplier q

noncomputable def dfiEquation29Integrand (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (n : ℂ) ^ (-(1 - z)) * dfiEquation29Multiplier q branch z * mellin g z

noncomputable def dfiEquation29TransformAt (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ) (n : ℕ) (σ : ℝ) : ℂ :=
  VerticalIntegral' (dfiEquation29Integrand q branch g n) σ

noncomputable def dfiEquation29InitialTransform (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  match branch with
  | .minusTerm => dfiVoronoiMinusTransform q (mellin g) n
  | .plusTerm => dfiVoronoiPlusTransform q (mellin g) n

/-- Exact unit-shift recurrence for the common archimedean factor.  This is
the Gamma recurrence in the normalization used by DFI's Voronoi formula. -/
theorem dfiPeriodicArchimedeanFactor_add_one
    (q : ℕ) [NeZero q] (s : ℂ) (hs : s ≠ 0) :
    dfiPeriodicArchimedeanFactor q (s + 1) =
      (q : ℂ) / (2 * Real.pi : ℂ) * s *
        dfiPeriodicArchimedeanFactor q s := by
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

/-- Under a unit displacement of the Mellin variable, the mixed-sign
Voronoi multiplier gains the exact quadratic differential factor. -/
theorem dfiVoronoiPlusMultiplier_sub_one
    (q : ℕ) [NeZero q] (z : ℂ) (hz : z ≠ 1) :
    dfiVoronoiPlusMultiplier q (z - 1) =
      ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 * (1 - z) ^ 2 *
        dfiVoronoiPlusMultiplier q z := by
  have hs : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold dfiVoronoiPlusMultiplier
  rw [show 1 - (z - 1) = (1 - z) + 1 by ring]
  rw [dfiPeriodicArchimedeanFactor_add_one q (1 - z) hs]
  ring

/-- The equal-sign Voronoi multiplier obeys the same shift recurrence with
the sign change forced by the two exponential factors. -/
theorem dfiVoronoiMinusMultiplier_sub_one
    (q : ℕ) [NeZero q] (z : ℂ) (hz : z ≠ 1) :
    dfiVoronoiMinusMultiplier q (z - 1) =
      -(((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 * (1 - z) ^ 2) *
        dfiVoronoiMinusMultiplier q z := by
  have hs : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold dfiVoronoiMinusMultiplier
  rw [show 1 - (z - 1) = (1 - z) + 1 by ring]
  rw [dfiPeriodicArchimedeanFactor_add_one q (1 - z) hs]
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

/-- Mellin Euler differentiation preserves the exact compactly supported
DFI test-function class. -/
noncomputable def DFIVoronoiTestFunction.mellinLogOperator
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

/-- The signed physical weights generated by logarithmic Mellin
differentiation remain DFI test functions at every order. -/
noncomputable def DFIVoronoiTestFunction.mellinLogDerivativeIterate
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

/-- Compact support away from zero makes the Mellin transform absolutely
convergent at every complex argument, not only at a real point. -/
theorem DFIVoronoiTestFunction.mellinConvergent_complex
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (z : ℂ) :
    MellinConvergent g z := by
  exact mellinConvergent_of_isBigO_rpow
    (hg.continuous.locallyIntegrable.locallyIntegrableOn (Set.Ioi 0))
    (hg.isBigO_atTop (z.re + 1)) (by simp)
    (hg.isBigO_atZero (z.re - 1)) (by simp)

/-- One logarithmic derivative of the physical Mellin kernel multiplies
its Mellin transform by the exact vertical frequency. -/
theorem DFIVoronoiTestFunction.mellin_logDerivativeIterate_one_line
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (σ u : ℝ) :
    mellin (dfiMellinLogDerivativeIterate σ 1 g)
        ((σ : ℂ) + (u : ℂ) * I) =
      ((u : ℂ) * I) * mellin g ((σ : ℂ) + (u : ℂ) * I) := by
  let f : ℝ → ℂ := dfiVoronoiMellinKernel σ g
  let g₁ : ℝ → ℂ := dfiMellinLogDerivativeIterate σ 1 g
  have hg₁ : DFIVoronoiTestFunction g₁ := hg.mellinLogDerivativeIterate σ 1
  have hfInt : Integrable f :=
    (hg.contDiff_mellinKernel σ).continuous.integrable_of_hasCompactSupport
      (hg.hasCompactSupport_mellinKernel σ)
  have hfDiff : Differentiable ℝ f :=
    (hg.contDiff_mellinKernel σ).differentiable (by simp)
  have hderiv : deriv f = dfiVoronoiMellinKernel σ g₁ := by
    funext v
    simpa [f, g₁, dfiMellinLogDerivativeIterate,
      dfiVoronoiMellinKernel] using
      iteratedDeriv_dfiVoronoiMellinKernel hg.smooth 1 v
  have hfDerivInt : Integrable (deriv f) := by
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

/-- Mellin transform of the physical Euler operator on an arbitrary
vertical line.  Taking `ρ = 1` produces the factor `1-z` required by the
Bessel recurrence. -/
theorem DFIVoronoiTestFunction.mellin_mellinLogOperator_line
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (ρ σ u : ℝ) :
    mellin (dfiMellinLogOperator ρ g) ((σ : ℂ) + (u : ℂ) * I) =
      (((ρ - σ : ℝ) : ℂ) - (u : ℂ) * I) *
        mellin g ((σ : ℂ) + (u : ℂ) * I) := by
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I
  let Lσ : ℝ → ℂ := dfiMellinLogOperator σ g
  let g₁ : ℝ → ℂ := dfiMellinLogDerivativeIterate σ 1 g
  have hLσ : DFIVoronoiTestFunction Lσ := hg.mellinLogOperator σ
  have hm₁ : mellin g₁ z = ((u : ℂ) * I) * mellin g z := by
    simpa [z, g₁] using hg.mellin_logDerivativeIterate_one_line σ u
  have hneg : mellin g₁ z = -mellin Lσ z := by
    have h := mellin_const_smul Lσ z (-1 : ℂ)
    simpa [g₁, Lσ, dfiMellinLogDerivativeIterate, smul_eq_mul] using h
  have hmLσ : mellin Lσ z = -((u : ℂ) * I) * mellin g z := by
    calc
      mellin Lσ z = -mellin g₁ z := by rw [hneg]; ring
      _ = -((u : ℂ) * I) * mellin g z := by rw [hm₁]; ring
  have hcg := hasMellin_const_smul (hg.mellinConvergent_complex z)
    ((ρ - σ : ℝ) : ℂ)
  have hadd := hasMellin_add hcg.1 (hLσ.mellinConvergent_complex z)
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

/-- Starting with the inverse source weight, repeatedly apply the Euler
operator whose Mellin symbol is `1-z`. -/
noncomputable def dfiEquation29BesselShiftIterate :
    ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, g => dfiVoronoiInvWeight g
  | k + 1, g => dfiMellinLogOperator 1 (dfiEquation29BesselShiftIterate k g)

@[simp] theorem dfiEquation29BesselShiftIterate_zero (g : ℝ → ℂ) :
    dfiEquation29BesselShiftIterate 0 g = dfiVoronoiInvWeight g := rfl

@[simp] theorem dfiEquation29BesselShiftIterate_succ (k : ℕ) (g : ℝ → ℂ) :
    dfiEquation29BesselShiftIterate (k + 1) g =
      dfiMellinLogOperator 1 (dfiEquation29BesselShiftIterate k g) := rfl

/-- Every iterated Bessel-shift weight remains in the same positive compact
support interval as the source. -/
noncomputable def DFIVoronoiTestFunction.besselShiftIterate
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (k : ℕ) :
    DFIVoronoiTestFunction (dfiEquation29BesselShiftIterate k g) := by
  induction k with
  | zero => simpa using hg.invWeight
  | succ k ih => simpa [dfiEquation29BesselShiftIterate] using ih.mellinLogOperator 1

/-- The first Euler operation cancels the inverse source weight exactly.
This elementary identity is the reason the recurrence has the source-scale
strength asserted in DFI (29). -/
theorem DFIVoronoiTestFunction.mellinLogOperator_one_invWeight
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    dfiMellinLogOperator 1 (dfiVoronoiInvWeight g) = deriv g := by
  funext x
  by_cases hx : x = 0
  · subst x
    have hzero : g =ᶠ[nhds (0 : ℝ)] 0 := by
      filter_upwards [Iio_mem_nhds hg.lower_pos] with y hy
      have hgy : g y = 0 := by
        by_contra hne
        exact (not_le_of_gt hy) (hg.support_subset hne).1
      simp [hgy]
    have hizero : dfiVoronoiInvWeight g =ᶠ[nhds (0 : ℝ)] 0 := by
      filter_upwards [hzero] with y hy
      simp [dfiVoronoiInvWeight, hy]
    have hdg : deriv g 0 = 0 := by
      simpa using Filter.EventuallyEq.deriv_eq hzero
    have hdi : deriv (dfiVoronoiInvWeight g) 0 = 0 := by
      simpa using Filter.EventuallyEq.deriv_eq hizero
    simp [dfiMellinLogOperator, dfiVoronoiInvWeight, hdg, hdi]
  · have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    have hinv0 := hasDerivAt_ofReal_cpow_const
      (x := x) hx (r := (-1 : ℂ)) (by norm_num)
    have hinv : HasDerivAt (fun y : ℝ => ((y : ℂ))⁻¹)
        (-((x : ℂ) ^ 2)⁻¹) x := by
      convert hinv0 using 1
      · simp [Complex.cpow_neg_one]
      · rw [show (-1 : ℂ) - 1 = ((-2 : ℤ) : ℂ) by norm_num,
          Complex.cpow_intCast]
        norm_num [zpow_neg, hxC, pow_two]
        field_simp
    have hgderiv : HasDerivAt g (deriv g x) x :=
      (hg.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
    have hprod := hinv.mul hgderiv
    unfold dfiMellinLogOperator dfiVoronoiInvWeight
    rw [show deriv (fun y : ℝ => (y : ℂ)⁻¹ * g y) x =
        -((x : ℂ) ^ 2)⁻¹ * g x + (x : ℂ)⁻¹ * deriv g x from hprod.deriv]
    field_simp
    norm_num

/-- Consequently, one complete Bessel shift is the local differential
operator `g' + x g''`, with no residual inverse weight. -/
theorem DFIVoronoiTestFunction.besselShift_two_eq
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) :
    dfiEquation29BesselShiftIterate 2 g =
      dfiMellinLogOperator 1 (deriv g) := by
  rw [show dfiEquation29BesselShiftIterate 2 g =
      dfiMellinLogOperator 1
        (dfiMellinLogOperator 1 (dfiVoronoiInvWeight g)) by rfl]
  rw [hg.mellinLogOperator_one_invWeight]

theorem DFIVoronoiTestFunction.besselShift_two_apply
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (x : ℝ) :
    dfiEquation29BesselShiftIterate 2 g x =
      deriv g x + (x : ℂ) * deriv (deriv g) x := by
  rw [congrFun hg.besselShift_two_eq x]
  simp [dfiMellinLogOperator]

/-- Ordinary differentiation commutes with iteration in the expected
successor form. -/
theorem iteratedDeriv_deriv_eq_succ
    {g : ℝ → ℂ} (j : ℕ) :
    iteratedDeriv j (deriv g) = iteratedDeriv (j + 1) g := by
  induction j with
  | zero => simp [iteratedDeriv_one]
  | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      rw [← iteratedDeriv_succ]

/-- Exact derivative formula for the complete source recurrence.  It
raises derivative order by at most two and exposes the sole physical-scale
factor `x`. -/
theorem DFIVoronoiTestFunction.iteratedDeriv_besselShift_two
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (dfiEquation29BesselShiftIterate 2 g) x =
      ((1 : ℂ) + j) * iteratedDeriv (j + 1) g x +
        (x : ℂ) * iteratedDeriv (j + 2) g x := by
  rw [hg.besselShift_two_eq]
  rw [iteratedDeriv_dfiMellinLogOperator
    (show ContDiff ℝ ∞ (deriv g) by
      simpa [iteratedDeriv_one] using
        (ContDiff.contDiff_iteratedDeriv_top hg.smooth 1)) j x]
  rw [congrFun (iteratedDeriv_deriv_eq_succ (g := g) j) x]
  rw [congrFun (iteratedDeriv_deriv_eq_succ (g := g) (j + 1)) x]
  congr 2

/-- Quantitative one-step form of the complete Bessel recurrence.  Under
the derivative profile in DFI (2), the local operator `g' + x g''` costs
exactly one physical support scale and two derivative scales. -/
theorem DFIVoronoiTestFunction.norm_iteratedDeriv_besselShift_two_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {A B S : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 < S)
    (hSB : 1 ≤ S * B) (j : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc S (2 * S))
    (hDeriv : ∀ r ≤ j + 2,
      ‖iteratedDeriv r g x‖ ≤ A * B ^ r) :
    ‖iteratedDeriv j (dfiEquation29BesselShiftIterate 2 g) x‖ ≤
      A * (((j : ℝ) + 3) * S * B ^ 2) * B ^ j := by
  rw [hg.iteratedDeriv_besselShift_two]
  have h1 := hDeriv (j + 1) (by omega)
  have h2 := hDeriv (j + 2) (by omega)
  have hx0 : 0 ≤ x := hS.le.trans hx.1
  have hxnorm : ‖(x : ℂ)‖ ≤ 2 * S := by
    simpa [Real.norm_of_nonneg hx0] using hx.2
  have hcoeff : ‖(1 : ℂ) + j‖ = (j : ℝ) + 1 := by
    rw [show (1 : ℂ) + j = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_of_nonneg]
    positivity
  have hBstep : B ^ (j + 1) ≤ S * B ^ (j + 2) := by
    rw [show B ^ (j + 1) = B ^ j * B by
      simpa using pow_succ B j]
    rw [show B ^ (j + 2) = B ^ j * B ^ 2 by
      calc
        B ^ (j + 2) = B ^ j * B ^ 2 := by rw [pow_add]
        _ = _ := rfl]
    have hBB : B ≤ S * B ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hSB hB]
    calc
      B ^ j * B ≤ B ^ j * (S * B ^ 2) :=
        mul_le_mul_of_nonneg_left hBB (pow_nonneg hB j)
      _ = S * (B ^ j * B ^ 2) := by ring
  calc
    ‖((1 : ℂ) + j) * iteratedDeriv (j + 1) g x +
        (x : ℂ) * iteratedDeriv (j + 2) g x‖ ≤
      ‖(1 : ℂ) + j‖ * ‖iteratedDeriv (j + 1) g x‖ +
        ‖(x : ℂ)‖ * ‖iteratedDeriv (j + 2) g x‖ := by
          calc
            _ ≤ ‖((1 : ℂ) + j) * iteratedDeriv (j + 1) g x‖ +
                ‖(x : ℂ) * iteratedDeriv (j + 2) g x‖ := norm_add_le _ _
            _ = _ := by rw [norm_mul, norm_mul]
    _ ≤ ((j : ℝ) + 1) * (A * B ^ (j + 1)) +
        (2 * S) * (A * B ^ (j + 2)) := by
          rw [hcoeff]
          gcongr
    _ ≤ ((j : ℝ) + 1) * (A * (S * B ^ (j + 2))) +
        (2 * S) * (A * B ^ (j + 2)) := by
          gcongr
    _ = A * (((j : ℝ) + 3) * S * B ^ 2) * B ^ j := by
      rw [show B ^ (j + 2) = B ^ j * B ^ 2 by
        rw [show j + 2 = j + 1 + 1 by omega, pow_succ, pow_succ]
        ring]
      ring

/-- Integral form of one complete Bessel recurrence.  This is the form
needed in the tail argument after DFI (29): it preserves the localized
physical mass instead of replacing it by support length times a supremum. -/
theorem DFIVoronoiTestFunction.integral_norm_iteratedDeriv_besselShift_two_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {S : ℝ} (hS : 0 < S) (j : ℕ) :
    (∫ x in Set.Icc S (2 * S),
        ‖iteratedDeriv j (dfiEquation29BesselShiftIterate 2 g) x‖) ≤
      ((j : ℝ) + 1) *
          (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv (j + 1) g x‖) +
        (2 * S) *
          (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv (j + 2) g x‖) := by
  let u : ℝ → ℝ := fun x =>
    ‖iteratedDeriv j (dfiEquation29BesselShiftIterate 2 g) x‖
  let v : ℝ → ℝ := fun x =>
    ((j : ℝ) + 1) * ‖iteratedDeriv (j + 1) g x‖ +
      (2 * S) * ‖iteratedDeriv (j + 2) g x‖
  have hRg : DFIVoronoiTestFunction
      (dfiEquation29BesselShiftIterate 2 g) := hg.besselShiftIterate 2
  have hu : Continuous u := by
    dsimp only [u]
    exact (hRg.smooth.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))).norm
  have hv : Continuous v := by
    dsimp only [v]
    have h1 := hg.smooth.continuous_iteratedDeriv (j + 1)
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top (j + 1))))
    have h2 := hg.smooth.continuous_iteratedDeriv (j + 2)
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top (j + 2))))
    fun_prop
  have huv : ∀ x ∈ Set.Icc S (2 * S), u x ≤ v x := by
    intro x hx
    have hux : u x =
        ‖((1 : ℂ) + j) * iteratedDeriv (j + 1) g x +
          (x : ℂ) * iteratedDeriv (j + 2) g x‖ := by
      dsimp only [u]
      rw [hg.iteratedDeriv_besselShift_two]
    rw [hux]
    have hx0 : 0 ≤ x := hS.le.trans hx.1
    have hxnorm : ‖(x : ℂ)‖ ≤ 2 * S := by
      simpa [Real.norm_of_nonneg hx0] using hx.2
    have hcoeff : ‖(1 : ℂ) + j‖ = (j : ℝ) + 1 := by
      rw [show (1 : ℂ) + j = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_real, Real.norm_of_nonneg]
      positivity
    dsimp only [v]
    calc
      ‖((1 : ℂ) + j) * iteratedDeriv (j + 1) g x +
          (x : ℂ) * iteratedDeriv (j + 2) g x‖ ≤
        ‖(1 : ℂ) + j‖ * ‖iteratedDeriv (j + 1) g x‖ +
          ‖(x : ℂ)‖ * ‖iteratedDeriv (j + 2) g x‖ := by
            simpa only [norm_mul] using norm_add_le
              (((1 : ℂ) + j) * iteratedDeriv (j + 1) g x)
              ((x : ℂ) * iteratedDeriv (j + 2) g x)
      _ ≤ ((j : ℝ) + 1) * ‖iteratedDeriv (j + 1) g x‖ +
          (2 * S) * ‖iteratedDeriv (j + 2) g x‖ := by
            rw [hcoeff]
            gcongr
  have hmono : (∫ x in Set.Icc S (2 * S), u x) ≤
      ∫ x in Set.Icc S (2 * S), v x := by
    apply MeasureTheory.integral_mono_ae
      (hu.continuousOn.integrableOn_compact isCompact_Icc)
      (hv.continuousOn.integrableOn_compact isCompact_Icc)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact huv x hx
  calc
    (∫ x in Set.Icc S (2 * S),
        ‖iteratedDeriv j (dfiEquation29BesselShiftIterate 2 g) x‖) =
        ∫ x in Set.Icc S (2 * S), u x := rfl
    _ ≤ ∫ x in Set.Icc S (2 * S), v x := hmono
    _ = ((j : ℝ) + 1) *
          (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv (j + 1) g x‖) +
        (2 * S) *
          (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv (j + 2) g x‖) := by
      dsimp only [v]
      rw [MeasureTheory.integral_add]
      · rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      · exact (continuous_const.mul
          (hg.smooth.continuous_iteratedDeriv (j + 1)
            (WithTop.coe_le_coe.mpr
              (le_of_lt (ENat.coe_lt_top (j + 1))))).norm).continuousOn
                |>.integrableOn_compact isCompact_Icc
      · exact (continuous_const.mul
          (hg.smooth.continuous_iteratedDeriv (j + 2)
            (WithTop.coe_le_coe.mpr
              (le_of_lt (ENat.coe_lt_top (j + 2))))).norm).continuousOn
                |>.integrableOn_compact isCompact_Icc

/-- Repeated application of the complete two-Euler-derivative Bessel
operator. -/
noncomputable def dfiEquation29BesselRecurrenceIterate :
    ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, g => g
  | k + 1, g => dfiEquation29BesselRecurrenceIterate k
      (dfiEquation29BesselShiftIterate 2 g)

@[simp] theorem dfiEquation29BesselRecurrenceIterate_zero (g : ℝ → ℂ) :
    dfiEquation29BesselRecurrenceIterate 0 g = g := rfl

@[simp] theorem dfiEquation29BesselRecurrenceIterate_succ
    (k : ℕ) (g : ℝ → ℂ) :
    dfiEquation29BesselRecurrenceIterate (k + 1) g =
      dfiEquation29BesselRecurrenceIterate k
        (dfiEquation29BesselShiftIterate 2 g) := rfl

/-- Iterated integral recurrence preserving the physical `L¹` mass.
Compared with the pointwise recurrence, this theorem removes the spurious
support-length factor which would destroy DFI's uniformity when `X` and
`Y` have very different sizes. -/
theorem DFIVoronoiTestFunction.integral_norm_besselRecurrenceIterate_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {A B S D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 < S)
    (hSB : 1 ≤ S * B) (k : ℕ)
    (hD : (2 * k + 3 : ℕ) ≤ D)
    (hL1 : ∀ r ≤ 2 * k,
      (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv r g x‖) ≤ A * B ^ r) :
    (∫ x in Set.Icc S (2 * S),
        ‖dfiEquation29BesselRecurrenceIterate k g x‖) ≤
      A * (D * S * B ^ 2) ^ k := by
  induction k generalizing g A with
  | zero =>
      simpa using hL1 0 (by simp)
  | succ k ih =>
      let Rg : ℝ → ℂ := dfiEquation29BesselShiftIterate 2 g
      let F : ℝ := D * S * B ^ 2
      let A' : ℝ := A * F
      have hRg : DFIVoronoiTestFunction Rg := hg.besselShiftIterate 2
      have hD0 : 0 ≤ D := le_trans (Nat.cast_nonneg _) hD
      have hF : 0 ≤ F := by dsimp only [F]; positivity
      have hA' : 0 ≤ A' := mul_nonneg hA hF
      have hD' : (2 * k + 3 : ℕ) ≤ D := by
        exact le_trans (by exact_mod_cast (show 2 * k + 3 ≤
          2 * (k + 1) + 3 by omega)) hD
      have hRgL1 : ∀ r ≤ 2 * k,
          (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv r Rg x‖) ≤
            A' * B ^ r := by
        intro r hr
        have hOne := hg.integral_norm_iteratedDeriv_besselShift_two_le hS r
        have h1 := hL1 (r + 1) (by omega)
        have h2 := hL1 (r + 2) (by omega)
        have hBstep : B ^ (r + 1) ≤ S * B ^ (r + 2) := by
          have hBB : B ≤ S * B ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_left hSB hB]
          calc
            B ^ (r + 1) = B ^ r * B := by rw [pow_succ]
            B ^ r * B ≤ B ^ r * (S * B ^ 2) :=
              mul_le_mul_of_nonneg_left hBB (pow_nonneg hB r)
            _ = S * B ^ (r + 2) := by rw [pow_add]; ring
        have hrD : (r : ℝ) + 3 ≤ D := by
          have hrNat : r + 3 ≤ 2 * (k + 1) + 3 := by omega
          exact le_trans (by exact_mod_cast hrNat) hD
        calc
          (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv r Rg x‖) ≤
              ((r : ℝ) + 1) *
                  (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv (r + 1) g x‖) +
                (2 * S) *
                  (∫ x in Set.Icc S (2 * S), ‖iteratedDeriv (r + 2) g x‖) :=
            by simpa only [Rg] using hOne
          _ ≤ ((r : ℝ) + 1) * (A * B ^ (r + 1)) +
                (2 * S) * (A * B ^ (r + 2)) := by gcongr
          _ ≤ ((r : ℝ) + 1) * (A * (S * B ^ (r + 2))) +
                (2 * S) * (A * B ^ (r + 2)) := by gcongr
          _ = A * (((r : ℝ) + 3) * S * B ^ 2) * B ^ r := by
            have hpow : B ^ (r + 2) = B ^ r * B ^ 2 := by rw [pow_add]
            rw [hpow]
            ring
          _ ≤ A * (D * S * B ^ 2) * B ^ r := by gcongr
          _ = A' * B ^ r := by dsimp only [A', F]
      have hout := ih hRg hA' hD' hRgL1
      calc
        (∫ x in Set.Icc S (2 * S),
            ‖dfiEquation29BesselRecurrenceIterate (k + 1) g x‖) =
            ∫ x in Set.Icc S (2 * S),
              ‖dfiEquation29BesselRecurrenceIterate k Rg x‖ := rfl
        _ ≤ A' * F ^ k := by simpa only [F] using hout
        _ = A * (D * S * B ^ 2) ^ (k + 1) := by
          dsimp only [A', F]
          rw [pow_succ]
          ring

/-- Every complete Bessel recurrence stays in the source dyadic support.
This makes the later physical Bessel norm estimate use the literal interval
from DFI (2), rather than the auxiliary endpoints of a structure witness. -/
theorem DFIVoronoiTestFunction.support_besselRecurrenceIterate_subset
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {S : ℝ}
    (hSupport : Function.support g ⊆ Set.Icc S (2 * S)) (k : ℕ) :
    Function.support (dfiEquation29BesselRecurrenceIterate k g) ⊆
      Set.Icc S (2 * S) := by
  induction k generalizing g with
  | zero => simpa using hSupport
  | succ k ih =>
      let Rg : ℝ → ℂ := dfiEquation29BesselShiftIterate 2 g
      have hRg : DFIVoronoiTestFunction Rg := hg.besselShiftIterate 2
      have hRgSupport : Function.support Rg ⊆ Set.Icc S (2 * S) := by
        intro x hx
        apply closure_minimal hSupport isClosed_Icc
        have hxR : x ∈ tsupport Rg := subset_tsupport Rg hx
        have hxL : x ∈ tsupport (dfiMellinLogOperator 1 (deriv g)) := by
          rw [show Rg = dfiMellinLogOperator 1 (deriv g) from
            hg.besselShift_two_eq] at hxR
          exact hxR
        exact tsupport_deriv_subset
          (tsupport_dfiMellinLogOperator_subset 1 (deriv g) hxL)
      simpa [dfiEquation29BesselRecurrenceIterate_succ, Rg] using
        ih hRg hRgSupport

/-- Iterating the exact Bessel recurrence preserves the original dyadic
support and costs `(D*S*B^2)^k`.  This is the quantitative source bridge
from DFI (2) to the arbitrary-power truncation asserted after (29). -/
theorem DFIVoronoiTestFunction.norm_iteratedDeriv_besselRecurrenceIterate_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    {A B S D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hS : 0 < S)
    (hSB : 1 ≤ S * B)
    (hSupport : Function.support g ⊆ Set.Icc S (2 * S)) (k p : ℕ)
    (hD : (p + 2 * k + 3 : ℕ) ≤ D)
    (hDeriv : ∀ r ≤ p + 2 * k, ∀ x : ℝ,
      ‖iteratedDeriv r g x‖ ≤ A * B ^ r) :
    ∀ j ≤ p, ∀ x ∈ Set.Icc S (2 * S),
      ‖iteratedDeriv j (dfiEquation29BesselRecurrenceIterate k g) x‖ ≤
        A * (D * S * B ^ 2) ^ k * B ^ j := by
  induction k generalizing g A p with
  | zero =>
      intro j hj x hx
      simp only [dfiEquation29BesselRecurrenceIterate_zero, pow_zero, mul_one]
      exact hDeriv j (by simpa using hj) x
  | succ k ih =>
      let Rg : ℝ → ℂ := dfiEquation29BesselShiftIterate 2 g
      have hRg : DFIVoronoiTestFunction Rg := hg.besselShiftIterate 2
      have hRgSupport : Function.support Rg ⊆ Set.Icc S (2 * S) := by
        intro x hx
        apply closure_minimal hSupport isClosed_Icc
        have hxR : x ∈ tsupport Rg := subset_tsupport Rg hx
        have hxL : x ∈ tsupport (dfiMellinLogOperator 1 (deriv g)) := by
          rw [show Rg = dfiMellinLogOperator 1 (deriv g) from
            hg.besselShift_two_eq] at hxR
          exact hxR
        exact tsupport_deriv_subset
          (tsupport_dfiMellinLogOperator_subset 1 (deriv g) hxL)
      have hSS : S ≤ 2 * S := by linarith
      let hRgS : DFIVoronoiTestFunction Rg := {
        lower := S
        upper := 2 * S
        lower_pos := hS
        lower_le_upper := hSS
        smooth := hRg.smooth
        support_subset := hRgSupport }
      let A' : ℝ := A * (D * S * B ^ 2)
      have hFactor : 0 ≤ D * S * B ^ 2 := by
        have hD0 : 0 ≤ D := by
          exact le_trans (Nat.cast_nonneg _) hD
        positivity
      have hA' : 0 ≤ A' := mul_nonneg hA hFactor
      have hD' : (p + 2 * k + 3 : ℕ) ≤ D := by
        exact le_trans (by exact_mod_cast (show p + 2 * k + 3 ≤
          p + 2 * (k + 1) + 3 by omega)) hD
      have hRgDeriv : ∀ r ≤ p + 2 * k, ∀ x : ℝ,
          ‖iteratedDeriv r Rg x‖ ≤ A' * B ^ r := by
        intro r hr x
        by_cases hx : x ∈ Set.Icc S (2 * S)
        · have hsource : ∀ s ≤ r + 2,
              ‖iteratedDeriv s g x‖ ≤ A * B ^ s := by
            intro s hs
            apply hDeriv s
            omega
          have hone := hg.norm_iteratedDeriv_besselShift_two_le
            hA hB hS hSB r x hx hsource
          have hrD : (r : ℝ) + 3 ≤ D := by
            have hrNat : r + 3 ≤ p + 2 * (k + 1) + 3 := by omega
            exact le_trans (by exact_mod_cast hrNat) hD
          calc
            ‖iteratedDeriv r Rg x‖ ≤
                A * (((r : ℝ) + 3) * S * B ^ 2) * B ^ r := hone
            _ ≤ A * (D * S * B ^ 2) * B ^ r := by gcongr
            _ = A' * B ^ r := rfl
        · have hxzero : iteratedDeriv r Rg x = 0 :=
            hRgS.iteratedDeriv_eq_zero_of_not_mem r (by simpa [hRgS] using hx)
          rw [hxzero, norm_zero]
          exact mul_nonneg hA' (pow_nonneg hB r)
      intro j hj x hx
      rw [dfiEquation29BesselRecurrenceIterate_succ]
      have hout := ih hRgS hA' hRgSupport p hD' hRgDeriv j hj x hx
      calc
        ‖iteratedDeriv j
            (dfiEquation29BesselRecurrenceIterate k Rg) x‖ ≤
            A' * (D * S * B ^ 2) ^ k * B ^ j := hout
        _ = A * (D * S * B ^ 2) ^ (k + 1) * B ^ j := by
          dsimp [A']
          rw [pow_succ]
          ring

/-- Exact Mellin symbol of the iterated Bessel-shift weight on any vertical
line. -/
theorem DFIVoronoiTestFunction.mellin_besselShiftIterate_line
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (k : ℕ) (σ u : ℝ) :
    mellin (dfiEquation29BesselShiftIterate k g)
        ((σ : ℂ) + (u : ℂ) * I) =
      (1 - ((σ : ℂ) + (u : ℂ) * I)) ^ k *
        mellin (dfiVoronoiInvWeight g) ((σ : ℂ) + (u : ℂ) * I) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [dfiEquation29BesselShiftIterate_succ]
      rw [(hg.besselShiftIterate k).mellin_mellinLogOperator_line 1 σ u]
      rw [ih, pow_succ]
      push_cast
      ring

/-- The inverse weight translates the preceding identity back to the
original source Mellin transform. -/
theorem DFIVoronoiTestFunction.mellin_besselShiftIterate_line_eq_source
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (k : ℕ) (σ u : ℝ) :
    mellin (dfiEquation29BesselShiftIterate k g)
        ((σ : ℂ) + (u : ℂ) * I) =
      (1 - ((σ : ℂ) + (u : ℂ) * I)) ^ k *
        mellin g (((σ : ℂ) + (u : ℂ) * I) - 1) := by
  rw [hg.mellin_besselShiftIterate_line k σ u]
  have htranslate := hg.mellin_invWeight_add_one
    (((σ : ℂ) + (u : ℂ) * I) - 1)
  rw [show (((σ : ℂ) + (u : ℂ) * I) - 1) + 1 =
    ((σ : ℂ) + (u : ℂ) * I) by ring] at htranslate
  rw [htranslate]

/-- Sign acquired by a Voronoi branch under one Bessel recurrence. -/
def dfiEquation29BranchShiftSign : DFIVoronoiDualBranch → ℂ
  | .minusTerm => -1
  | .plusTerm => 1

/-- The branch sign has unit norm, so the exact recurrence multiplier has
the same positive real size in both Voronoi branches. -/
theorem norm_dfiEquation29BranchShiftMultiplier
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) (n : ℕ) :
    ‖dfiEquation29BranchShiftSign branch *
        ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)‖ =
      ((q : ℝ) / (2 * Real.pi)) ^ 2 / (n : ℝ) := by
  cases branch <;>
    simp [dfiEquation29BranchShiftSign,
      Real.norm_of_nonneg Real.pi_pos.le]

/-- Uniform form of the two exact multiplier recurrences. -/
theorem dfiEquation29Multiplier_sub_one
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (z : ℂ) (hz : z ≠ 1) :
    dfiEquation29Multiplier q branch (z - 1) =
      dfiEquation29BranchShiftSign branch *
        ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 * (1 - z) ^ 2 *
          dfiEquation29Multiplier q branch z := by
  cases branch
  · simp only [dfiEquation29Multiplier, dfiEquation29BranchShiftSign]
    rw [dfiVoronoiMinusMultiplier_sub_one q z hz]
    ring
  · simp only [dfiEquation29Multiplier, dfiEquation29BranchShiftSign, one_mul]
    exact dfiVoronoiPlusMultiplier_sub_one q z hz

/-- Pointwise recurrence for the complete equation-(29) Mellin integrand.
The physical Euler weight absorbs the entire `(1-z)^2` factor, and the
remaining scalar is exactly `±q²/(4π²n)`. -/
theorem DFIVoronoiTestFunction.dfiEquation29Integrand_sub_one
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (σ u : ℝ) (hσ : σ < 1) :
    dfiEquation29Integrand q branch g n
        (((σ - 1 : ℝ) : ℂ) + (u : ℂ) * I) =
      (dfiEquation29BranchShiftSign branch *
          ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)) *
        dfiEquation29Integrand q branch
          (dfiEquation29BesselShiftIterate 2 g) n
          ((σ : ℂ) + (u : ℂ) * I) := by
  let z : ℂ := (σ : ℂ) + (u : ℂ) * I
  have hz : z ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [z] at hre
    linarith
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hline : (((σ - 1 : ℝ) : ℂ) + (u : ℂ) * I) = z - 1 := by
    simp only [z]
    push_cast
    ring
  have hpow : (n : ℂ) ^ (-(1 - (z - 1))) =
      (n : ℂ)⁻¹ * (n : ℂ) ^ (-(1 - z)) := by
    rw [show -(1 - (z - 1)) = (-1 : ℂ) + (-(1 - z)) by ring]
    rw [Complex.cpow_add _ _ hnC, Complex.cpow_neg_one]
  have hmult := dfiEquation29Multiplier_sub_one q branch z hz
  have hmellin := hg.mellin_besselShiftIterate_line_eq_source 2 σ u
  rw [hline]
  unfold dfiEquation29Integrand
  rw [hpow, hmult]
  change _ = _ *
    ((n : ℂ) ^ (-(1 - z)) * dfiEquation29Multiplier q branch z *
      mellin (dfiEquation29BesselShiftIterate 2 g) z)
  rw [hmellin]
  simp only [pow_two]
  field_simp
  ring

/-- Translating a vertical integrand and its line by one leaves the complete
vertical integral unchanged. -/
theorem verticalIntegral'_translate_one (f : ℂ → ℂ) (σ : ℝ) :
    VerticalIntegral' (fun z => f (z + 1)) (σ - 1) =
      VerticalIntegral' f σ := by
  unfold VerticalIntegral' VerticalIntegral
  congr 2
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  congr 1
  push_cast
  ring

/-- Exact source-faithful one-step Bessel/Voronoi recurrence for the full
equation-(29) transform. -/
theorem DFIVoronoiTestFunction.dfiEquation29TransformAt_sub_one_besselShift
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (σ : ℝ) (hσ : σ < 1) :
    dfiEquation29TransformAt q branch g n (σ - 1) =
      (dfiEquation29BranchShiftSign branch *
          ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)) *
        dfiEquation29TransformAt q branch
          (dfiEquation29BesselShiftIterate 2 g) n σ := by
  let c : ℂ := dfiEquation29BranchShiftSign branch *
    ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)
  let F : ℂ → ℂ := dfiEquation29Integrand q branch
    (dfiEquation29BesselShiftIterate 2 g) n
  unfold dfiEquation29TransformAt
  calc
    VerticalIntegral' (dfiEquation29Integrand q branch g n) (σ - 1) =
        VerticalIntegral' (fun z => c * F (z + 1)) (σ - 1) := by
      apply verticalIntegral'_congr_line
      intro u
      dsimp [c, F]
      rw [hg.dfiEquation29Integrand_sub_one q branch hn σ u hσ]
      congr 2
      push_cast
      ring
    _ = c * VerticalIntegral' (fun z => F (z + 1)) (σ - 1) :=
      verticalIntegral'_const_mul_bridge c _ _
    _ = c * VerticalIntegral' F σ := by rw [verticalIntegral'_translate_one]
    _ = _ := rfl

/-- The complete recurrence preserves the source test class at every
iteration. -/
noncomputable def DFIVoronoiTestFunction.besselRecurrenceIterate
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (k : ℕ) :
    DFIVoronoiTestFunction (dfiEquation29BesselRecurrenceIterate k g) := by
  induction k generalizing g with
  | zero => simpa using hg
  | succ k ih =>
      simpa [dfiEquation29BesselRecurrenceIterate] using
        ih (hg.besselShiftIterate 2)

/-- Exact `k`-step Bessel/Voronoi recurrence.  This is the source-faithful
replacement for estimating a contour shifted `k` units left with a generic
high-derivative Mellin bound. -/
theorem DFIVoronoiTestFunction.dfiEquation29TransformAt_sub_nat_besselRecurrence
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (k : ℕ) (σ : ℝ) (hσ : σ < 1) :
    dfiEquation29TransformAt q branch g n (σ - k) =
      (dfiEquation29BranchShiftSign branch *
          ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)) ^ k *
        dfiEquation29TransformAt q branch
          (dfiEquation29BesselRecurrenceIterate k g) n σ := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
      let c : ℂ := dfiEquation29BranchShiftSign branch *
        ((q : ℂ) / (2 * Real.pi : ℂ)) ^ 2 / (n : ℂ)
      have hσk : σ - k < 1 := by
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      rw [show σ - (↑(Nat.succ k) : ℝ) = (σ - (k : ℝ)) - 1 by
        push_cast
        ring]
      rw [hg.dfiEquation29TransformAt_sub_one_besselShift
        q branch hn (σ - k) hσk]
      rw [ih (hg.besselShiftIterate 2)]
      rw [dfiEquation29BesselRecurrenceIterate_succ, pow_succ]
      dsimp [c]
      ring

theorem dfiEquation29TransformAt_initial (q : ℕ) [NeZero q]
    (branch : DFIVoronoiDualBranch) (g : ℝ → ℂ) (n : ℕ) :
    dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) =
      dfiEquation29InitialTransform q branch g n := by
  cases branch <;>
    unfold dfiEquation29TransformAt dfiEquation29InitialTransform
      dfiVoronoiMinusTransform dfiVoronoiPlusTransform <;>
    apply congrArg (fun f : ℂ → ℂ => VerticalIntegral' f (-(1 / 2 : ℝ))) <;>
    funext z <;>
    unfold dfiEquation29Integrand dfiEquation29Multiplier <;>
    rw [show -(1 - z) = z - 1 by ring]

/-- Exact extraction of the modulus scale from the DFI archimedean factor. -/
theorem dfiPeriodicArchimedeanFactor_eq_modulus_cpow_mul_one
    (q : ℕ) [NeZero q] (s : ℂ) :
    dfiPeriodicArchimedeanFactor q s =
      (q : ℂ) ^ (s - 1) * dfiPeriodicArchimedeanFactor 1 s := by
  unfold dfiPeriodicArchimedeanFactor
  simp only [Nat.cast_one, one_cpow, one_mul]
  ring

/-- The full modulus dependence of either DFI dual multiplier is the single
power `q^(1-2z)`.  This identity is what makes the frequency scale in (29)
quantitative rather than hidden in an existential contour constant. -/
theorem dfiEquation29Multiplier_eq_modulus_cpow_mul_one
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) (z : ℂ) :
    dfiEquation29Multiplier q branch z =
      (q : ℂ) ^ (1 - 2 * z) * dfiEquation29Multiplier 1 branch z := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow : (q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2 =
      (q : ℂ) ^ (1 - 2 * z) := by
    calc
      (q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2 =
          (q : ℂ) ^ (1 : ℂ) * (q : ℂ) ^ (-z + -z) := by
            rw [pow_two, Complex.cpow_add _ _ hq0]
            simp
      _ = (q : ℂ) ^ ((1 : ℂ) + (-z + -z)) := by
            exact (Complex.cpow_add (1 : ℂ) (-z + -z) hq0).symm
      _ = (q : ℂ) ^ (1 - 2 * z) := by
            congr 1
            ring
  cases branch
  · simp only [dfiEquation29Multiplier, dfiVoronoiMinusMultiplier]
    rw [dfiPeriodicArchimedeanFactor_eq_modulus_cpow_mul_one]
    simp only [Nat.cast_one, one_mul]
    rw [show (1 - z - 1 : ℂ) = -z by ring]
    rw [show
      ((q : ℂ) ^ (-z) * dfiPeriodicArchimedeanFactor 1 (1 - z)) ^ 2 =
        ((q : ℂ) ^ (-z)) ^ 2 *
          dfiPeriodicArchimedeanFactor 1 (1 - z) ^ 2 by ring]
    rw [← hpow]
    ring

  · simp only [dfiEquation29Multiplier, dfiVoronoiPlusMultiplier]
    rw [dfiPeriodicArchimedeanFactor_eq_modulus_cpow_mul_one]
    simp only [Nat.cast_one]
    rw [show (1 - z - 1 : ℂ) = -z by ring]
    rw [show
      ((q : ℂ) ^ (-z) * dfiPeriodicArchimedeanFactor 1 (1 - z)) ^ 2 =
        ((q : ℂ) ^ (-z)) ^ 2 *
          dfiPeriodicArchimedeanFactor 1 (1 - z) ^ 2 by ring]
    rw [← hpow]
    ring

/-- Exact norm of the positive-sign (`K₀`) Voronoi multiplier on DFI's
retained line.  In particular, its entire vertical dependence is the
integrable square of `Γ(1/4-iu)`. -/
theorem norm_dfiEquation29_plusMultiplier_one_threeQuarter (u : ℝ) :
    ‖dfiEquation29Multiplier 1 .plusTerm
        ((3 / 4 : ℂ) + (u : ℂ) * I)‖ =
      2 * (2 * Real.pi : ℝ) ^ (-(1 / 2 : ℝ)) *
        ‖Complex.Gamma ((1 / 4 : ℂ) - (u : ℂ) * I)‖ ^ 2 := by
  unfold dfiEquation29Multiplier dfiVoronoiPlusMultiplier
    dfiPeriodicArchimedeanFactor
  simp only [Nat.cast_one, one_mul, one_cpow, norm_mul, norm_pow,
    Complex.norm_ofNat, norm_one]
  have hbase : (0 : ℝ) < 2 * Real.pi := by positivity
  have hbaseC : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hbaseC, Complex.norm_cpow_eq_rpow_re_of_pos hbase]
  have hre : (-(1 - ((3 / 4 : ℂ) + (u : ℂ) * I))).re =
      -(1 / 4 : ℝ) := by
    norm_num
  rw [hre]
  have hGammaArg : 1 - ((3 / 4 : ℂ) + (u : ℂ) * I) =
      (1 / 4 : ℂ) - (u : ℂ) * I := by ring
  rw [hGammaArg, mul_pow]
  have hpow : ((2 * Real.pi : ℝ) ^ (-(1 / 4 : ℝ))) ^ 2 =
      (2 * Real.pi : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_mul_natCast hbase.le]
    norm_num
  rw [hpow]
  ring

/-- Exact modulus scaling of the preceding retained-line formula. -/
theorem norm_dfiEquation29_plusMultiplier_threeQuarter
    (q : ℕ) [NeZero q] (u : ℝ) :
    ‖dfiEquation29Multiplier q .plusTerm
        ((3 / 4 : ℂ) + (u : ℂ) * I)‖ =
      2 * (2 * Real.pi : ℝ) ^ (-(1 / 2 : ℝ)) *
        (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        ‖Complex.Gamma ((1 / 4 : ℂ) - (u : ℂ) * I)‖ ^ 2 := by
  rw [dfiEquation29Multiplier_eq_modulus_cpow_mul_one]
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
  have hre : (1 - 2 * ((3 / 4 : ℂ) + (u : ℂ) * I)).re =
      -(1 / 2 : ℝ) := by norm_num
  rw [hre, norm_dfiEquation29_plusMultiplier_one_threeQuarter]
  ring

/-- Physical `x^{-1/4}` mass paired with the retained Mellin line. -/
noncomputable def dfiMellinQuarterNorm (g : ℝ → ℂ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), ‖g x‖ / x ^ (1 / 4 : ℝ)

/-- The Mellin transform on `Re z=3/4` is bounded by the literal physical
quarter-weighted mass, uniformly in the vertical frequency. -/
theorem norm_mellin_threeQuarter_le_dfiMellinQuarterNorm
    (g : ℝ → ℂ)
    (hMajor : IntegrableOn
      (fun x : ℝ => ‖g x‖ / x ^ (1 / 4 : ℝ)) (Set.Ioi 0))
    (u : ℝ) :
    ‖mellin g ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤
      dfiMellinQuarterNorm g := by
  unfold mellin dfiMellinQuarterNorm
  apply norm_integral_le_of_norm_le hMajor
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxPos : 0 < x := hx
  simp only [norm_smul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
  have hre : (((3 / 4 : ℂ) + (u : ℂ) * I) - 1).re =
      -(1 / 4 : ℝ) := by norm_num
  rw [hre, Real.rpow_neg hxPos.le]
  simp [div_eq_mul_inv, mul_comm]

/-- Source-strength pointwise domination of the positive-sign retained
Mellin integrand.  Unlike the generic contour bound, this consumes no
derivative seminorm of the physical weight. -/
theorem norm_dfiEquation29_plusIntegrand_threeQuarter_le
    (q n : ℕ) [NeZero q] (hn : 0 < n) (g : ℝ → ℂ) (B : ℝ)
    (hMellin : ∀ u : ℝ,
      ‖mellin g ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ B)
    (u : ℝ) :
    ‖dfiEquation29Integrand q .plusTerm g n
        ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤
      (2 * (2 * Real.pi : ℝ) ^ (-(1 / 2 : ℝ))) *
        (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        (n : ℝ) ^ (-(1 / 4 : ℝ)) * B *
        ‖Complex.Gamma ((1 / 4 : ℂ) - (u : ℂ) * I)‖ ^ 2 := by
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((3 / 4 : ℂ) + (u : ℂ) * I)))‖ =
        (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    norm_num
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul, hPower,
    norm_dfiEquation29_plusMultiplier_threeQuarter]
  calc
    (n : ℝ) ^ (-(1 / 4 : ℝ)) *
          (2 * (2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
            (q : ℝ) ^ (-(1 / 2 : ℝ)) *
            ‖Gamma (1 / 4 - (u : ℂ) * I)‖ ^ 2) *
          ‖mellin g (3 / 4 + (u : ℂ) * I)‖ ≤
        (n : ℝ) ^ (-(1 / 4 : ℝ)) *
          (2 * (2 * Real.pi) ^ (-(1 / 2 : ℝ)) *
            (q : ℝ) ^ (-(1 / 2 : ℝ)) *
            ‖Gamma (1 / 4 - (u : ℂ) * I)‖ ^ 2) * B := by
      exact mul_le_mul_of_nonneg_left (hMellin u)
        (mul_nonneg
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          (by positivity))
    _ = _ := by ring

/-- The normalization of a complete vertical contour contributes only the
explicit factor `‖1/(2πi)‖‖i‖`. -/
theorem norm_VerticalIntegral'_le_integral_norm
    (f : ℂ → ℂ) (σ : ℝ) :
    ‖VerticalIntegral' f σ‖ ≤
      ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖I‖ *
        ∫ u : ℝ, ‖f ((σ : ℂ) + (u : ℂ) * I)‖ := by
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul, norm_mul]
  have hNorm :
      ‖∫ u : ℝ, f ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        ∫ u : ℝ, ‖f ((σ : ℂ) + (u : ℂ) * I)‖ := by
    exact MeasureTheory.norm_integral_le_integral_norm
      (fun u : ℝ => f ((σ : ℂ) + (u : ℂ) * I))
  have hNonneg : 0 ≤ ‖(1 / (2 * Real.pi * I) : ℂ)‖ * ‖(I : ℂ)‖ := by
    positivity
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left hNorm hNonneg

/-- The Gamma-square weight occurring on the positive-sign retained line is
integrable with the sign convention used by equation (29). -/
theorem integrable_sq_norm_Gamma_quarter_minus :
    Integrable (fun u : ℝ =>
      ‖Complex.Gamma ((1 / 4 : ℂ) - (u : ℂ) * I)‖ ^ 2) := by
  have hPlus := integrable_sq_norm_appendixC_Gamma_horizontal
    (a := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  have hNeg := hPlus.comp_neg
  convert hNeg using 1
  funext u
  congr 3
  push_cast
  ring

/-- Absolute Gamma mass of DFI's positive-sign retained Mellin kernel. -/
noncomputable def dfiGammaQuarterSquareMass : ℝ :=
  ∫ u : ℝ, ‖Complex.Gamma ((1 / 4 : ℂ) - (u : ℂ) * I)‖ ^ 2

theorem dfiGammaQuarterSquareMass_nonneg :
    0 ≤ dfiGammaQuarterSquareMass := by
  unfold dfiGammaQuarterSquareMass
  exact integral_nonneg fun _ => sq_nonneg _

theorem differentiableAt_dfiEquation29Multiplier_of_re_lt_one
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {z : ℂ} (hz : z.re < 1) :
    DifferentiableAt ℂ (dfiEquation29Multiplier q branch) z := by
  cases branch
  · exact differentiableAt_dfiVoronoiMinusMultiplier_of_re_lt_one q hz
  · exact differentiableAt_dfiVoronoiPlusMultiplier_of_re_lt_one q hz

theorem DFIVoronoiTestFunction.differentiableAt_dfiEquation29Integrand
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) {z : ℂ} (hz : z.re < 1) :
    DifferentiableAt ℂ (dfiEquation29Integrand q branch g n) z := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hExponent : DifferentiableAt ℂ (fun w : ℂ => -(1 - w)) z := by fun_prop
  have hPower : DifferentiableAt ℂ (fun w : ℂ => (n : ℂ) ^ (-(1 - w))) z :=
    hExponent.const_cpow (Or.inl hn0)
  exact (hPower.mul
    (differentiableAt_dfiEquation29Multiplier_of_re_lt_one q branch hz)).mul
      (hg.differentiable_mellin z)

theorem dfiEquation29Multiplier_shifted_strip_bound
    (q k : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) - k ≤ σ → σ ≤ -(1 / 2 : ℝ) → ∀ u : ℝ,
      ‖dfiEquation29Multiplier q branch
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        C * (1 + |u|) ^ (2 * (k + 1)) := by
  obtain ⟨C, hC, hBoth⟩ :=
    exists_norm_dfiVoronoiMultipliers_shifted_strip_bound q k
  refine ⟨C, hC, ?_⟩
  intro σ hσLower hσUpper u
  cases branch
  · exact (hBoth σ hσLower (by linarith [hσUpper]) u).1
  · exact (hBoth σ hσLower (by linarith [hσUpper]) u).2

/-- Multiplier control on the right-shift strip `-1/2 ≤ Re z ≤ 1/2`. -/
theorem dfiEquation29Multiplier_half_strip_bound
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 1 / 2 → ∀ u : ℝ,
      ‖dfiEquation29Multiplier q branch
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C * (1 + |u|) ^ 2 := by
  obtain ⟨C, hC, hBoth⟩ :=
    exists_norm_dfiVoronoiMultipliers_three_quarter_strip_bound q
  refine ⟨C, hC, ?_⟩
  intro σ hσLower hσUpper u
  cases branch
  · exact (hBoth σ hσLower (by linarith [hσUpper]) u).1
  · exact (hBoth σ hσLower (by linarith [hσUpper]) u).2

/-- Multiplier control on the full source strip
`-1/2 ≤ Re z ≤ 3/4`. -/
theorem dfiEquation29Multiplier_threeQuarter_strip_bound
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 3 / 4 → ∀ u : ℝ,
      ‖dfiEquation29Multiplier q branch
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C * (1 + |u|) ^ 2 := by
  obtain ⟨C, hC, hBoth⟩ :=
    exists_norm_dfiVoronoiMultipliers_three_quarter_strip_bound q
  refine ⟨C, hC, ?_⟩
  intro σ hσLower hσUpper u
  cases branch
  · exact (hBoth σ hσLower (by linarith) u).1
  · exact (hBoth σ hσLower (by linarith) u).2

/-- Multiplier control on the interior physical strip
`-1/2 ≤ Re z ≤ 13/16`. -/
theorem dfiEquation29Multiplier_thirteenSixteenths_strip_bound
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 13 / 16 → ∀ u : ℝ,
      ‖dfiEquation29Multiplier q branch
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C * (1 + |u|) ^ 2 := by
  obtain ⟨C, hC, hBoth⟩ :=
    exists_norm_dfiVoronoiMultipliers_three_quarter_strip_bound q
  refine ⟨C, hC, ?_⟩
  intro σ hσLower hσUpper u
  cases branch
  · exact (hBoth σ hσLower hσUpper u).1
  · exact (hBoth σ hσLower hσUpper u).2

/-- On the retained-frequency line `Re z = 1/2`, the exact modulus factor
`q^(1-2z)` has norm one.  Hence the multiplier bound is uniform in `q`. -/
theorem exists_dfiEquation29Multiplier_half_line_uniform_bound
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_hq : NeZero q) (u : ℝ),
      ‖dfiEquation29Multiplier q branch
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ C * (1 + |u|) ^ 2 := by
  obtain ⟨C, hC, hOne⟩ :=
    dfiEquation29Multiplier_half_strip_bound 1 branch
  refine ⟨C, hC, ?_⟩
  intro q hq u
  letI : NeZero q := hq
  have hqPos : 0 < q := NeZero.pos q
  rw [dfiEquation29Multiplier_eq_modulus_cpow_mul_one, norm_mul,
    Complex.norm_natCast_cpow_of_pos hqPos]
  have hRe :
      (1 - 2 * ((1 / 2 : ℂ) + (u : ℂ) * I)).re = 0 := by simp
  rw [hRe, Real.rpow_zero, one_mul]
  simpa using hOne (1 / 2) (by norm_num) (by norm_num) u

/-- On DFI's retained-frequency line `Re z = 3/4`, the exact modulus
factor is `q^(-1/2)`.  The remaining archimedean factor is uniform in
the positive modulus. -/
theorem exists_dfiEquation29Multiplier_threeQuarter_line_uniform_bound
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_hq : NeZero q) (u : ℝ),
      ‖dfiEquation29Multiplier q branch
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤
        C * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + |u|) ^ 2 := by
  obtain ⟨C, hC, hOne⟩ :=
    dfiEquation29Multiplier_threeQuarter_strip_bound 1 branch
  refine ⟨C, hC, ?_⟩
  intro q hq u
  letI : NeZero q := hq
  have hqPos : 0 < q := NeZero.pos q
  rw [dfiEquation29Multiplier_eq_modulus_cpow_mul_one, norm_mul,
    Complex.norm_natCast_cpow_of_pos hqPos]
  have hRe :
      (1 - 2 * ((3 / 4 : ℂ) + (u : ℂ) * I)).re = -(1 / 2 : ℝ) := by
    norm_num
  rw [hRe]
  have hOne' :
      ‖dfiEquation29Multiplier 1 branch
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ C * (1 + |u|) ^ 2 := by
    simpa using hOne (3 / 4) (by norm_num) (by norm_num) u
  calc
    (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        ‖dfiEquation29Multiplier 1 branch
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤
      (q : ℝ) ^ (-(1 / 2 : ℝ)) * (C * (1 + |u|) ^ 2) :=
        mul_le_mul_of_nonneg_left
          hOne'
          (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    _ = C * (q : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + |u|) ^ 2 := by ring

/-- Uniform-in-the-modulus version of the shifted-strip multiplier bound.
The factor `q^(2+2k)` is the exact worst modulus power on the strip
`-1/2-k ≤ Re z ≤ -1/2`; unlike the earlier fixed-`q` estimate, its
constant is independent of `q`. -/
theorem exists_dfiEquation29Multiplier_explicit_modulus_bound
    (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (_hq : NeZero q) (σ : ℝ),
      -(1 / 2 : ℝ) - k ≤ σ → σ ≤ -(1 / 2 : ℝ) → ∀ u : ℝ,
      ‖dfiEquation29Multiplier q branch
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (1 + |u|) ^ (2 * (k + 1)) := by
  obtain ⟨C, hC, hOne⟩ :=
    dfiEquation29Multiplier_shifted_strip_bound 1 k branch
  refine ⟨C, hC, ?_⟩
  intro q hq σ hσLower hσUpper u
  letI : NeZero q := hq
  have hqPos : 0 < q := NeZero.pos q
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqPos
  have hExponent : 1 - 2 * σ ≤ 2 + 2 * (k : ℝ) := by linarith
  have hqPower : (q : ℝ) ^ (1 - 2 * σ) ≤
      (q : ℝ) ^ (2 + 2 * (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hqOne hExponent
  rw [dfiEquation29Multiplier_eq_modulus_cpow_mul_one, norm_mul,
    Complex.norm_natCast_cpow_of_pos hqPos]
  have hRealPart :
      (1 - 2 * ((σ : ℂ) + (u : ℂ) * I)).re = 1 - 2 * σ := by simp
  rw [hRealPart]
  calc
    (q : ℝ) ^ (1 - 2 * σ) *
        ‖dfiEquation29Multiplier 1 branch ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      (q : ℝ) ^ (1 - 2 * σ) *
        (C * (1 + |u|) ^ (2 * (k + 1))) :=
      mul_le_mul_of_nonneg_left (hOne σ hσLower hσUpper u)
        (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    _ ≤ (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
        (C * (1 + |u|) ^ (2 * (k + 1))) := by
      gcongr
    _ = C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
        (1 + |u|) ^ (2 * (k + 1)) := by ring

/-- Normalize a positive-half-line test function by its physical scale.
The resulting support endpoints are dimensionless. -/
noncomputable def DFIVoronoiTestFunction.scaleNormalize
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) :
    DFIVoronoiTestFunction (fun x ↦ g (S * x)) where
  lower := hg.lower / S
  upper := hg.upper / S
  lower_pos := div_pos hg.lower_pos hS
  lower_le_upper := (div_le_div_iff_of_pos_right hS).2 hg.lower_le_upper
  smooth := hg.smooth.comp (by fun_prop)
  support_subset := by
    intro x hx
    have hs := hg.support_subset hx
    constructor
    · exact (div_le_iff₀ hS).2 (by simpa [mul_comm] using hs.1)
    · exact (le_div_iff₀ hS).2 (by simpa [mul_comm] using hs.2)

/-- Exact Mellin scaling used to expose the physical support scale in DFI
(29).  No asymptotic constant is hidden in this identity. -/
theorem mellin_eq_scale_cpow_mul_normalized
    (g : ℝ → ℂ) (S : ℝ) (hS : 0 < S) (z : ℂ) :
    mellin g z = (S : ℂ) ^ z * mellin (fun x ↦ g (S * x)) z := by
  have hscale := mellin_comp_mul_left g z hS
  rw [hscale]
  simp only [smul_eq_mul]
  have hSC : (S : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  rw [← mul_assoc, ← Complex.cpow_add _ _ hSC]
  simp

/-- Elementary cancellation of a polynomial growth factor against four extra
powers of Mellin decay, in the integrable `1 / (1 + u²)` form. -/
theorem norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    {A B : ℝ} {p : ℕ} (hA : 0 ≤ A)
    {F G : ℂ} {u : ℝ}
    (hF : ‖F‖ ≤ A * (1 + |u|) ^ p)
    (hG : (1 + |u|) ^ (p + 4) * ‖G‖ ≤ B) :
    ‖F * G‖ ≤ A * B * (1 + u ^ 2)⁻¹ := by
  have hw : 0 < 1 + |u| := by positivity
  have hquad : 1 + u ^ 2 ≤ (1 + |u|) ^ 4 := by
    have huSq : |u| ^ 2 = u ^ 2 := sq_abs u
    nlinarith [abs_nonneg u, sq_nonneg (1 + |u|),
      mul_nonneg (sq_nonneg (1 + |u|)) (sq_nonneg (1 + |u|))]
  have hScale :
      (1 + u ^ 2) * (1 + |u|) ^ p ≤ (1 + |u|) ^ (p + 4) := by
    calc
      (1 + u ^ 2) * (1 + |u|) ^ p ≤
          (1 + |u|) ^ 4 * (1 + |u|) ^ p :=
        mul_le_mul_of_nonneg_right hquad (by positivity)
      _ = (1 + |u|) ^ (p + 4) := by rw [← pow_add]; ring_nf
  have hNormScaled : (1 + u ^ 2) * ‖F * G‖ ≤ A * B := by
    rw [norm_mul]
    calc
      (1 + u ^ 2) * (‖F‖ * ‖G‖) ≤
          (1 + u ^ 2) * (A * (1 + |u|) ^ p * ‖G‖) := by
        gcongr
      _ = A * (((1 + u ^ 2) * (1 + |u|) ^ p) * ‖G‖) := by ring
      _ ≤ A * ((1 + |u|) ^ (p + 4) * ‖G‖) := by gcongr
      _ ≤ A * B := mul_le_mul_of_nonneg_left hG hA
  rw [le_mul_inv_iff₀ (by positivity : 0 < 1 + u ^ 2)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hNormScaled

theorem DFIVoronoiTestFunction.integrable_dfiEquation29Integrand_vertical
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q k : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) {σ : ℝ}
    (hσLower : -(1 / 2 : ℝ) - k ≤ σ)
    (hσUpper : σ ≤ -(1 / 2 : ℝ)) :
    Integrable (fun u : ℝ => dfiEquation29Integrand q branch g n
      ((σ : ℂ) + (u : ℂ) * I)) := by
  let p : ℕ := 2 * (k + 1)
  obtain ⟨A, hA, hMultiplier⟩ :=
    dfiEquation29Multiplier_shifted_strip_bound q k branch
  obtain ⟨B, _, hMellin⟩ :=
    hg.exists_mellin_one_add_abs_pow_line_bound (p + 4) σ
  let D : ℝ := (n : ℝ) ^ (σ - 1)
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hMajor : Integrable (fun u : ℝ =>
      D * A * B * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using integrable_inv_one_add_sq.const_mul (D * A * B)
  have hCont : Continuous (fun u : ℝ => dfiEquation29Integrand q branch g n
      ((σ : ℂ) + (u : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro u
    let φ : ℝ → ℂ := fun v => (σ : ℂ) + (v : ℂ) * I
    have hφ : ContinuousAt φ u := by fun_prop
    have hout : ContinuousAt (dfiEquation29Integrand q branch g n) (φ u) :=
      (hg.differentiableAt_dfiEquation29Integrand q branch hn
        (by simp [φ]; linarith : (φ u).re < 1)).continuousAt
    exact hout.comp hφ
  apply hMajor.mono' hCont.aestronglyMeasurable
  filter_upwards with u
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ = D := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    simp
  have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    hA.le
    (hMultiplier σ hσLower hσUpper u)
    (hMellin u)
  rw [norm_mul] at hCore
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul, hPower]
  calc
    D * ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
      D * (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤
      D * (A * B * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hCore hD
    _ = D * A * B * (1 + u ^ 2)⁻¹ := by ring

theorem DFIVoronoiTestFunction.exists_dfiEquation29Integrand_step_strip_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q r : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) - (r + 1) ≤ σ →
      σ ≤ -(1 / 2 : ℝ) - r → ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        C * (1 + u ^ 2)⁻¹ := by
  let k : ℕ := r + 1
  let p : ℕ := 2 * (k + 1)
  obtain ⟨A, hA, hMultiplier⟩ :=
    dfiEquation29Multiplier_shifted_strip_bound q k branch
  obtain ⟨B, hB, hMellin⟩ :=
    hg.exists_mellin_one_add_abs_pow_shifted_strip_bound (p + 4) k
  refine ⟨A * B, mul_nonneg hA.le hB, ?_⟩
  intro σ hσLower hσUpper u
  have hσGlobalLower : -(1 / 2 : ℝ) - k ≤ σ := by simpa [k] using hσLower
  have hσGlobalUpper : σ ≤ -(1 / 2 : ℝ) := by
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hσMellinUpper : σ ≤ (3 / 2 : ℝ) - k := by
    dsimp [k]
    norm_num at hσUpper ⊢
    linarith
  have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    hA.le
    (hMultiplier σ hσGlobalLower hσGlobalUpper u)
    (hMellin σ hσGlobalLower hσMellinUpper u)
  rw [norm_mul] at hCore
  have hPowerEq :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ =
        (n : ℝ) ^ (σ - 1) := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    simp
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ ≤ 1 := by
    rw [hPowerEq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hnOne (by linarith)
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul]
  calc
    ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ *
        ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ *
        (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ 1 * (A * B * (1 + u ^ 2)⁻¹) :=
      mul_le_mul hPower hCore (by positivity) (by norm_num)
    _ = (A * B) * (1 + u ^ 2)⁻¹ := by ring

theorem DFIVoronoiTestFunction.tendsto_dfiEquation29_horizontal_zero
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q r : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in
        (-(1 / 2 : ℝ) - (r + 1))..(-(1 / 2 : ℝ) - r),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) ∧
    Tendsto (fun y : ℝ => ∫ x : ℝ in
        (-(1 / 2 : ℝ) - (r + 1))..(-(1 / 2 : ℝ) - r),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
  obtain ⟨C, _, hDecay⟩ :=
    hg.exists_dfiEquation29Integrand_step_strip_decay q r branch hn
  let left : ℝ := -(1 / 2 : ℝ) - (r + 1)
  let right : ℝ := -(1 / 2 : ℝ) - r
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  let envelope : ℝ → ℝ := fun y => C * (1 + y ^ 2)⁻¹
  have hDen : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by norm_num))
  have hEnv : Tendsto envelope atTop (𝓝 0) := by
    dsimp [envelope]
    simpa [div_eq_mul_inv] using tendsto_const_nhds.div_atTop hDen
  have hTop : Tendsto (fun y : ℝ => ∫ x : ℝ in left..right,
      f ((x : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards with y
      have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I))
        (C := envelope y) (fun x hx => by
          have hx' : x ∈ Set.uIcc left right := Set.uIoc_subset_uIcc hx
          have hleftRight : left ≤ right := by dsimp [left, right]; linarith
          rw [Set.uIcc_of_le hleftRight] at hx'
          have hxLower : -(1 / 2 : ℝ) - (r + 1) ≤ x := by
            simpa [left] using hx'.1
          have hxUpper : x ≤ -(1 / 2 : ℝ) - r := by
            simpa [right] using hx'.2
          simpa [f, envelope, left, right] using
            hDecay x hxLower hxUpper y)
      have hLength : |right - left| = 1 := by
        dsimp [left, right]
        norm_num
      simpa [hLength] using hInt
    · exact hEnv
  have hBottomTop : Tendsto (fun H : ℝ => ∫ x : ℝ in left..right,
      f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    · filter_upwards with H
      have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x : ℝ => f ((x : ℂ) + ((-H : ℝ) : ℂ) * I))
        (C := envelope H) (fun x hx => by
          have hx' : x ∈ Set.uIcc left right := Set.uIoc_subset_uIcc hx
          have hleftRight : left ≤ right := by dsimp [left, right]; linarith
          rw [Set.uIcc_of_le hleftRight] at hx'
          have hxLower : -(1 / 2 : ℝ) - (r + 1) ≤ x := by
            simpa [left] using hx'.1
          have hxUpper : x ≤ -(1 / 2 : ℝ) - r := by
            simpa [right] using hx'.2
          have h := hDecay x hxLower hxUpper (-H)
          simpa [f, envelope] using h)
      have hLength : |right - left| = 1 := by
        dsimp [left, right]
        norm_num
      simpa [hLength] using hInt
    · exact hEnv
  constructor
  · simpa [left, right, f] using hTop
  · have hComp := hBottomTop.comp tendsto_neg_atBot_atTop
    have hfun :
        ((fun H : ℝ => ∫ x : ℝ in left..right,
          f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) ∘ Neg.neg) =
        (fun y : ℝ => ∫ x : ℝ in left..right,
          f ((x : ℂ) + (y : ℂ) * I)) := by
      funext y
      simp
    rw [hfun] at hComp
    simpa [left, right, f] using hComp

/-- One source-faithful unit displacement of the Mellin contour in DFI (29).
There are no residues: all factors are holomorphic throughout the closed strip,
and the horizontal sides vanish by the preceding uniform strip estimate. -/
theorem DFIVoronoiTestFunction.dfiEquation29TransformAt_step
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q r : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    dfiEquation29TransformAt q branch g n
        (-(1 / 2 : ℝ) - (r + 1)) =
      dfiEquation29TransformAt q branch g n
        (-(1 / 2 : ℝ) - r) := by
  let left : ℝ := -(1 / 2 : ℝ) - (r + 1)
  let right : ℝ := -(1 / 2 : ℝ) - r
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  have hleftRight : left ≤ right := by
    dsimp [left, right]
    linarith
  have hHol : HolomorphicOn f ([[left, right]] ×ℂ (Set.univ : Set ℝ)) := by
    intro z hz
    have hzRe : z.re ≤ right := by
      have hz' := hz.1
      rw [Set.uIcc_of_le hleftRight] at hz'
      exact hz'.2
    dsimp [right] at hzRe
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hzOne : z.re < 1 := by linarith
    exact (hg.differentiableAt_dfiEquation29Integrand q branch hn hzOne).differentiableWithinAt
  obtain ⟨hTop, hBot⟩ := hg.tendsto_dfiEquation29_horizontal_zero q r branch hn
  have hLeft : Integrable (fun u : ℝ => f ((left : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_vertical q (r + 1) branch hn
    · simp [left]
    · dsimp [left]
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
  have hRight : Integrable (fun u : ℝ => f ((right : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_vertical q (r + 1) branch hn
    · have hrSucc : (r : ℝ) ≤ (r + 1 : ℕ) := by exact_mod_cast Nat.le_succ r
      dsimp [right]
      linarith
    · dsimp [right]
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      linarith
  have hVertical : VerticalIntegral f left = VerticalIntegral f right :=
    dfiEquation29_verticalIntegral_eq hHol
      (by simpa [left, right, f] using hBot)
      (by simpa [left, right, f] using hTop) hLeft hRight
  unfold dfiEquation29TransformAt VerticalIntegral'
  simpa [left, right, f] using congrArg
    (fun z : ℂ => (1 / (2 * Real.pi * I) : ℂ) * z) hVertical

/-- Iteration of the residue-free displacement.  This is the exact contour
identity used to obtain arbitrary power saving in the dual frequency. -/
theorem DFIVoronoiTestFunction.dfiEquation29TransformAt_shift
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q k : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) =
      dfiEquation29TransformAt q branch g n
        (-(1 / 2 : ℝ) - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) =
            dfiEquation29TransformAt q branch g n
              (-(1 / 2 : ℝ) - k) := ih
        _ = dfiEquation29TransformAt q branch g n
              (-(1 / 2 : ℝ) - (k + 1)) := by
          exact (hg.dfiEquation29TransformAt_step q k branch hn).symm
        _ = dfiEquation29TransformAt q branch g n
              (-(1 / 2 : ℝ) - (Nat.succ k)) := by simp

theorem DFIVoronoiTestFunction.integrable_dfiEquation29Integrand_right_vertical
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) {σ : ℝ}
    (hσLower : -(1 / 2 : ℝ) ≤ σ) (hσUpper : σ ≤ 13 / 16) :
    Integrable (fun u : ℝ => dfiEquation29Integrand q branch g n
      ((σ : ℂ) + (u : ℂ) * I)) := by
  obtain ⟨A, hA, hMultiplier⟩ :=
    dfiEquation29Multiplier_thirteenSixteenths_strip_bound q branch
  obtain ⟨B, _, hMellin⟩ :=
    hg.exists_mellin_one_add_abs_pow_line_bound 6 σ
  let D : ℝ := (n : ℝ) ^ (σ - 1)
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hMajor : Integrable (fun u : ℝ =>
      D * A * B * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using integrable_inv_one_add_sq.const_mul (D * A * B)
  have hCont : Continuous (fun u : ℝ => dfiEquation29Integrand q branch g n
      ((σ : ℂ) + (u : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro u
    let φ : ℝ → ℂ := fun v => (σ : ℂ) + (v : ℂ) * I
    exact (hg.differentiableAt_dfiEquation29Integrand q branch hn
      (by simp [φ]; linarith : (φ u).re < 1)).continuousAt.comp (by fun_prop)
  apply hMajor.mono' hCont.aestronglyMeasurable
  filter_upwards with u
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ = D := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    simp
  have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    hA.le (hMultiplier σ hσLower hσUpper u) (hMellin u)
  rw [norm_mul] at hCore
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul, hPower]
  calc
    D * ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
      D * (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ D * (A * B * (1 + u ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hCore hD
    _ = D * A * B * (1 + u ^ 2)⁻¹ := by ring

/-- Source-strength retained-line estimate for the positive-sign Voronoi
transform.  The physical weight enters only through its `x^{-1/4}` Mellin
mass; no derivative seminorm is introduced. -/
theorem DFIVoronoiTestFunction.norm_dfiEquation29PlusTransformAt_threeQuarter_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (hMajor : IntegrableOn
      (fun x : ℝ => ‖g x‖ / x ^ (1 / 4 : ℝ)) (Set.Ioi 0))
    (q : ℕ) [NeZero q] {n : ℕ} (hn : 0 < n) :
    ‖dfiEquation29TransformAt q .plusTerm g n (3 / 4 : ℝ)‖ ≤
      ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ((2 * (2 * Real.pi : ℝ) ^ (-(1 / 2 : ℝ))) *
          (q : ℝ) ^ (-(1 / 2 : ℝ)) *
          (n : ℝ) ^ (-(1 / 4 : ℝ)) * dfiMellinQuarterNorm g *
          dfiGammaQuarterSquareMass) := by
  let C : ℝ :=
    (2 * (2 * Real.pi : ℝ) ^ (-(1 / 2 : ℝ))) *
      (q : ℝ) ^ (-(1 / 2 : ℝ)) *
      (n : ℝ) ^ (-(1 / 4 : ℝ)) * dfiMellinQuarterNorm g
  have hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q .plusTerm g n
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤
        C * ‖Complex.Gamma ((1 / 4 : ℂ) - (u : ℂ) * I)‖ ^ 2 := by
    intro u
    simpa [C, mul_assoc] using
      norm_dfiEquation29_plusIntegrand_threeQuarter_le q n hn g
        (dfiMellinQuarterNorm g)
        (norm_mellin_threeQuarter_le_dfiMellinQuarterNorm g hMajor) u
  have hTargetInt : Integrable (fun u : ℝ =>
      ‖dfiEquation29Integrand q .plusTerm g n
        ((3 / 4 : ℂ) + (u : ℂ) * I)‖) := by
    have hInt := hg.integrable_dfiEquation29Integrand_right_vertical
      (σ := (3 / 4 : ℝ)) q .plusTerm hn (by norm_num) (by norm_num)
    simpa using hInt.norm
  have hMajorInt : Integrable (fun u : ℝ =>
      C * ‖Complex.Gamma ((1 / 4 : ℂ) - (u : ℂ) * I)‖ ^ 2) :=
    integrable_sq_norm_Gamma_quarter_minus.const_mul C
  have hIntegral :
      (∫ u : ℝ, ‖dfiEquation29Integrand q .plusTerm g n
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖) ≤
        C * dfiGammaQuarterSquareMass := by
    calc
      (∫ u : ℝ, ‖dfiEquation29Integrand q .plusTerm g n
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖) ≤
          ∫ u : ℝ, C *
            ‖Complex.Gamma ((1 / 4 : ℂ) - (u : ℂ) * I)‖ ^ 2 :=
        integral_mono hTargetInt hMajorInt hPoint
      _ = C * dfiGammaQuarterSquareMass := by
        rw [MeasureTheory.integral_const_mul]
        rfl
  calc
    ‖dfiEquation29TransformAt q .plusTerm g n (3 / 4 : ℝ)‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ∫ u : ℝ, ‖dfiEquation29Integrand q .plusTerm g n
            ((3 / 4 : ℂ) + (u : ℂ) * I)‖ := by
      unfold dfiEquation29TransformAt
      simpa using norm_verticalIntegral'_le_integral_norm
        (dfiEquation29Integrand q .plusTerm g n) (3 / 4 : ℝ)
    _ ≤ ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        (C * dfiGammaQuarterSquareMass) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg _)
    _ = _ := by simp only [C]

theorem DFIVoronoiTestFunction.exists_dfiEquation29Integrand_right_strip_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ),
      -(1 / 2 : ℝ) ≤ σ → σ ≤ 13 / 16 → ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ C * (1 + u ^ 2)⁻¹ := by
  obtain ⟨A, hA, hMultiplier⟩ :=
    dfiEquation29Multiplier_thirteenSixteenths_strip_bound q branch
  obtain ⟨B, hB, hMellin⟩ :=
    hg.exists_mellin_one_add_abs_pow_shifted_strip_bound 6 0
  refine ⟨A * B, mul_nonneg hA.le hB, ?_⟩
  intro σ hσLower hσUpper u
  have hσMellinUpper : σ ≤ (3 / 2 : ℝ) := by linarith
  have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    hA.le (hMultiplier σ hσLower hσUpper u)
      (hMellin σ (by simpa using hσLower) (by simpa using hσMellinUpper) u)
  rw [norm_mul] at hCore
  have hPowerEq :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ =
        (n : ℝ) ^ (σ - 1) := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    simp
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ ≤ 1 := by
    rw [hPowerEq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hnOne (by linarith)
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul]
  calc
    ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ *
        ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
      ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ *
        (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ 1 * (A * B * (1 + u ^ 2)⁻¹) :=
      mul_le_mul hPower hCore (by positivity) (by norm_num)
    _ = (A * B) * (1 + u ^ 2)⁻¹ := by ring

theorem DFIVoronoiTestFunction.tendsto_dfiEquation29_half_horizontal_zero
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) ∧
    Tendsto (fun y : ℝ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
  obtain ⟨C, _, hDecay⟩ :=
    hg.exists_dfiEquation29Integrand_right_strip_decay q branch hn
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  let envelope : ℝ → ℝ := fun y => C * (1 + y ^ 2)⁻¹
  have hDen : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by norm_num))
  have hEnv : Tendsto envelope atTop (𝓝 0) := by
    dsimp [envelope]
    simpa [div_eq_mul_inv] using tendsto_const_nhds.div_atTop hDen
  have boundIntegral : ∀ y : ℝ,
      ‖∫ x : ℝ in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          f ((x : ℂ) + (y : ℂ) * I)‖ ≤ envelope y := by
    intro y
    have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I))
      (C := envelope y) (fun x hx => by
        have hx' := Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] at hx'
        simpa [f, envelope] using hDecay x hx'.1 (by linarith [hx'.2]) y)
    norm_num at hInt ⊢
    simpa using hInt
  have hTop : Tendsto (fun y : ℝ => ∫ x : ℝ in
      (-(1 / 2 : ℝ))..(1 / 2 : ℝ), f ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall boundIntegral) hEnv
  have hBottomTop : Tendsto (fun H : ℝ => ∫ x : ℝ in
      (-(1 / 2 : ℝ))..(1 / 2 : ℝ), f ((x : ℂ) + ((-H : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun H => ?_) hEnv
    simpa [envelope] using boundIntegral (-H)
  constructor
  · simpa [f] using hTop
  · have hComp := hBottomTop.comp tendsto_neg_atBot_atTop
    simpa [f, Function.comp_def] using hComp

/-- The horizontal sides of the source rectangle from `Re z = -1/2` to
`Re z = 3/4` vanish. -/
theorem DFIVoronoiTestFunction.tendsto_dfiEquation29_threeQuarter_horizontal_zero
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(3 / 4 : ℝ),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) ∧
    Tendsto (fun y : ℝ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(3 / 4 : ℝ),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
  obtain ⟨C, _, hDecay⟩ :=
    hg.exists_dfiEquation29Integrand_right_strip_decay q branch hn
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  let envelope : ℝ → ℝ := fun y => (5 / 4 : ℝ) * C * (1 + y ^ 2)⁻¹
  have hDen : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by norm_num))
  have hEnv : Tendsto envelope atTop (𝓝 0) := by
    change Tendsto
      (fun y : ℝ => ((5 / 4 : ℝ) * C) * (1 + y ^ 2)⁻¹) atTop (𝓝 0)
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.div_atTop hDen :
        Tendsto (fun y : ℝ => ((5 / 4 : ℝ) * C) / (1 + y ^ 2)) atTop (𝓝 0))
  have boundIntegral : ∀ y : ℝ,
      ‖∫ x : ℝ in (-(1 / 2 : ℝ))..(3 / 4 : ℝ),
          f ((x : ℂ) + (y : ℂ) * I)‖ ≤ envelope y := by
    intro y
    have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I))
      (C := C * (1 + y ^ 2)⁻¹) (fun x hx => by
        have hx' := Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 3 / 4)] at hx'
        simpa [f] using hDecay x hx'.1 (by linarith [hx'.2]) y)
    norm_num at hInt ⊢
    convert hInt using 1
    dsimp [envelope]
    ring
  have hTop : Tendsto (fun y : ℝ => ∫ x : ℝ in
      (-(1 / 2 : ℝ))..(3 / 4 : ℝ), f ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall boundIntegral) hEnv
  have hBottomTop : Tendsto (fun H : ℝ => ∫ x : ℝ in
      (-(1 / 2 : ℝ))..(3 / 4 : ℝ),
        f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun H => ?_) hEnv
    simpa [envelope] using boundIntegral (-H)
  constructor
  · simpa [f] using hTop
  · have hComp := hBottomTop.comp tendsto_neg_atBot_atTop
    simpa [f, Function.comp_def] using hComp

/-- The horizontal sides of the physical-identification rectangle from
`Re z = -1/2` to the interior line `Re z = 13/16` vanish. -/
theorem DFIVoronoiTestFunction.tendsto_dfiEquation29_thirteenSixteenths_horizontal_zero
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun y : ℝ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(13 / 16 : ℝ),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atTop (nhds 0) ∧
    Tendsto (fun y : ℝ => ∫ x : ℝ in (-(1 / 2 : ℝ))..(13 / 16 : ℝ),
        dfiEquation29Integrand q branch g n ((x : ℂ) + (y : ℂ) * I))
      atBot (nhds 0) := by
  obtain ⟨C, _, hDecay⟩ :=
    hg.exists_dfiEquation29Integrand_right_strip_decay q branch hn
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  let envelope : ℝ → ℝ := fun y => (21 / 16 : ℝ) * C * (1 + y ^ 2)⁻¹
  have hDen : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_pow_atTop (by norm_num))
  have hEnv : Tendsto envelope atTop (nhds 0) := by
    change Tendsto
      (fun y : ℝ => ((21 / 16 : ℝ) * C) * (1 + y ^ 2)⁻¹) atTop (nhds 0)
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.div_atTop hDen :
        Tendsto (fun y : ℝ => ((21 / 16 : ℝ) * C) / (1 + y ^ 2))
          atTop (nhds 0))
  have boundIntegral : ∀ y : ℝ,
      ‖∫ x : ℝ in (-(1 / 2 : ℝ))..(13 / 16 : ℝ),
          f ((x : ℂ) + (y : ℂ) * I)‖ ≤ envelope y := by
    intro y
    have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I))
      (C := C * (1 + y ^ 2)⁻¹) (fun x hx => by
        have hx' := Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 13 / 16)] at hx'
        simpa [f] using hDecay x hx'.1 hx'.2 y)
    norm_num at hInt ⊢
    convert hInt using 1
    dsimp [envelope]
    ring
  have hTop : Tendsto (fun y : ℝ => ∫ x : ℝ in
      (-(1 / 2 : ℝ))..(13 / 16 : ℝ), f ((x : ℂ) + (y : ℂ) * I))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall boundIntegral) hEnv
  have hBottomTop : Tendsto (fun H : ℝ => ∫ x : ℝ in
      (-(1 / 2 : ℝ))..(13 / 16 : ℝ),
        f ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (Eventually.of_forall fun H => ?_) hEnv
    simpa [envelope] using boundIntegral (-H)
  constructor
  · simpa [f] using hTop
  · have hComp := hBottomTop.comp tendsto_neg_atBot_atTop
    simpa [f, Function.comp_def] using hComp

/-- Residue-free displacement from the initial Voronoi line to DFI's
retained-frequency line `Re z = 3/4`. -/
theorem DFIVoronoiTestFunction.dfiEquation29TransformAt_threeQuarter
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) =
      dfiEquation29TransformAt q branch g n (3 / 4 : ℝ) := by
  let left : ℝ := -(1 / 2 : ℝ)
  let right : ℝ := 3 / 4
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  have hHol : HolomorphicOn f ([[left, right]] ×ℂ (Set.univ : Set ℝ)) := by
    intro z hz
    have hzRe : z.re ≤ right := by
      have hz' := hz.1
      rw [Set.uIcc_of_le (by norm_num : left ≤ right)] at hz'
      exact hz'.2
    exact (hg.differentiableAt_dfiEquation29Integrand q branch hn
      (by dsimp [right] at hzRe; linarith)).differentiableWithinAt
  obtain ⟨hTop, hBot⟩ :=
    hg.tendsto_dfiEquation29_threeQuarter_horizontal_zero q branch hn
  have hLeft : Integrable (fun u : ℝ => f ((left : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_right_vertical q branch hn
    · simp [left]
    · norm_num [left]
  have hRight : Integrable (fun u : ℝ => f ((right : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_right_vertical q branch hn
    · norm_num [right]
    · norm_num [right]
  have hVertical : VerticalIntegral f left = VerticalIntegral f right :=
    dfiEquation29_verticalIntegral_eq hHol
      (by simpa [left, right, f] using hBot)
      (by simpa [left, right, f] using hTop) hLeft hRight
  unfold dfiEquation29TransformAt VerticalIntegral'
  simpa [left, right, f] using congrArg
    (fun z : ℂ => (1 / (2 * Real.pi * I) : ℂ) * z) hVertical

/-- Residue-free displacement from the initial Voronoi line to the interior
physical `Y₀` line `Re z = 13/16`. -/
theorem DFIVoronoiTestFunction.dfiEquation29TransformAt_thirteenSixteenths
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) =
      dfiEquation29TransformAt q branch g n (13 / 16 : ℝ) := by
  let left : ℝ := -(1 / 2 : ℝ)
  let right : ℝ := 13 / 16
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  have hHol : HolomorphicOn f ([[left, right]] ×ℂ (Set.univ : Set ℝ)) := by
    intro z hz
    have hzRe : z.re ≤ right := by
      have hz' := hz.1
      rw [Set.uIcc_of_le (by norm_num : left ≤ right)] at hz'
      exact hz'.2
    exact (hg.differentiableAt_dfiEquation29Integrand q branch hn
      (by dsimp [right] at hzRe; linarith)).differentiableWithinAt
  obtain ⟨hTop, hBot⟩ :=
    hg.tendsto_dfiEquation29_thirteenSixteenths_horizontal_zero q branch hn
  have hLeft : Integrable (fun u : ℝ => f ((left : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_right_vertical q branch hn
    · simp [left]
    · norm_num [left]
  have hRight : Integrable (fun u : ℝ => f ((right : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_right_vertical q branch hn
    · norm_num [right]
    · norm_num [right]
  have hVertical : VerticalIntegral f left = VerticalIntegral f right :=
    dfiEquation29_verticalIntegral_eq hHol
      (by simpa [left, right, f] using hBot)
      (by simpa [left, right, f] using hTop) hLeft hRight
  unfold dfiEquation29TransformAt VerticalIntegral'
  simpa [left, right, f] using congrArg
    (fun z : ℂ => (1 / (2 * Real.pi * I) : ℂ) * z) hVertical

/-- The equal-sign Mellin--Barnes transform in DFI Proposition 1 is the
literal Neumann-kernel transform, with all constants and scalings exact. -/
theorem DFIVoronoiTestFunction.dfiEquation29InitialMinusTransform_eq_bessel
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] {n : ℕ} (hn : 0 < n) :
    dfiEquation29InitialTransform q .minusTerm g n =
      dfiVoronoiMinusBesselTransform q g n := by
  calc
    dfiEquation29InitialTransform q .minusTerm g n =
        dfiEquation29TransformAt q .minusTerm g n (-(1 / 2 : ℝ)) :=
      (dfiEquation29TransformAt_initial q .minusTerm g n).symm
    _ = dfiEquation29TransformAt q .minusTerm g n (13 / 16 : ℝ) :=
      hg.dfiEquation29TransformAt_thirteenSixteenths q .minusTerm hn
    _ = dfiVoronoiMinusBesselTransform q g n := by
      unfold dfiEquation29TransformAt dfiEquation29Integrand
        dfiEquation29Multiplier
      exact verticalIntegral_dfiVoronoiMinus_mellin_thirteenSixteenths_eq_bessel
        q n hn hg

/-- Both signs of the source equation-(29) transform satisfy the literal
quarter-power Bessel estimate.  The common constant is deliberately the sum
of the two branch constants, so this statement can be consumed without a
case-dependent maximum. -/
theorem DFIVoronoiTestFunction.norm_dfiEquation29InitialTransform_le_besselQuarterNorm
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n)
    (hMajor : IntegrableOn
      (fun x : ℝ => ‖g x‖ / Real.sqrt (Real.sqrt (x * n))) (Set.Ioi 0)) :
    ‖dfiEquation29InitialTransform q branch g n‖ ≤
      (14 * Real.pi + 8) / Real.sqrt q * dfiBesselQuarterNorm g n := by
  have hNorm : 0 ≤ dfiBesselQuarterNorm g n := by
    unfold dfiBesselQuarterNorm
    exact MeasureTheory.integral_nonneg (fun _ => by positivity)
  cases branch with
  | minusTerm =>
      rw [hg.dfiEquation29InitialMinusTransform_eq_bessel q hn]
      refine (norm_dfiVoronoiMinusBesselTransform_le q g n hn hMajor).trans ?_
      gcongr
      nlinarith [Real.pi_pos]
  | plusTerm =>
      change ‖dfiVoronoiPlusTransform q (mellin g) n‖ ≤ _
      refine (norm_dfiVoronoiPlusTransform_mellin_le q n hn hg hMajor).trans ?_
      gcongr
      nlinarith [Real.pi_pos]

/-- Residue-free rightward displacement from the source line `Re z=-1/2`
to the retained-frequency line `Re z=1/2`. -/
theorem DFIVoronoiTestFunction.dfiEquation29TransformAt_half
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) :
    dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) =
      dfiEquation29TransformAt q branch g n (1 / 2 : ℝ) := by
  let left : ℝ := -(1 / 2 : ℝ)
  let right : ℝ := 1 / 2
  let f : ℂ → ℂ := dfiEquation29Integrand q branch g n
  have hHol : HolomorphicOn f ([[left, right]] ×ℂ (Set.univ : Set ℝ)) := by
    intro z hz
    have hzRe : z.re ≤ right := by
      have hz' := hz.1
      rw [Set.uIcc_of_le (by norm_num : left ≤ right)] at hz'
      exact hz'.2
    exact (hg.differentiableAt_dfiEquation29Integrand q branch hn
      (by dsimp [right] at hzRe; linarith)).differentiableWithinAt
  obtain ⟨hTop, hBot⟩ := hg.tendsto_dfiEquation29_half_horizontal_zero q branch hn
  have hLeft : Integrable (fun u : ℝ => f ((left : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_right_vertical q branch hn
    · simp [left]
    · norm_num [left]
  have hRight : Integrable (fun u : ℝ => f ((right : ℂ) + (u : ℂ) * I)) := by
    apply hg.integrable_dfiEquation29Integrand_right_vertical q branch hn
    · norm_num [right]
    · norm_num [right]
  have hVertical : VerticalIntegral f left = VerticalIntegral f right :=
    dfiEquation29_verticalIntegral_eq hHol
      (by simpa [left, right, f] using hBot)
      (by simpa [left, right, f] using hTop) hLeft hRight
  unfold dfiEquation29TransformAt VerticalIntegral'
  simpa [left, right, f] using congrArg
    (fun z : ℂ => (1 / (2 * Real.pi * I) : ℂ) * z) hVertical

theorem DFIVoronoiTestFunction.exists_mellin_scaled_half_line_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (S : ℝ) (hS : 0 < S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      (1 + |u|) ^ 6 * ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
        S ^ (1 / 2 : ℝ) * B := by
  let g₁ : ℝ → ℂ := fun x ↦ g (S * x)
  have hg₁ : DFIVoronoiTestFunction g₁ := by
    simpa [g₁] using hg.scaleNormalize S hS
  obtain ⟨B, hB, hMellin⟩ :=
    hg₁.exists_mellin_one_add_abs_pow_line_bound 6 (1 / 2)
  refine ⟨B, hB, ?_⟩
  intro u
  let R : ℝ := S ^ (1 / 2 : ℝ)
  have hR : 0 ≤ R := Real.rpow_nonneg hS.le _
  rw [mellin_eq_scale_cpow_mul_normalized g S hS, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hS]
  have hRe : (((1 / 2 : ℂ) + (u : ℂ) * I).re) = (1 / 2 : ℝ) := by simp
  rw [hRe]
  change (1 + |u|) ^ 6 *
      (R * ‖mellin g₁ ((1 / 2 : ℂ) + (u : ℂ) * I)‖) ≤ R * B
  calc
    (1 + |u|) ^ 6 *
        (R * ‖mellin g₁ ((1 / 2 : ℂ) + (u : ℂ) * I)‖) =
      R * ((1 + |u|) ^ 6 *
        ‖mellin g₁ ((1 / 2 : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ R * B := by
      have hm : (1 + |u|) ^ 6 *
          ‖mellin g₁ ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ B := by
        simpa using hMellin u
      exact mul_le_mul_of_nonneg_left hm hR

/-- Scaling of the Mellin transform on DFI's source line `Re z = 3/4`.
All dependence on the physical scale is the exact factor `S^(3/4)`. -/
theorem DFIVoronoiTestFunction.exists_mellin_scaled_threeQuarter_line_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (S : ℝ) (hS : 0 < S) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      (1 + |u|) ^ 6 * ‖mellin g ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤
        S ^ (3 / 4 : ℝ) * B := by
  let g₁ : ℝ → ℂ := fun x ↦ g (S * x)
  have hg₁ : DFIVoronoiTestFunction g₁ := by
    simpa [g₁] using hg.scaleNormalize S hS
  obtain ⟨B, hB, hMellin⟩ :=
    hg₁.exists_mellin_one_add_abs_pow_line_bound 6 (3 / 4)
  refine ⟨B, hB, ?_⟩
  intro u
  let R : ℝ := S ^ (3 / 4 : ℝ)
  have hR : 0 ≤ R := Real.rpow_nonneg hS.le _
  rw [mellin_eq_scale_cpow_mul_normalized g S hS, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hS]
  have hRe : (((3 / 4 : ℂ) + (u : ℂ) * I).re) = (3 / 4 : ℝ) := by
    norm_num
  rw [hRe]
  change (1 + |u|) ^ 6 *
      (R * ‖mellin g₁ ((3 / 4 : ℂ) + (u : ℂ) * I)‖) ≤ R * B
  calc
    (1 + |u|) ^ 6 *
        (R * ‖mellin g₁ ((3 / 4 : ℂ) + (u : ℂ) * I)‖) =
      R * ((1 + |u|) ^ 6 *
        ‖mellin g₁ ((3 / 4 : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ R * B := by
      have hm : (1 + |u|) ^ 6 *
          ‖mellin g₁ ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ B := by
        simpa using hMellin u
      exact mul_le_mul_of_nonneg_left hm hR

/-- Pointwise source-line estimate for the normalized DFI Voronoi transform.
The exact physical powers are exposed rather than absorbed into the constant. -/
theorem DFIVoronoiTestFunction.exists_dfiEquation29Integrand_scaled_threeQuarter_line_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n → ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤
        C * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
          (n : ℝ) ^ (-(1 / 4 : ℝ)) * (1 + u ^ 2)⁻¹ := by
  obtain ⟨A, hA, hMultiplier⟩ :=
    exists_dfiEquation29Multiplier_threeQuarter_line_uniform_bound branch
  obtain ⟨B, hB, hMellin⟩ :=
    hg.exists_mellin_scaled_threeQuarter_line_bound S hS
  refine ⟨A * B, mul_nonneg hA.le hB, ?_⟩
  intro q hq n hn u
  letI : NeZero q := hq
  have hqPow : 0 ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    (mul_nonneg hA.le hqPow) (hMultiplier q hq u) (hMellin u)
  rw [norm_mul] at hCore
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((3 / 4 : ℂ) + (u : ℂ) * I)))‖ =
        (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    norm_num
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul, hPower]
  calc
    (n : ℝ) ^ (-(1 / 4 : ℝ)) *
        ‖dfiEquation29Multiplier q branch ((3 / 4 : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((3 / 4 : ℂ) + (u : ℂ) * I)‖ =
      (n : ℝ) ^ (-(1 / 4 : ℝ)) *
        (‖dfiEquation29Multiplier q branch ((3 / 4 : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((3 / 4 : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) *
        ((A * (q : ℝ) ^ (-(1 / 2 : ℝ))) *
          (S ^ (3 / 4 : ℝ) * B) * (1 + u ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hCore
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (A * B) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
        (n : ℝ) ^ (-(1 / 4 : ℝ)) * (1 + u ^ 2)⁻¹ := by ring

theorem DFIVoronoiTestFunction.exists_dfiEquation29Integrand_scaled_half_line_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n → ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
        C * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (1 + u ^ 2)⁻¹ := by
  obtain ⟨A, hA, hMultiplier⟩ :=
    exists_dfiEquation29Multiplier_half_line_uniform_bound branch
  obtain ⟨B, hB, hMellin⟩ := hg.exists_mellin_scaled_half_line_bound S hS
  refine ⟨A * B, mul_nonneg hA.le hB, ?_⟩
  intro q hq n hn u
  letI : NeZero q := hq
  have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
    hA.le (hMultiplier q hq u) (hMellin u)
  rw [norm_mul] at hCore
  have hPower :
      ‖(n : ℂ) ^ (-(1 - ((1 / 2 : ℂ) + (u : ℂ) * I)))‖ =
        (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    congr 1
    norm_num
  unfold dfiEquation29Integrand
  rw [norm_mul, norm_mul, hPower]
  calc
    (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        ‖dfiEquation29Multiplier q branch ((1 / 2 : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        (‖dfiEquation29Multiplier q branch ((1 / 2 : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖) := by ring
    _ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        (A * (S ^ (1 / 2 : ℝ) * B) * (1 + u ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hCore
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (A * B) * S ^ (1 / 2 : ℝ) *
        (n : ℝ) ^ (-(1 / 2 : ℝ)) * (1 + u ^ 2)⁻¹ := by ring

theorem DFIVoronoiTestFunction.norm_dfiEquation29TransformAt_half_le_of_pointwise
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (D : ℝ)
    (hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ D * (1 + u ^ 2)⁻¹) :
    ‖dfiEquation29TransformAt q branch g n (1 / 2 : ℝ)‖ ≤
      ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D *
        (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
  have hTargetInt : Integrable (fun u : ℝ =>
      ‖dfiEquation29Integrand q branch g n
        ((1 / 2 : ℂ) + (u : ℂ) * I)‖) := by
    have hInt := hg.integrable_dfiEquation29Integrand_right_vertical
      (σ := (1 / 2 : ℝ)) q branch hn (by norm_num) (by norm_num)
    simpa using hInt.norm
  have hMajorInt : Integrable (fun u : ℝ => D * (1 + u ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul D
  have hIntegral :
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖) ≤
        D * (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
    calc
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖) ≤
          ∫ u : ℝ, D * (1 + u ^ 2)⁻¹ :=
        integral_mono hTargetInt hMajorInt hPoint
      _ = D * (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
        rw [MeasureTheory.integral_const_mul]
  calc
    ‖dfiEquation29TransformAt q branch g n (1 / 2 : ℝ)‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
            ((1 / 2 : ℂ) + (u : ℂ) * I)‖ :=
      by
        unfold dfiEquation29TransformAt
        simpa using norm_verticalIntegral'_le_integral_norm
          (dfiEquation29Integrand q branch g n) (1 / 2 : ℝ)
    _ ≤ ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        (D * (∫ u : ℝ, (1 + u ^ 2)⁻¹)) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg _)
    _ = ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D *
        (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by ring

/-- Integrate a pointwise majorant on DFI's retained line `Re z = 3/4`. -/
theorem DFIVoronoiTestFunction.norm_dfiEquation29TransformAt_threeQuarter_le_of_pointwise
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    {n : ℕ} (hn : 0 < n) (D : ℝ)
    (hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ D * (1 + u ^ 2)⁻¹) :
    ‖dfiEquation29TransformAt q branch g n (3 / 4 : ℝ)‖ ≤
      ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D *
        (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
  have hTargetInt : Integrable (fun u : ℝ =>
      ‖dfiEquation29Integrand q branch g n
        ((3 / 4 : ℂ) + (u : ℂ) * I)‖) := by
    have hInt := hg.integrable_dfiEquation29Integrand_right_vertical
      (σ := (3 / 4 : ℝ)) q branch hn (by norm_num) (by norm_num)
    simpa using hInt.norm
  have hMajorInt : Integrable (fun u : ℝ => D * (1 + u ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul D
  have hIntegral :
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖) ≤
        D * (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
    calc
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖) ≤
          ∫ u : ℝ, D * (1 + u ^ 2)⁻¹ :=
        integral_mono hTargetInt hMajorInt hPoint
      _ = D * (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by
        rw [MeasureTheory.integral_const_mul]
  calc
    ‖dfiEquation29TransformAt q branch g n (3 / 4 : ℝ)‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
            ((3 / 4 : ℂ) + (u : ℂ) * I)‖ := by
      unfold dfiEquation29TransformAt
      simpa using norm_verticalIntegral'_le_integral_norm
        (dfiEquation29Integrand q branch g n) (3 / 4 : ℝ)
    _ ≤ ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        (D * (∫ u : ℝ, (1 + u ^ 2)⁻¹)) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg _)
    _ = ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D *
        (∫ u : ℝ, (1 + u ^ 2)⁻¹) := by ring

/-- The original normalized Voronoi transform, estimated on DFI's
`Re z = 3/4` line.  The constant is independent of `q`, `S`, and `n`. -/
theorem DFIVoronoiTestFunction.exists_dfiEquation29InitialTransform_scaled_threeQuarter_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n →
      ‖dfiEquation29InitialTransform q branch g n‖ ≤
        C * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
          (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨A, hA, hPoint⟩ :=
    hg.exists_dfiEquation29Integrand_scaled_threeQuarter_line_bound S hS branch
  let J : ℝ := ∫ u : ℝ, (1 + u ^ 2)⁻¹
  let C : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖ * A * J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun u ↦ inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q hq n hn
  letI : NeZero q := hq
  let D : ℝ := A * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
    (n : ℝ) ^ (-(1 / 4 : ℝ))
  have hThreeQuarter :=
    hg.norm_dfiEquation29TransformAt_threeQuarter_le_of_pointwise
      q branch hn D (fun u => by simpa [D] using hPoint q hq n hn u)
  have hShift : dfiEquation29InitialTransform q branch g n =
      dfiEquation29TransformAt q branch g n (3 / 4 : ℝ) := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n (3 / 4 : ℝ) :=
        hg.dfiEquation29TransformAt_threeQuarter q branch hn
  rw [hShift]
  calc
    ‖dfiEquation29TransformAt q branch g n (3 / 4 : ℝ)‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D * J := by
      simpa [J] using hThreeQuarter
    _ = C * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
        (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      dsimp [C, D]
      ring

/-- Universal retained-frequency estimate on `Re z = 3/4`.  The constant is
chosen before the source test function; its entire source dependence is the
explicit Mellin bound `B`. -/
theorem exists_dfiEquation29InitialTransform_threeQuarter_constant
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : ℝ → ℂ}, DFIVoronoiTestFunction g →
      ∀ {B : ℝ}, (∀ u : ℝ,
        (1 + |u|) ^ 6 *
          ‖mellin g ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ B) →
      ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform q branch g n‖ ≤
          C * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B *
            (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨A, hA, hMultiplier⟩ :=
    exists_dfiEquation29Multiplier_threeQuarter_line_uniform_bound branch
  let J : ℝ := ∫ u : ℝ, (1 + u ^ 2)⁻¹
  let C : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖ * A * J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun u ↦ inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro g hg B hMellin q hq n hn
  letI : NeZero q := hq
  let D : ℝ := A * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B *
    (n : ℝ) ^ (-(1 / 4 : ℝ))
  have hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤ D * (1 + u ^ 2)⁻¹ := by
    intro u
    have hqPow : 0 ≤ (q : ℝ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg q) _
    have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
      (mul_nonneg hA.le hqPow) (hMultiplier q hq u) (hMellin u)
    rw [norm_mul] at hCore
    have hPower :
        ‖(n : ℂ) ^ (-(1 - ((3 / 4 : ℂ) + (u : ℂ) * I)))‖ =
          (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      congr 1
      norm_num
    unfold dfiEquation29Integrand
    rw [norm_mul, norm_mul, hPower]
    calc
      (n : ℝ) ^ (-(1 / 4 : ℝ)) *
          ‖dfiEquation29Multiplier q branch ((3 / 4 : ℂ) + (u : ℂ) * I)‖ *
            ‖mellin g ((3 / 4 : ℂ) + (u : ℂ) * I)‖ =
        (n : ℝ) ^ (-(1 / 4 : ℝ)) *
          (‖dfiEquation29Multiplier q branch ((3 / 4 : ℂ) + (u : ℂ) * I)‖ *
            ‖mellin g ((3 / 4 : ℂ) + (u : ℂ) * I)‖) := by ring
      _ ≤ (n : ℝ) ^ (-(1 / 4 : ℝ)) *
          ((A * (q : ℝ) ^ (-(1 / 2 : ℝ))) * B * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hCore
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = D * (1 + u ^ 2)⁻¹ := by
        dsimp [D]
        ring
  have hThreeQuarter :=
    hg.norm_dfiEquation29TransformAt_threeQuarter_le_of_pointwise
      q branch hn D hPoint
  have hShift : dfiEquation29InitialTransform q branch g n =
      dfiEquation29TransformAt q branch g n (3 / 4 : ℝ) := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n (3 / 4 : ℝ) :=
        hg.dfiEquation29TransformAt_threeQuarter q branch hn
  rw [hShift]
  calc
    ‖dfiEquation29TransformAt q branch g n (3 / 4 : ℝ)‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D * J := by
      simpa [J] using hThreeQuarter
    _ = C * (q : ℝ) ^ (-(1 / 2 : ℝ)) * B *
        (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      dsimp [C, D]
      ring

/-- Universal right-contour constant for Equation (29).  It is selected
before the test function and its Mellin bound, so later arithmetic slices
cannot alter it. -/
theorem exists_dfiEquation29InitialTransform_retained_constant
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : ℝ → ℂ}, DFIVoronoiTestFunction g →
      ∀ {B : ℝ}, (∀ u : ℝ,
        (1 + |u|) ^ 6 *
          ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ B) →
      ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform q branch g n‖ ≤
          C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨A, hA, hMultiplier⟩ :=
    exists_dfiEquation29Multiplier_half_line_uniform_bound branch
  let J : ℝ := ∫ u : ℝ, (1 + u ^ 2)⁻¹
  let C : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖ * A * J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun u ↦ inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro g hg B hMellin q hq n hn
  letI : NeZero q := hq
  let D : ℝ := A * B * (n : ℝ) ^ (-(1 / 2 : ℝ))
  have hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ D * (1 + u ^ 2)⁻¹ := by
    intro u
    have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
      hA.le (hMultiplier q hq u) (hMellin u)
    rw [norm_mul] at hCore
    have hPower :
        ‖(n : ℂ) ^ (-(1 - ((1 / 2 : ℂ) + (u : ℂ) * I)))‖ =
          (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      congr 1
      norm_num
    unfold dfiEquation29Integrand
    rw [norm_mul, norm_mul, hPower]
    calc
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          ‖dfiEquation29Multiplier q branch ((1 / 2 : ℂ) + (u : ℂ) * I)‖ *
            ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ =
        (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (‖dfiEquation29Multiplier q branch ((1 / 2 : ℂ) + (u : ℂ) * I)‖ *
            ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖) := by ring
      _ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          (A * B * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hCore
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = D * (1 + u ^ 2)⁻¹ := by
        dsimp [D]
        ring
  have hHalf := hg.norm_dfiEquation29TransformAt_half_le_of_pointwise
    q branch hn D hPoint
  have hShift : dfiEquation29InitialTransform q branch g n =
      dfiEquation29TransformAt q branch g n (1 / 2 : ℝ) := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n (1 / 2 : ℝ) :=
        hg.dfiEquation29TransformAt_half q branch hn
  rw [hShift]
  calc
    ‖dfiEquation29TransformAt q branch g n (1 / 2 : ℝ)‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D * J := by
      simpa [J] using hHalf
    _ = C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      dsimp [C, D]
      ring

/-- Right-contour estimate with an explicit Mellin-decay input.  The output
constant depends only on the fixed Voronoi branch and universal vertical
integral, while all source dependence remains visible in `B`. -/
theorem DFIVoronoiTestFunction.exists_dfiEquation29InitialTransform_retained_of_mellin_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (branch : DFIVoronoiDualBranch) {B : ℝ}
    (hMellin : ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q)
      (n : ℕ), 0 < n →
      ‖dfiEquation29InitialTransform q branch g n‖ ≤
        C * B * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hUniversal⟩ :=
    exists_dfiEquation29InitialTransform_retained_constant branch
  exact ⟨C, hC, hUniversal hg hMellin⟩

/-- Scale-uniform retained-frequency estimate obtained on `Re z = 1/2`.
The modulus disappears exactly on this line; the physical scale and dual
frequency contribute `S^(1/2)` and `n^(-1/2)`, respectively. -/
theorem DFIVoronoiTestFunction.exists_dfiEquation29InitialTransform_scaled_retained_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n →
      ‖dfiEquation29InitialTransform q branch g n‖ ≤
        C * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨A, hA, hPoint⟩ :=
    hg.exists_dfiEquation29Integrand_scaled_half_line_bound S hS branch
  let J : ℝ := ∫ u : ℝ, (1 + u ^ 2)⁻¹
  let C : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖ * A * J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun u ↦ inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q hq n hn
  letI : NeZero q := hq
  let D : ℝ := A * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))
  have hHalf := hg.norm_dfiEquation29TransformAt_half_le_of_pointwise
    q branch hn D (fun u => by simpa [D] using hPoint q hq n hn u)
  have hShift : dfiEquation29InitialTransform q branch g n =
      dfiEquation29TransformAt q branch g n (1 / 2 : ℝ) := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n (1 / 2 : ℝ) :=
        hg.dfiEquation29TransformAt_half q branch hn
  rw [hShift]
  calc
    ‖dfiEquation29TransformAt q branch g n (1 / 2 : ℝ)‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ * D * J := by
      simpa [J] using hHalf
    _ = C * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      dsimp [C, D]
      ring

/-- Arbitrary polynomial decay of either DFI dual transform.  The constant is
uniform in the positive dual frequency `n`; its dependence on the modulus,
branch, test function, and chosen decay order is explicit in the binders. -/
theorem DFIVoronoiTestFunction.exists_dfiEquation29InitialTransform_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (q k : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      ‖dfiEquation29InitialTransform q branch g n‖ ≤
        C * (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  let σ : ℝ := -(1 / 2 : ℝ) - k
  let p : ℕ := 2 * (k + 1)
  obtain ⟨A, hA, hMultiplier⟩ :=
    dfiEquation29Multiplier_shifted_strip_bound q k branch
  obtain ⟨B, hB, hMellin⟩ :=
    hg.exists_mellin_one_add_abs_pow_line_bound (p + 4) σ
  let J : ℝ := ∫ u : ℝ, (1 + u ^ 2)⁻¹
  let C : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖ * A * B * J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun u => inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro n hn
  let D : ℝ := (n : ℝ) ^ (σ - 1)
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hσLower : -(1 / 2 : ℝ) - k ≤ σ := by simp [σ]
  have hσUpper : σ ≤ -(1 / 2 : ℝ) := by
    dsimp [σ]
    exact sub_le_self _ (Nat.cast_nonneg k)
  have hTargetInt : Integrable (fun u : ℝ =>
      ‖dfiEquation29Integrand q branch g n
        ((σ : ℂ) + (u : ℂ) * I)‖) :=
    (hg.integrable_dfiEquation29Integrand_vertical q k branch hn
      hσLower hσUpper).norm
  have hMajorInt : Integrable (fun u : ℝ =>
      D * A * B * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using integrable_inv_one_add_sq.const_mul (D * A * B)
  have hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        D * A * B * (1 + u ^ 2)⁻¹ := by
    intro u
    have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
      hA.le
      (hMultiplier σ hσLower hσUpper u)
      (hMellin u)
    rw [norm_mul] at hCore
    have hPower :
        ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ = D := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      congr 1
      simp
    unfold dfiEquation29Integrand
    rw [norm_mul, norm_mul, hPower]
    calc
      D * ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
        D * (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
      _ ≤ D * (A * B * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hCore hD
      _ = D * A * B * (1 + u ^ 2)⁻¹ := by ring
  have hIntegral :
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖) ≤ D * A * B * J := by
    calc
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖) ≤
          ∫ u : ℝ, D * A * B * (1 + u ^ 2)⁻¹ :=
        integral_mono hTargetInt hMajorInt hPoint
      _ = D * A * B * J := by
        rw [MeasureTheory.integral_const_mul]
  have hInitialShift : dfiEquation29InitialTransform q branch g n =
      dfiEquation29TransformAt q branch g n σ := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n σ := by
        simpa [σ] using hg.dfiEquation29TransformAt_shift q k branch hn
  have hD_eq : D = (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
    dsimp [D, σ]
    congr 1
    ring
  rw [hInitialShift]
  calc
    ‖dfiEquation29TransformAt q branch g n σ‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
            ((σ : ℂ) + (u : ℂ) * I)‖ :=
      norm_verticalIntegral'_le_integral_norm _ _
    _ ≤ ‖(1 / (2 * Real.pi * I) : ℂ)‖ * (D * A * B * J) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg _)
    _ = C * (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
      rw [hD_eq]
      dsimp [C]
      ring

/-- Source-uniform left-contour form of DFI (29).  An explicit Mellin bound
is preserved as a visible factor, while the remaining constant is universal
for the chosen contour depth and Voronoi branch. -/
theorem exists_dfiEquation29InitialTransform_decay_constant
    (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : ℝ → ℂ}, DFIVoronoiTestFunction g →
      ∀ {B : ℝ}, (∀ u : ℝ,
        (1 + |u|) ^ (2 * (k + 1) + 4) *
          ‖mellin g (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ B) →
      ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n →
        ‖dfiEquation29InitialTransform q branch g n‖ ≤
          C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B *
            (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  let σ : ℝ := -(1 / 2 : ℝ) - k
  let p : ℕ := 2 * (k + 1)
  obtain ⟨A, hA, hMultiplier⟩ :=
    exists_dfiEquation29Multiplier_explicit_modulus_bound k branch
  let J : ℝ := ∫ u : ℝ, (1 + u ^ 2)⁻¹
  let C : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖ * A * J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun u ↦ inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro g hg B hMellin q hq n hn
  letI : NeZero q := hq
  let D : ℝ := (n : ℝ) ^ (σ - 1)
  let Qk : ℝ := (q : ℝ) ^ (2 + 2 * (k : ℝ))
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hQk : 0 ≤ Qk := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hσLower : -(1 / 2 : ℝ) - k ≤ σ := by simp [σ]
  have hσUpper : σ ≤ -(1 / 2 : ℝ) := by
    dsimp [σ]
    exact sub_le_self _ (Nat.cast_nonneg k)
  have hTargetInt : Integrable (fun u : ℝ ↦
      ‖dfiEquation29Integrand q branch g n
        ((σ : ℂ) + (u : ℂ) * I)‖) :=
    (hg.integrable_dfiEquation29Integrand_vertical q k branch hn
      hσLower hσUpper).norm
  have hMajorInt : Integrable (fun u : ℝ ↦
      D * (A * Qk) * B * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using
      integrable_inv_one_add_sq.const_mul (D * (A * Qk) * B)
  have hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        D * (A * Qk) * B * (1 + u ^ 2)⁻¹ := by
    intro u
    have hMellinAt :
        (1 + |u|) ^ (p + 4) *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ B := by
      simpa [σ, p] using hMellin u
    have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
      (mul_nonneg hA.le hQk)
      (by simpa [Qk, p, mul_assoc] using
        hMultiplier q hq σ hσLower hσUpper u)
      hMellinAt
    rw [norm_mul] at hCore
    have hPower :
        ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ = D := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      congr 1
      simp
    unfold dfiEquation29Integrand
    rw [norm_mul, norm_mul, hPower]
    calc
      D * ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
        D * (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
      _ ≤ D * ((A * Qk) * B * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hCore hD
      _ = D * (A * Qk) * B * (1 + u ^ 2)⁻¹ := by ring
  have hIntegral :
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖) ≤
        D * (A * Qk) * B * J := by
    calc
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖) ≤
          ∫ u : ℝ, D * (A * Qk) * B * (1 + u ^ 2)⁻¹ :=
        integral_mono hTargetInt hMajorInt hPoint
      _ = D * (A * Qk) * B * J := by
        rw [MeasureTheory.integral_const_mul]
  have hInitialShift : dfiEquation29InitialTransform q branch g n =
      dfiEquation29TransformAt q branch g n σ := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n σ := by
        simpa [σ] using hg.dfiEquation29TransformAt_shift q k branch hn
  have hD_eq : D = (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
    dsimp [D, σ]
    congr 1
    ring
  rw [hInitialShift]
  calc
    ‖dfiEquation29TransformAt q branch g n σ‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
            ((σ : ℂ) + (u : ℂ) * I)‖ :=
      norm_verticalIntegral'_le_integral_norm _ _
    _ ≤ ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        (D * (A * Qk) * B * J) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg _)
    _ = C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B *
        (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
      rw [hD_eq]
      dsimp [C, Qk]
      ring

/-- Test-function-facing wrapper around the universal source-uniform
left-contour constant. -/
theorem DFIVoronoiTestFunction.exists_dfiEquation29InitialTransform_decay_of_mellin_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (k : ℕ) (branch : DFIVoronoiDualBranch) {B : ℝ}
    (hMellin : ∀ u : ℝ,
      (1 + |u|) ^ (2 * (k + 1) + 4) *
        ‖mellin g (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ),
      0 < n →
      ‖dfiEquation29InitialTransform q branch g n‖ ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B *
          (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  obtain ⟨C, hC, hUniversal⟩ :=
    exists_dfiEquation29InitialTransform_decay_constant k branch
  exact ⟨C, hC, hUniversal hg hMellin⟩

/-- The residue-independent Voronoi summand is the divisor weight times the
equation-(29) initial transform. -/
theorem dfiVoronoiDualTerm_eq_divisorWeight_mul_initial
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (n : ℕ) :
    dfiVoronoiDualTerm q branch g n =
      divisorWeight n * dfiEquation29InitialTransform q branch g n := by
  cases branch <;> rfl

/-- Universal divisor-weighted version of the explicit Mellin-input decay.
The exponent `1/2` in the native divisor bound converts
`n^(-3/2-k)` into the summable `n^(-1-k)`. -/
theorem exists_dfiVoronoiDualTerm_decay_constant
    (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : ℝ → ℂ}, DFIVoronoiTestFunction g →
      ∀ {B : ℝ}, (∀ u : ℝ,
        (1 + |u|) ^ (2 * (k + 1) + 4) *
          ‖mellin g (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ B) →
      ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n →
        ‖dfiVoronoiDualTerm q branch g n‖ ≤
          C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B *
            (n : ℝ) ^ (-(1 : ℝ) - k) := by
  obtain ⟨A, hA, hTransform⟩ :=
    exists_dfiEquation29InitialTransform_decay_constant k branch
  obtain ⟨D, hD, hDivisor⟩ :=
    divisorCountBound_native (1 / 2 : ℝ) (by norm_num)
  refine ⟨D * A, mul_nonneg hD.le hA, ?_⟩
  intro g hg B hMellin q hq n hn
  letI : NeZero q := hq
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  have hWeight : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ (1 / 2 : ℝ) := by
    simpa [divisorWeight] using hDivisor n hn
  have hTransform' := hTransform hg hMellin q hq n hn
  calc
    ‖divisorWeight n‖ * ‖dfiEquation29InitialTransform q branch g n‖ ≤
        (D * (n : ℝ) ^ (1 / 2 : ℝ)) *
          (A * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B *
            (n : ℝ) ^ (-(3 / 2 : ℝ) - k)) :=
      mul_le_mul hWeight hTransform' (norm_nonneg _)
        (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ = (D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B *
        (n : ℝ) ^ (-(1 : ℝ) - k) := by
      calc
        (D * (n : ℝ) ^ (1 / 2 : ℝ)) *
            (A * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B *
              (n : ℝ) ^ (-(3 / 2 : ℝ) - k)) =
          ((D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B) *
            ((n : ℝ) ^ (1 / 2 : ℝ) *
              (n : ℝ) ^ (-(3 / 2 : ℝ) - k)) := by ring
        _ = ((D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B) *
            (n : ℝ) ^ ((1 / 2 : ℝ) + (-(3 / 2 : ℝ) - k)) := by
          rw [Real.rpow_add (Nat.cast_pos.mpr hn)]
        _ = (D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B *
            (n : ℝ) ^ (-(1 : ℝ) - k) := by
          congr 1
          ring_nf

/-- Summed universal Equation (29) tail with the explicit source Mellin
factor retained. -/
theorem exists_dfiVoronoiDualTerm_tail_decay_constant
    (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : ℝ → ℂ}, DFIVoronoiTestFunction g →
      ∀ {B : ℝ}, 0 ≤ B → (∀ u : ℝ,
        (1 + |u|) ^ (2 * (k + 1) + 4) *
          ‖mellin g (((-(1 / 2 : ℝ) - k : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤ B) →
      ∀ (q L : ℕ) (_hq : NeZero q), 0 < L →
        ∑' j : ℕ, ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖ ≤
          C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨C, hC, hPoint⟩ :=
    exists_dfiVoronoiDualTerm_decay_constant k branch
  refine ⟨C, hC, ?_⟩
  intro g hg B hB hMellin q L hq hL
  letI : NeZero q := hq
  let A : ℝ := C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hSeries := tsum_nat_add_one_rpow_neg_le
    (L := (L : ℝ)) (p := 1 + (k : ℝ))
    (Nat.cast_pos.mpr hL) (by
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      linarith)
  have hSeries' :
      ∑' j : ℕ, ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) ≤
        (L : ℝ) ^ (-(k : ℝ)) / (k : ℝ) := by
    convert hSeries using 1
    all_goals ring_nf
  have hPowerSummable : Summable (fun j : ℕ ↦
      ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ)))) := by
    have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(1 + (k : ℝ)))) :=
      Real.summable_nat_rpow.mpr (by
        have hk' : (0 : ℝ) < k := by exact_mod_cast hk
        linarith)
    have hshift := (summable_nat_add_iff (L + 1)).2 hbase
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hshift
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact norm_nonneg _
  · intro N
    calc
      ∑ j ∈ Finset.range N,
          ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖ ≤
          ∑ j ∈ Finset.range N,
            A * ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) := by
        gcongr with j hj
        have hn : 0 < L + (j + 1) := by omega
        have hpnt := hPoint hg hMellin q hq (L + (j + 1)) hn
        have hexp : -(1 + (k : ℝ)) = -(1 : ℝ) - k := by ring_nf
        dsimp [A]
        rw [hexp]
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
          add_left_comm] using hpnt
      _ = A * ∑ j ∈ Finset.range N,
            ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) := by
        rw [Finset.mul_sum]
      _ ≤ A * ∑' j : ℕ,
            ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) := by
        gcongr
        exact hPowerSummable.sum_le_tsum
          (Finset.range N) (fun j _ ↦ Real.rpow_nonneg (by positivity) _)
      _ ≤ A * ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) :=
        mul_le_mul_of_nonneg_left hSeries' hA
      _ = C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) * B *
          ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := rfl

/-- Scale-explicit form of DFI (29).  After normalizing a test function at
physical scale `S`, the constant is uniform in the modulus and positive dual
frequency.  The displayed factor is
`q^(2+2k) S^(-1/2-k) n^(-3/2-k)`, so every further contour displacement gains
the source ratio `q²/(nS)`. -/
theorem DFIVoronoiTestFunction.exists_dfiEquation29InitialTransform_scaled_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ),
      0 < n →
      ‖dfiEquation29InitialTransform q branch g n‖ ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  let σ : ℝ := -(1 / 2 : ℝ) - k
  let p : ℕ := 2 * (k + 1)
  let g₁ : ℝ → ℂ := fun x ↦ g (S * x)
  have hg₁ : DFIVoronoiTestFunction g₁ := by
    simpa [g₁] using hg.scaleNormalize S hS
  obtain ⟨A, hA, hMultiplier⟩ :=
    exists_dfiEquation29Multiplier_explicit_modulus_bound k branch
  obtain ⟨B, hB, hMellin⟩ :=
    hg₁.exists_mellin_one_add_abs_pow_line_bound (p + 4) σ
  let J : ℝ := ∫ u : ℝ, (1 + u ^ 2)⁻¹
  let C : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖ * A * B * J
  have hJ : 0 ≤ J := by
    dsimp [J]
    exact integral_nonneg fun u ↦ inv_nonneg.mpr (by positivity : 0 ≤ 1 + u ^ 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro q hq n hn
  letI : NeZero q := hq
  let D : ℝ := (n : ℝ) ^ (σ - 1)
  let Qk : ℝ := (q : ℝ) ^ (2 + 2 * (k : ℝ))
  let Sk : ℝ := S ^ σ
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hQk : 0 ≤ Qk := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hSk : 0 ≤ Sk := Real.rpow_nonneg hS.le _
  have hσLower : -(1 / 2 : ℝ) - k ≤ σ := by simp [σ]
  have hσUpper : σ ≤ -(1 / 2 : ℝ) := by
    dsimp [σ]
    exact sub_le_self _ (Nat.cast_nonneg k)
  have hMellinScaled : ∀ u : ℝ,
      (1 + |u|) ^ (p + 4) *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤ Sk * B := by
    intro u
    rw [mellin_eq_scale_cpow_mul_normalized g S hS, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hS]
    have hRe : (((σ : ℂ) + (u : ℂ) * I).re) = σ := by simp
    rw [hRe]
    change (1 + |u|) ^ (p + 4) *
        (Sk * ‖mellin g₁ ((σ : ℂ) + (u : ℂ) * I)‖) ≤ Sk * B
    calc
      (1 + |u|) ^ (p + 4) *
          (Sk * ‖mellin g₁ ((σ : ℂ) + (u : ℂ) * I)‖) =
        Sk * ((1 + |u|) ^ (p + 4) *
          ‖mellin g₁ ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
      _ ≤ Sk * B := mul_le_mul_of_nonneg_left (hMellin u) hSk
  have hTargetInt : Integrable (fun u : ℝ ↦
      ‖dfiEquation29Integrand q branch g n
        ((σ : ℂ) + (u : ℂ) * I)‖) :=
    (hg.integrable_dfiEquation29Integrand_vertical q k branch hn
      hσLower hσUpper).norm
  have hMajorInt : Integrable (fun u : ℝ ↦
      D * (A * Qk) * (Sk * B) * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using
      integrable_inv_one_add_sq.const_mul (D * (A * Qk) * (Sk * B))
  have hPoint : ∀ u : ℝ,
      ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤
        D * (A * Qk) * (Sk * B) * (1 + u ^ 2)⁻¹ := by
    intro u
    have hCore := norm_mul_le_inv_one_add_sq_of_pow_growth_decay
      (mul_nonneg hA.le hQk)
      (by simpa [Qk, p, mul_assoc] using
        hMultiplier q hq σ hσLower hσUpper u)
      (hMellinScaled u)
    rw [norm_mul] at hCore
    have hPower :
        ‖(n : ℂ) ^ (-(1 - ((σ : ℂ) + (u : ℂ) * I)))‖ = D := by
      rw [Complex.norm_natCast_cpow_of_pos hn]
      congr 1
      simp
    unfold dfiEquation29Integrand
    rw [norm_mul, norm_mul, hPower]
    calc
      D * ‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ =
        D * (‖dfiEquation29Multiplier q branch ((σ : ℂ) + (u : ℂ) * I)‖ *
          ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖) := by ring
      _ ≤ D * ((A * Qk) * (Sk * B) * (1 + u ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hCore hD
      _ = D * (A * Qk) * (Sk * B) * (1 + u ^ 2)⁻¹ := by ring
  have hIntegral :
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖) ≤
        D * (A * Qk) * (Sk * B) * J := by
    calc
      (∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
          ((σ : ℂ) + (u : ℂ) * I)‖) ≤
          ∫ u : ℝ, D * (A * Qk) * (Sk * B) * (1 + u ^ 2)⁻¹ :=
        integral_mono hTargetInt hMajorInt hPoint
      _ = D * (A * Qk) * (Sk * B) * J := by
        rw [MeasureTheory.integral_const_mul]
  have hInitialShift : dfiEquation29InitialTransform q branch g n =
      dfiEquation29TransformAt q branch g n σ := by
    calc
      dfiEquation29InitialTransform q branch g n =
          dfiEquation29TransformAt q branch g n (-(1 / 2 : ℝ)) :=
        (dfiEquation29TransformAt_initial q branch g n).symm
      _ = dfiEquation29TransformAt q branch g n σ := by
        simpa [σ] using hg.dfiEquation29TransformAt_shift q k branch hn
  have hD_eq : D = (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
    dsimp [D, σ]
    congr 1
    ring
  have hSk_eq : Sk = S ^ (-(1 / 2 : ℝ) - k) := by rfl
  rw [hInitialShift]
  calc
    ‖dfiEquation29TransformAt q branch g n σ‖ ≤
        ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ∫ u : ℝ, ‖dfiEquation29Integrand q branch g n
            ((σ : ℂ) + (u : ℂ) * I)‖ :=
      norm_verticalIntegral'_le_integral_norm _ _
    _ ≤ ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        (D * (A * Qk) * (Sk * B) * J) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg _)
    _ = C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
        S ^ (-(1 / 2 : ℝ) - k) *
          (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
      rw [hD_eq, hSk_eq]
      dsimp [C, Qk]
      ring

/-- Retained-frequency version of DFI (29), after inserting the native
divisor estimate with exponent `1/4`. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualTerm_scaled_retained_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n →
      ‖dfiVoronoiDualTerm q branch g n‖ ≤
        C * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨A, hA, hTransform⟩ :=
    hg.exists_dfiEquation29InitialTransform_scaled_retained_bound S hS branch
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native (1 / 4 : ℝ) (by norm_num)
  refine ⟨D * A, mul_nonneg hD.le hA, ?_⟩
  intro q hq n hn
  letI : NeZero q := hq
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  have hWeight : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ (1 / 4 : ℝ) := by
    simpa [divisorWeight] using hDivisor n hn
  have hTransform' := hTransform q hq n hn
  calc
    ‖divisorWeight n‖ * ‖dfiEquation29InitialTransform q branch g n‖ ≤
        (D * (n : ℝ) ^ (1 / 4 : ℝ)) *
          (A * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul hWeight hTransform' (norm_nonneg _)
        (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ = (D * A) * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      calc
        (D * (n : ℝ) ^ (1 / 4 : ℝ)) *
            (A * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) =
          ((D * A) * S ^ (1 / 2 : ℝ)) *
            ((n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
        _ = ((D * A) * S ^ (1 / 2 : ℝ)) *
            (n : ℝ) ^ ((1 / 4 : ℝ) + (-(1 / 2 : ℝ))) := by
          rw [Real.rpow_add (Nat.cast_pos.mpr hn)]
        _ = (D * A) * S ^ (1 / 2 : ℝ) *
            (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
          congr 1
          ring_nf

/-- Source-strength retained-frequency bound on DFI's `Re z = 3/4` line.
After inserting the divisor estimate with an arbitrary positive exponent,
the normalized dual summand has the paper's `n^(-1/4+ε)` decay. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualTerm_scaled_threeQuarter_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (ε : ℝ) (hε : 0 < ε)
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ), 0 < n →
      ‖dfiVoronoiDualTerm q branch g n‖ ≤
        C * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
          (n : ℝ) ^ (ε - 1 / 4) := by
  obtain ⟨A, hA, hTransform⟩ :=
    hg.exists_dfiEquation29InitialTransform_scaled_threeQuarter_bound S hS branch
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native ε hε
  refine ⟨D * A, mul_nonneg hD.le hA, ?_⟩
  intro q hq n hn
  letI : NeZero q := hq
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  have hWeight : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ ε := by
    simpa [divisorWeight] using hDivisor n hn
  have hTransform' := hTransform q hq n hn
  calc
    ‖divisorWeight n‖ * ‖dfiEquation29InitialTransform q branch g n‖ ≤
        (D * (n : ℝ) ^ ε) *
          (A * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
            (n : ℝ) ^ (-(1 / 4 : ℝ))) :=
      mul_le_mul hWeight hTransform' (norm_nonneg _)
        (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ = ((D * A) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ)) *
        ((n : ℝ) ^ ε * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by ring
    _ = ((D * A) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ)) *
        (n : ℝ) ^ (ε + (-(1 / 4 : ℝ))) := by
      rw [Real.rpow_add (Nat.cast_pos.mpr hn)]
    _ = (D * A) * (q : ℝ) ^ (-(1 / 2 : ℝ)) * S ^ (3 / 4 : ℝ) *
        (n : ℝ) ^ (ε - 1 / 4) := by ring

/-- DFI (29) after inserting the native divisor-function estimate.  The
constant remains uniform in the modulus and positive dual frequency. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualTerm_scaled_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (_hq : NeZero q) (n : ℕ),
      0 < n →
      ‖dfiVoronoiDualTerm q branch g n‖ ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            (n : ℝ) ^ (-(1 : ℝ) - k) := by
  obtain ⟨A, hA, hTransform⟩ :=
    hg.exists_dfiEquation29InitialTransform_scaled_decay S hS k branch
  obtain ⟨D, hD, hDivisor⟩ := divisorCountBound_native (1 / 2 : ℝ) (by norm_num)
  refine ⟨D * A, mul_nonneg hD.le hA, ?_⟩
  intro q hq n hn
  letI : NeZero q := hq
  rw [dfiVoronoiDualTerm_eq_divisorWeight_mul_initial, norm_mul]
  have hWeight : ‖divisorWeight n‖ ≤ D * (n : ℝ) ^ (1 / 2 : ℝ) := by
    simpa [divisorWeight] using hDivisor n hn
  have hTransform' := hTransform q hq n hn
  calc
    ‖divisorWeight n‖ * ‖dfiEquation29InitialTransform q branch g n‖ ≤
        (D * (n : ℝ) ^ (1 / 2 : ℝ)) *
          (A * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
            S ^ (-(1 / 2 : ℝ) - k) *
              (n : ℝ) ^ (-(3 / 2 : ℝ) - k)) :=
      mul_le_mul hWeight hTransform' (norm_nonneg _)
        (mul_nonneg hD.le (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    _ = (D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            (n : ℝ) ^ (-(1 : ℝ) - k) := by
      calc
        (D * (n : ℝ) ^ (1 / 2 : ℝ)) *
            (A * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
              S ^ (-(1 / 2 : ℝ) - k) *
                (n : ℝ) ^ (-(3 / 2 : ℝ) - k)) =
            ((D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
              S ^ (-(1 / 2 : ℝ) - k)) *
                ((n : ℝ) ^ (1 / 2 : ℝ) *
                  (n : ℝ) ^ (-(3 / 2 : ℝ) - k)) := by ring_nf
        _ = ((D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
              S ^ (-(1 / 2 : ℝ) - k)) *
                (n : ℝ) ^ ((1 / 2 : ℝ) + (-(3 / 2 : ℝ) - k)) := by
              rw [Real.rpow_add (Nat.cast_pos.mpr hn)]
        _ = (D * A) * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
              S ^ (-(1 / 2 : ℝ) - k) *
                (n : ℝ) ^ (-(1 : ℝ) - k) := by
              congr 1
              ring_nf

/-- Summed, quantitative form of DFI (29).  Frequencies strictly beyond `L`
have total norm bounded by the displayed power tail.  Choosing
`L` larger than the transition scale `q²/S` by a small power and then taking
`k` large gives the arbitrary power saving used in the source. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualTerm_tail_scaled_decay
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q L : ℕ) (_hq : NeZero q), 0 < L →
      ∑' j : ℕ, ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖ ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨C, hC, hPoint⟩ :=
    hg.exists_dfiVoronoiDualTerm_scaled_decay S hS k branch
  refine ⟨C, hC, ?_⟩
  intro q L hq hL
  letI : NeZero q := hq
  let B : ℝ := C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
    S ^ (-(1 / 2 : ℝ) - k)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hSeries := tsum_nat_add_one_rpow_neg_le
    (L := (L : ℝ)) (p := 1 + (k : ℝ))
    (Nat.cast_pos.mpr hL) (by
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      linarith)
  have hSeries' :
      ∑' j : ℕ, ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) ≤
        (L : ℝ) ^ (-(k : ℝ)) / (k : ℝ) := by
    convert hSeries using 1
    all_goals ring_nf
  have hPowerSummable : Summable (fun j : ℕ ↦
      ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ)))) := by
    have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(1 + (k : ℝ)))) :=
      Real.summable_nat_rpow.mpr (by
        have hk' : (0 : ℝ) < k := by exact_mod_cast hk
        linarith)
    have hshift := (summable_nat_add_iff (L + 1)).2 hbase
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hshift
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact norm_nonneg _
  · intro N
    calc
      ∑ j ∈ Finset.range N,
          ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖ ≤
          ∑ j ∈ Finset.range N,
            B * ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) := by
        gcongr with j hj
        have hn : 0 < L + (j + 1) := by omega
        have hpnt := hPoint q hq (L + (j + 1)) hn
        have hexp : -(1 + (k : ℝ)) = -(1 : ℝ) - k := by ring_nf
        dsimp [B]
        rw [hexp]
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hpnt
      _ = B * ∑ j ∈ Finset.range N,
            ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) := by
          rw [Finset.mul_sum]
      _ ≤ B * ∑' j : ℕ,
            ((L : ℝ) + (j + 1 : ℕ)) ^ (-(1 + (k : ℝ))) := by
          gcongr
          exact hPowerSummable.sum_le_tsum
            (Finset.range N) (fun j _ ↦ Real.rpow_nonneg (by positivity) _)
      _ ≤ B * ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) :=
          mul_le_mul_of_nonneg_left hSeries' hB
      _ = C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by rfl

/-- Effective transition-scale version of DFI (29).  If the retained dual
window extends past `(q²/S) R`, then the discarded tail gains the factor
`((q²/S) R)^(-k)`.  This is the precise quantified form in which the paper
takes `R` to be a small power of its global parameter and then chooses `k`
arbitrarily large. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualTerm_tail_of_transition
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q L : ℕ) (_hq : NeZero q) (R : ℝ), 0 < L → 0 < R →
        (q : ℝ) ^ 2 / S * R ≤ L →
        ∑' j : ℕ, ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖ ≤
          C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
            S ^ (-(1 / 2 : ℝ) - k) *
              (((q : ℝ) ^ 2 / S * R) ^ (-(k : ℝ))) := by
  obtain ⟨C, hC, hTail⟩ :=
    hg.exists_dfiVoronoiDualTerm_tail_scaled_decay S hS k hk branch
  refine ⟨C, hC, ?_⟩
  intro q L hq R hL hR hcut
  letI : NeZero q := hq
  have hqPos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have htransition : 0 < (q : ℝ) ^ 2 / S * R := by positivity
  have hkNonpos : -(k : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg k)
  have hpow : (L : ℝ) ^ (-(k : ℝ)) ≤
      ((q : ℝ) ^ 2 / S * R) ^ (-(k : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos htransition hcut hkNonpos
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hdiv : (L : ℝ) ^ (-(k : ℝ)) / (k : ℝ) ≤
      (L : ℝ) ^ (-(k : ℝ)) :=
    div_le_self (Real.rpow_nonneg (Nat.cast_nonneg L) _) hkOne
  have hfactor : 0 ≤ C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
      S ^ (-(1 / 2 : ℝ) - k) := by positivity
  exact (hTail q L hq hL).trans
    (mul_le_mul_of_nonneg_left (hdiv.trans hpow) hfactor)

/-- Equation (29), first-variable source entry: the literal localized
equation-(23) slice has physical scale `X/a`, and its two Voronoi transforms
therefore gain the exact ratio `r²/(m(X/a))` per contour displacement. -/
theorem exists_dfiEquation29_xSlice_scaled_decay
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (y : ℝ) (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℕ) (_hr : NeZero r) (m : ℕ), 0 < m →
      ‖dfiEquation29InitialTransform r branch
          (fun x ↦ dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x y) m‖ ≤
        C * (r : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (X / a) ^ (-(1 / 2 : ℝ) - k) *
            (m : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  have hScale : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) (by exact_mod_cast ha)
  exact (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
    |>.exists_dfiEquation29InitialTransform_scaled_decay
      (X / a) hScale k branch

/-- Equation (29), first-variable source tail.  This is the actual localized
equation-(23) test function, not an independently supplied smooth function. -/
theorem exists_dfiEquation29_xSlice_tail_scaled_decay
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (y : ℝ) (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L : ℕ) (_hr : NeZero r), 0 < L →
      ∑' j : ℕ, ‖dfiVoronoiDualTerm r branch
          (fun x ↦ dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x y) (L + (j + 1))‖ ≤
        C * (r : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (X / a) ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  have hScale : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) (by exact_mod_cast ha)
  exact (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
    |>.exists_dfiVoronoiDualTerm_tail_scaled_decay
      (X / a) hScale k hk branch

/-- Equation (29), second-variable source entry, with physical scale `Y/b`.
This is the symmetric consumer needed before the double-dual branch of (24)
is estimated. -/
theorem exists_dfiEquation29_ySlice_scaled_decay
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (hb : 0 < b) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (x : ℝ) (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℕ) (_hr : NeZero r) (n : ℕ), 0 < n →
      ‖dfiEquation29InitialTransform r branch
          (dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x) n‖ ≤
        C * (r : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (Y / b) ^ (-(1 / 2 : ℝ) - k) *
            (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  have hScale : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) (by exact_mod_cast hb)
  exact (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
    |>.exists_dfiEquation29InitialTransform_scaled_decay
      (Y / b) hScale k branch

/-- Equation (29), second-variable source tail, symmetric to the preceding
first-variable theorem. -/
theorem exists_dfiEquation29_ySlice_tail_scaled_decay
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (hb : 0 < b) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (x : ℝ) (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L : ℕ) (_hr : NeZero r), 0 < L →
      ∑' j : ℕ, ‖dfiVoronoiDualTerm r branch
          (dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x) (L + (j + 1))‖ ≤
        C * (r : ℝ) ^ (2 + 2 * (k : ℝ)) *
          (Y / b) ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  have hScale : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) (by exact_mod_cast hb)
  exact (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
    |>.exists_dfiVoronoiDualTerm_tail_scaled_decay
      (Y / b) hScale k hk branch

/-- DFI equations (28)--(29), with the source quantifiers in their required
order: a single constant profile is selected before `a,b,q,h,x`, and the
literal equation-(23) second-variable slice receives an explicit Mellin-line
bound. -/
theorem exists_dfiEquation28_ySlice_mellin_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x u : ℝ),
        let C₆ := ∑ j ∈ Finset.range 7, C j
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * Y / b)
        (1 + |u|) ^ 6 *
            ‖mellin
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x)
              ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ 6 *
            (64 *
              ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
              (D * A + D * (512 * A * (1 + D * B) ^ 6))) := by
  choose C hC hBound using fun j =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ 0 j
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x u
  dsimp only
  let C₆ : ℝ := ∑ j ∈ Finset.range 7, C j
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := C₆ * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hC₆ : 0 < C₆ := by
    dsimp [C₆]
    exact Finset.sum_pos
      (fun j hj => hC j) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hDeriv : ∀ j ≤ 6, ∀ y : ℝ,
      ‖iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y‖ ≤ A * B ^ j := by
    intro j hj y
    have hjMem : j ∈ Finset.range 7 := by
      simp only [Finset.mem_range]
      omega
    have hCle : C j ≤ C₆ := by
      dsimp [C₆]
      exact Finset.single_le_sum (fun k hk => (hC k).le) hjMem
    have hEq : iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y =
        dfiMixedDeriv 0 j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C j * qQ⁻¹ * B ^ (0 + j) := by
        simpa only [qQ, B] using
          hBound j a b q ha hb hq hqQ h x y
      _ ≤ C₆ * qQ⁻¹ * B ^ j := by
        simp only [zero_add]
        gcongr
      _ = A * B ^ j := rfl
  have hMellin :=
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
      |>.mellin_half_line_bound_of_physical_profile hA hB hDeriv u
  simpa only [A, B, C₆] using hMellin

/-- Source-uniform three-quarter-line version of the preceding
second-variable Mellin estimate. -/
theorem exists_dfiEquation28_ySlice_mellin_threeQuarter_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x u : ℝ),
        let C₆ := ∑ j ∈ Finset.range 7, C j
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * Y / b)
        (1 + |u|) ^ 6 *
            ‖mellin
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x)
              ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ 6 *
            (64 *
              ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
              (D * A + D * (1024 * A * (1 + D * B) ^ 6))) := by
  choose C hC hBound using fun j =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ 0 j
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x u
  dsimp only
  let C₆ : ℝ := ∑ j ∈ Finset.range 7, C j
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := C₆ * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hC₆ : 0 < C₆ := by
    dsimp [C₆]
    exact Finset.sum_pos (fun j hj => hC j) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hDeriv : ∀ j ≤ 6, ∀ y : ℝ,
      ‖iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y‖ ≤ A * B ^ j := by
    intro j hj y
    have hjMem : j ∈ Finset.range 7 := by
      simp only [Finset.mem_range]
      omega
    have hCle : C j ≤ C₆ := by
      dsimp [C₆]
      exact Finset.single_le_sum (fun k hk => (hC k).le) hjMem
    have hEq : iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y =
        dfiMixedDeriv 0 j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C j * qQ⁻¹ * B ^ (0 + j) := by
        simpa only [qQ, B] using
          hBound j a b q ha hb hq hqQ h x y
      _ ≤ C₆ * qQ⁻¹ * B ^ j := by
        simp only [zero_add]
        gcongr
      _ = A * B ^ j := rfl
  have hMellin :=
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
      |>.mellin_threeQuarter_line_bound_of_physical_profile hA hB hDeriv u
  simpa only [A, B, C₆] using hMellin

/-- Source-uniform arbitrary-line counterpart for the second-variable
slice.  Together with the first-variable theorem below this supplies both
left-contour tails in the double Voronoi branch of DFI (24). -/
theorem exists_dfiEquation28_ySlice_mellin_line_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x u : ℝ),
        let C₆ := ∑ j ∈ Finset.range 7, C j
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * Y / b) (Y / b)⁻¹)
        (1 + |u|) ^ 6 *
            ‖mellin
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x)
              ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ 6 *
            (64 * ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
              (D ^ |σ| * A +
                D ^ |σ| * (A * (|σ| + 6 + D * B) ^ 6))) := by
  choose C hC hBound using fun j =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ 0 j
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x u
  dsimp only
  let C₆ : ℝ := ∑ j ∈ Finset.range 7, C j
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := C₆ * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hC₆ : 0 < C₆ := by
    dsimp [C₆]
    exact Finset.sum_pos (fun j hj => hC j) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hDeriv : ∀ j ≤ 6, ∀ y : ℝ,
      ‖iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y‖ ≤ A * B ^ j := by
    intro j hj y
    have hjMem : j ∈ Finset.range 7 := by
      simp only [Finset.mem_range]
      omega
    have hCle : C j ≤ C₆ := by
      dsimp [C₆]
      exact Finset.single_le_sum (fun k hk => (hC k).le) hjMem
    have hEq : iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y =
        dfiMixedDeriv 0 j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C j * qQ⁻¹ * B ^ (0 + j) := by
        simpa only [qQ, B] using
          hBound j a b q ha hb hq hqQ h x y
      _ ≤ C₆ * qQ⁻¹ * B ^ j := by
        simp only [zero_add]
        gcongr
      _ = A * B ^ j := rfl
  have hMellin :=
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
      |>.mellin_line_bound_of_physical_profile σ hA hB hDeriv u
  simpa only [A, B, C₆] using hMellin

/-- First-variable counterpart of `exists_dfiEquation28_ySlice_mellin_bound`.
The same source-level quantifier discipline is preserved. -/
theorem exists_dfiEquation28_xSlice_mellin_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y u : ℝ),
        let C₆ := ∑ i ∈ Finset.range 7, C i
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * X / a)
        (1 + |u|) ^ 6 *
            ‖mellin
              (fun x => dfiEquation23Weight w
                (dfiLocalizedWeight f φ h) a b h q x y)
              ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ 6 *
            (64 *
              ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
              (D * A + D * (512 * A * (1 + D * B) ^ 6))) := by
  choose C hC hBound using fun i =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ i 0
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y u
  dsimp only
  let C₆ : ℝ := ∑ i ∈ Finset.range 7, C i
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := C₆ * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hC₆ : 0 < C₆ := by
    dsimp [C₆]
    exact Finset.sum_pos (fun i hi => hC i) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hDeriv : ∀ i ≤ 6, ∀ x : ℝ,
      ‖iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x‖ ≤ A * B ^ i := by
    intro i hi x
    have hiMem : i ∈ Finset.range 7 := by
      simp only [Finset.mem_range]
      omega
    have hCle : C i ≤ C₆ := by
      dsimp [C₆]
      exact Finset.single_le_sum (fun k hk => (hC k).le) hiMem
    have hEq : iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x =
        dfiMixedDeriv i 0
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C i * qQ⁻¹ * B ^ (i + 0) := by
        simpa only [qQ, B] using
          hBound i a b q ha hb hq hqQ h x y
      _ ≤ C₆ * qQ⁻¹ * B ^ i := by
        simp only [add_zero]
        gcongr
      _ = A * B ^ i := rfl
  have hMellin :=
    (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
      |>.mellin_half_line_bound_of_physical_profile hA hB hDeriv u
  simpa only [A, B, C₆] using hMellin

/-- Source-uniform three-quarter-line counterpart for the first variable. -/
theorem exists_dfiEquation28_xSlice_mellin_threeQuarter_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y u : ℝ),
        let C₆ := ∑ i ∈ Finset.range 7, C i
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * X / a)
        (1 + |u|) ^ 6 *
            ‖mellin
              (fun x => dfiEquation23Weight w
                (dfiLocalizedWeight f φ h) a b h q x y)
              ((3 / 4 : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ 6 *
            (64 *
              ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
              (D * A + D * (1024 * A * (1 + D * B) ^ 6))) := by
  choose C hC hBound using fun i =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ i 0
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y u
  dsimp only
  let C₆ : ℝ := ∑ i ∈ Finset.range 7, C i
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := C₆ * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hC₆ : 0 < C₆ := by
    dsimp [C₆]
    exact Finset.sum_pos (fun i hi => hC i) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hDeriv : ∀ i ≤ 6, ∀ x : ℝ,
      ‖iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x‖ ≤ A * B ^ i := by
    intro i hi x
    have hiMem : i ∈ Finset.range 7 := by
      simp only [Finset.mem_range]
      omega
    have hCle : C i ≤ C₆ := by
      dsimp [C₆]
      exact Finset.single_le_sum (fun k hk => (hC k).le) hiMem
    have hEq : iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x =
        dfiMixedDeriv i 0
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C i * qQ⁻¹ * B ^ (i + 0) := by
        simpa only [qQ, B] using
          hBound i a b q ha hb hq hqQ h x y
      _ ≤ C₆ * qQ⁻¹ * B ^ i := by
        simp only [add_zero]
        gcongr
      _ = A * B ^ i := rfl
  have hMellin :=
    (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
      |>.mellin_threeQuarter_line_bound_of_physical_profile hA hB hDeriv u
  simpa only [A, B, C₆] using hMellin

/-- Source-uniform arbitrary-line Mellin bound for the first-variable
equation-(23) slice.  Taking `σ = -1/2-k` is the repeated-contour-shift
input that makes the complement of DFI's range (29) arbitrarily small. -/
theorem exists_dfiEquation28_xSlice_mellin_line_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y u : ℝ),
        let C₆ := ∑ i ∈ Finset.range 7, C i
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * X / a) (X / a)⁻¹)
        (1 + |u|) ^ 6 *
            ‖mellin
              (fun x => dfiEquation23Weight w
                (dfiLocalizedWeight f φ h) a b h q x y)
              ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ 6 *
            (64 * ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
              (D ^ |σ| * A +
                D ^ |σ| * (A * (|σ| + 6 + D * B) ^ 6))) := by
  choose C hC hBound using fun i =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ i 0
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y u
  dsimp only
  let C₆ : ℝ := ∑ i ∈ Finset.range 7, C i
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := C₆ * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hC₆ : 0 < C₆ := by
    dsimp [C₆]
    exact Finset.sum_pos (fun i hi => hC i) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hDeriv : ∀ i ≤ 6, ∀ x : ℝ,
      ‖iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x‖ ≤ A * B ^ i := by
    intro i hi x
    have hiMem : i ∈ Finset.range 7 := by
      simp only [Finset.mem_range]
      omega
    have hCle : C i ≤ C₆ := by
      dsimp [C₆]
      exact Finset.single_le_sum (fun k hk => (hC k).le) hiMem
    have hEq : iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x =
        dfiMixedDeriv i 0
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C i * qQ⁻¹ * B ^ (i + 0) := by
        simpa only [qQ, B] using
          hBound i a b q ha hb hq hqQ h x y
      _ ≤ C₆ * qQ⁻¹ * B ^ i := by
        simp only [add_zero]
        gcongr
      _ = A * B ^ i := rfl
  have hMellin :=
    (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
      |>.mellin_line_bound_of_physical_profile σ hA hB hDeriv u
  simpa only [A, B, C₆] using hMellin

/-- All-orders, source-uniform Mellin bound for the second-variable slice
of DFI (23).  The constants are chosen before every arithmetic parameter. -/
theorem exists_dfiEquation28_ySlice_mellin_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x u : ℝ),
        let Csum := ∑ j ∈ Finset.range (p + 1), C j
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * Y / b) (Y / b)⁻¹)
        (1 + |u|) ^ p *
            ‖mellin
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x)
              ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ p *
            ((2 : ℝ) ^ p *
              ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
              (D ^ |σ| * A +
                D ^ |σ| * (A * (|σ| + (p : ℝ) + D * B) ^ p))) := by
  choose C hC hBound using fun j =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ 0 j
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x u
  dsimp only
  let Csum : ℝ := ∑ j ∈ Finset.range (p + 1), C j
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := Csum * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun j hj => hC j) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hDeriv : ∀ j ≤ p, ∀ y : ℝ,
      ‖iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y‖ ≤ A * B ^ j := by
    intro j hj y
    have hjMem : j ∈ Finset.range (p + 1) := by
      simp only [Finset.mem_range]
      omega
    have hCle : C j ≤ Csum := by
      dsimp [Csum]
      exact Finset.single_le_sum (fun k hk => (hC k).le) hjMem
    have hEq : iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y =
        dfiMixedDeriv 0 j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C j * qQ⁻¹ * B ^ (0 + j) := by
        simpa only [qQ, B] using
          hBound j a b q ha hb hq hqQ h x y
      _ ≤ Csum * qQ⁻¹ * B ^ j := by
        simp only [zero_add]
        gcongr
      _ = A * B ^ j := rfl
  have hMellin :=
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
      |>.mellin_line_bound_of_physical_profile_order σ p hA hB hDeriv u
  simpa only [A, B, Csum] using hMellin

/-- Sign-sensitive all-orders bound for a second-variable source slice on a
nonpositive Mellin line. -/
theorem exists_dfiEquation28_ySlice_mellin_nonpos_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x u : ℝ),
        let Csum := ∑ j ∈ Finset.range (p + 1), C j
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        (1 + |u|) ^ p *
            ‖mellin
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x)
              ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ p *
            ((2 : ℝ) ^ p *
              ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
              ((Y / b) ^ σ * A +
                (Y / b) ^ σ *
                  (A * (|σ| + (p : ℝ) + (2 * Y / b) * B) ^ p))) := by
  choose C hC hBound using fun j =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ 0 j
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x u
  dsimp only
  let Csum : ℝ := ∑ j ∈ Finset.range (p + 1), C j
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := Csum * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun j _hj => hC j) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hDeriv : ∀ j ≤ p, ∀ y : ℝ,
      ‖iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y‖ ≤ A * B ^ j := by
    intro j hj y
    have hjMem : j ∈ Finset.range (p + 1) := by
      simp only [Finset.mem_range]
      omega
    have hCle : C j ≤ Csum := by
      dsimp [Csum]
      exact Finset.single_le_sum (fun k _hk => (hC k).le) hjMem
    have hEq : iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y =
        dfiMixedDeriv 0 j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C j * qQ⁻¹ * B ^ (0 + j) := by
        simpa only [qQ, B] using
          hBound j a b q ha hb hq hqQ h x y
      _ ≤ Csum * qQ⁻¹ * B ^ j := by
        simp only [zero_add]
        gcongr
      _ = A * B ^ j := rfl
  have hMellin :=
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
      |>.mellin_line_bound_of_physical_profile_order_of_nonpos
        σ p hσ hA hB hDeriv u
  simpa only [A, B, Csum] using hMellin

/-- All-orders, source-uniform Mellin bound for the first-variable slice
of DFI (23). -/
theorem exists_dfiEquation28_xSlice_mellin_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (σ : ℝ) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y u : ℝ),
        let Csum := ∑ i ∈ Finset.range (p + 1), C i
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * X / a) (X / a)⁻¹)
        (1 + |u|) ^ p *
            ‖mellin
              (fun x => dfiEquation23Weight w
                (dfiLocalizedWeight f φ h) a b h q x y)
              ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ p *
            ((2 : ℝ) ^ p *
              ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
              (D ^ |σ| * A +
                D ^ |σ| * (A * (|σ| + (p : ℝ) + D * B) ^ p))) := by
  choose C hC hBound using fun i =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ i 0
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y u
  dsimp only
  let Csum : ℝ := ∑ i ∈ Finset.range (p + 1), C i
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := Csum * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun i hi => hC i) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hDeriv : ∀ i ≤ p, ∀ x : ℝ,
      ‖iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x‖ ≤ A * B ^ i := by
    intro i hi x
    have hiMem : i ∈ Finset.range (p + 1) := by
      simp only [Finset.mem_range]
      omega
    have hCle : C i ≤ Csum := by
      dsimp [Csum]
      exact Finset.single_le_sum (fun k hk => (hC k).le) hiMem
    have hEq : iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x =
        dfiMixedDeriv i 0
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C i * qQ⁻¹ * B ^ (i + 0) := by
        simpa only [qQ, B] using
          hBound i a b q ha hb hq hqQ h x y
      _ ≤ Csum * qQ⁻¹ * B ^ i := by
        simp only [add_zero]
        gcongr
      _ = A * B ^ i := rfl
  have hMellin :=
    (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
      |>.mellin_line_bound_of_physical_profile_order σ p hA hB hDeriv u
  simpa only [A, B, Csum] using hMellin

/-- Sign-sensitive all-orders bound for a first-variable source slice on a
nonpositive Mellin line. -/
theorem exists_dfiEquation28_xSlice_mellin_nonpos_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y u : ℝ),
        let Csum := ∑ i ∈ Finset.range (p + 1), C i
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        (1 + |u|) ^ p *
            ‖mellin
              (fun x => dfiEquation23Weight w
                (dfiLocalizedWeight f φ h) a b h q x y)
              ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ p *
            ((2 : ℝ) ^ p *
              ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
              ((X / a) ^ σ * A +
                (X / a) ^ σ *
                  (A * (|σ| + (p : ℝ) + (2 * X / a) * B) ^ p))) := by
  choose C hC hBound using fun i =>
    dfiEquation28_uniform hf hbox hφ hscale w hUQ i 0
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y u
  dsimp only
  let Csum : ℝ := ∑ i ∈ Finset.range (p + 1), C i
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := Csum * qQ⁻¹
  let B : ℝ := ((a : ℝ) * (b : ℝ)) / qQ
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun i _hi => hC i) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hDeriv : ∀ i ≤ p, ∀ x : ℝ,
      ‖iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x‖ ≤ A * B ^ i := by
    intro i hi x
    have hiMem : i ∈ Finset.range (p + 1) := by
      simp only [Finset.mem_range]
      omega
    have hCle : C i ≤ Csum := by
      dsimp [Csum]
      exact Finset.single_le_sum (fun k _hk => (hC k).le) hiMem
    have hEq : iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x =
        dfiMixedDeriv i 0
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C i * qQ⁻¹ * B ^ (i + 0) := by
        simpa only [qQ, B] using
          hBound i a b q ha hb hq hqQ h x y
      _ ≤ Csum * qQ⁻¹ * B ^ i := by
        simp only [add_zero]
        gcongr
      _ = A * B ^ i := rfl
  have hMellin :=
    (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
      |>.mellin_line_bound_of_physical_profile_order_of_nonpos
        σ p hσ hA hB hDeriv u
  simpa only [A, B, Csum] using hMellin

/-- Variable-separated version of the preceding first-variable estimate.
The derivative scale is `a/(qQ)`, exactly as obtained before the coarsening
in DFI (28); this is the form used in the equation-(29) truncation. -/
theorem exists_dfiEquation28_xSlice_mellin_nonpos_separated_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y u : ℝ),
        let Csum := ∑ i ∈ Finset.range (p + 1), C i
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := (a : ℝ) / qQ
        (1 + |u|) ^ p *
            ‖mellin
              (fun x => dfiEquation23Weight w
                (dfiLocalizedWeight f φ h) a b h q x y)
              ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ p *
            ((2 : ℝ) ^ p *
              ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
              ((X / a) ^ σ * A +
                (X / a) ^ σ *
                  (A * (|σ| + (p : ℝ) + (2 * X / a) * B) ^ p))) := by
  choose C hC hBound using fun i =>
    dfiEquation28_separated_uniform hf hbox hφ hscale w hUQ i 0
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y u
  dsimp only
  let Csum : ℝ := ∑ i ∈ Finset.range (p + 1), C i
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := Csum * qQ⁻¹
  let B : ℝ := (a : ℝ) / qQ
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun i _hi => hC i) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hDeriv : ∀ i ≤ p, ∀ x : ℝ,
      ‖iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x‖ ≤ A * B ^ i := by
    intro i hi x
    have hiMem : i ∈ Finset.range (p + 1) := by
      simp only [Finset.mem_range]
      omega
    have hCle : C i ≤ Csum := by
      dsimp [Csum]
      exact Finset.single_le_sum (fun k _hk => (hC k).le) hiMem
    have hEq : iteratedDeriv i
        (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x =
        dfiMixedDeriv i 0
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C i * qQ⁻¹ * B ^ i * ((b : ℝ) / qQ) ^ 0 := by
        simpa only [qQ, B] using
          hBound i a b q ha hb hq hqQ h x y
      _ = C i * qQ⁻¹ * B ^ i := by ring
      _ ≤ Csum * qQ⁻¹ * B ^ i := by gcongr
      _ = A * B ^ i := rfl
  have hMellin :=
    (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
      |>.mellin_line_bound_of_physical_profile_order_of_nonpos
        σ p hσ hA hB hDeriv u
  simpa only [A, B, Csum] using hMellin

/-- Variable-separated second-variable companion used in DFI (29). -/
theorem exists_dfiEquation28_ySlice_mellin_nonpos_separated_line_bound_order
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x u : ℝ),
        let Csum := ∑ j ∈ Finset.range (p + 1), C j
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := (b : ℝ) / qQ
        (1 + |u|) ^ p *
            ‖mellin
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x)
              ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ p *
            ((2 : ℝ) ^ p *
              ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
              ((Y / b) ^ σ * A +
                (Y / b) ^ σ *
                  (A * (|σ| + (p : ℝ) + (2 * Y / b) * B) ^ p))) := by
  choose C hC hBound using fun j =>
    dfiEquation28_separated_uniform hf hbox hφ hscale w hUQ 0 j
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x u
  dsimp only
  let Csum : ℝ := ∑ j ∈ Finset.range (p + 1), C j
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := Csum * qQ⁻¹
  let B : ℝ := (b : ℝ) / qQ
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun j _hj => hC j) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hDeriv : ∀ j ≤ p, ∀ y : ℝ,
      ‖iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y‖ ≤ A * B ^ j := by
    intro j hj y
    have hjMem : j ∈ Finset.range (p + 1) := by
      simp only [Finset.mem_range]
      omega
    have hCle : C j ≤ Csum := by
      dsimp [Csum]
      exact Finset.single_le_sum (fun k _hk => (hC k).le) hjMem
    have hEq : iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y =
        dfiMixedDeriv 0 j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C j * qQ⁻¹ * ((a : ℝ) / qQ) ^ 0 * B ^ j := by
        simpa only [qQ, B] using
          hBound j a b q ha hb hq hqQ h x y
      _ = C j * qQ⁻¹ * B ^ j := by ring
      _ ≤ Csum * qQ⁻¹ * B ^ j := by gcongr
      _ = A * B ^ j := rfl
  have hMellin :=
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
      |>.mellin_line_bound_of_physical_profile_order_of_nonpos
        σ p hσ hA hB hDeriv u
  simpa only [A, B, Csum] using hMellin

/-- Full source-uniform left-shifted transform bound for the second variable
in DFI (29).  This is the rapid-decay complement to the retained range. -/
theorem exists_dfiEquation29_ySlice_decay_transform_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (r : ℕ) (_hr : NeZero r) (n : ℕ), 0 < n →
        let p := 2 * (k + 1) + 4
        let Csum := ∑ j ∈ Finset.range (p + 1), C j
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * Y / b) (Y / b)⁻¹)
        let M := (1 + 2 * Real.pi) ^ p *
          ((2 : ℝ) ^ p *
            ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
            (D ^ |-(1 / 2 : ℝ) - k| * A +
              D ^ |-(1 / 2 : ℝ) - k| *
                (A * (|-(1 / 2 : ℝ) - k| + (p : ℝ) + D * B) ^ p)))
        ‖dfiEquation29InitialTransform r branch
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b h q x) n‖ ≤
          K * (r : ℝ) ^ (2 + 2 * (k : ℝ)) * M *
            (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  obtain ⟨K, hK, hTransform⟩ :=
    exists_dfiEquation29InitialTransform_decay_constant k branch
  obtain ⟨C, hC, hMellin⟩ :=
    exists_dfiEquation28_ySlice_mellin_line_bound_order
      hf hbox hφ hscale w hUQ (-(1 / 2 : ℝ) - k) (2 * (k + 1) + 4)
  refine ⟨K, hK, C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x r hr n hn
  dsimp only
  exact hTransform
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
    (hMellin a b q ha hb hq hqQ h x) r hr n hn

/-- Full source-uniform left-shifted transform bound for the first variable
in DFI (29). -/
theorem exists_dfiEquation29_xSlice_decay_transform_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (k : ℕ) (branch : DFIVoronoiDualBranch) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (r : ℕ) (_hr : NeZero r) (n : ℕ), 0 < n →
        let p := 2 * (k + 1) + 4
        let Csum := ∑ i ∈ Finset.range (p + 1), C i
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * X / a) (X / a)⁻¹)
        let M := (1 + 2 * Real.pi) ^ p *
          ((2 : ℝ) ^ p *
            ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
            (D ^ |-(1 / 2 : ℝ) - k| * A +
              D ^ |-(1 / 2 : ℝ) - k| *
                (A * (|-(1 / 2 : ℝ) - k| + (p : ℝ) + D * B) ^ p)))
        ‖dfiEquation29InitialTransform r branch
            (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b h q x y) n‖ ≤
          K * (r : ℝ) ^ (2 + 2 * (k : ℝ)) * M *
            (n : ℝ) ^ (-(3 / 2 : ℝ) - k) := by
  obtain ⟨K, hK, hTransform⟩ :=
    exists_dfiEquation29InitialTransform_decay_constant k branch
  obtain ⟨C, hC, hMellin⟩ :=
    exists_dfiEquation28_xSlice_mellin_line_bound_order
      hf hbox hφ hscale w hUQ (-(1 / 2 : ℝ) - k) (2 * (k + 1) + 4)
  refine ⟨K, hK, C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y r hr n hn
  dsimp only
  exact hTransform
    (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
    (hMellin a b q ha hb hq hqQ h y) r hr n hn

/-- Source-uniform summed complement of the second-variable retained window
in DFI (29). -/
theorem exists_dfiEquation29_ySlice_tail_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (r L : ℕ) (_hr : NeZero r), 0 < L →
        let p := 2 * (k + 1) + 4
        let Csum := ∑ j ∈ Finset.range (p + 1), C j
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * Y / b) (Y / b)⁻¹)
        let M := (1 + 2 * Real.pi) ^ p *
          ((2 : ℝ) ^ p *
            ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
            (D ^ |-(1 / 2 : ℝ) - k| * A +
              D ^ |-(1 / 2 : ℝ) - k| *
                (A * (|-(1 / 2 : ℝ) - k| + (p : ℝ) + D * B) ^ p)))
        ∑' j : ℕ, ‖dfiVoronoiDualTerm r branch
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b h q x) (L + (j + 1))‖ ≤
          K * (r : ℝ) ^ (2 + 2 * (k : ℝ)) * M *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨K, hK, hTail⟩ :=
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  obtain ⟨C, hC, hMellin⟩ :=
    exists_dfiEquation28_ySlice_mellin_line_bound_order
      hf hbox hφ hscale w hUQ (-(1 / 2 : ℝ) - k) (2 * (k + 1) + 4)
  refine ⟨K, hK, C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x r L hr hL
  let M : ℝ := (1 + 2 * Real.pi) ^ (2 * (k + 1) + 4) *
    ((2 : ℝ) ^ (2 * (k + 1) + 4) *
      ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
      ((max 1 (max (2 * Y / b) (Y / b)⁻¹)) ^ |-(1 / 2 : ℝ) - k| *
          ((∑ j ∈ Finset.range (2 * (k + 1) + 4 + 1), C j) *
            ((q : ℝ) * Q)⁻¹) +
        (max 1 (max (2 * Y / b) (Y / b)⁻¹)) ^ |-(1 / 2 : ℝ) - k| *
          (((∑ j ∈ Finset.range (2 * (k + 1) + 4 + 1), C j) *
              ((q : ℝ) * Q)⁻¹) *
            (|-(1 / 2 : ℝ) - k| + ((2 * (k + 1) + 4 : ℕ) : ℝ) +
              (max 1 (max (2 * Y / b) (Y / b)⁻¹)) *
                (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q))) ^
                  (2 * (k + 1) + 4))))
  have hMellin' := hMellin a b q ha hb hq hqQ h x
  have hM : 0 ≤ M := by
    have hz := hMellin' 0
    exact (norm_nonneg _).trans
      (by simpa [M] using hz)
  simpa [M] using hTail
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
    hM hMellin' r L hr hL

/-- Source-uniform summed complement of the first-variable retained window
in DFI (29). -/
theorem exists_dfiEquation29_xSlice_tail_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (k : ℕ) (hk : 0 < k) (branch : DFIVoronoiDualBranch) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (r L : ℕ) (_hr : NeZero r), 0 < L →
        let p := 2 * (k + 1) + 4
        let Csum := ∑ i ∈ Finset.range (p + 1), C i
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (max (2 * X / a) (X / a)⁻¹)
        let M := (1 + 2 * Real.pi) ^ p *
          ((2 : ℝ) ^ p *
            ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
            (D ^ |-(1 / 2 : ℝ) - k| * A +
              D ^ |-(1 / 2 : ℝ) - k| *
                (A * (|-(1 / 2 : ℝ) - k| + (p : ℝ) + D * B) ^ p)))
        ∑' j : ℕ, ‖dfiVoronoiDualTerm r branch
            (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b h q x y) (L + (j + 1))‖ ≤
          K * (r : ℝ) ^ (2 + 2 * (k : ℝ)) * M *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨K, hK, hTail⟩ :=
    exists_dfiVoronoiDualTerm_tail_decay_constant k hk branch
  obtain ⟨C, hC, hMellin⟩ :=
    exists_dfiEquation28_xSlice_mellin_line_bound_order
      hf hbox hφ hscale w hUQ (-(1 / 2 : ℝ) - k) (2 * (k + 1) + 4)
  refine ⟨K, hK, C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y r L hr hL
  let M : ℝ := (1 + 2 * Real.pi) ^ (2 * (k + 1) + 4) *
    ((2 : ℝ) ^ (2 * (k + 1) + 4) *
      ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
      ((max 1 (max (2 * X / a) (X / a)⁻¹)) ^ |-(1 / 2 : ℝ) - k| *
          ((∑ i ∈ Finset.range (2 * (k + 1) + 4 + 1), C i) *
            ((q : ℝ) * Q)⁻¹) +
        (max 1 (max (2 * X / a) (X / a)⁻¹)) ^ |-(1 / 2 : ℝ) - k| *
          (((∑ i ∈ Finset.range (2 * (k + 1) + 4 + 1), C i) *
              ((q : ℝ) * Q)⁻¹) *
            (|-(1 / 2 : ℝ) - k| + ((2 * (k + 1) + 4 : ℕ) : ℝ) +
              (max 1 (max (2 * X / a) (X / a)⁻¹)) *
                (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q))) ^
                  (2 * (k + 1) + 4))))
  have hMellin' := hMellin a b q ha hb hq hqQ h y
  have hM : 0 ≤ M := by
    have hz := hMellin' 0
    exact (norm_nonneg _).trans
      (by simpa [M] using hz)
  simpa [M] using hTail
    (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
    hM hMellin' r L hr hL

/-- DFI (29), retained second-variable transform with all source parameters
and the universal contour constant quantified in the source order. -/
theorem exists_dfiEquation29_ySlice_threeQuarter_transform_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (branch : DFIVoronoiDualBranch) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ)
        (r : ℕ) (_hr : NeZero r) (n : ℕ), 0 < n →
        let C₆ := ∑ j ∈ Finset.range 7, C j
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * Y / b)
        ‖dfiEquation29InitialTransform r branch
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b h q x) n‖ ≤
          K * (r : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((1 + 2 * Real.pi) ^ 6 *
              (64 * ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
                (D * A + D * (1024 * A * (1 + D * B) ^ 6)))) *
            (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨K, hK, hUniversal⟩ :=
    exists_dfiEquation29InitialTransform_threeQuarter_constant branch
  obtain ⟨C, hC, hMellin⟩ :=
    exists_dfiEquation28_ySlice_mellin_threeQuarter_bound
      hf hbox hφ hscale w hUQ
  refine ⟨K, hK, C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x r hr n hn
  dsimp only
  exact hUniversal
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
    (hMellin a b q ha hb hq hqQ h x) r hr n hn

/-- First-variable counterpart of the source-uniform retained transform
bound in DFI (29). -/
theorem exists_dfiEquation29_xSlice_threeQuarter_transform_bound
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (branch : DFIVoronoiDualBranch) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ)
        (r : ℕ) (_hr : NeZero r) (m : ℕ), 0 < m →
        let C₆ := ∑ i ∈ Finset.range 7, C i
        let qQ := (q : ℝ) * Q
        let A := C₆ * qQ⁻¹
        let B := ((a : ℝ) * (b : ℝ)) / qQ
        let D := max 1 (2 * X / a)
        ‖dfiEquation29InitialTransform r branch
            (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b h q x y) m‖ ≤
          K * (r : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((1 + 2 * Real.pi) ^ 6 *
              (64 * ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
                (D * A + D * (1024 * A * (1 + D * B) ^ 6)))) *
            (m : ℝ) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨K, hK, hUniversal⟩ :=
    exists_dfiEquation29InitialTransform_threeQuarter_constant branch
  obtain ⟨C, hC, hMellin⟩ :=
    exists_dfiEquation28_xSlice_mellin_threeQuarter_bound
      hf hbox hφ hscale w hUQ
  refine ⟨K, hK, C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y r hr m hm
  dsimp only
  exact hUniversal
    (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
    (hMellin a b q ha hb hq hqQ h y) r hr m hm

/-- Profile-uniform first-variable Mellin line bound used in equation (29). -/
theorem exists_dfiEquation28_xSlice_mellin_nonpos_separated_line_bound_order_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ i, 0 < C i) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y u : ℝ),
        let Csum := ∑ i ∈ Finset.range (p + 1), C i
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := (a : ℝ) / qQ
        (1 + |u|) ^ p *
            ‖mellin
              (fun x ↦ dfiEquation23Weight w
                (dfiLocalizedWeight f φ h) a b h q x y)
              ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ p *
            ((2 : ℝ) ^ p *
              ((-Real.log (X / a)) - (-Real.log (2 * X / a))) *
              ((X / a) ^ σ * A +
                (X / a) ^ σ *
                  (A * (|σ| + (p : ℝ) + (2 * X / a) * B) ^ p))) := by
  choose C hC hBound using fun i ↦
    dfiEquation28_separated_uniform_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hUQ i 0
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y u
  dsimp only
  let Csum : ℝ := ∑ i ∈ Finset.range (p + 1), C i
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := Csum * qQ⁻¹
  let B : ℝ := (a : ℝ) / qQ
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun i _hi ↦ hC i) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hDeriv : ∀ i ≤ p, ∀ x : ℝ,
      ‖iteratedDeriv i
        (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x‖ ≤ A * B ^ i := by
    intro i hi x
    have hiMem : i ∈ Finset.range (p + 1) := by simp only [Finset.mem_range]; omega
    have hCle : C i ≤ Csum := by
      dsimp [Csum]
      exact Finset.single_le_sum (fun k _hk ↦ (hC k).le) hiMem
    have hEq : iteratedDeriv i
        (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x y) x =
        dfiMixedDeriv i 0
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C i * qQ⁻¹ * B ^ i * ((b : ℝ) / qQ) ^ 0 := by
        simpa only [qQ, B] using hBound i a b q ha hb hq hqQ h x y
      _ = C i * qQ⁻¹ * B ^ i := by ring
      _ ≤ Csum * qQ⁻¹ * B ^ i := by gcongr
      _ = A * B ^ i := rfl
  have hMellin :=
    (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
      |>.mellin_line_bound_of_physical_profile_order_of_nonpos
        σ p hσ hA hB hDeriv u
  simpa only [A, B, Csum] using hMellin

/-- Profile-uniform second-variable companion of the preceding theorem. -/
theorem exists_dfiEquation28_ySlice_mellin_nonpos_separated_line_bound_order_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (σ : ℝ) (hσ : σ ≤ 0) (p : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x u : ℝ),
        let Csum := ∑ j ∈ Finset.range (p + 1), C j
        let qQ := (q : ℝ) * Q
        let A := Csum * qQ⁻¹
        let B := (b : ℝ) / qQ
        (1 + |u|) ^ p *
            ‖mellin
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
                a b h q x)
              ((σ : ℂ) + (u : ℂ) * I)‖ ≤
          (1 + 2 * Real.pi) ^ p *
            ((2 : ℝ) ^ p *
              ((-Real.log (Y / b)) - (-Real.log (2 * Y / b))) *
              ((Y / b) ^ σ * A +
                (Y / b) ^ σ *
                  (A * (|σ| + (p : ℝ) + (2 * Y / b) * B) ^ p))) := by
  choose C hC hBound using fun j ↦
    dfiEquation28_separated_uniform_of_profiles
      hf hfC hbox hφ hφC hscale w hwC hUQ 0 j
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x u
  dsimp only
  let Csum : ℝ := ∑ j ∈ Finset.range (p + 1), C j
  let qQ : ℝ := (q : ℝ) * Q
  let A : ℝ := Csum * qQ⁻¹
  let B : ℝ := (b : ℝ) / qQ
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun j _hj ↦ hC j) ⟨0, by simp⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQPos : 0 < qQ := by
    dsimp [qQ]
    exact mul_pos hqR w.Q_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hDeriv : ∀ j ≤ p, ∀ y : ℝ,
      ‖iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y‖ ≤ A * B ^ j := by
    intro j hj y
    have hjMem : j ∈ Finset.range (p + 1) := by simp only [Finset.mem_range]; omega
    have hCle : C j ≤ Csum := by
      dsimp [Csum]
      exact Finset.single_le_sum (fun k _hk ↦ (hC k).le) hjMem
    have hEq : iteratedDeriv j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
          a b h q x) y =
        dfiMixedDeriv 0 j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q) x y := by
      simp [dfiMixedDeriv]
    rw [hEq]
    calc
      _ ≤ C j * qQ⁻¹ * ((a : ℝ) / qQ) ^ 0 * B ^ j := by
        simpa only [qQ, B] using hBound j a b q ha hb hq hqQ h x y
      _ = C j * qQ⁻¹ * B ^ j := by ring
      _ ≤ Csum * qQ⁻¹ * B ^ j := by gcongr
      _ = A * B ^ j := rfl
  have hMellin :=
    (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
      |>.mellin_line_bound_of_physical_profile_order_of_nonpos
        σ p hσ hA hB hDeriv u
  simpa only [A, B, Csum] using hMellin

end RiemannZeta.GuthMaynard
