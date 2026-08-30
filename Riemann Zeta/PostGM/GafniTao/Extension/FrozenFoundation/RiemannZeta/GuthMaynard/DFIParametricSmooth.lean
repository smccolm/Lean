import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import RiemannZeta.GuthMaynard.DFIEquation23Weight

/-!
# Smooth dependence of a compact parametric integral

DFI equation (23) applies Voronoi in one variable and then in the other.
The missing analytic bridge is that integration in one compact variable
preserves smooth dependence on the remaining variable.  This file proves
that fact directly from Mathlib's dominated differentiation theorem.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ContDiff Topology Interval

namespace RiemannZeta.GuthMaynard

theorem hasDerivAt_dfiPartialX_slice (n : ℕ) {F : ℝ → ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (x y : ℝ) :
    HasDerivAt (fun u => dfiPartialX n (Function.uncurry F) (u, y))
      (dfiPartialX (n + 1) (Function.uncurry F) (x, y)) x := by
  have hsmooth : ContDiff ℝ ∞ (fun u : ℝ => F u y) :=
    hF.comp (by fun_prop : ContDiff ℝ ∞ (fun u : ℝ => (u, y)))
  have hnlt : (n : ℕ∞ω) < ∞ := by
    exact_mod_cast ENat.coe_lt_top n
  have hdifferentiable : Differentiable ℝ (iteratedDeriv n (fun u : ℝ => F u y)) :=
    hsmooth.differentiable_iteratedDeriv n hnlt
  have hderiv : HasDerivAt (iteratedDeriv n (fun u : ℝ => F u y))
      (deriv (iteratedDeriv n (fun u : ℝ => F u y)) x) x :=
    hdifferentiable.differentiableAt.hasDerivAt
  have hfun : (fun u => dfiPartialX n (Function.uncurry F) (u, y)) =
      iteratedDeriv n (fun u : ℝ => F u y) := by
    funext u
    exact dfiPartialX_apply n hF u y
  have hval : dfiPartialX (n + 1) (Function.uncurry F) (x, y) =
      iteratedDeriv (n + 1) (fun u : ℝ => F u y) x :=
    dfiPartialX_apply (n + 1) hF x y
  rw [hfun, hval, iteratedDeriv_succ]
  exact hderiv

/-- The `n`th first-coordinate derivative integrated over a compact interval
in the second coordinate. -/
noncomputable def dfiPartialIntegral (n : ℕ) (A B : ℝ)
    (F : ℝ → ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Set.Icc A B, dfiPartialX n (Function.uncurry F) (x, y)

theorem hasDerivAt_dfiPartialIntegral (n : ℕ) (A B : ℝ)
    {F : ℝ → ℝ → ℂ} (hF : ContDiff ℝ ∞ (Function.uncurry F)) (x₀ : ℝ) :
    HasDerivAt (dfiPartialIntegral n A B F)
      (dfiPartialIntegral (n + 1) A B F x₀) x₀ := by
  let K : Set (ℝ × ℝ) := Set.Icc (x₀ - 1) (x₀ + 1) ×ˢ Set.Icc A B
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous (dfiPartialX (n + 1) (Function.uncurry F)) :=
    (contDiff_dfiPartialX (n + 1) hF).continuous
  obtain ⟨C, hC⟩ := hK.bddAbove_image hcont.norm.continuousOn
  let bound : ℝ → ℝ := fun _ => max C 0
  have hmeasure : volume (Set.Icc A B) ≠ (⊤ : ENNReal) := measure_Icc_lt_top.ne
  have hbound_int : Integrable bound (volume.restrict (Set.Icc A B)) := by
    exact integrableOn_const hmeasure
  have hslice_cont (u : ℝ) : Continuous
      (fun y => dfiPartialX n (Function.uncurry F) (u, y)) := by
    exact (contDiff_dfiPartialX n hF).continuous.comp (by fun_prop)
  have hslice_int (u : ℝ) :
      Integrable (fun y => dfiPartialX n (Function.uncurry F) (u, y))
        (volume.restrict (Set.Icc A B)) := by
    exact (hslice_cont u).continuousOn.integrableOn_compact isCompact_Icc
  have hderiv_meas : AEStronglyMeasurable
      (fun y => (1 : ℝ →L[ℝ] ℝ).smulRight
        (dfiPartialX (n + 1) (Function.uncurry F) (x₀, y)))
      (volume.restrict (Set.Icc A B)) := by
    fun_prop
  have hmajor : ∀ᵐ y ∂volume.restrict (Set.Icc A B),
      ∀ u ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
        ‖(1 : ℝ →L[ℝ] ℝ).smulRight
          (dfiPartialX (n + 1) (Function.uncurry F) (u, y))‖ ≤ bound y := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with y hy u hu
    have hxy : (u, y) ∈ K := by
      exact ⟨⟨hu.1.le, hu.2.le⟩, hy⟩
    have hleC : ‖dfiPartialX (n + 1) (Function.uncurry F) (u, y)‖ ≤ C :=
      hC ⟨(u, y), hxy, rfl⟩
    have hnorm : ‖(1 : ℝ →L[ℝ] ℝ).smulRight
        (dfiPartialX (n + 1) (Function.uncurry F) (u, y))‖ =
        ‖dfiPartialX (n + 1) (Function.uncurry F) (u, y)‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      simp
    rw [hnorm]
    exact hleC.trans (le_max_left C 0)
  have hdiff : ∀ᵐ y ∂volume.restrict (Set.Icc A B),
      ∀ u ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
        HasFDerivAt (fun v => dfiPartialX n (Function.uncurry F) (v, y))
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (dfiPartialX (n + 1) (Function.uncurry F) (u, y))) u := by
    filter_upwards with y u hu
    exact (hasDerivAt_dfiPartialX_slice n hF u y).hasFDerivAt
  have hmeas : ∀ᶠ u in 𝓝 x₀, AEStronglyMeasurable
      (fun y => dfiPartialX n (Function.uncurry F) (u, y))
      (volume.restrict (Set.Icc A B)) := by
    filter_upwards with u
    exact (hslice_cont u).aestronglyMeasurable
  have hs : Set.Ioo (x₀ - 1) (x₀ + 1) ∈ 𝓝 x₀ := by
    exact Ioo_mem_nhds (by linarith) (by linarith)
  have hfd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Set.Icc A B)) hs hmeas (hslice_int x₀)
    hderiv_meas hmajor hbound_int hdiff
  have hderiv_int : Integrable
      (fun y => (1 : ℝ →L[ℝ] ℝ).smulRight
        (dfiPartialX (n + 1) (Function.uncurry F) (x₀, y)))
      (volume.restrict (Set.Icc A B)) := by
    have hc : Continuous (fun y => (1 : ℝ →L[ℝ] ℝ).smulRight
        (dfiPartialX (n + 1) (Function.uncurry F) (x₀, y))) := by
      fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hd := hfd.hasDerivAt
  rw [ContinuousLinearMap.integral_apply hderiv_int] at hd
  simpa [dfiPartialIntegral] using hd

theorem iteratedDeriv_dfiPartialIntegral (n : ℕ) (A B : ℝ)
    {F : ℝ → ℝ → ℂ} (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    iteratedDeriv n (dfiPartialIntegral 0 A B F) =
      dfiPartialIntegral n A B F := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_dfiPartialIntegral n A B hF x).deriv

/-- Integration over a fixed compact interval preserves smooth dependence on
the first variable. -/
theorem contDiff_integral_Icc_right {A B : ℝ} {F : ℝ → ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun x => ∫ y in Set.Icc A B, F x y) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _hn
  have hzero : (fun x => ∫ y in Set.Icc A B, F x y) =
      dfiPartialIntegral 0 A B F := by
    funext x
    simp [dfiPartialIntegral, dfiPartialX]
  rw [hzero]
  rw [iteratedDeriv_dfiPartialIntegral n A B hF]
  exact fun x => (hasDerivAt_dfiPartialIntegral n A B hF x).differentiableAt

/-- The weighted version needed for the logarithmic main term and the Mellin
kernel.  The fixed weight needs only to be continuous on the compact interval;
all differentiations are in the first variable. -/
noncomputable def dfiWeightedPartialIntegral (n : ℕ) (A B : ℝ)
    (w : ℝ → ℂ) (F : ℝ → ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y in Set.Icc A B, w y * dfiPartialX n (Function.uncurry F) (x, y)

theorem hasDerivAt_dfiWeightedPartialIntegral (n : ℕ) (A B : ℝ)
    {w : ℝ → ℂ} (hw : Continuous w) {F : ℝ → ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (x₀ : ℝ) :
    HasDerivAt (dfiWeightedPartialIntegral n A B w F)
      (dfiWeightedPartialIntegral (n + 1) A B w F x₀) x₀ := by
  let D : ℝ → ℝ → ℂ := fun x y =>
    w y * dfiPartialX (n + 1) (Function.uncurry F) (x, y)
  let K : Set (ℝ × ℝ) := Set.Icc (x₀ - 1) (x₀ + 1) ×ˢ Set.Icc A B
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hD : Continuous (Function.uncurry D) := by
    exact (hw.comp (by fun_prop)).mul
      ((contDiff_dfiPartialX (n + 1) hF).continuous)
  obtain ⟨C, hC⟩ := hK.bddAbove_image hD.norm.continuousOn
  let bound : ℝ → ℝ := fun _ => max C 0
  have hmeasure : volume (Set.Icc A B) ≠ (⊤ : ENNReal) := measure_Icc_lt_top.ne
  have hbound_int : Integrable bound (volume.restrict (Set.Icc A B)) :=
    integrableOn_const hmeasure
  have hslice_cont (u : ℝ) : Continuous
      (fun y => w y * dfiPartialX n (Function.uncurry F) (u, y)) := by
    exact hw.mul ((contDiff_dfiPartialX n hF).continuous.comp (by fun_prop))
  have hslice_int (u : ℝ) : Integrable
      (fun y => w y * dfiPartialX n (Function.uncurry F) (u, y))
      (volume.restrict (Set.Icc A B)) :=
    (hslice_cont u).continuousOn.integrableOn_compact isCompact_Icc
  have hderiv_cont : Continuous (fun y => (1 : ℝ →L[ℝ] ℝ).smulRight (D x₀ y)) := by
    have hDy : Continuous (fun y => D x₀ y) :=
      hD.comp (by fun_prop : Continuous (fun y : ℝ => (x₀, y)))
    let L := ContinuousLinearMap.smulRightL ℝ ℝ ℂ (1 : ℝ →L[ℝ] ℝ)
    simpa [L] using L.continuous.comp hDy
  have hderiv_meas : AEStronglyMeasurable
      (fun y => (1 : ℝ →L[ℝ] ℝ).smulRight (D x₀ y))
      (volume.restrict (Set.Icc A B)) := hderiv_cont.aestronglyMeasurable
  have hmajor : ∀ᵐ y ∂volume.restrict (Set.Icc A B),
      ∀ u ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
        ‖(1 : ℝ →L[ℝ] ℝ).smulRight (D u y)‖ ≤ bound y := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with y hy u hu
    have hxy : (u, y) ∈ K := ⟨⟨hu.1.le, hu.2.le⟩, hy⟩
    have hleC : ‖D u y‖ ≤ C := hC ⟨(u, y), hxy, rfl⟩
    have hnorm : ‖(1 : ℝ →L[ℝ] ℝ).smulRight (D u y)‖ = ‖D u y‖ := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      simp
    rw [hnorm]
    exact hleC.trans (le_max_left C 0)
  have hdiff : ∀ᵐ y ∂volume.restrict (Set.Icc A B),
      ∀ u ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
        HasFDerivAt
          (fun v => w y * dfiPartialX n (Function.uncurry F) (v, y))
          ((1 : ℝ →L[ℝ] ℝ).smulRight (D u y)) u := by
    filter_upwards with y u hu
    exact ((hasDerivAt_dfiPartialX_slice n hF u y).const_mul (w y)).hasFDerivAt
  have hmeas : ∀ᶠ u in 𝓝 x₀, AEStronglyMeasurable
      (fun y => w y * dfiPartialX n (Function.uncurry F) (u, y))
      (volume.restrict (Set.Icc A B)) := by
    filter_upwards with u
    exact (hslice_cont u).aestronglyMeasurable
  have hs : Set.Ioo (x₀ - 1) (x₀ + 1) ∈ 𝓝 x₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hfd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Set.Icc A B)) hs hmeas (hslice_int x₀)
    hderiv_meas hmajor hbound_int hdiff
  have hderiv_int : Integrable
      (fun y => (1 : ℝ →L[ℝ] ℝ).smulRight (D x₀ y))
      (volume.restrict (Set.Icc A B)) :=
    hderiv_cont.continuousOn.integrableOn_compact isCompact_Icc
  have hd := hfd.hasDerivAt
  rw [ContinuousLinearMap.integral_apply hderiv_int] at hd
  simpa [dfiWeightedPartialIntegral, D] using hd

theorem iteratedDeriv_dfiWeightedPartialIntegral (n : ℕ) (A B : ℝ)
    {w : ℝ → ℂ} (hw : Continuous w) {F : ℝ → ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    iteratedDeriv n (dfiWeightedPartialIntegral 0 A B w F) =
      dfiWeightedPartialIntegral n A B w F := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_dfiWeightedPartialIntegral n A B hw hF x).deriv

theorem contDiff_integral_Icc_right_mul_left {A B : ℝ} {w : ℝ → ℂ}
    (hw : Continuous w) {F : ℝ → ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun x => ∫ y in Set.Icc A B, w y * F x y) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro n _hn
  have hzero : (fun x => ∫ y in Set.Icc A B, w y * F x y) =
      dfiWeightedPartialIntegral 0 A B w F := by
    funext x
    simp [dfiWeightedPartialIntegral, dfiPartialX]
  rw [hzero, iteratedDeriv_dfiWeightedPartialIntegral n A B hw hF]
  exact fun x =>
    (hasDerivAt_dfiWeightedPartialIntegral n A B hw hF x).differentiableAt

end RiemannZeta.GuthMaynard
