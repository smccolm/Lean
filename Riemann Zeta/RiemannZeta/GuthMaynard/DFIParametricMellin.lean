import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ParametricIntegral
import RiemannZeta.GuthMaynard.DFIParametricSmooth
import RiemannZeta.GuthMaynard.DFIProposition1Native

/-!
# Uniform parametric Mellin decay for the DFI double Voronoi formula

This module supplies the missing analytic bridge between the grouped form of
DFI equation (23) and the nine separate branches in equation (24).  It treats
the first variable as a smooth parameter and proves bounds uniform in that
parameter before any infinite sum or integral is interchanged.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology
open Classical

namespace RiemannZeta.GuthMaynard

/-- The logarithmic Mellin kernel of a two-variable source weight, with the
first variable retained as a parameter. -/
noncomputable def dfiParametricMellinKernel
    (σ : ℝ) (E : ℝ → ℝ → ℂ) (x u : ℝ) : ℂ :=
  (Real.exp (-σ * u) : ℂ) * E x (Real.exp (-u))

theorem contDiff_uncurry_dfiParametricMellinKernel
    {σ : ℝ} {E : ℝ → ℝ → ℂ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E)) :
    ContDiff ℝ ∞
      (Function.uncurry (dfiParametricMellinKernel σ E)) := by
  unfold dfiParametricMellinKernel Function.uncurry
  have hWeight : ContDiff ℝ ∞
      (fun p : ℝ × ℝ ↦ (Real.exp (-σ * p.2) : ℂ)) := by
    have hReal : ContDiff ℝ ∞
        (fun p : ℝ × ℝ ↦ Real.exp (-σ * p.2)) := by
      exact Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd)
    exact Complex.ofRealCLM.contDiff.comp hReal
  have hArg : ContDiff ℝ ∞
      (fun p : ℝ × ℝ ↦ (p.1, Real.exp (-p.2))) := by
    fun_prop
  exact hWeight.mul (hE.comp hArg)

theorem support_uncurry_dfiParametricMellinKernel_subset
    {σ A B C D : ℝ} {E : ℝ → ℝ → ℂ}
    (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) :
    Function.support
        (Function.uncurry (dfiParametricMellinKernel σ E)) ⊆
      Set.Icc A B ×ˢ Set.Icc (-Real.log D) (-Real.log C) := by
  intro p hp
  have hEne : E p.1 (Real.exp (-p.2)) ≠ 0 := by
    intro hz
    exact hp (by simp [Function.uncurry, dfiParametricMellinKernel, hz])
  have hmem := hSupport (show
    (p.1, Real.exp (-p.2)) ∈ Function.support (Function.uncurry E) by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hEne)
  have hD : 0 < D := hC.trans_le (hmem.2.1.trans hmem.2.2)
  refine ⟨hmem.1, ?_⟩
  constructor
  · have hlog : -p.2 ≤ Real.log D := by
      apply (Real.exp_le_exp).mp
      rw [Real.exp_log hD]
      exact hmem.2.2
    linarith
  · have hlog : Real.log C ≤ -p.2 := by
      apply (Real.exp_le_exp).mp
      rw [Real.exp_log hC]
      exact hmem.2.1
    linarith

theorem tsupport_uncurry_dfiParametricMellinKernel_subset
    {σ A B C D : ℝ} {E : ℝ → ℝ → ℂ}
    (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) :
    tsupport (Function.uncurry (dfiParametricMellinKernel σ E)) ⊆
      Set.Icc A B ×ˢ Set.Icc (-Real.log D) (-Real.log C) := by
  exact closure_minimal
    (support_uncurry_dfiParametricMellinKernel_subset hC hSupport)
    (isClosed_Icc.prod isClosed_Icc)

theorem contDiff_uncurry_dfiMixedDeriv
    {F : ℝ → ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (i j : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (dfiMixedDeriv i j F)) := by
  have hPartial : ContDiff ℝ ∞
      (dfiPartialX i (dfiPartialY j (Function.uncurry F))) :=
    contDiff_dfiPartialX i (contDiff_dfiPartialY j hF)
  convert hPartial using 1
  ext p
  rcases p with ⟨x, y⟩
  simp only [Function.uncurry_apply_pair]
  exact dfiMixedDeriv_eq_partialXY hF i j x y

/-- Every mixed derivative of a smooth rectangularly supported source is
uniformly bounded.  The bound is qualitative here; equation (28) later
provides the source-scale dependence needed for the quantitative error. -/
theorem exists_uniform_norm_dfiMixedDeriv_of_support
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (i j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : ℝ,
      ‖dfiMixedDeriv i j F x y‖ ≤ K := by
  let R : Set (ℝ × ℝ) := Set.Icc A B ×ˢ Set.Icc C D
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hCont : Continuous
      (fun p : ℝ × ℝ ↦ ‖dfiMixedDeriv i j F p.1 p.2‖) := by
    exact (contDiff_uncurry_dfiMixedDeriv hF i j).continuous.norm
  obtain ⟨K, hK⟩ := hR.bddAbove_image hCont.continuousOn
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro x y
  by_cases hxy : (x, y) ∈ R
  · exact (hK ⟨(x, y), hxy, rfl⟩).trans (le_max_left _ _)
  · have htsupport : tsupport (Function.uncurry F) ⊆ R :=
      closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc)
    have hzero : dfiMixedDeriv i j F x y = 0 := by
      by_contra hne
      have hs : (x, y) ∈ Function.support
          (Function.uncurry (dfiMixedDeriv i j F)) := by
        simpa only [Function.uncurry_apply_pair] using hne
      exact hxy (htsupport
        (support_dfiMixedDeriv_subset_tsupport hF i j hs))
    rw [hzero, norm_zero]
    exact le_max_right _ _

theorem support_dfiMixedDeriv_slice_subset
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (i j : ℕ) (x : ℝ) :
    Function.support (dfiMixedDeriv i j F x) ⊆ Set.Icc C D := by
  have htsupport : tsupport (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D :=
    closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc)
  intro y hy
  have hpair : (x, y) ∈ Function.support
      (Function.uncurry (dfiMixedDeriv i j F)) := by
    simpa only [Function.mem_support, Function.uncurry_apply_pair] using hy
  exact (htsupport (support_dfiMixedDeriv_subset_tsupport hF i j hpair)).2

/-- A rectangularly supported slice has a literal compact-interval Mellin
integral.  This equality, rather than an appeal to formal differentiation of
an improper integral, is used below. -/
theorem mellin_slice_eq_Icc
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (x : ℝ) (z : ℂ) :
    mellin (F x) z = ∫ y in Set.Icc C D,
      (y : ℂ) ^ (z - 1) * F x y := by
  unfold mellin
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
  · intro y hy
    exact hC.trans_le hy.1
  · intro y hy
    have hFy : F x y = 0 := by
      by_contra hne
      exact hy.2 (hSupport (show
        (x, y) ∈ Function.support (Function.uncurry F) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).2
    simp [hFy]

/-- Exact commutation of every first-parameter derivative with the Mellin
transform of a compactly supported two-variable source. -/
theorem iteratedDeriv_mellin_slice
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (i : ℕ) (x : ℝ) (z : ℂ) :
    iteratedDeriv i (fun x' ↦ mellin (F x') z) x =
      mellin (dfiMixedDeriv i 0 F x) z := by
  let w : ℝ → ℂ := fun y ↦ (y : ℂ) ^ (z - 1)
  have hwGlobal : Continuous (fun y : ℝ ↦
      ((max C y : ℝ) : ℂ) ^ (z - 1)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (Complex.continuousAt_ofReal_cpow_const (max C y) (z - 1)
      (Or.inr (ne_of_gt (hC.trans_le (le_max_left C y))))).comp
        (continuousAt_const.max continuousAt_id)
  let wg : ℝ → ℂ := fun y ↦ ((max C y : ℝ) : ℂ) ^ (z - 1)
  have hwg : Continuous wg := by simpa [wg] using hwGlobal
  have hwEq : ∀ y ∈ Set.Icc C D, wg y = w y := by
    intro y hy
    simp [wg, w, max_eq_right hy.1]
  have hLeft : (fun x' ↦ mellin (F x') z) =
      fun x' ↦ ∫ y in Set.Icc C D, wg y * F x' y := by
    funext x'
    rw [mellin_slice_eq_Icc hC hSupport]
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    change w y * F x' y = wg y * F x' y
    rw [hwEq y hy]
  rw [hLeft]
  have hZero : (fun x' ↦ ∫ y in Set.Icc C D, wg y * F x' y) =
      dfiWeightedPartialIntegral 0 C D wg F := by
    funext x'
    simp [dfiWeightedPartialIntegral, dfiPartialX]
  rw [hZero]
  rw [congrFun (iteratedDeriv_dfiWeightedPartialIntegral i C D hwg hF) x]
  unfold dfiWeightedPartialIntegral
  have hDerivSupport : Function.support
      (Function.uncurry (dfiMixedDeriv i 0 F)) ⊆
        Set.Icc A B ×ˢ Set.Icc C D :=
    (support_dfiMixedDeriv_subset_tsupport hF i 0).trans
      (closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc))
  rw [mellin_slice_eq_Icc hC hDerivSupport]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  change wg y * dfiPartialX i (Function.uncurry F) (x, y) =
    w y * dfiMixedDeriv i 0 F x y
  rw [hwEq y hy]
  rw [dfiMixedDeriv_eq_partialXY hF i 0]
  simp [dfiPartialY]

/-- The Mellin transform of a smooth rectangularly supported family is
smooth in the retained real parameter on every fixed vertical point. -/
theorem contDiff_mellin_slice
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hC : 0 < C)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (z : ℂ) :
    ContDiff ℝ ∞ (fun x ↦ mellin (F x) z) := by
  let w : ℝ → ℂ := fun y ↦ ((max C y : ℝ) : ℂ) ^ (z - 1)
  have hw : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (Complex.continuousAt_ofReal_cpow_const (max C y) (z - 1)
      (Or.inr (ne_of_gt (hC.trans_le (le_max_left C y))))).comp
        (continuousAt_const.max continuousAt_id)
  have hEq : (fun x ↦ mellin (F x) z) =
      fun x ↦ ∫ y in Set.Icc C D, w y * F x y := by
    funext x
    rw [mellin_slice_eq_Icc hC hSupport]
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    simp [w, max_eq_right hy.1]
  rw [hEq]
  exact contDiff_integral_Icc_right_mul_left hw hF

/-- Each mixed derivative slice remains in the exact DFI test-function
class with the same positive support interval. -/
noncomputable def dfiMixedDerivSliceTestFunction
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (i j : ℕ) (x : ℝ) :
    DFIVoronoiTestFunction (dfiMixedDeriv i j F x) where
  lower := C
  upper := D
  lower_pos := hC
  lower_le_upper := hCD
  smooth := (contDiff_uncurry_dfiMixedDeriv hF i j).comp
    (by fun_prop : ContDiff ℝ ∞ (fun y : ℝ ↦ (x, y)))
  support_subset := support_dfiMixedDeriv_slice_subset
    hF hSupport i j x

/-- The parameter derivative of a Mellin slice is represented by the
Fourier transform of the corresponding differentiated logarithmic kernel. -/
theorem iteratedDeriv_mellin_slice_eq_fourier
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (i : ℕ) (x σ u : ℝ) :
    iteratedDeriv i (fun x' ↦
        mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x =
      𝓕 (dfiVoronoiMellinKernelSchwartz
        (dfiMixedDerivSliceTestFunction hF hC hCD hSupport i 0 x) σ)
        (u / (2 * Real.pi)) := by
  rw [iteratedDeriv_mellin_slice hF hC hSupport]
  exact DFIVoronoiTestFunction.mellin_eq_fourier_mellinKernel
    (dfiMixedDerivSliceTestFunction hF hC hCD hSupport i 0 x) σ u

/-- Every derivative of a smooth compactly supported complex-valued
function is integrable.  This is the complex-valued form needed for the
individual Mellin branches in DFI (24). -/
theorem integrable_iteratedDeriv_of_complex
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (j : ℕ) :
    Integrable (iteratedDeriv j f) := by
  have hcont : Continuous (iteratedDeriv j f) :=
    hf.continuous_iteratedDeriv j
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top j)))
  have hcomp : HasCompactSupport (iteratedDeriv j f) := by
    have haux : ∀ k : ℕ, HasCompactSupport (iteratedDeriv k f) := by
      intro k
      induction k with
      | zero => simpa using hfc
      | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
    exact haux j
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- Fourier integration by parts for a complex-valued smooth compactly
supported function.  Mathlib's `(2π)^j` normalization is discarded using
`2π ≥ 1`, leaving the source-friendly factor `|ξ|^j`. -/
theorem abs_pow_mul_norm_fourier_complex_le
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (j : ℕ) (ξ : ℝ) :
    |ξ| ^ j * ‖𝓕 f ξ‖ ≤ ∫ x : ℝ, ‖iteratedDeriv j f x‖ := by
  have hall : ∀ n : ℕ, n ≤ (⊤ : ℕ∞) →
      Integrable (iteratedDeriv n f) := by
    intro n _hn
    exact integrable_iteratedDeriv_of_complex f hf hfc n
  have hjtop : j ≤ (⊤ : ℕ∞) := le_of_lt (ENat.coe_lt_top j)
  have hpoint := congrFun (Real.fourier_iteratedDeriv hf hall hjtop) ξ
  have hfactor :
      ‖(2 * Real.pi * Complex.I * (ξ : ℂ)) ^ j‖ =
        (2 * Real.pi * |ξ|) ^ j := by
    rw [norm_pow, norm_mul, norm_mul]
    simp [abs_of_nonneg Real.pi_pos.le]
  have hnormeq := congrArg norm hpoint
  rw [norm_smul, hfactor] at hnormeq
  have hbase : |ξ| ≤ 2 * Real.pi * |ξ| := by
    nlinarith [abs_nonneg ξ, Real.pi_gt_three]
  have hpow : |ξ| ^ j ≤ (2 * Real.pi * |ξ|) ^ j :=
    pow_le_pow_left₀ (abs_nonneg ξ) hbase j
  calc
    |ξ| ^ j * ‖𝓕 f ξ‖ ≤
        (2 * Real.pi * |ξ|) ^ j * ‖𝓕 f ξ‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = ‖𝓕 (iteratedDeriv j f) ξ‖ := hnormeq.symm
    _ ≤ ∫ x : ℝ, ‖iteratedDeriv j f x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 MeasureTheory.volume (innerₗ ℝ) (iteratedDeriv j f) ξ

/-- Quantitative Fourier decay for one compactly supported function.  Both
derivative bounds are explicit, so this lemma can be used inside an
arithmetic family without introducing a family-dependent compactness
constant. -/
theorem one_add_abs_fourier_decay_of_support_of_bounds
    {f : ℝ → ℂ} {C D K₀ K₆ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hCD : C ≤ D)
    (hSupport : Function.support f ⊆ Set.Icc C D)
    (hK₀ : 0 ≤ K₀) (hK₆ : 0 ≤ K₆)
    (hBound₀ : ∀ u : ℝ, ‖iteratedDeriv 0 f u‖ ≤ K₀)
    (hBound₆ : ∀ u : ℝ, ‖iteratedDeriv 6 f u‖ ≤ K₆) :
    ∀ ξ : ℝ, (1 + |ξ|) ^ 6 * ‖𝐽 f ξ‖ ≤
      64 * (D - C) * (K₀ + K₆) := by
  have hCompact : HasCompactSupport f := by
    apply HasCompactSupport.intro isCompact_Icc
    intro u hu
    by_contra hne
    exact hu (hSupport (by simpa only [Function.mem_support] using hne))
  have derivativeSupport (j : ℕ) :
      Function.support (iteratedDeriv j f) ⊆ Set.Icc C D := by
    exact (support_iteratedDeriv_subset_tsupport j).trans
      (closure_minimal hSupport isClosed_Icc)
  have integralBound (j : ℕ) (K : ℝ)
      (hBound : ∀ u : ℝ, ‖iteratedDeriv j f u‖ ≤ K) :
      ∫ u : ℝ, ‖iteratedDeriv j f u‖ ≤ (D - C) * K := by
    have hIntegralEq :
        (∫ u : ℝ, ‖iteratedDeriv j f u‖) =
          ∫ u in Set.Icc C D, ‖iteratedDeriv j f u‖ := by
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with u
      by_cases hu : u ∈ Set.Icc C D
      · simp [Set.indicator_of_mem hu]
      · have hz : iteratedDeriv j f u = 0 := by
          by_contra hne
          exact hu (derivativeSupport j (by
            simpa only [Function.mem_support] using hne))
        simp [Set.indicator_of_notMem hu, hz]
    have hNonneg : 0 ≤ ∫ u in Set.Icc C D, ‖iteratedDeriv j f u‖ :=
      MeasureTheory.setIntegral_nonneg measurableSet_Icc fun _ _ => norm_nonneg _
    have hSetBound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (μ := MeasureTheory.volume) (s := Set.Icc C D) (C := K)
      (f := fun u : ℝ => ‖iteratedDeriv j f u‖)
      measure_Icc_lt_top fun u _hu => hBound u
    have hMeasure : (MeasureTheory.volume (Set.Icc C D)).toReal = D - C := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hCD)]
    rw [hIntegralEq]
    calc
      (∫ u in Set.Icc C D, ‖iteratedDeriv j f u‖) =
          ‖∫ u in Set.Icc C D, ‖iteratedDeriv j f u‖‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
      _ ≤ K * (MeasureTheory.volume (Set.Icc C D)).toReal := hSetBound
      _ = (D - C) * K := by rw [hMeasure]; ring
  have hZero (ξ : ℝ) : ‖𝐽 f ξ‖ ≤ (D - C) * K₀ := by
    have h := abs_pow_mul_norm_fourier_complex_le f hf hCompact 0 ξ
    simpa using h.trans (integralBound 0 K₀ hBound₀)
  have hSix (ξ : ℝ) :
      |ξ| ^ 6 * ‖𝐽 f ξ‖ ≤ (D - C) * K₆ :=
    (abs_pow_mul_norm_fourier_complex_le f hf hCompact 6 ξ).trans
      (integralBound 6 K₆ hBound₆)
  intro ξ
  by_cases hξ : |ξ| ≤ 1
  · have hWeight : (1 + |ξ|) ^ 6 ≤ 64 := by
      have hTwo : 1 + |ξ| ≤ 2 := by linarith
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |ξ|) hTwo 6
      norm_num at hp
      exact hp
    calc
      (1 + |ξ|) ^ 6 * ‖𝐽 f ξ‖ ≤ 64 * ((D - C) * K₀) :=
        mul_le_mul hWeight (hZero ξ) (norm_nonneg _) (by positivity)
      _ ≤ 64 * (D - C) * (K₀ + K₆) := by
        have hLen : 0 ≤ D - C := sub_nonneg.mpr hCD
        nlinarith
  · have hξOne : 1 ≤ |ξ| := le_of_lt (lt_of_not_ge hξ)
    have hWeight : (1 + |ξ|) ^ 6 ≤ 64 * |ξ| ^ 6 := by
      have hTwo : 1 + |ξ| ≤ 2 * |ξ| := by linarith
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |ξ|) hTwo 6
      rw [mul_pow] at hp
      norm_num at hp
      exact hp
    calc
      (1 + |ξ|) ^ 6 * ‖𝐽 f ξ‖ ≤
          (64 * |ξ| ^ 6) * ‖𝐽 f ξ‖ :=
        mul_le_mul_of_nonneg_right hWeight (norm_nonneg _)
      _ = 64 * (|ξ| ^ 6 * ‖𝐽 f ξ‖) := by ring
      _ ≤ 64 * ((D - C) * K₆) :=
        mul_le_mul_of_nonneg_left (hSix ξ) (by positivity)
      _ ≤ 64 * (D - C) * (K₀ + K₆) := by
        have hLen : 0 ≤ D - C := sub_nonneg.mpr hCD
        nlinarith

/-- Explicit Mellin-line decay obtained from explicit bounds for the
logarithmic Mellin kernel.  This is the quantitative bridge between DFI
equation (28) and the retained-transform estimate in equation (29). -/
theorem DFIVoronoiTestFunction.mellin_half_line_bound_of_kernel_bounds
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {K₀ K₆ : ℝ}
    (hK₀ : 0 ≤ K₀) (hK₆ : 0 ≤ K₆)
    (hBound₀ : ∀ v : ℝ,
      ‖iteratedDeriv 0 (dfiVoronoiMellinKernel (1 / 2) g) v‖ ≤ K₀)
    (hBound₆ : ∀ v : ℝ,
      ‖iteratedDeriv 6 (dfiVoronoiMellinKernel (1 / 2) g) v‖ ≤ K₆) :
    ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
      (1 + 2 * Real.pi) ^ 6 *
        (64 * ((-Real.log hg.lower) - (-Real.log hg.upper)) *
          (K₀ + K₆)) := by
  let G : ℝ → ℂ := dfiVoronoiMellinKernel (1 / 2) g
  have hG : ContDiff ℝ ∞ G := hg.contDiff_mellinKernel (1 / 2)
  have hGSupport : Function.support G ⊆
      Set.Icc (-Real.log hg.upper) (-Real.log hg.lower) := by
    exact support_dfiVoronoiMellinKernel_subset hg (1 / 2)
  have hLog : -Real.log hg.upper ≤ -Real.log hg.lower := by
    exact neg_le_neg (Real.log_le_log hg.lower_pos hg.lower_le_upper)
  have hFourier := one_add_abs_fourier_decay_of_support_of_bounds
    hG hLog hGSupport hK₀ hK₆ hBound₀ hBound₆
  intro u
  have hTwoPi : 0 < 2 * Real.pi := by positivity
  have huEq : |u| = (2 * Real.pi) * |u / (2 * Real.pi)| := by
    calc
      |u| = |(2 * Real.pi) * (u / (2 * Real.pi))| := by
        congr 1
        field_simp
      _ = (2 * Real.pi) * |u / (2 * Real.pi)| := by
        rw [abs_mul, abs_of_pos hTwoPi]
  have hScale :
      1 + |u| ≤ (1 + 2 * Real.pi) * (1 + |u / (2 * Real.pi)|) := by
    rw [huEq]
    nlinarith [Real.pi_pos, abs_nonneg (u / (2 * Real.pi))]
  have hPow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |u|) hScale 6
  rw [hg.mellin_eq_fourier_mellinKernel (1 / 2) u]
  calc
    (1 + |u|) ^ 6 *
        ‖𝐽 (dfiVoronoiMellinKernelSchwartz hg (1 / 2))
          (u / (2 * Real.pi))‖ ≤
      ((1 + 2 * Real.pi) * (1 + |u / (2 * Real.pi)|)) ^ 6 *
        ‖𝐽 (dfiVoronoiMellinKernelSchwartz hg (1 / 2))
          (u / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ 6 *
        ((1 + |u / (2 * Real.pi)|) ^ 6 *
          ‖𝐽 G (u / (2 * Real.pi))‖) := by rfl
    _ ≤ (1 + 2 * Real.pi) ^ 6 *
        (64 * ((-Real.log hg.lower) - (-Real.log hg.upper)) *
          (K₀ + K₆)) :=
      mul_le_mul_of_nonneg_left (hFourier (u / (2 * Real.pi)))
        (pow_nonneg (by positivity) 6)

/-- Quantitative form of Fourier integration by parts for a family supported
in one fixed interval.  Unlike the compactness-based existence theorem below,
the constant is supplied by an explicit uniform derivative bound.  This is
the form needed to feed DFI equation (28) into equation (29) without allowing
the implied constant to depend on the arithmetic slice. -/
theorem uniform_fourier_decay_of_rectangular_support_of_bound
    {F : ℝ → ℝ → ℂ} {A B C D K : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (j : ℕ)
    (hBound : ∀ x u : ℝ, ‖dfiMixedDeriv 0 j F x u‖ ≤ K) :
    ∀ x ξ : ℝ,
      |ξ| ^ j * ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤ (D - C) * K := by
  intro x ξ
  have hSliceSmooth : ContDiff ℝ ∞ (fun u : ℝ => F x u) :=
    hF.comp (contDiff_prodMk_right x)
  have hSliceSupport : Function.support (fun u : ℝ => F x u) ⊆
      Set.Icc C D := by
    intro u hu
    exact (hSupport (show (x, u) ∈ Function.support (Function.uncurry F) by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hu)).2
  have hSliceCompact : HasCompactSupport (fun u : ℝ => F x u) := by
    apply HasCompactSupport.intro isCompact_Icc
    intro u hu
    by_contra hne
    exact hu (hSliceSupport (by
      simpa only [Function.mem_support] using hne))
  have hFourier := abs_pow_mul_norm_fourier_complex_le
    (fun u : ℝ => F x u) hSliceSmooth hSliceCompact j ξ
  have hDerivSupport : Function.support
      (iteratedDeriv j (fun u : ℝ => F x u)) ⊆ Set.Icc C D := by
    simpa only [dfiMixedDeriv] using
      (support_dfiMixedDeriv_slice_subset hF hSupport 0 j x)
  have hIntegralEq :
      (∫ u : ℝ, ‖iteratedDeriv j (fun v : ℝ => F x v) u‖) =
        ∫ u in Set.Icc C D,
          ‖iteratedDeriv j (fun v : ℝ => F x v) u‖ := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with u
    by_cases hu : u ∈ Set.Icc C D
    · simp [Set.indicator_of_mem hu]
    · have hz : iteratedDeriv j (fun v : ℝ => F x v) u = 0 := by
        by_contra hne
        exact hu (hDerivSupport (by
          simpa only [Function.mem_support] using hne))
      simp [Set.indicator_of_notMem hu, hz]
  have hNonneg : 0 ≤ ∫ u in Set.Icc C D,
      ‖iteratedDeriv j (fun v : ℝ => F x v) u‖ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun _ _ => norm_nonneg _
  have hSetBound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume) (s := Set.Icc C D) (C := K)
    (f := fun u : ℝ => ‖iteratedDeriv j (fun v : ℝ => F x v) u‖)
    measure_Icc_lt_top fun u _hu => by
      simpa [dfiMixedDeriv] using hBound x u
  have hMeasure : (MeasureTheory.volume (Set.Icc C D)).toReal = D - C := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hCD)]
  rw [hIntegralEq] at hFourier
  calc
    |ξ| ^ j * ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤
        ∫ u in Set.Icc C D,
          ‖iteratedDeriv j (fun v : ℝ => F x v) u‖ := hFourier
    _ = ‖∫ u in Set.Icc C D,
          ‖iteratedDeriv j (fun v : ℝ => F x v) u‖‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    _ ≤ K * (MeasureTheory.volume (Set.Icc C D)).toReal := hSetBound
    _ = (D - C) * K := by rw [hMeasure]; ring

/-- Explicit low/high-frequency combination.  The right side depends only
on the interval length and the supplied zeroth- and sixth-derivative bounds,
not on the retained family parameter. -/
theorem uniform_one_add_abs_fourier_decay_of_rectangular_support_of_bounds
    {F : ℝ → ℝ → ℂ} {A B C D K₀ K₆ : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (hK₀ : 0 ≤ K₀) (hK₆ : 0 ≤ K₆)
    (hBound₀ : ∀ x u : ℝ, ‖dfiMixedDeriv 0 0 F x u‖ ≤ K₀)
    (hBound₆ : ∀ x u : ℝ, ‖dfiMixedDeriv 0 6 F x u‖ ≤ K₆) :
    ∀ x ξ : ℝ,
      (1 + |ξ|) ^ 6 * ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤
        64 * (D - C) * (K₀ + K₆) := by
  have hZero := uniform_fourier_decay_of_rectangular_support_of_bound
    hF hCD hSupport 0 hBound₀
  have hSix := uniform_fourier_decay_of_rectangular_support_of_bound
    hF hCD hSupport 6 hBound₆
  intro x ξ
  by_cases hξ : |ξ| ≤ 1
  · have hWeight : (1 + |ξ|) ^ 6 ≤ 64 := by
      have hTwo : 1 + |ξ| ≤ 2 := by linarith
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |ξ|) hTwo 6
      norm_num at hp
      exact hp
    have hBase : ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤ (D - C) * K₀ := by
      simpa using hZero x ξ
    calc
      (1 + |ξ|) ^ 6 * ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤
          64 * ((D - C) * K₀) :=
        mul_le_mul hWeight hBase (norm_nonneg _) (by positivity)
      _ ≤ 64 * (D - C) * (K₀ + K₆) := by
        have hLen : 0 ≤ D - C := sub_nonneg.mpr hCD
        nlinarith
  · have hξOne : 1 ≤ |ξ| := le_of_lt (lt_of_not_ge hξ)
    have hWeight : (1 + |ξ|) ^ 6 ≤ 64 * |ξ| ^ 6 := by
      have hTwo : 1 + |ξ| ≤ 2 * |ξ| := by linarith
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |ξ|) hTwo 6
      rw [mul_pow] at hp
      norm_num at hp
      exact hp
    have hBase := hSix x ξ
    calc
      (1 + |ξ|) ^ 6 * ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤
          (64 * |ξ| ^ 6) * ‖𝓕 (fun u : ℝ => F x u) ξ‖ :=
        mul_le_mul_of_nonneg_right hWeight (norm_nonneg _)
      _ = 64 * (|ξ| ^ 6 * ‖𝓕 (fun u : ℝ => F x u) ξ‖) := by ring
      _ ≤ 64 * ((D - C) * K₆) :=
        mul_le_mul_of_nonneg_left hBase (by positivity)
      _ ≤ 64 * (D - C) * (K₀ + K₆) := by
        have hLen : 0 ≤ D - C := sub_nonneg.mpr hCD
        nlinarith

/-- A smooth family supported in one fixed rectangle has a Fourier decay
constant uniform in the retained parameter.  This is the uniformity needed
before the two Voronoi transforms in DFI (24) may be separated. -/
theorem exists_uniform_fourier_decay_of_rectangular_support
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ξ : ℝ,
      |ξ| ^ j * ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤ K := by
  obtain ⟨K₀, hK₀, hK₀bound⟩ :=
    exists_uniform_norm_dfiMixedDeriv_of_support hF hSupport 0 j
  refine ⟨(D - C) * K₀, mul_nonneg (sub_nonneg.mpr hCD) hK₀, ?_⟩
  intro x ξ
  have hSliceSmooth : ContDiff ℝ ∞ (fun u : ℝ => F x u) :=
    hF.comp (contDiff_prodMk_right x)
  have hSliceSupport : Function.support (fun u : ℝ => F x u) ⊆
      Set.Icc C D := by
    intro u hu
    exact (hSupport (show (x, u) ∈ Function.support (Function.uncurry F) by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hu)).2
  have hSliceCompact : HasCompactSupport (fun u : ℝ => F x u) := by
    apply HasCompactSupport.intro isCompact_Icc
    intro u hu
    by_contra hne
    exact hu (hSliceSupport (by
      simpa only [Function.mem_support] using hne))
  have hFourier := abs_pow_mul_norm_fourier_complex_le
    (fun u : ℝ => F x u) hSliceSmooth hSliceCompact j ξ
  have hDerivSupport : Function.support
      (iteratedDeriv j (fun u : ℝ => F x u)) ⊆ Set.Icc C D := by
    simpa only [dfiMixedDeriv] using
      (support_dfiMixedDeriv_slice_subset hF hSupport 0 j x)
  have hIntegralEq :
      (∫ u : ℝ, ‖iteratedDeriv j (fun v : ℝ => F x v) u‖) =
        ∫ u in Set.Icc C D,
          ‖iteratedDeriv j (fun v : ℝ => F x v) u‖ := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with u
    by_cases hu : u ∈ Set.Icc C D
    · simp [Set.indicator_of_mem hu]
    · have hz : iteratedDeriv j (fun v : ℝ => F x v) u = 0 := by
        by_contra hne
        exact hu (hDerivSupport (by
          simpa only [Function.mem_support] using hne))
      simp [Set.indicator_of_notMem hu, hz]
  have hNonneg : 0 ≤ ∫ u in Set.Icc C D,
      ‖iteratedDeriv j (fun v : ℝ => F x v) u‖ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc fun _ _ => norm_nonneg _
  have hSetBound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (μ := MeasureTheory.volume) (s := Set.Icc C D) (C := K₀)
    (f := fun u : ℝ => ‖iteratedDeriv j (fun v : ℝ => F x v) u‖)
    measure_Icc_lt_top fun u _hu => by
      simpa [dfiMixedDeriv] using hK₀bound x u
  have hMeasure : (MeasureTheory.volume (Set.Icc C D)).toReal = D - C := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hCD)]
  rw [hIntegralEq] at hFourier
  calc
    |ξ| ^ j * ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤
        ∫ u in Set.Icc C D,
          ‖iteratedDeriv j (fun v : ℝ => F x v) u‖ := hFourier
    _ = ‖∫ u in Set.Icc C D,
          ‖iteratedDeriv j (fun v : ℝ => F x v) u‖‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    _ ≤ K₀ * (MeasureTheory.volume (Set.Icc C D)).toReal := hSetBound
    _ = (D - C) * K₀ := by rw [hMeasure]; ring

/-- The low- and high-frequency estimates combine into the standard
Schwartz weight, uniformly in the retained parameter. -/
theorem exists_uniform_one_add_abs_fourier_decay_of_rectangular_support
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ξ : ℝ,
      (1 + |ξ|) ^ 6 * ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤ K := by
  obtain ⟨K₀, hK₀, hBound₀⟩ :=
    exists_uniform_fourier_decay_of_rectangular_support
      hF hCD hSupport 0
  obtain ⟨K₆, hK₆, hBound₆⟩ :=
    exists_uniform_fourier_decay_of_rectangular_support
      hF hCD hSupport 6
  refine ⟨64 * (K₀ + K₆), by positivity, ?_⟩
  intro x ξ
  by_cases hξ : |ξ| ≤ 1
  · have hWeight : (1 + |ξ|) ^ 6 ≤ 64 := by
      have hTwo : 1 + |ξ| ≤ 2 := by linarith
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |ξ|) hTwo 6
      norm_num at hp
      exact hp
    have hZero : ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤ K₀ := by
      simpa using hBound₀ x ξ
    calc
      (1 + |ξ|) ^ 6 * ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤
          64 * K₀ := mul_le_mul hWeight hZero (norm_nonneg _) (by norm_num)
      _ ≤ 64 * (K₀ + K₆) := by nlinarith
  · have hξOne : 1 ≤ |ξ| := le_of_lt (lt_of_not_ge hξ)
    have hWeight : (1 + |ξ|) ^ 6 ≤ 64 * |ξ| ^ 6 := by
      have hTwo : 1 + |ξ| ≤ 2 * |ξ| := by linarith
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |ξ|) hTwo 6
      rw [mul_pow] at hp
      norm_num at hp
      exact hp
    have hSix := hBound₆ x ξ
    calc
      (1 + |ξ|) ^ 6 * ‖𝓕 (fun u : ℝ => F x u) ξ‖ ≤
          (64 * |ξ| ^ 6) * ‖𝓕 (fun u : ℝ => F x u) ξ‖ :=
        mul_le_mul_of_nonneg_right hWeight (norm_nonneg _)
      _ = 64 * (|ξ| ^ 6 * ‖𝓕 (fun u : ℝ => F x u) ξ‖) := by ring
      _ ≤ 64 * K₆ := mul_le_mul_of_nonneg_left hSix (by norm_num)
      _ ≤ 64 * (K₀ + K₆) := by nlinarith

/-- Uniform sixth-order vertical decay for every retained-parameter
derivative of a compactly supported Mellin slice.  The frequency is written
with Mathlib's Fourier normalization, exactly as it occurs in Mellin
inversion. -/
theorem exists_uniform_iteratedDeriv_mellin_frequency_decay
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (i : ℕ) (σ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x u : ℝ,
      |u / (2 * Real.pi)| ^ 6 *
        ‖iteratedDeriv i (fun x' ↦
          mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x‖ ≤ K := by
  let E : ℝ → ℝ → ℂ := dfiMixedDeriv i 0 F
  have hE : ContDiff ℝ ∞ (Function.uncurry E) := by
    exact contDiff_uncurry_dfiMixedDeriv hF i 0
  have hESupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D := by
    exact (support_dfiMixedDeriv_subset_tsupport hF i 0).trans
      (closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc))
  let G : ℝ → ℝ → ℂ := dfiParametricMellinKernel σ E
  have hG : ContDiff ℝ ∞ (Function.uncurry G) := by
    exact contDiff_uncurry_dfiParametricMellinKernel hE
  have hGSupport : Function.support (Function.uncurry G) ⊆
      Set.Icc A B ×ˢ Set.Icc (-Real.log D) (-Real.log C) := by
    exact support_uncurry_dfiParametricMellinKernel_subset hC hESupport
  have hLog : -Real.log D ≤ -Real.log C := by
    exact neg_le_neg (Real.log_le_log hC hCD)
  obtain ⟨K, hK, hBound⟩ :=
    exists_uniform_fourier_decay_of_rectangular_support
      hG hLog hGSupport 6
  refine ⟨K, hK, ?_⟩
  intro x u
  rw [iteratedDeriv_mellin_slice_eq_fourier
    hF hC hCD hSupport i x σ u]
  simpa [G, E, dfiVoronoiMellinKernelSchwartz,
    dfiVoronoiMellinKernel] using hBound x (u / (2 * Real.pi))

/-- Source-normalized vertical decay: every first-parameter derivative of
a rectangularly supported Mellin slice is bounded by one constant times
`(1+|u|)⁻⁶`, uniformly in the retained parameter. -/
theorem exists_uniform_iteratedDeriv_mellin_decay
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (i : ℕ) (σ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x u : ℝ,
      (1 + |u|) ^ 6 *
        ‖iteratedDeriv i (fun x' ↦
          mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x‖ ≤ K := by
  let E : ℝ → ℝ → ℂ := dfiMixedDeriv i 0 F
  have hE : ContDiff ℝ ∞ (Function.uncurry E) :=
    contDiff_uncurry_dfiMixedDeriv hF i 0
  have hESupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D :=
    (support_dfiMixedDeriv_subset_tsupport hF i 0).trans
      (closure_minimal hSupport (isClosed_Icc.prod isClosed_Icc))
  let G : ℝ → ℝ → ℂ := dfiParametricMellinKernel σ E
  have hG : ContDiff ℝ ∞ (Function.uncurry G) :=
    contDiff_uncurry_dfiParametricMellinKernel hE
  have hGSupport : Function.support (Function.uncurry G) ⊆
      Set.Icc A B ×ˢ Set.Icc (-Real.log D) (-Real.log C) :=
    support_uncurry_dfiParametricMellinKernel_subset hC hESupport
  have hLog : -Real.log D ≤ -Real.log C :=
    neg_le_neg (Real.log_le_log hC hCD)
  obtain ⟨K, hK, hBound⟩ :=
    exists_uniform_one_add_abs_fourier_decay_of_rectangular_support
      hG hLog hGSupport
  let R : ℝ := 1 + 2 * Real.pi
  refine ⟨R ^ 6 * K, mul_nonneg (pow_nonneg (by positivity) 6) hK, ?_⟩
  intro x u
  have hTwoPi : 0 < 2 * Real.pi := by positivity
  have huEq : |u| = (2 * Real.pi) * |u / (2 * Real.pi)| := by
    have hne : 2 * Real.pi ≠ 0 := ne_of_gt hTwoPi
    calc
      |u| = |(2 * Real.pi) * (u / (2 * Real.pi))| := by
        congr 1
        field_simp
      _ = (2 * Real.pi) * |u / (2 * Real.pi)| := by
        rw [abs_mul, abs_of_pos hTwoPi]
  have hScale : 1 + |u| ≤ R * (1 + |u / (2 * Real.pi)|) := by
    rw [huEq]
    dsimp [R]
    nlinarith [Real.pi_pos, abs_nonneg (u / (2 * Real.pi))]
  have hPow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |u|) hScale 6
  rw [iteratedDeriv_mellin_slice_eq_fourier
    hF hC hCD hSupport i x σ u]
  have hFourier :
      (1 + |u / (2 * Real.pi)|) ^ 6 *
          ‖𝓕 (fun v : ℝ => G x v) (u / (2 * Real.pi))‖ ≤ K :=
    hBound x (u / (2 * Real.pi))
  have hIdentify :
      𝓕 (dfiVoronoiMellinKernelSchwartz
        (dfiMixedDerivSliceTestFunction hF hC hCD hSupport i 0 x) σ)
          (u / (2 * Real.pi)) =
      𝓕 (fun v : ℝ => G x v) (u / (2 * Real.pi)) := by
    apply congrArg (fun H : ℝ → ℂ => 𝓕 H (u / (2 * Real.pi)))
    funext v
    rfl
  rw [hIdentify]
  calc
    (1 + |u|) ^ 6 * ‖𝓕 (fun v : ℝ => G x v)
        (u / (2 * Real.pi))‖ ≤
      (R * (1 + |u / (2 * Real.pi)|)) ^ 6 *
        ‖𝓕 (fun v : ℝ => G x v) (u / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
    _ = R ^ 6 * ((1 + |u / (2 * Real.pi)|) ^ 6 *
        ‖𝓕 (fun v : ℝ => G x v) (u / (2 * Real.pi))‖) := by ring
    _ ≤ R ^ 6 * K := mul_le_mul_of_nonneg_left hFourier (pow_nonneg (by positivity) 6)

/-- Quadratic multiplier growth times sixth-order Mellin decay is dominated
by the integrable Cauchy kernel. -/
theorem norm_mul_le_cauchy_of_quadratic_and_sixth_decay
    {W M : ℂ} {C K u : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hW : ‖W‖ ≤ C * (1 + |u|) ^ 2)
    (hM : (1 + |u|) ^ 6 * ‖M‖ ≤ K) :
    ‖W * M‖ ≤ C * K * (1 + u ^ 2)⁻¹ := by
  let w : ℝ := 1 + |u|
  have hw : 0 < w := by dsimp [w]; positivity
  have hM' : ‖M‖ ≤ K / w ^ 6 := by
    apply (le_div_iff₀ (pow_pos hw 6)).2
    simpa [w, mul_comm] using hM
  have hnum : 0 ≤ C * K := mul_nonneg hC hK
  have hden : 0 < 1 + u ^ 2 := by positivity
  have hdenLarge : 1 + u ^ 2 ≤ w ^ 4 := by
    dsimp [w]
    nlinarith [abs_nonneg u, sq_abs u]
  rw [norm_mul]
  calc
    ‖W‖ * ‖M‖ ≤ (C * w ^ 2) * (K / w ^ 6) :=
      mul_le_mul hW hM' (norm_nonneg _) (mul_nonneg hC (pow_nonneg hw.le 2))
    _ = (C * K) / w ^ 4 := by
      field_simp [ne_of_gt hw]
    _ ≤ (C * K) / (1 + u ^ 2) := by
      apply (div_le_div_iff₀ (pow_pos hw 4) hden).2
      exact mul_le_mul_of_nonneg_left hdenLarge hnum
    _ = C * K * (1 + u ^ 2)⁻¹ := by rw [div_eq_mul_inv]

theorem continuous_iteratedDeriv_mellin_vertical
    {F : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (i : ℕ) (x σ : ℝ) :
    Continuous (fun u : ℝ ↦ iteratedDeriv i (fun x' ↦
      mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x) := by
  have hEq : (fun u : ℝ ↦ iteratedDeriv i (fun x' ↦
      mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x) =
      fun u : ℝ ↦ mellin (dfiMixedDeriv i 0 F x)
        ((σ : ℂ) + (u : ℂ) * I) := by
    funext u
    exact iteratedDeriv_mellin_slice hF hC hSupport i x _
  rw [hEq]
  exact (DFIVoronoiTestFunction.differentiable_mellin
    (dfiMixedDerivSliceTestFunction hF hC hCD hSupport i 0 x)).continuous.comp
      (by fun_prop)

/-- The `i`th formal parameter derivative of a vertical Mellin integral. -/
noncomputable def dfiParametricVerticalIntegralDeriv
    (i : ℕ) (W : ℝ → ℂ) (σ : ℝ) (F : ℝ → ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ u : ℝ, W u * iteratedDeriv i (fun x' ↦
    mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x

theorem integrable_dfiParametricVerticalIntegralDeriv
    {F : ℝ → ℝ → ℂ} {A B C D Cw : ℝ} {W : ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (hWcont : Continuous W) (hCw : 0 ≤ Cw)
    (hW : ∀ u : ℝ, ‖W u‖ ≤ Cw * (1 + |u|) ^ 2)
    (i : ℕ) (σ x : ℝ) :
    Integrable (fun u : ℝ ↦ W u * iteratedDeriv i (fun x' ↦
      mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x) := by
  obtain ⟨K, hK, hDecay⟩ :=
    exists_uniform_iteratedDeriv_mellin_decay
      hF hC hCD hSupport i σ
  have hMajor : Integrable (fun u : ℝ ↦
      Cw * K * (1 + u ^ 2)⁻¹) := by
    simpa [mul_assoc] using integrable_inv_one_add_sq.const_mul (Cw * K)
  have hMeas : AEStronglyMeasurable (fun u : ℝ ↦
      W u * iteratedDeriv i (fun x' ↦
        mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x) :=
    (hWcont.mul (continuous_iteratedDeriv_mellin_vertical
      hF hC hCD hSupport i x σ)).aestronglyMeasurable
  apply hMajor.mono' hMeas
  filter_upwards with u
  exact norm_mul_le_cauchy_of_quadratic_and_sixth_decay
    hCw hK (hW u) (hDecay x u)

/-- Successive formal derivatives of the vertical Mellin integral are its
actual derivatives.  The proof uses one global integrable Cauchy majorant,
so no compact truncation or hidden interchange assumption remains. -/
theorem hasDerivAt_dfiParametricVerticalIntegralDeriv
    {F : ℝ → ℝ → ℂ} {A B C D Cw : ℝ} {W : ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (hWcont : Continuous W) (hCw : 0 ≤ Cw)
    (hW : ∀ u : ℝ, ‖W u‖ ≤ Cw * (1 + |u|) ^ 2)
    (i : ℕ) (σ x₀ : ℝ) :
    HasDerivAt (dfiParametricVerticalIntegralDeriv i W σ F)
      (dfiParametricVerticalIntegralDeriv (i + 1) W σ F x₀) x₀ := by
  let G : ℝ → ℝ → ℂ := fun x u ↦ W u * iteratedDeriv i (fun x' ↦
    mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x
  let G' : ℝ → ℝ → ℝ →L[ℝ] ℂ := fun x u ↦
    (1 : ℝ →L[ℝ] ℝ).smulRight
      (W u * iteratedDeriv (i + 1) (fun x' ↦
        mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x)
  obtain ⟨K, hK, hDecay⟩ :=
    exists_uniform_iteratedDeriv_mellin_decay
      hF hC hCD hSupport (i + 1) σ
  let bound : ℝ → ℝ := fun u ↦ Cw * K * (1 + u ^ 2)⁻¹
  have hBoundInt : Integrable bound := by
    simpa [bound, mul_assoc] using
      integrable_inv_one_add_sq.const_mul (Cw * K)
  have hGMeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (G x) := by
    filter_upwards with x
    exact (hWcont.mul (continuous_iteratedDeriv_mellin_vertical
      hF hC hCD hSupport i x σ)).aestronglyMeasurable
  have hGInt : Integrable (G x₀) := by
    exact integrable_dfiParametricVerticalIntegralDeriv
      hF hC hCD hSupport hWcont hCw hW i σ x₀
  have hG'Meas : AEStronglyMeasurable (G' x₀) := by
    have hc : Continuous (fun u : ℝ ↦
        W u * iteratedDeriv (i + 1) (fun x' ↦
          mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x₀) :=
      hWcont.mul (continuous_iteratedDeriv_mellin_vertical
        hF hC hCD hSupport (i + 1) x₀ σ)
    exact ((ContinuousLinearMap.smulRightL ℝ ℝ ℂ
      (1 : ℝ →L[ℝ] ℝ)).continuous.comp hc).aestronglyMeasurable
  have hMajor : ∀ᵐ u ∂MeasureTheory.volume, ∀ x ∈ Set.univ,
      ‖G' x u‖ ≤ bound u := by
    filter_upwards with u
    intro x _hx
    have hnorm : ‖G' x u‖ = ‖W u * iteratedDeriv (i + 1) (fun x' ↦
        mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x‖ := by
      simp [G']
    rw [hnorm]
    exact norm_mul_le_cauchy_of_quadratic_and_sixth_decay
      hCw hK (hW u) (hDecay x u)
  have hDiff : ∀ᵐ u ∂MeasureTheory.volume, ∀ x ∈ Set.univ,
      HasFDerivAt (G · u) (G' x u) x := by
    filter_upwards with u
    intro x _hx
    have hSmooth := contDiff_mellin_slice hF hC hSupport
      ((σ : ℂ) + (u : ℂ) * I)
    have hiTop : (i : WithTop ℕ∞) < ∞ :=
      WithTop.coe_lt_coe.mpr (ENat.coe_lt_top i)
    have hd : HasDerivAt (iteratedDeriv i (fun x' ↦
        mellin (F x') ((σ : ℂ) + (u : ℂ) * I)))
        (iteratedDeriv (i + 1) (fun x' ↦
          mellin (F x') ((σ : ℂ) + (u : ℂ) * I)) x) x := by
      have hbase := ((hSmooth.differentiable_iteratedDeriv i hiTop)
        x).hasDerivAt
      simpa [iteratedDeriv_succ] using hbase
    simpa [G, G'] using (hd.const_mul (W u)).hasFDerivAt
  have hfd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Set.univ) (μ := MeasureTheory.volume) univ_mem hGMeas hGInt
    hG'Meas hMajor hBoundInt hDiff
  have hG'Int : Integrable (G' x₀) := by
    exact hBoundInt.mono' hG'Meas (hMajor.mono fun u hu => hu x₀ (Set.mem_univ x₀))
  have hd := hfd.hasDerivAt
  rw [ContinuousLinearMap.integral_apply hG'Int] at hd
  simpa [dfiParametricVerticalIntegralDeriv, G, G'] using hd

theorem contDiff_dfiParametricVerticalIntegral
    {F : ℝ → ℝ → ℂ} {A B C D Cw : ℝ} {W : ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (hWcont : Continuous W) (hCw : 0 ≤ Cw)
    (hW : ∀ u : ℝ, ‖W u‖ ≤ Cw * (1 + |u|) ^ 2)
    (σ : ℝ) :
    ContDiff ℝ ∞ (dfiParametricVerticalIntegralDeriv 0 W σ F) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro i _hi
  have hIter : iteratedDeriv i
      (dfiParametricVerticalIntegralDeriv 0 W σ F) =
      dfiParametricVerticalIntegralDeriv i W σ F := by
    induction i with
    | zero => rfl
    | succ i ih =>
        rw [iteratedDeriv_succ, ih (by simp)]
        funext x
        exact (hasDerivAt_dfiParametricVerticalIntegralDeriv
          hF hC hCD hSupport hWcont hCw hW i σ x).deriv
  rw [hIter]
  exact fun x => (hasDerivAt_dfiParametricVerticalIntegralDeriv
    hF hC hCD hSupport hWcont hCw hW i σ x).differentiableAt

end RiemannZeta.GuthMaynard
