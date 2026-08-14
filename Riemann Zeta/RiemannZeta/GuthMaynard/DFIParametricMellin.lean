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
    ∀ ξ : ℝ, (1 + |ξ|) ^ 6 * ‖𝓕 f ξ‖ ≤
      64 * (D - C) * (K₀ + K₆) := by
  have hCompact : HasCompactSupport f := by
    apply HasCompactSupport.intro isCompact_Icc
    intro u hu
    by_contra hne
    exact hu (hSupport (by simpa only [Function.mem_support] using hne))
  have derivativeSupport (j : ℕ) :
      Function.support (iteratedDeriv j f) ⊆ Set.Icc C D := by
    have hTsupport : tsupport (iteratedDeriv j f) ⊆ tsupport f := by
      induction j with
      | zero => simp
      | succ j ih =>
          rw [iteratedDeriv_succ]
          exact tsupport_deriv_subset.trans ih
    exact (subset_tsupport _).trans <|
      hTsupport.trans (closure_minimal hSupport isClosed_Icc)
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
      measure_Icc_lt_top fun u _hu => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hBound u
    have hMeasure : (MeasureTheory.volume (Set.Icc C D)).toReal = D - C := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hCD)]
    rw [hIntegralEq]
    calc
      (∫ u in Set.Icc C D, ‖iteratedDeriv j f u‖) =
          ‖∫ u in Set.Icc C D, ‖iteratedDeriv j f u‖‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
      _ ≤ K * (MeasureTheory.volume (Set.Icc C D)).toReal := hSetBound
      _ = (D - C) * K := by rw [hMeasure]; ring
  have hZero (ξ : ℝ) : ‖𝓕 f ξ‖ ≤ (D - C) * K₀ := by
    have h := abs_pow_mul_norm_fourier_complex_le f hf hCompact 0 ξ
    simpa using h.trans (integralBound 0 K₀ hBound₀)
  have hSix (ξ : ℝ) :
      |ξ| ^ 6 * ‖𝓕 f ξ‖ ≤ (D - C) * K₆ :=
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
      (1 + |ξ|) ^ 6 * ‖𝓕 f ξ‖ ≤ 64 * ((D - C) * K₀) :=
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
      (1 + |ξ|) ^ 6 * ‖𝓕 f ξ‖ ≤
          (64 * |ξ| ^ 6) * ‖𝓕 f ξ‖ :=
        mul_le_mul_of_nonneg_right hWeight (norm_nonneg _)
      _ = 64 * (|ξ| ^ 6 * ‖𝓕 f ξ‖) := by ring
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
    intro v hv
    have hgNonzero : g (Real.exp (-v)) ≠ 0 := by
      intro hz
      exact hv (by simp [G, dfiVoronoiMellinKernel, hz])
    have hs := hg.support_subset hgNonzero
    have hUpperPos : 0 < hg.upper := hg.lower_pos.trans_le hg.lower_le_upper
    constructor
    · have hlog : -v ≤ Real.log hg.upper := by
        apply (Real.exp_le_exp).mp
        rw [Real.exp_log hUpperPos]
        exact hs.2
      linarith
    · have hlog : Real.log hg.lower ≤ -v := by
        apply (Real.exp_le_exp).mp
        rw [Real.exp_log hg.lower_pos]
        exact hs.1
      linarith
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
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
    hg.mellin_eq_fourier_mellinKernel (1 / 2) u]
  calc
    (1 + |u|) ^ 6 *
        ‖𝓕 (dfiVoronoiMellinKernelSchwartz hg (1 / 2))
          (u / (2 * Real.pi))‖ ≤
      ((1 + 2 * Real.pi) * (1 + |u / (2 * Real.pi)|)) ^ 6 *
        ‖𝓕 (dfiVoronoiMellinKernelSchwartz hg (1 / 2))
          (u / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ 6 *
        ((1 + |u / (2 * Real.pi)|) ^ 6 *
          ‖𝓕 G (u / (2 * Real.pi))‖) := by
      rw [SchwartzMap.fourier_coe]
      change ((1 + 2 * Real.pi) * (1 + |u / (2 * Real.pi)|)) ^ 6 *
          ‖𝓕 G (u / (2 * Real.pi))‖ = _
      rw [mul_pow]
      ring
    _ ≤ (1 + 2 * Real.pi) ^ 6 *
        (64 * ((-Real.log hg.lower) - (-Real.log hg.upper)) *
          (K₀ + K₆)) :=
      mul_le_mul_of_nonneg_left (hFourier (u / (2 * Real.pi)))
        (pow_nonneg (by positivity) 6)

/-- The physical-variable Euler operator produced by one derivative in the
logarithmic Mellin coordinate. -/
noncomputable def dfiMellinLogOperator
    (σ : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (σ : ℂ) * g x + (x : ℂ) * deriv g x

/-- One logarithmic derivative of the Mellin kernel is exactly minus the
same kernel with the Euler operator applied to its physical weight. -/
theorem deriv_dfiVoronoiMellinKernel
    {σ : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (u : ℝ) :
    deriv (dfiVoronoiMellinKernel σ g) u =
      -(Real.exp (-σ * u) : ℂ) *
        dfiMellinLogOperator σ g (Real.exp (-u)) := by
  have hInnerWeight : HasDerivAt (fun v : ℝ => -σ * v) (-σ) u := by
    simpa using (hasDerivAt_id u).const_mul (-σ)
  have hWeightReal : HasDerivAt (fun v : ℝ => Real.exp (-σ * v))
      (Real.exp (-σ * u) * (-σ)) u :=
    (Real.hasDerivAt_exp (-σ * u)).comp u hInnerWeight
  have hWeight : HasDerivAt
      (fun v : ℝ => (Real.exp (-σ * v) : ℂ))
      ((Real.exp (-σ * u) * (-σ) : ℝ) : ℂ) u := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u hWeightReal
  have hInnerArg : HasDerivAt (fun v : ℝ => -v) (-1) u :=
    hasDerivAt_neg u
  have hArg : HasDerivAt (fun v : ℝ => Real.exp (-v))
      (-Real.exp (-u)) u := by
    simpa only [mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-u)).comp u hInnerArg
  have hgDeriv : HasDerivAt g (deriv g (Real.exp (-u))) (Real.exp (-u)) :=
    (hg.differentiable (by simp)).differentiableAt.hasDerivAt
  have hComp := hgDeriv.scomp u hArg
  have hProduct := hWeight.mul hComp
  apply HasDerivAt.deriv
  convert hProduct using 1
  unfold dfiMellinLogOperator
  simp only [Function.comp_apply, real_smul]
  push_cast
  ring

/-- The physical weight obtained after `k` logarithmic derivatives of a
Mellin kernel.  The sign is included, so the next kernel identity has no
external parity bookkeeping. -/
noncomputable def dfiMellinLogDerivativeIterate
    (σ : ℝ) : ℕ → (ℝ → ℂ) → ℝ → ℂ
  | 0, g => g
  | k + 1, g => fun x =>
      -dfiMellinLogOperator σ (dfiMellinLogDerivativeIterate σ k g) x

@[simp]
theorem dfiMellinLogDerivativeIterate_zero (σ : ℝ) (g : ℝ → ℂ) :
    dfiMellinLogDerivativeIterate σ 0 g = g := rfl

@[simp]
theorem dfiMellinLogDerivativeIterate_succ
    (σ : ℝ) (k : ℕ) (g : ℝ → ℂ) :
    dfiMellinLogDerivativeIterate σ (k + 1) g =
      fun x => -dfiMellinLogOperator σ
        (dfiMellinLogDerivativeIterate σ k g) x := rfl

theorem contDiff_dfiMellinLogOperator
    {σ : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (dfiMellinLogOperator σ g) := by
  have hDeriv : ContDiff ℝ ∞ (deriv g) := by
    simpa [iteratedDeriv_one] using
      (ContDiff.contDiff_iteratedDeriv_top hg 1)
  unfold dfiMellinLogOperator
  have hCast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) :=
    Complex.ofRealCLM.contDiff
  exact contDiff_const.mul hg |>.add (hCast.mul hDeriv)

theorem contDiff_dfiMellinLogDerivativeIterate
    {σ : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    ContDiff ℝ ∞ (dfiMellinLogDerivativeIterate σ k g) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      simpa [dfiMellinLogDerivativeIterate] using
        (contDiff_dfiMellinLogOperator ih).neg

/-- Exact chain-rule expansion of every logarithmic Mellin derivative into
the recursively generated physical Euler weight. -/
theorem iteratedDeriv_dfiVoronoiMellinKernel
    {σ : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (k : ℕ) (u : ℝ) :
    iteratedDeriv k (dfiVoronoiMellinKernel σ g) u =
      dfiVoronoiMellinKernel σ
        (dfiMellinLogDerivativeIterate σ k g) u := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hFunctions : iteratedDeriv k (dfiVoronoiMellinKernel σ g) =
          dfiVoronoiMellinKernel σ
            (dfiMellinLogDerivativeIterate σ k g) := by
        funext v
        exact ih v
      rw [hFunctions, deriv_dfiVoronoiMellinKernel
        (contDiff_dfiMellinLogDerivativeIterate hg k) u]
      simp only [dfiMellinLogDerivativeIterate_succ,
        dfiVoronoiMellinKernel]
      ring

/-- The physical monomials generated by repeated application of the Mellin
logarithmic Euler operator. -/
noncomputable def dfiMellinEulerBasis
    (j : ℕ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ j * iteratedDeriv j g x

theorem hasDerivAt_dfiMellinEulerBasis
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (j : ℕ) (x : ℝ) :
    HasDerivAt (dfiMellinEulerBasis j g)
      ((j : ℂ) * (x : ℂ) ^ (j - 1) * iteratedDeriv j g x +
        (x : ℂ) ^ j * iteratedDeriv (j + 1) g x) x := by
  have hPowReal : HasDerivAt (fun y : ℝ => y ^ j)
      ((j : ℝ) * x ^ (j - 1)) x := hasDerivAt_pow j x
  have hPow : HasDerivAt (fun y : ℝ => ((y : ℂ) ^ j))
      ((j : ℂ) * (x : ℂ) ^ (j - 1)) x := by
    convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hPowReal using 1 <;>
      simp [Function.comp_def]
  have hIter : HasDerivAt (iteratedDeriv j g)
      (iteratedDeriv (j + 1) g x) x := by
    rw [iteratedDeriv_succ]
    exact ((ContDiff.contDiff_iteratedDeriv_top hg j).differentiable
      (by simp)).differentiableAt.hasDerivAt
  simpa only [dfiMellinEulerBasis] using hPow.mul hIter

/-- The Euler operator sends the `j`th physical basis term to the adjacent
two basis terms.  This is the finite algebra underlying DFI's repeated
Mellin integration by parts. -/
theorem dfiMellinLogOperator_eulerBasis
    {σ : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (j : ℕ) (x : ℝ) :
    dfiMellinLogOperator σ (dfiMellinEulerBasis j g) x =
      ((σ : ℂ) + j) * dfiMellinEulerBasis j g x +
        dfiMellinEulerBasis (j + 1) g x := by
  unfold dfiMellinLogOperator
  rw [(hasDerivAt_dfiMellinEulerBasis hg j x).deriv]
  cases j with
  | zero => simp [dfiMellinEulerBasis]
  | succ j =>
      simp only [dfiMellinEulerBasis, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_cancel, pow_succ]
      ring

theorem dfiMellinLogOperator_add
    {σ : ℝ} {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (x : ℝ) :
    dfiMellinLogOperator σ (fun y => f y + g y) x =
      dfiMellinLogOperator σ f x + dfiMellinLogOperator σ g x := by
  have hf' : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by simp)).differentiableAt.hasDerivAt
  have hg' : HasDerivAt g (deriv g x) x :=
    (hg.differentiable (by simp)).differentiableAt.hasDerivAt
  have hDeriv : deriv (fun y => f y + g y) x = deriv f x + deriv g x := by
    simpa only [Pi.add_apply] using (hf'.add hg').deriv
  unfold dfiMellinLogOperator
  rw [hDeriv]
  ring

theorem dfiMellinLogOperator_const_mul
    {σ : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (c : ℂ) (x : ℝ) :
    dfiMellinLogOperator σ (fun y => c * f y) x =
      c * dfiMellinLogOperator σ f x := by
  have hf' : HasDerivAt f (deriv f x) x :=
    (hf.differentiable (by simp)).differentiableAt.hasDerivAt
  have hDeriv : deriv (fun y => c * f y) x = c * deriv f x := by
    exact (hf'.const_mul c).deriv
  unfold dfiMellinLogOperator
  rw [hDeriv]
  ring

theorem dfiMellinLogOperator_neg
    {σ : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    dfiMellinLogOperator σ (fun y => -f y) x =
      -dfiMellinLogOperator σ f x := by
  simpa only [neg_one_mul] using
    dfiMellinLogOperator_const_mul hf (-1) x

@[fun_prop]
theorem contDiff_dfiMellinEulerBasis
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (j : ℕ) :
    ContDiff ℝ ∞ (dfiMellinEulerBasis j g) := by
  unfold dfiMellinEulerBasis
  exact (Complex.ofRealCLM.contDiff.pow j).mul
    (ContDiff.contDiff_iteratedDeriv_top hg j)

noncomputable def dfiMellinEulerPolynomial6
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ : ℂ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  c₀ * dfiMellinEulerBasis 0 g x +
  c₁ * dfiMellinEulerBasis 1 g x +
  c₂ * dfiMellinEulerBasis 2 g x +
  c₃ * dfiMellinEulerBasis 3 g x +
  c₄ * dfiMellinEulerBasis 4 g x +
  c₅ * dfiMellinEulerBasis 5 g x +
  c₆ * dfiMellinEulerBasis 6 g x

theorem contDiff_dfiMellinEulerPolynomial6
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ : ℂ) :
    ContDiff ℝ ∞ (dfiMellinEulerPolynomial6 c₀ c₁ c₂ c₃ c₄ c₅ c₆ g) := by
  unfold dfiMellinEulerPolynomial6
  have h (j : ℕ) (c : ℂ) :
      ContDiff ℝ ∞ (fun x => c * dfiMellinEulerBasis j g x) :=
    contDiff_const.mul (contDiff_dfiMellinEulerBasis hg j)
  exact ((((((h 0 c₀).add (h 1 c₁)).add (h 2 c₂)).add
    (h 3 c₃)).add (h 4 c₄)).add (h 5 c₅)).add (h 6 c₆)

/-- One application of the half-line Mellin Euler operator to a degree-six
Euler polynomial. -/
theorem dfiMellinLogOperator_eulerPolynomial6_half
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ : ℂ) (x : ℝ) :
    dfiMellinLogOperator (1 / 2)
        (dfiMellinEulerPolynomial6 c₀ c₁ c₂ c₃ c₄ c₅ c₆ g) x =
      dfiMellinEulerPolynomial6
        ((1 / 2 : ℂ) * c₀)
        ((3 / 2 : ℂ) * c₁ + c₀)
        ((5 / 2 : ℂ) * c₂ + c₁)
        ((7 / 2 : ℂ) * c₃ + c₂)
        ((9 / 2 : ℂ) * c₄ + c₃)
        ((11 / 2 : ℂ) * c₅ + c₄)
        ((13 / 2 : ℂ) * c₆ + c₅) g x +
      c₆ * dfiMellinEulerBasis 7 g x := by
  unfold dfiMellinEulerPolynomial6
  repeat' rw [dfiMellinLogOperator_add]
  all_goals try fun_prop
  repeat' rw [dfiMellinLogOperator_const_mul]
  all_goals try exact contDiff_dfiMellinEulerBasis hg _
  repeat' rw [dfiMellinLogOperator_eulerBasis hg]
  norm_num
  ring

/-- The exact sixth logarithmic derivative used in the quantitative
Mellin-line estimate.  The rational coefficients are the shifted Stirling
coefficients of `(1/2 + x d/dx)^6`. -/
theorem dfiMellinLogDerivativeIterate_six_half
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) :
    dfiMellinLogDerivativeIterate (1 / 2) 6 g =
      dfiMellinEulerPolynomial6 (1 / 64) (91 / 8) (1771 / 16)
        190 (395 / 4) 18 1 g := by
  have step (c₀ c₁ c₂ c₃ c₄ c₅ : ℂ) :
      dfiMellinLogOperator (1 / 2)
          (dfiMellinEulerPolynomial6 c₀ c₁ c₂ c₃ c₄ c₅ 0 g) =
        dfiMellinEulerPolynomial6
          ((1 / 2 : ℂ) * c₀)
          ((3 / 2 : ℂ) * c₁ + c₀)
          ((5 / 2 : ℂ) * c₂ + c₁)
          ((7 / 2 : ℂ) * c₃ + c₂)
          ((9 / 2 : ℂ) * c₄ + c₃)
          ((11 / 2 : ℂ) * c₅ + c₄) c₅ g := by
    funext x
    simpa using dfiMellinLogOperator_eulerPolynomial6_half
      hg c₀ c₁ c₂ c₃ c₄ c₅ 0 x
  have hZero : g = dfiMellinEulerPolynomial6 1 0 0 0 0 0 0 g := by
    funext x
    simp [dfiMellinEulerPolynomial6, dfiMellinEulerBasis]
  have h₁ : dfiMellinLogDerivativeIterate (1 / 2) 1 g =
      fun x => -dfiMellinEulerPolynomial6 (1 / 2) 1 0 0 0 0 0 g x := by
    change (fun x => -dfiMellinLogOperator (1 / 2) g x) = _
    rw (occs := .pos [1]) [hZero]
    rw [step]
    norm_num
  have h₂ : dfiMellinLogDerivativeIterate (1 / 2) 2 g =
      dfiMellinEulerPolynomial6 (1 / 4) 2 1 0 0 0 0 g := by
    change (fun x => -dfiMellinLogOperator (1 / 2)
      (dfiMellinLogDerivativeIterate (1 / 2) 1 g) x) = _
    rw [h₁]
    funext x
    rw [dfiMellinLogOperator_neg
      (contDiff_dfiMellinEulerPolynomial6 hg _ _ _ _ _ _ _) x,
      congr_fun (step (1 / 2) 1 0 0 0 0) x]
    norm_num
  have h₃ : dfiMellinLogDerivativeIterate (1 / 2) 3 g =
      fun x => -dfiMellinEulerPolynomial6 (1 / 8) (13 / 4)
        (9 / 2) 1 0 0 0 g x := by
    change (fun x => -dfiMellinLogOperator (1 / 2)
      (dfiMellinLogDerivativeIterate (1 / 2) 2 g) x) = _
    rw [h₂, step]
    norm_num
  have h₄ : dfiMellinLogDerivativeIterate (1 / 2) 4 g =
      dfiMellinEulerPolynomial6 (1 / 16) 5 (29 / 2) 8 1 0 0 g := by
    change (fun x => -dfiMellinLogOperator (1 / 2)
      (dfiMellinLogDerivativeIterate (1 / 2) 3 g) x) = _
    rw [h₃]
    funext x
    rw [dfiMellinLogOperator_neg
      (contDiff_dfiMellinEulerPolynomial6 hg _ _ _ _ _ _ _) x,
      congr_fun (step (1 / 8) (13 / 4) (9 / 2) 1 0 0) x]
    norm_num
  have h₅ : dfiMellinLogDerivativeIterate (1 / 2) 5 g =
      fun x => -dfiMellinEulerPolynomial6 (1 / 32) (121 / 16)
        (165 / 4) (85 / 2) (25 / 2) 1 0 g x := by
    change (fun x => -dfiMellinLogOperator (1 / 2)
      (dfiMellinLogDerivativeIterate (1 / 2) 4 g) x) = _
    rw [h₄, step]
    norm_num
  change (fun x => -dfiMellinLogOperator (1 / 2)
    (dfiMellinLogDerivativeIterate (1 / 2) 5 g) x) = _
  rw [h₅]
  funext x
  rw [dfiMellinLogOperator_neg
    (contDiff_dfiMellinEulerPolynomial6 hg _ _ _ _ _ _ _) x,
    congr_fun (step (1 / 32) (121 / 16) (165 / 4) (85 / 2) (25 / 2) 1) x]
  norm_num

/-- Explicit sixth-order kernel bound from physical Euler-basis bounds.  The
constant `512` dominates the sum of the seven shifted-Stirling
coefficients, while `(1+R)^6` simultaneously dominates every `R^j` for
`j ≤ 6`. -/
theorem norm_dfiMellinLogDerivativeIterate_six_half_le
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (x : ℝ) {A R : ℝ}
    (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hBasis : ∀ j ≤ 6,
      ‖dfiMellinEulerBasis j g x‖ ≤ A * R ^ j) :
    ‖dfiMellinLogDerivativeIterate (1 / 2) 6 g x‖ ≤
      512 * A * (1 + R) ^ 6 := by
  rw [congr_fun (dfiMellinLogDerivativeIterate_six_half hg) x]
  unfold dfiMellinEulerPolynomial6
  simp only [one_mul]
  have hPow (j : ℕ) (hj : j ≤ 6) : R ^ j ≤ (1 + R) ^ 6 := by
    have hbase : R ≤ 1 + R := by linarith
    have hj' : R ^ j ≤ (1 + R) ^ j :=
      pow_le_pow_left₀ hR hbase j
    exact hj'.trans (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + R) hj)
  have hTerm (c : ℝ) (hc : 0 ≤ c) (j : ℕ) (hj : j ≤ 6) :
      ‖(c : ℂ) * dfiMellinEulerBasis j g x‖ ≤
        c * (A * (1 + R) ^ 6) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
    calc
      c * ‖dfiMellinEulerBasis j g x‖ ≤ c * (A * R ^ j) := by
        gcongr
        exact hBasis j hj
      _ ≤ c * (A * (1 + R) ^ 6) := by
        gcongr
        exact hPow j hj
  have hTriangle :
      ‖(1 / 64 : ℂ) * dfiMellinEulerBasis 0 g x +
          (91 / 8 : ℂ) * dfiMellinEulerBasis 1 g x +
          (1771 / 16 : ℂ) * dfiMellinEulerBasis 2 g x +
          (190 : ℂ) * dfiMellinEulerBasis 3 g x +
          (395 / 4 : ℂ) * dfiMellinEulerBasis 4 g x +
          (18 : ℂ) * dfiMellinEulerBasis 5 g x +
          dfiMellinEulerBasis 6 g x‖ ≤
        ‖(1 / 64 : ℂ) * dfiMellinEulerBasis 0 g x‖ +
        ‖(91 / 8 : ℂ) * dfiMellinEulerBasis 1 g x‖ +
        ‖(1771 / 16 : ℂ) * dfiMellinEulerBasis 2 g x‖ +
        ‖(190 : ℂ) * dfiMellinEulerBasis 3 g x‖ +
        ‖(395 / 4 : ℂ) * dfiMellinEulerBasis 4 g x‖ +
        ‖(18 : ℂ) * dfiMellinEulerBasis 5 g x‖ +
        ‖dfiMellinEulerBasis 6 g x‖ := by
    calc
      _ ≤ ‖(1 / 64 : ℂ) * dfiMellinEulerBasis 0 g x +
            (91 / 8 : ℂ) * dfiMellinEulerBasis 1 g x +
            (1771 / 16 : ℂ) * dfiMellinEulerBasis 2 g x +
            (190 : ℂ) * dfiMellinEulerBasis 3 g x +
            (395 / 4 : ℂ) * dfiMellinEulerBasis 4 g x +
            (18 : ℂ) * dfiMellinEulerBasis 5 g x‖ +
          ‖dfiMellinEulerBasis 6 g x‖ := norm_add_le _ _
      _ ≤ (‖(1 / 64 : ℂ) * dfiMellinEulerBasis 0 g x +
              (91 / 8 : ℂ) * dfiMellinEulerBasis 1 g x +
              (1771 / 16 : ℂ) * dfiMellinEulerBasis 2 g x +
              (190 : ℂ) * dfiMellinEulerBasis 3 g x +
              (395 / 4 : ℂ) * dfiMellinEulerBasis 4 g x‖ +
            ‖(18 : ℂ) * dfiMellinEulerBasis 5 g x‖) +
          ‖dfiMellinEulerBasis 6 g x‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖(1 / 64 : ℂ) * dfiMellinEulerBasis 0 g x +
                (91 / 8 : ℂ) * dfiMellinEulerBasis 1 g x +
                (1771 / 16 : ℂ) * dfiMellinEulerBasis 2 g x +
                (190 : ℂ) * dfiMellinEulerBasis 3 g x‖ +
              ‖(395 / 4 : ℂ) * dfiMellinEulerBasis 4 g x‖) +
            ‖(18 : ℂ) * dfiMellinEulerBasis 5 g x‖) +
          ‖dfiMellinEulerBasis 6 g x‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ (((‖(1 / 64 : ℂ) * dfiMellinEulerBasis 0 g x +
                  (91 / 8 : ℂ) * dfiMellinEulerBasis 1 g x +
                  (1771 / 16 : ℂ) * dfiMellinEulerBasis 2 g x‖ +
                ‖(190 : ℂ) * dfiMellinEulerBasis 3 g x‖) +
              ‖(395 / 4 : ℂ) * dfiMellinEulerBasis 4 g x‖) +
            ‖(18 : ℂ) * dfiMellinEulerBasis 5 g x‖) +
          ‖dfiMellinEulerBasis 6 g x‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((((‖(1 / 64 : ℂ) * dfiMellinEulerBasis 0 g x +
                    (91 / 8 : ℂ) * dfiMellinEulerBasis 1 g x‖ +
                  ‖(1771 / 16 : ℂ) * dfiMellinEulerBasis 2 g x‖) +
                ‖(190 : ℂ) * dfiMellinEulerBasis 3 g x‖) +
              ‖(395 / 4 : ℂ) * dfiMellinEulerBasis 4 g x‖) +
            ‖(18 : ℂ) * dfiMellinEulerBasis 5 g x‖) +
          ‖dfiMellinEulerBasis 6 g x‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ _ := by
        gcongr
        exact norm_add_le _ _
  refine hTriangle.trans ?_
  have h₀ : ‖(1 / 64 : ℂ) * dfiMellinEulerBasis 0 g x‖ ≤
      (1 / 64) * (A * (1 + R) ^ 6) := by
    convert hTerm (1 / 64) (by norm_num) 0 (by norm_num) using 1
    norm_num
  have h₁ : ‖(91 / 8 : ℂ) * dfiMellinEulerBasis 1 g x‖ ≤
      (91 / 8) * (A * (1 + R) ^ 6) := by
    convert hTerm (91 / 8) (by norm_num) 1 (by norm_num) using 1
    norm_num
  have h₂ : ‖(1771 / 16 : ℂ) * dfiMellinEulerBasis 2 g x‖ ≤
      (1771 / 16) * (A * (1 + R) ^ 6) := by
    convert hTerm (1771 / 16) (by norm_num) 2 (by norm_num) using 1
    norm_num
  have h₃ : ‖(190 : ℂ) * dfiMellinEulerBasis 3 g x‖ ≤
      190 * (A * (1 + R) ^ 6) := by
    exact hTerm 190 (by norm_num) 3 (by norm_num)
  have h₄ : ‖(395 / 4 : ℂ) * dfiMellinEulerBasis 4 g x‖ ≤
      (395 / 4) * (A * (1 + R) ^ 6) := by
    convert hTerm (395 / 4) (by norm_num) 4 (by norm_num) using 1
    norm_num
  have h₅ : ‖(18 : ℂ) * dfiMellinEulerBasis 5 g x‖ ≤
      18 * (A * (1 + R) ^ 6) := by
    exact hTerm 18 (by norm_num) 5 (by norm_num)
  have h₆ : ‖dfiMellinEulerBasis 6 g x‖ ≤ A * (1 + R) ^ 6 := by
    exact (hBasis 6 le_rfl).trans (mul_le_mul_of_nonneg_left
      (hPow 6 le_rfl) hA)
  have hScale : 0 ≤ A * (1 + R) ^ 6 := by positivity
  calc
    _ ≤ (1 / 64) * (A * (1 + R) ^ 6) +
          (91 / 8) * (A * (1 + R) ^ 6) +
          (1771 / 16) * (A * (1 + R) ^ 6) +
          190 * (A * (1 + R) ^ 6) +
          (395 / 4) * (A * (1 + R) ^ 6) +
          18 * (A * (1 + R) ^ 6) +
          A * (1 + R) ^ 6 := by
      gcongr
    _ ≤ 512 * (A * (1 + R) ^ 6) := by linarith
    _ = 512 * A * (1 + R) ^ 6 := by ring

theorem DFIVoronoiTestFunction.iteratedDeriv_eq_zero_of_not_mem
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) (j : ℕ) {x : ℝ}
    (hx : x ∉ Set.Icc hg.lower hg.upper) :
    iteratedDeriv j g x = 0 := by
  have hTsupport : tsupport (iteratedDeriv j g) ⊆ tsupport g := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [iteratedDeriv_succ]
        exact tsupport_deriv_subset.trans ih
  by_contra hne
  have hxSupport : x ∈ Function.support (iteratedDeriv j g) := by
    simpa only [Function.mem_support] using hne
  have hxClosure : x ∈ tsupport g :=
    hTsupport (subset_tsupport _ hxSupport)
  exact hx ((closure_minimal hg.support_subset isClosed_Icc) hxClosure)

/-- Uniform physical derivative bounds imply an explicit sixth-order
Mellin-line bound.  This is the source-uniform form of the integration by
parts step between DFI equations (28) and (29). -/
theorem DFIVoronoiTestFunction.mellin_half_line_bound_of_physical_profile
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDeriv : ∀ j ≤ 6, ∀ x : ℝ,
      ‖iteratedDeriv j g x‖ ≤ A * B ^ j) :
    ∀ u : ℝ,
      (1 + |u|) ^ 6 *
        ‖mellin g ((1 / 2 : ℂ) + (u : ℂ) * I)‖ ≤
      (1 + 2 * Real.pi) ^ 6 *
        (64 * ((-Real.log hg.lower) - (-Real.log hg.upper)) *
          ((max 1 hg.upper) * A +
            (max 1 hg.upper) *
              (512 * A * (1 + (max 1 hg.upper) * B) ^ 6))) := by
  let D : ℝ := max 1 hg.upper
  have hDOne : 1 ≤ D := le_max_left _ _
  have hD : 0 ≤ D := zero_le_one.trans hDOne
  have hUpperD : hg.upper ≤ D := le_max_right _ _
  have kernelWeightBound (v : ℝ)
      (hv : Real.exp (-v) ∈ Set.Icc hg.lower hg.upper) :
      Real.exp (-(1 / 2 : ℝ) * v) ≤ D := by
    have hyD : Real.exp (-v) ≤ D := hv.2.trans hUpperD
    have hsq : Real.exp (-(1 / 2 : ℝ) * v) ^ 2 = Real.exp (-v) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hweight : 0 ≤ Real.exp (-(1 / 2 : ℝ) * v) := (Real.exp_pos _).le
    nlinarith [mul_self_le_mul_self (zero_le_one.trans hDOne)
      (show D ≤ D ^ 2 by nlinarith)]
  have hKernelZero (j : ℕ) (v : ℝ)
      (hv : Real.exp (-v) ∉ Set.Icc hg.lower hg.upper) :
      dfiMellinEulerBasis j g (Real.exp (-v)) = 0 := by
    unfold dfiMellinEulerBasis
    rw [hg.iteratedDeriv_eq_zero_of_not_mem j hv]
    simp
  have hKernelBasis (v : ℝ) (hv : Real.exp (-v) ∈ Set.Icc hg.lower hg.upper) :
      ∀ j ≤ 6,
        ‖dfiMellinEulerBasis j g (Real.exp (-v))‖ ≤
          A * (D * B) ^ j := by
    intro j hj
    unfold dfiMellinEulerBasis
    rw [norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      Real.exp (-v) ^ j * ‖iteratedDeriv j g (Real.exp (-v))‖ ≤
          D ^ j * (A * B ^ j) := by
        gcongr
        · exact hv.2.trans hUpperD
        · exact hDeriv j hj (Real.exp (-v))
      _ = A * (D * B) ^ j := by
        rw [mul_pow]
        ring
  have hK₀ : ∀ v : ℝ,
      ‖iteratedDeriv 0 (dfiVoronoiMellinKernel (1 / 2) g) v‖ ≤ D * A := by
    intro v
    rw [iteratedDeriv_dfiVoronoiMellinKernel hg.smooth 0 v]
    by_cases hv : Real.exp (-v) ∈ Set.Icc hg.lower hg.upper
    · unfold dfiVoronoiMellinKernel
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      simp only [dfiMellinLogDerivativeIterate_zero]
      calc
        Real.exp (-(1 / 2 : ℝ) * v) * ‖g (Real.exp (-v))‖ ≤
            D * (A * B ^ 0) := by
          gcongr
          · exact kernelWeightBound v hv
          · exact hDeriv 0 (by norm_num) (Real.exp (-v))
        _ = D * A := by ring
    · have hz := hKernelZero 0 v hv
      simp [dfiMellinEulerBasis] at hz
      simp only [dfiVoronoiMellinKernel,
        dfiMellinLogDerivativeIterate_zero, hz, mul_zero, norm_zero]
      exact mul_nonneg hD hA
  have hK₆ : ∀ v : ℝ,
      ‖iteratedDeriv 6 (dfiVoronoiMellinKernel (1 / 2) g) v‖ ≤
        D * (512 * A * (1 + D * B) ^ 6) := by
    intro v
    rw [iteratedDeriv_dfiVoronoiMellinKernel hg.smooth 6 v]
    by_cases hv : Real.exp (-v) ∈ Set.Icc hg.lower hg.upper
    · unfold dfiVoronoiMellinKernel
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul (kernelWeightBound v hv)
        (norm_dfiMellinLogDerivativeIterate_six_half_le hg.smooth
          (Real.exp (-v)) hA (mul_nonneg hD hB) (hKernelBasis v hv))
        (norm_nonneg _) (by positivity)
    · have hzero (j : ℕ) :
          dfiMellinEulerBasis j g (Real.exp (-v)) = 0 :=
        hKernelZero j v hv
      unfold dfiVoronoiMellinKernel
      rw [congr_fun (dfiMellinLogDerivativeIterate_six_half hg.smooth)
        (Real.exp (-v))]
      simp only [dfiMellinEulerPolynomial6, hzero, mul_zero, add_zero,
        norm_zero]
      positivity
  simpa only [D] using hg.mellin_half_line_bound_of_kernel_bounds
    (mul_nonneg hD hA)
    (mul_nonneg hD (by positivity)) hK₀ hK₆

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
