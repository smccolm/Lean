import RiemannZeta.GuthMaynard.DFIEquation23Main
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Two-variable Mellin decay for the DFI double Voronoi formula

This file supplies the absolute-convergence theorem needed to pass from the
literal double transform in DFI equation (24) to its source-ordered pair of
dual frequencies.  The two logarithmic Mellin variables are treated as one
Schwartz function on the Euclidean `L²` product of two real lines.
-/

open Complex Set MeasureTheory
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Classical

namespace RiemannZeta.GuthMaynard

/-- The two-variable logarithmic Mellin kernel before equipping the product
with its Euclidean `L²` norm. -/
noncomputable def dfiBiMellinKernelRaw
    (σ τ : ℝ) (E : ℝ → ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (Real.exp (-σ * p.1) : ℂ) * (Real.exp (-τ * p.2) : ℂ) *
    E (Real.exp (-p.1)) (Real.exp (-p.2))

theorem contDiff_dfiBiMellinKernelRaw
    {σ τ : ℝ} {E : ℝ → ℝ → ℂ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E)) :
    ContDiff ℝ ∞ (dfiBiMellinKernelRaw σ τ E) := by
  unfold dfiBiMellinKernelRaw
  have hx : ContDiff ℝ ∞
      (fun p : ℝ × ℝ ↦ (Real.exp (-σ * p.1) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst))
  have hy : ContDiff ℝ ∞
      (fun p : ℝ × ℝ ↦ (Real.exp (-τ * p.2) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd))
  have harg : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦
      (Real.exp (-p.1), Real.exp (-p.2))) := by
    fun_prop
  exact (hx.mul hy).mul (hE.comp harg)

theorem hasCompactSupport_dfiBiMellinKernelRaw
    {σ τ A B C D : ℝ} {E : ℝ → ℝ → ℂ}
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) :
    HasCompactSupport (dfiBiMellinKernelRaw σ τ E) := by
  have hB : 0 < B := hA.trans_le hAB
  have hD : 0 < D := hC.trans_le hCD
  apply HasCompactSupport.intro
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Set.Icc (-Real.log B) (-Real.log A) ×ˢ
        Set.Icc (-Real.log D) (-Real.log C)))
  intro p hp
  have hzero : E (Real.exp (-p.1)) (Real.exp (-p.2)) = 0 := by
    by_contra hne
    have hs := hSupport (show
      (Real.exp (-p.1), Real.exp (-p.2)) ∈
          Function.support (Function.uncurry E) by
        simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)
    obtain ⟨⟨hxA, hxB⟩, ⟨hyC, hyD⟩⟩ := hs
    apply hp
    constructor
    · constructor
      · have := Real.log_le_log (Real.exp_pos _) hxB
        rw [Real.log_exp] at this
        linarith
      · have := Real.log_le_log hA hxA
        rw [Real.log_exp] at this
        linarith
    · constructor
      · have := Real.log_le_log (Real.exp_pos _) hyD
        rw [Real.log_exp] at this
        linarith
      · have := Real.log_le_log hC hyC
        rw [Real.log_exp] at this
        linarith
  simp [dfiBiMellinKernelRaw, hzero]

/-- The logarithmic kernel on the genuine Euclidean product used by
Mathlib's finite-dimensional Fourier transform. -/
noncomputable def dfiBiMellinKernel
    (σ τ : ℝ) (E : ℝ → ℝ → ℂ)
    (p : WithLp 2 (ℝ × ℝ)) : ℂ :=
  dfiBiMellinKernelRaw σ τ E (WithLp.ofLp p)

theorem contDiff_dfiBiMellinKernel
    {σ τ : ℝ} {E : ℝ → ℝ → ℂ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E)) :
    ContDiff ℝ ∞ (dfiBiMellinKernel σ τ E) := by
  exact (contDiff_dfiBiMellinKernelRaw hE).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).contDiff

theorem hasCompactSupport_dfiBiMellinKernel
    {σ τ A B C D : ℝ} {E : ℝ → ℝ → ℂ}
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) :
    HasCompactSupport (dfiBiMellinKernel σ τ E) := by
  exact (hasCompactSupport_dfiBiMellinKernelRaw hA hAB hC hCD hSupport).comp_homeomorph
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).toHomeomorph

/-- The two-variable logarithmic Mellin kernel as a Schwartz function. -/
noncomputable def dfiBiMellinKernelSchwartz
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (σ τ : ℝ) :
    𝓢(WithLp 2 (ℝ × ℝ), ℂ) :=
  (hasCompactSupport_dfiBiMellinKernel (σ := σ) (τ := τ)
    hA hAB hC hCD hSupport).toSchwartzMap
    (contDiff_dfiBiMellinKernel (σ := σ) (τ := τ) hE)

@[simp]
theorem dfiBiMellinKernelSchwartz_apply
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (σ τ : ℝ)
    (p : WithLp 2 (ℝ × ℝ)) :
    dfiBiMellinKernelSchwartz hE hA hAB hC hCD hSupport σ τ p =
      dfiBiMellinKernel σ τ E p := rfl

/-- The iterated two-variable Mellin transform, in the source order used by
DFI: first the second physical variable and then the first. -/
noncomputable def dfiBiMellin
    (E : ℝ → ℝ → ℂ) (z w : ℂ) : ℂ :=
  mellin (fun x ↦ mellin (E x) w) z

theorem dfiFourierChar_prod_phase (r s u v : ℝ) :
    𝐞 (-inner ℝ (WithLp.toLp 2 (r, s)) (WithLp.toLp 2 (u, v))) =
      𝐞 (-(r * u)) * 𝐞 (-(s * v)) := by
  rw [show -inner ℝ (WithLp.toLp 2 (r, s))
      (WithLp.toLp 2 (u, v)) = -(r * u) + -(s * v) by
    simp only [WithLp.prod_inner_apply]
    simp
    ring]
  exact AddChar.map_add_eq_mul Real.fourierChar _ _

/-- Direct logarithmic-coordinate representation of the iterated Mellin
transform.  This exact identity fixes the Fourier signs and the `2π`
normalization before any decay estimate is used. -/
theorem dfiBiMellin_eq_iterated_log_integral
    (E : ℝ → ℝ → ℂ) (σ τ u v : ℝ) :
    dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
        ((τ : ℂ) + (v : ℂ) * I) =
      ∫ r : ℝ, ∫ s : ℝ,
        (𝐞 (-(r * (u / (2 * Real.pi)))) : ℂ) *
          (𝐞 (-(s * (v / (2 * Real.pi)))) : ℂ) *
            dfiBiMellinKernelRaw σ τ E (r, s) := by
  unfold dfiBiMellin
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, add_zero, zero_add, mul_one, neg_mul]
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with r
  rw [mellin_eq_fourier, Real.fourier_eq]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, add_zero, zero_add, mul_one, neg_mul]
  simp only [Circle.smul_def, Complex.real_smul, smul_eq_mul]
  rw [← MeasureTheory.integral_const_mul]
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  simp [dfiBiMellinKernelRaw]
  ring_nf

/-- The two-dimensional Fourier transform of the logarithmic kernel is the
iterated Mellin transform, with both source normalizations visible. -/
theorem dfiBiMellin_eq_fourier_biKernel
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (σ τ u v : ℝ) :
    dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
        ((τ : ℂ) + (v : ℂ) * I) =
      𝓕 (dfiBiMellinKernelSchwartz hE hA hAB hC hCD hSupport σ τ)
        (WithLp.toLp 2
          (u / (2 * Real.pi), v / (2 * Real.pi))) := by
  rw [dfiBiMellin_eq_iterated_log_integral]
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  let ξ : WithLp 2 (ℝ × ℝ) := WithLp.toLp 2
    (u / (2 * Real.pi), v / (2 * Real.pi))
  let G : WithLp 2 (ℝ × ℝ) → ℂ := fun p ↦
    𝐞 (-inner ℝ p ξ) • dfiBiMellinKernel σ τ E p
  have hChange : (∫ p : ℝ × ℝ, G (WithLp.toLp 2 p)) =
      ∫ p : WithLp 2 (ℝ × ℝ), G p :=
    (WithLp.volume_preserving_toLp ℝ ℝ).integral_comp
      (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding G
  have hRawCont : Continuous (fun p : ℝ × ℝ ↦
      G (WithLp.toLp 2 p)) := by
    change Continuous (fun p : ℝ × ℝ ↦
      (𝐞 (-inner ℝ (WithLp.toLp 2 p) ξ) : ℂ) *
        dfiBiMellinKernelRaw σ τ E p)
    have hPhase : Continuous (fun p : ℝ × ℝ ↦
        -inner ℝ (WithLp.toLp 2 p) ξ) := by fun_prop
    have hChar : Continuous (fun p : ℝ × ℝ ↦
        𝐞 (-inner ℝ (WithLp.toLp 2 p) ξ)) :=
      Real.continuous_fourierChar.comp hPhase
    exact (continuous_subtype_val.comp hChar).mul
      (contDiff_dfiBiMellinKernelRaw hE).continuous
  have hRawCompact : HasCompactSupport (fun p : ℝ × ℝ ↦
      G (WithLp.toLp 2 p)) := by
    change HasCompactSupport (fun p : ℝ × ℝ ↦
      (𝐞 (-inner ℝ (WithLp.toLp 2 p) ξ) : ℂ) *
        dfiBiMellinKernelRaw σ τ E p)
    exact (hasCompactSupport_dfiBiMellinKernelRaw
      hA hAB hC hCD hSupport).mul_left
  have hRawInt : Integrable (fun p : ℝ × ℝ ↦
      G (WithLp.toLp 2 p)) :=
    hRawCont.integrable_of_hasCompactSupport hRawCompact
  calc
    (∫ r : ℝ, ∫ s : ℝ,
        (𝐞 (-(r * (u / (2 * Real.pi)))) : ℂ) *
          (𝐞 (-(s * (v / (2 * Real.pi)))) : ℂ) *
            dfiBiMellinKernelRaw σ τ E (r, s)) =
        ∫ p : ℝ × ℝ, G (WithLp.toLp 2 p) := by
      rw [Measure.volume_eq_prod ℝ ℝ,
        MeasureTheory.integral_prod _ hRawInt]
      apply integral_congr_ae
      filter_upwards with r
      apply integral_congr_ae
      filter_upwards with s
      change _ =
        (𝐞 (-inner ℝ (WithLp.toLp 2 (r, s))
          (WithLp.toLp 2
            (u / (2 * Real.pi), v / (2 * Real.pi)))) : ℂ) *
          dfiBiMellinKernelRaw σ τ E (r, s)
      rw [dfiFourierChar_prod_phase]
      simp only [Circle.coe_mul]
    _ = ∫ p : WithLp 2 (ℝ × ℝ), G p := hChange
    _ = _ := by rfl

/-- Fourth polynomial moments of a Schwartz function are integrable in the
source-friendly `(1+‖x‖)^4` form. -/
theorem integrable_one_add_norm_pow_four_mul_norm
    (F : 𝓢(WithLp 2 (ℝ × ℝ), ℂ)) :
    Integrable (fun x : WithLp 2 (ℝ × ℝ) ↦
      (1 + ‖x‖) ^ 4 * ‖F x‖) := by
  have h0 : Integrable (fun x : WithLp 2 (ℝ × ℝ) ↦ ‖F x‖) :=
    F.integrable.norm
  have h1 : Integrable (fun x : WithLp 2 (ℝ × ℝ) ↦ ‖x‖ * ‖F x‖) :=
    by simpa using F.integrable_pow_mul volume 1
  have h2 : Integrable (fun x : WithLp 2 (ℝ × ℝ) ↦
      ‖x‖ ^ 2 * ‖F x‖) :=
    F.integrable_pow_mul volume 2
  have h3 : Integrable (fun x : WithLp 2 (ℝ × ℝ) ↦
      ‖x‖ ^ 3 * ‖F x‖) :=
    F.integrable_pow_mul volume 3
  have h4 : Integrable (fun x : WithLp 2 (ℝ × ℝ) ↦
      ‖x‖ ^ 4 * ‖F x‖) :=
    F.integrable_pow_mul volume 4
  have hsum := h0.add (((h1.const_mul 4).add (h2.const_mul 6)).add
    ((h3.const_mul 4).add h4))
  convert hsum using 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- Absolute convergence of the double DFI vertical kernel after both
quadratically growing Estermann multipliers are inserted.  This is the
Tonelli input for the four double-dual branches in equation (24). -/
theorem integrable_biMellin_quadratic_weight
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (σ τ : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦
      (1 + |p.1|) ^ 2 * (1 + |p.2|) ^ 2 *
        ‖dfiBiMellin E ((σ : ℂ) + (p.1 : ℂ) * I)
          ((τ : ℂ) + (p.2 : ℂ) * I)‖) := by
  let F : 𝓢(WithLp 2 (ℝ × ℝ), ℂ) :=
    𝓕 (dfiBiMellinKernelSchwartz hE hA hAB hC hCD hSupport σ τ)
  let c : ℝ := 2 * Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hcOne : 1 ≤ c := by
    dsimp [c]
    nlinarith [Real.pi_gt_three]
  have hPoly : Integrable (fun q : WithLp 2 (ℝ × ℝ) ↦
      (1 + ‖q‖) ^ 4 * ‖F q‖) :=
    integrable_one_add_norm_pow_four_mul_norm F
  have hScaled : Integrable (fun q : WithLp 2 (ℝ × ℝ) ↦
      (1 + ‖c⁻¹ • q‖) ^ 4 * ‖F (c⁻¹ • q)‖) := by
    simpa only using hPoly.comp_smul (inv_ne_zero (ne_of_gt hc))
  have hPair : Integrable (fun p : ℝ × ℝ ↦
      (1 + ‖c⁻¹ • WithLp.toLp 2 p‖) ^ 4 *
        ‖F (c⁻¹ • WithLp.toLp 2 p)‖) := by
    exact ((WithLp.volume_preserving_toLp ℝ ℝ).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (ℝ × ℝ)).measurableEmbedding).2 hScaled
  have hDom : Integrable (fun p : ℝ × ℝ ↦
      c ^ 4 * ((1 + ‖c⁻¹ • WithLp.toLp 2 p‖) ^ 4 *
        ‖F (c⁻¹ • WithLp.toLp 2 p)‖)) :=
    hPair.const_mul (c ^ 4)
  have hTargetEq : (fun p : ℝ × ℝ ↦
      (1 + |p.1|) ^ 2 * (1 + |p.2|) ^ 2 *
        ‖dfiBiMellin E ((σ : ℂ) + (p.1 : ℂ) * I)
          ((τ : ℂ) + (p.2 : ℂ) * I)‖) =
      fun p : ℝ × ℝ ↦
        (1 + |p.1|) ^ 2 * (1 + |p.2|) ^ 2 *
          ‖F (c⁻¹ • WithLp.toLp 2 p)‖ := by
    funext p
    rw [dfiBiMellin_eq_fourier_biKernel
      hE hA hAB hC hCD hSupport]
    congr 3
    apply WithLp.ofLp_injective
    ext <;> simp [c, div_eq_mul_inv, mul_comm]
  rw [hTargetEq]
  have hTargetCont : Continuous (fun p : ℝ × ℝ ↦
      (1 + |p.1|) ^ 2 * (1 + |p.2|) ^ 2 *
        ‖F (c⁻¹ • WithLp.toLp 2 p)‖) := by
    fun_prop
  apply hDom.mono' hTargetCont.aestronglyMeasurable
  filter_upwards with p
  let q : WithLp 2 (ℝ × ℝ) := c⁻¹ • WithLp.toLp 2 p
  have hqfst : |p.1 / c| ≤ ‖q‖ := by
    have := WithLp.norm_fst_le ℝ q
    simpa [q, div_eq_mul_inv, mul_comm] using this
  have hqsnd : |p.2 / c| ≤ ‖q‖ := by
    have := WithLp.norm_snd_le ℝ q
    simpa [q, div_eq_mul_inv, mul_comm] using this
  have hAbsFst : |p.1| = c * |p.1 / c| := by
    calc
      |p.1| = |c * (p.1 / c)| := by
        congr 1
        field_simp [ne_of_gt hc]
      _ = c * |p.1 / c| := by rw [abs_mul, abs_of_pos hc]
  have hAbsSnd : |p.2| = c * |p.2 / c| := by
    calc
      |p.2| = |c * (p.2 / c)| := by
        congr 1
        field_simp [ne_of_gt hc]
      _ = c * |p.2 / c| := by rw [abs_mul, abs_of_pos hc]
  have hFst : 1 + |p.1| ≤ c * (1 + ‖q‖) := by
    rw [hAbsFst]
    nlinarith
  have hSnd : 1 + |p.2| ≤ c * (1 + ‖q‖) := by
    rw [hAbsSnd]
    nlinarith
  have hFstSq := pow_le_pow_left₀
    (by positivity : 0 ≤ 1 + |p.1|) hFst 2
  have hSndSq := pow_le_pow_left₀
    (by positivity : 0 ≤ 1 + |p.2|) hSnd 2
  have hWeights :
      (1 + |p.1|) ^ 2 * (1 + |p.2|) ^ 2 ≤
        c ^ 4 * (1 + ‖q‖) ^ 4 := by
    calc
      _ ≤ (c * (1 + ‖q‖)) ^ 2 * (c * (1 + ‖q‖)) ^ 2 :=
        mul_le_mul hFstSq hSndSq (by positivity) (by positivity)
      _ = c ^ 4 * (1 + ‖q‖) ^ 4 := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa [q, mul_assoc] using
    mul_le_mul_of_nonneg_right hWeights
      (norm_nonneg (F (c⁻¹ • WithLp.toLp 2 p)))

theorem continuous_dfiBiMellin_vertical
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D) (σ τ : ℝ) :
    Continuous (fun p : ℝ × ℝ ↦
      dfiBiMellin E ((σ : ℂ) + (p.1 : ℂ) * I)
        ((τ : ℂ) + (p.2 : ℂ) * I)) := by
  let F : 𝓢(WithLp 2 (ℝ × ℝ), ℂ) :=
    𝓕 (dfiBiMellinKernelSchwartz hE hA hAB hC hCD hSupport σ τ)
  have hEq : (fun p : ℝ × ℝ ↦
      dfiBiMellin E ((σ : ℂ) + (p.1 : ℂ) * I)
        ((τ : ℂ) + (p.2 : ℂ) * I)) =
      fun p : ℝ × ℝ ↦ F (WithLp.toLp 2
        (p.1 / (2 * Real.pi), p.2 / (2 * Real.pi))) := by
    funext p
    exact dfiBiMellin_eq_fourier_biKernel
      hE hA hAB hC hCD hSupport σ τ p.1 p.2
  rw [hEq]
  fun_prop

/-- Both DFI Estermann branch multipliers may be inserted into the double
Mellin kernel without losing absolute integrability. -/
theorem integrable_dfiDualBranchWeights_mul_biMellin
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (qx qy : ℕ) [NeZero qx] [NeZero qy]
    (dx : ZMod qx) (dy : ZMod qy)
    (xBranch yBranch : DFIVoronoiDualBranch) :
    Integrable (fun p : ℝ × ℝ ↦
      dfiDualBranchVerticalWeight qx dx xBranch p.1 *
        dfiDualBranchVerticalWeight qy dy yBranch p.2 *
          dfiBiMellin E
            (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
            (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)) := by
  obtain ⟨Cx, hCx, hx⟩ :=
    exists_dfiDualBranchVerticalWeight_quadratic_bound qx dx xBranch
  obtain ⟨Cy, hCy, hy⟩ :=
    exists_dfiDualBranchVerticalWeight_quadratic_bound qy dy yBranch
  have hBase := integrable_biMellin_quadratic_weight
    hE hA hAB hC hCD hSupport (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ))
  have hMajor : Integrable (fun p : ℝ × ℝ ↦
      (Cx * Cy) * ((1 + |p.1|) ^ 2 * (1 + |p.2|) ^ 2 *
        ‖dfiBiMellin E
          (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
          (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖)) :=
    by
      simpa only [Complex.ofReal_neg, Complex.ofReal_div,
        Complex.ofReal_one] using hBase.const_mul (Cx * Cy)
  have hCont : Continuous (fun p : ℝ × ℝ ↦
      dfiDualBranchVerticalWeight qx dx xBranch p.1 *
        dfiDualBranchVerticalWeight qy dy yBranch p.2 *
          dfiBiMellin E
            (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
            (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)) := by
    simpa [Function.comp_def, mul_assoc] using
      ((continuous_dfiDualBranchVerticalWeight qx dx xBranch).comp
      continuous_fst).mul
        (((continuous_dfiDualBranchVerticalWeight qy dy yBranch).comp
          continuous_snd).mul
            (continuous_dfiBiMellin_vertical hE hA hAB hC hCD hSupport
              (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ))))
  apply hMajor.mono' hCont.aestronglyMeasurable
  filter_upwards with p
  rw [norm_mul, norm_mul]
  have hWeights :
      ‖dfiDualBranchVerticalWeight qx dx xBranch p.1‖ *
          ‖dfiDualBranchVerticalWeight qy dy yBranch p.2‖ ≤
        (Cx * Cy) * ((1 + |p.1|) ^ 2 * (1 + |p.2|) ^ 2) := by
    calc
      _ ≤ (Cx * (1 + |p.1|) ^ 2) *
          (Cy * (1 + |p.2|) ^ 2) :=
        mul_le_mul (hx p.1) (hy p.2) (norm_nonneg _)
          (mul_nonneg hCx (by positivity))
      _ = _ := by ring
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right hWeights
    (norm_nonneg (dfiBiMellin E
      (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
      (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)))

end RiemannZeta.GuthMaynard
