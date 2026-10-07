/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

Adapted for Project 83 from LeanModularForms commit
7c41b9b1747d47298f76bdb51f07031087702198,
Modularforms/PeterssonInnerProduct.lean. This port uses Mathlib's existing
upper-half-plane volume, rather than adding a second measurable or measure instance.
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.Petersson

import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-! # Petersson integrals using the actual Mathlib invariant upper-half-plane measure

The pairing over the SL₂(ℤ) domain is a local pairing for higher-level forms.
The canonical higher-level pairing requires the appropriate coset-domain integral.
-/

namespace Dubon2026

open MeasureTheory Measure UpperHalfPlane ModularGroup Complex Set ENNReal
open scoped ComplexConjugate MatrixGroups Pointwise

noncomputable section

local notation "μ_hyp" => (volume : Measure ℍ)

theorem hyperbolicVolume_eq_withDensity : (volume : Measure ℍ) =
    (comap UpperHalfPlane.coe (volume : Measure ℂ)).withDensity
      (fun τ => ENNReal.ofReal (τ.im ^ (-2 : ℤ))) := by
  rw [UpperHalfPlane.volume_def]
  congr 1
  funext τ
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk]
  simp [zpow_neg, zpow_ofNat, one_div, inv_pow]

instance hyperbolicVolume_isOpenPosMeasure : IsOpenPosMeasure (volume : Measure ℍ) := by
  haveI : IsOpenPosMeasure (comap UpperHalfPlane.coe (volume : Measure ℂ)) :=
    IsOpenPosMeasure.comap volume isOpenEmbedding_coe
  have h : (comap UpperHalfPlane.coe (volume : Measure ℂ)) ≪ (volume : Measure ℍ) := by
    rw [hyperbolicVolume_eq_withDensity]
    apply withDensity_absolutelyContinuous'
    · exact (show Continuous (fun τ : ℍ => τ.im ^ (-2 : ℤ)) from
        continuous_im.zpow₀ (-2) (fun τ => Or.inl (ne_of_gt τ.im_pos))).measurable.ennreal_ofReal.aemeasurable
    · exact ae_of_all _ (fun τ => ENNReal.ofReal_ne_zero_iff.mpr (zpow_pos τ.im_pos _))
  exact h.isOpenPosMeasure

private theorem integrableOn_zpow_neg_two_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (· ^ (-2 : ℤ)) (Ioi c) (volume : Measure ℝ) := by
  have h := integrableOn_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hc
  rwa [show (· ^ (-2 : ℝ) : ℝ → ℝ) = (· ^ (-2 : ℤ)) from funext fun _ ↦ by
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_cast, Real.rpow_intCast]] at h

private theorem strip_lintegral_lt_top {c : ℝ} (hc : 0 < c) :
    ∫⁻ p in Icc (-1/2 : ℝ) (1/2) ×ˢ Ioi c,
      ENNReal.ofReal (p.2 ^ (-2 : ℤ)) ∂(volume : Measure (ℝ × ℝ)) < ⊤ := by
  rw [volume_eq_prod ℝ ℝ, setLIntegral_prod_symm _ (by fun_prop)]
  simp_rw [setLIntegral_const]
  calc ∫⁻ y in Ioi c, ENNReal.ofReal (y ^ (-2 : ℤ)) *
        volume (Icc (-1/2 : ℝ) (1/2)) ∂volume
      ≤ ∫⁻ y in Ioi c, ENNReal.ofReal (y ^ (-2 : ℤ)) * 1 ∂volume := by
        gcongr with y; rw [Real.volume_Icc]; norm_num
    _ = _ := by simp
    _ < ⊤ := lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi
        fun y _ ↦ Real.ofReal_le_enorm _)
        (integrableOn_zpow_neg_two_Ioi hc).hasFiniteIntegral

/-- The hyperbolic measure of the standard fundamental domain is finite. -/
theorem hyperbolicMeasure_fd_lt_top : μ_hyp fd < ⊤ := by
  have hfd : MeasurableSet (fd : Set ℍ) :=
    ((isClosed_le continuous_const (continuous_normSq.comp continuous_coe)).inter
      (isClosed_le (continuous_abs.comp continuous_re) continuous_const)).measurableSet
  rw [hyperbolicVolume_eq_withDensity, withDensity_apply _ hfd]
  set f : ℂ → ENNReal := fun z ↦ ENNReal.ofReal (z.im ^ (-2 : ℤ))
  change ∫⁻ τ in fd, f ↑τ ∂comap UpperHalfPlane.coe volume < ⊤
  rw [(⟨UpperHalfPlane.isOpenEmbedding_coe.measurableEmbedding.measurable,
       UpperHalfPlane.isOpenEmbedding_coe.measurableEmbedding.map_comap volume⟩ :
       MeasurePreserving UpperHalfPlane.coe _ _).setLIntegral_comp_emb
    UpperHalfPlane.isOpenEmbedding_coe.measurableEmbedding f fd]
  set T := Icc (-1/2 : ℝ) (1/2) ×ˢ Ioi (Real.sqrt 3 / 4)
  have h_prod : ∫⁻ z in equivRealProd ⁻¹' T, f z ∂(volume : Measure ℂ) =
      ∫⁻ p in T, ENNReal.ofReal (p.2 ^ (-2 : ℤ)) ∂(volume : Measure (ℝ × ℝ)) := by
    rw [show (⇑equivRealProd : ℂ → ℝ × ℝ) = ⇑measurableEquivRealProd from rfl]
    have h := volume_preserving_equiv_real_prod.setLIntegral_comp_emb
        measurableEquivRealProd.measurableEmbedding
        (fun p : ℝ × ℝ ↦ ENNReal.ofReal (p.2 ^ (-2 : ℤ)))
        (measurableEquivRealProd ⁻¹' T)
    rw [MeasurableEquiv.image_preimage] at h
    simpa only [measurableEquivRealProd_apply, f] using h
  calc ∫⁻ z in UpperHalfPlane.coe '' fd, f z ∂volume.restrict (range UpperHalfPlane.coe)
      ≤ ∫⁻ z in UpperHalfPlane.coe '' fd, f z ∂volume :=
        lintegral_mono' (restrict_mono Subset.rfl restrict_le_self) le_rfl
    _ ≤ ∫⁻ z in equivRealProd ⁻¹' T, f z ∂volume :=
        lintegral_mono_set fun z ↦ by
          rintro ⟨τ, hτ, rfl⟩
          simp only [mem_preimage, equivRealProd_apply, coe_re, coe_im]
          refine ⟨⟨by linarith [(abs_le.mp hτ.2).1], (abs_le.mp hτ.2).2⟩,
            mem_Ioi.mpr ?_⟩
          have h := three_le_four_mul_im_sq_of_mem_fd hτ
          rw [show (4 : ℝ) * τ.im ^ 2 = (2 * τ.im) ^ 2 from by ring] at h
          have h2 := Real.sqrt_le_sqrt h
          rw [Real.sqrt_sq (by linarith [τ.im_pos])] at h2
          nlinarith [Real.sqrt_pos_of_pos (show (3 : ℝ) > 0 by norm_num)]
    _ = ∫⁻ p in T, ENNReal.ofReal (p.2 ^ (-2 : ℤ)) ∂volume := h_prod
    _ < ⊤ := strip_lintegral_lt_top (by positivity)

/-- The Petersson inner product of two functions `f, g : ℍ → ℂ` of weight `k`,
integrated over a fundamental domain `D` with respect to the hyperbolic measure.

The integrand is `conj(f(τ)) · g(τ) · (Im τ)^k`, which equals
`petersson k f g τ` from `Mathlib.NumberTheory.ModularForms.Petersson`. -/
def peterssonInner (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) : ℂ :=
  ∫ τ in D, petersson k f g τ ∂μ_hyp

/-- Hermitian symmetry: `conj ⟨g, f⟩ = ⟨f, g⟩`. -/
theorem peterssonInner_conj_symm (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    conj (peterssonInner k D g f) = peterssonInner k D f g := by
  simp only [peterssonInner, ← integral_conj, petersson_symm k g f]

/-- The pairing with zero on the right vanishes. -/
theorem peterssonInner_zero_right (k : ℤ) (D : Set ℍ) (f : ℍ → ℂ) :
    peterssonInner k D f 0 = 0 := by
  simp [peterssonInner, petersson]

/-- The pairing with zero on the left vanishes. -/
theorem peterssonInner_zero_left (k : ℤ) (D : Set ℍ) (g : ℍ → ℂ) :
    peterssonInner k D 0 g = 0 := by
  simp [peterssonInner, petersson]

/-- Negation in the right argument. -/
theorem peterssonInner_neg_right (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    peterssonInner k D f (-g) = -peterssonInner k D f g := by
  simp only [peterssonInner, petersson, Pi.neg_apply, mul_neg, neg_mul, integral_neg]

/-- Negation in the left argument. -/
theorem peterssonInner_neg_left (k : ℤ) (D : Set ℍ) (f g : ℍ → ℂ) :
    peterssonInner k D (-f) g = -peterssonInner k D f g := by
  simp only [peterssonInner, petersson, Pi.neg_apply, map_neg, neg_mul, integral_neg]

/-- The Petersson integrand of cusp forms is integrable over the standard fundamental
domain against the hyperbolic measure. -/
theorem peterssonInner_integrableOn {F F' : Type*} [FunLike F ℍ ℂ] [FunLike F' ℍ ℂ]
    (k : ℤ) (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    [CuspFormClass F Γ k] [ModularFormClass F' Γ k]
    (f : F) (f' : F') :
    IntegrableOn (fun τ ↦ petersson k f f' τ) fd μ_hyp := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ f f'
  exact IntegrableOn.of_bound hyperbolicMeasure_fd_lt_top
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f')).aestronglyMeasurable.restrict) C
    (ae_of_all _ fun τ ↦ hC τ)

/-- Additivity in the second argument. -/
theorem peterssonInner_add_right (k : ℤ) (D : Set ℍ) (f g₁ g₂ : ℍ → ℂ)
    (hg₁ : IntegrableOn (fun τ ↦ petersson k f g₁ τ) D μ_hyp)
    (hg₂ : IntegrableOn (fun τ ↦ petersson k f g₂ τ) D μ_hyp) :
    peterssonInner k D f (g₁ + g₂) = peterssonInner k D f g₁ + peterssonInner k D f g₂ := by
  rw [show peterssonInner k D f (g₁ + g₂) =
      ∫ τ in D, (petersson k f g₁ τ + petersson k f g₂ τ) ∂μ_hyp from by
    simp only [peterssonInner, petersson, Pi.add_apply]; congr 1; ext τ; ring]
  exact integral_add hg₁ hg₂

/-- Scalar multiplication in the second argument. -/
theorem peterssonInner_smul_right (k : ℤ) (D : Set ℍ) (c : ℂ) (f g : ℍ → ℂ) :
    peterssonInner k D f (c • g) = c * peterssonInner k D f g := by
  rw [show peterssonInner k D f (c • g) = ∫ τ in D, c * petersson k f g τ ∂μ_hyp from by
    simp only [peterssonInner, petersson, Pi.smul_apply, smul_eq_mul]
    congr 1; ext τ; ring]
  exact integral_const_mul c _

/-- Conjugate-scalar multiplication in the left argument. -/
theorem peterssonInner_conj_smul_left (k : ℤ) (D : Set ℍ) (c : ℂ) (f g : ℍ → ℂ) :
    peterssonInner k D (c • f) g = conj c * peterssonInner k D f g := by
  rw [show peterssonInner k D (c • f) g = ∫ τ in D, conj c * petersson k f g τ ∂μ_hyp from by
    simp only [peterssonInner, petersson, Pi.smul_apply, smul_eq_mul, map_mul]
    congr 1; ext τ; ring]
  exact integral_const_mul (conj c) _

/-- The open fundamental domain `𝒟ᵒ` is open in `ℍ`. -/
theorem isOpen_fdo : IsOpen (fdo : Set ℍ) :=
  (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_coe)).inter
    (isOpen_lt (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const)

/-- `𝒟ᵒ ⊆ 𝒟`. -/
theorem fdo_subset_fd : (fdo : Set ℍ) ⊆ fd :=
  fun _ ⟨h1, h2⟩ ↦ ⟨le_of_lt h1, le_of_lt h2⟩

/-- `𝒟 ⊆ closure 𝒟ᵒ`: every point of the closed fundamental domain is a limit of
points in the open fundamental domain. -/
theorem fd_subset_closure_fdo : (fd : Set ℍ) ⊆ closure fdo := by
  intro z hz
  rw [isOpenEmbedding_coe.isInducing.closure_eq_preimage_closure_image fdo,
    mem_preimage, Metric.mem_closure_iff]
  intro ε hε
  set t := min (ε / 3) (1 / 2)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have him : 4 * z.im ^ 2 ≥ 3 := by linarith [three_le_four_mul_im_sq_of_mem_fd hz]
  have hre : z.re ^ 2 ≤ 1 / 4 := by have := hz.2; rw [abs_le] at this; nlinarith
  have hns : z.re ^ 2 + z.im ^ 2 ≥ 1 := by
    have := hz.1; simp [Complex.normSq_apply, coe_re, coe_im] at this; linarith
  have him_half : z.im > 1 / 2 := by nlinarith [z.im_pos]
  set wc : ℂ := ⟨(1 - t) * z.re, z.im + t⟩
  refine ⟨wc, ⟨⟨wc, by show 0 < wc.im; linarith [z.im_pos]⟩, ?_, rfl⟩, ?_⟩
  · refine ⟨?_, ?_⟩
    · show 1 < Complex.normSq wc; simp only [Complex.normSq_apply, wc]
      nlinarith [sq_nonneg (t * z.re)]
    · show |wc.re| < 1 / 2; simp only [wc]
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
      calc (1 - t) * |z.re| ≤ (1 - t) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hz.2 (by linarith)
        _ < 1 / 2 := by nlinarith
  · calc dist (↑z) wc
        ≤ |((↑z : ℂ) - wc).re| + |((↑z : ℂ) - wc).im| := by
          rw [Complex.dist_eq]; exact Complex.norm_le_abs_re_add_abs_im _
      _ = t * |z.re| + t := by
          simp [coe_re, coe_im, wc, sub_mul, abs_mul, abs_of_pos ht, abs_neg]
      _ ≤ t * (1 / 2) + t := by linarith [mul_le_mul_of_nonneg_left hz.2 ht.le]
      _ = t * (3 / 2) := by ring
      _ ≤ (ε / 3) * (3 / 2) := by linarith [min_le_left (ε / 3) (1 / 2 : ℝ)]
      _ < ε := by linarith

/-- A vertical line `{z : ℂ | z.re = c}` has zero Lebesgue measure in `ℂ`. -/
theorem volume_complex_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  rw [show {z : ℂ | z.re = c} = measurableEquivRealProd ⁻¹' ({c} ×ˢ univ) from by
    ext z; simp [measurableEquivRealProd]]
  rw [volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet,
    volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

private theorem finite_sq_eq (d : ℝ) : Set.Finite {y : ℝ | y ^ 2 = d} := by
  by_cases hd : d < 0
  · convert Set.finite_empty; ext y; simp; intro h; linarith [sq_nonneg y]
  · push Not at hd
    exact (({Real.sqrt d, -Real.sqrt d} : Set ℝ).toFinite).subset (fun y hy ↦ by
      simp only [mem_setOf_eq] at hy
      exact (sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [hy, Real.sq_sqrt hd])).elim
        (fun h ↦ Or.inl h) (fun h ↦ Or.inr (mem_singleton_iff.mpr h)))

/-- A level set `{z : ℂ | normSq z = c}` has zero Lebesgue measure in `ℂ`. -/
theorem volume_complex_normSq_eq (c : ℝ) :
    volume {z : ℂ | Complex.normSq z = c} = 0 := by
  calc volume {z : ℂ | Complex.normSq z = c}
      = volume (measurableEquivRealProd ⁻¹'
          {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = c}) := by
        congr 1; ext z; simp [measurableEquivRealProd, Complex.normSq_apply, sq]
    _ = volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = c} :=
        volume_preserving_equiv_real_prod.measure_preimage
          (measurableSet_eq_fun (by fun_prop) measurable_const).nullMeasurableSet
    _ = 0 := by
        rw [volume_eq_prod,
          measure_prod_null (measurableSet_eq_fun (by fun_prop) measurable_const)]
        filter_upwards with x; simp only [Pi.zero_apply]
        apply measure_mono_null (fun y (hy : x ^ 2 + y ^ 2 = c) ↦
          show y ^ 2 = c - x ^ 2 by linarith)
        exact (finite_sq_eq _).measure_zero _

/-- If a subset of `ℂ` has zero Lebesgue measure, its preimage in `ℍ` has
zero hyperbolic measure. -/
theorem hyperbolicMeasure_preimage_null {S : Set ℂ} (hS : volume S = 0) :
    μ_hyp (UpperHalfPlane.coe ⁻¹' S) = 0 := by
  rw [hyperbolicVolume_eq_withDensity]
  apply withDensity_absolutelyContinuous
  rw [UpperHalfPlane.isOpenEmbedding_coe.measurableEmbedding.comap_apply]
  exact measure_mono_null (image_preimage_subset _ _) hS

/-- **The boundary `fd \ fdo` has zero hyperbolic measure.**

`fd \ fdo ⊆ {normSq = 1} ∪ {Re = 1/2} ∪ {Re = −1/2}`, each of which has
zero Lebesgue measure in `ℂ`. -/
theorem hyperbolicMeasure_fd_boundary : μ_hyp (fd \ fdo) = 0 := by
  apply measure_mono_null _ (hyperbolicMeasure_preimage_null
    (measure_union_null
      (measure_union_null (volume_complex_normSq_eq 1) (volume_complex_re_eq (1/2)))
      (volume_complex_re_eq (-1/2))))
  intro τ ⟨hfd, hfdo⟩
  simp only [fd, fdo, mem_setOf_eq, not_and, not_lt] at hfd hfdo
  obtain ⟨h1, h2⟩ := hfd
  simp only [mem_preimage, mem_union, mem_setOf_eq]
  by_cases h : Complex.normSq (τ : ℂ) = 1
  · left; left; exact h
  · have hns : 1 < Complex.normSq (τ : ℂ) := lt_of_le_of_ne h1 (Ne.symm h)
    have habs : |τ.re| = 1 / 2 := le_antisymm h2 (hfdo hns)
    by_cases hre : 0 ≤ τ.re
    · left; right; rw [coe_re]; rwa [abs_of_nonneg hre] at habs
    · push Not at hre; right
      rw [coe_re]; rw [abs_of_neg hre] at habs; linarith

/-- `fd` and `fdo` are a.e. equal w.r.t. the hyperbolic measure. -/
theorem fd_ae_eq_fdo : (fd : Set ℍ) =ᶠ[ae μ_hyp] fdo :=
  ae_eq_set.mpr ⟨hyperbolicMeasure_fd_boundary, by
    rw [show (fdo : Set ℍ) \ fd = ∅ from diff_eq_empty.mpr fdo_subset_fd]
    exact measure_empty⟩

/-- Integrals over `fd` and `fdo` agree against `μ_hyp`. -/
theorem setIntegral_fd_eq_fdo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℍ → E) : ∫ τ in fd, f τ ∂μ_hyp = ∫ τ in fdo, f τ ∂μ_hyp :=
  setIntegral_congr_set fd_ae_eq_fdo

private lemma petersson_self_re_eq (z : ℂ) (y : ℝ) (k : ℤ) :
    (starRingEnd ℂ z * z * (↑y : ℂ) ^ k).re = Complex.normSq z * y ^ k := by
  rw [show starRingEnd ℂ z * z = ↑(Complex.normSq z) from Complex.normSq_eq_conj_mul_self.symm,
    ← Complex.ofReal_zpow, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem eq_zero_on_fd_of_peterssonInner_self_eq_zero {F : Type*} [FunLike F ℍ ℂ]
    {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    [CuspFormClass F Γ k]
    (f : F) (hpet : peterssonInner k fd (fun τ ↦ f τ) (fun τ ↦ f τ) = 0)
    {τ : ℍ} (hτ : τ ∈ fd) : f τ = 0 := by
  set g : ℍ → ℝ := fun z ↦ (petersson k (⇑f) (⇑f) z).re
  have hint := peterssonInner_integrableOn k Γ f f
  have hg_zero : ∫ z in fd, g z ∂(volume : Measure ℍ) = 0 := by
    trans RCLike.re (∫ z in fd, petersson k (⇑f) (⇑f) z ∂(volume : Measure ℍ))
    · exact integral_re hint
    · simp only [peterssonInner] at hpet; rw [hpet]; simp
  have hg_ae : g =ᶠ[ae ((volume : Measure ℍ).restrict fd)] 0 := by
    rwa [← integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ fun z ↦ show 0 ≤ g z from by
        simp only [g, petersson]
        exact (petersson_self_re_eq (f z) z.im k).symm ▸
          mul_nonneg (Complex.normSq_nonneg _) (zpow_nonneg z.im_pos.le _)) hint.re]
  have hg_cont : Continuous g :=
    Complex.continuous_re.comp (petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous f))
  have hg_fdo : EqOn g 0 fdo :=
    Measure.eqOn_open_of_ae_eq
      (hg_ae.filter_mono (ae_mono (restrict_mono fdo_subset_fd le_rfl)))
      isOpen_fdo hg_cont.continuousOn continuousOn_const
  have hgτ : g τ = 0 :=
    (EqOn.of_subset_closure hg_fdo hg_cont.continuousOn continuousOn_const
      fdo_subset_fd fd_subset_closure_fdo) hτ
  simp only [g, petersson] at hgτ
  rw [petersson_self_re_eq] at hgτ
  exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hgτ).elim id
    (fun h ↦ absurd h (ne_of_gt (zpow_pos τ.im_pos k))))


end

end Dubon2026
