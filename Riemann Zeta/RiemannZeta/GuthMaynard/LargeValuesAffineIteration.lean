import RiemannZeta.GuthMaynard.LargeValuesAffine

open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff FourierTransform Topology

namespace RiemannZeta.GuthMaynard

/-!
# Guth--Maynard Section 9: smoothing iteration

This module carries the exact smoothing identities from Lemma 9.2 through
the finite natural-number iteration replacing the paper's informal
downward induction in the exponent.
-/

/-- The normalized Section 9 smoother preserves mass up to the fixed
cutoff mass.  This is the exact real-valued convolution identity used in
the `L¹` part of the iteration. -/
theorem integral_gmAffineTildeSchwartz_eq_mul
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) :
    (∫ u : ℝ, gmAffineTildeSchwartz T hT f u) =
      (∫ x : ℝ, T * gmCubicLocalBump (T * x)) *
        ∫ u : ℝ, f u := by
  let k : ℝ → ℝ := fun x => T * gmCubicLocalBump (T * x)
  have hk : Integrable k := by
    have hcomplex : Integrable (fun x : ℝ => gmAffineSmoothingKernel T hT x) :=
      (gmAffineSmoothingKernel T hT).integrable
    have hreal : Integrable (fun x : ℝ =>
        Complex.re (gmAffineSmoothingKernel T hT x)) :=
      Complex.reCLM.integrable_comp hcomplex
    apply hreal.congr
    filter_upwards with x
    dsimp only [k]
    rw [gmAffineSmoothingKernel_apply]
    simp
  have hprod : Integrable (fun p : ℝ × ℝ =>
      (ContinuousLinearMap.mul ℝ ℝ) (k p.2) (f (p.1 - p.2))) :=
    hk.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) f.integrable
  simp_rw [gmAffineTildeSchwartz_apply T hT f]
  change (∫ u : ℝ, ∫ t : ℝ, k t * f (u - t)) =
    (∫ x : ℝ, k x) * ∫ u : ℝ, f u
  calc
    (∫ u : ℝ, ∫ t : ℝ, k t * f (u - t)) =
        ∫ t : ℝ, ∫ u : ℝ, k t * f (u - t) :=
      integral_integral_swap hprod
    _ = ∫ t : ℝ, k t * ∫ u : ℝ, f (u - t) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [integral_const_mul]
    _ = ∫ t : ℝ, k t * ∫ u : ℝ, f u := by
      simp_rw [integral_sub_right_eq_self]
    _ = (∫ x : ℝ, k x) * ∫ u : ℝ, f u := by
      rw [integral_mul_const]

/-- The source `L¹` estimate for the smoothed function, with the explicit
constant supplied by the fixed compact cutoff. -/
theorem integral_gmAffineTildeSchwartz_le
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ u, 0 ≤ f u) :
    (∫ u : ℝ, gmAffineTildeSchwartz T hT f u) ≤
      4 * ∫ u : ℝ, f u := by
  rw [integral_gmAffineTildeSchwartz_eq_mul]
  exact mul_le_mul_of_nonneg_right
    (integral_gmAffineSmoothingKernelReal_le_four T hT)
    (integral_nonneg hf)

/-- Exact Fourier multiplier identity for the Section 9 smoother. -/
theorem fourier_gmAffineComplexify_tilde
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) :
    fourier (gmAffineComplexify (gmAffineTildeSchwartz T hT f)) =
      SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
        (fourier (gmAffineSmoothingKernel T hT))
        (fourier (gmAffineComplexify f)) := by
  rw [gmAffineComplexify_tilde_eq_convolution,
    SchwartzMap.fourier_convolution]

/-- Uniform Fourier-multiplier bound for the normalized smoothing kernel. -/
theorem norm_fourier_gmAffineSmoothingKernel_le_four
    (T : ℝ) (hT : 0 < T) (xi : ℝ) :
    ‖fourier (gmAffineSmoothingKernel T hT) xi‖ ≤ 4 := by
  calc
    ‖fourier (gmAffineSmoothingKernel T hT) xi‖ ≤
        ∫ x : ℝ, ‖gmAffineSmoothingKernel T hT x‖ := by
      exact VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 volume (innerₗ ℝ) (gmAffineSmoothingKernel T hT) xi
    _ = ∫ x : ℝ, T * gmCubicLocalBump (T * x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [gmAffineSmoothingKernel_apply, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hT.le (gmCubicLocalBump_nonneg (T * x)))]
    _ ≤ 4 := integral_gmAffineSmoothingKernelReal_le_four T hT

/-- The exact `L²` stability estimate for `f_tilde`; the fixed constant
is immaterial to the `T^δ` iteration but is kept explicit. -/
theorem integral_gmAffineTildeSchwartz_sq_le
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) :
    (∫ u : ℝ, gmAffineTildeSchwartz T hT f u ^ 2) ≤
      16 * ∫ u : ℝ, f u ^ 2 := by
  let ft := gmAffineComplexify (gmAffineTildeSchwartz T hT f)
  let ff := gmAffineComplexify f
  have hffInt : Integrable (fun xi : ℝ => ‖fourier ff xi‖ ^ 2) := by
    let g := fourier ff
    have hg : Integrable (fun xi : ℝ => ‖g xi‖ ^ (2 : ℝ)) := by
      simpa using (g.memLp (2 : ENNReal)).integrable_norm_rpow
        (by norm_num : (2 : ENNReal) ≠ 0) ENNReal.ofNat_ne_top
    simpa only [g, Real.rpow_two] using hg
  have hftInt : Integrable (fun xi : ℝ => ‖fourier ft xi‖ ^ 2) := by
    let g := fourier ft
    have hg : Integrable (fun xi : ℝ => ‖g xi‖ ^ (2 : ℝ)) := by
      simpa using (g.memLp (2 : ENNReal)).integrable_norm_rpow
        (by norm_num : (2 : ENNReal) ≠ 0) ENNReal.ofNat_ne_top
    simpa only [g, Real.rpow_two] using hg
  have hpoint : ∀ xi : ℝ,
      ‖fourier ft xi‖ ^ 2 ≤ 16 * ‖fourier ff xi‖ ^ 2 := by
    intro xi
    have hmul : ‖fourier ft xi‖ ≤ 4 * ‖fourier ff xi‖ := by
      dsimp only [ft, ff]
      rw [fourier_gmAffineComplexify_tilde T hT f,
        SchwartzMap.pairing_apply_apply]
      change ‖fourier (gmAffineSmoothingKernel T hT) xi *
          fourier (gmAffineComplexify f) xi‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_fourier_gmAffineSmoothingKernel_le_four T hT xi) (norm_nonneg _)
    calc
      ‖fourier ft xi‖ ^ 2 ≤ (4 * ‖fourier ff xi‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))).mpr hmul
      _ = 16 * ‖fourier ff xi‖ ^ 2 := by ring
  calc
    (∫ u : ℝ, gmAffineTildeSchwartz T hT f u ^ 2) =
        ∫ u : ℝ, ‖ft u‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with u
      simp [ft]
    _ = ∫ xi : ℝ, ‖fourier ft xi‖ ^ 2 :=
      (SchwartzMap.integral_norm_sq_fourier ft).symm
    _ ≤ ∫ xi : ℝ, 16 * ‖fourier ff xi‖ ^ 2 := by
      exact integral_mono hftInt (hffInt.const_mul 16)
        hpoint
    _ = 16 * ∫ xi : ℝ, ‖fourier ff xi‖ ^ 2 := by
      rw [integral_const_mul]
    _ = 16 * ∫ u : ℝ, ‖ff u‖ ^ 2 := by
      rw [SchwartzMap.integral_norm_sq_fourier]
    _ = 16 * ∫ u : ℝ, f u ^ 2 := by
      congr 1
      apply integral_congr_ae
      filter_upwards with u
      simp [ff]

/-- The symmetric width-`1/T` interval used in the retained part of the
second Poisson sum. -/
def gmAffineUnitInterval (T x : ℝ) : Set ℝ :=
  Set.Icc (x - 1 / T) (x + 1 / T)

/-- The source smoother written in the `u'` variable used after the
second Poisson summation. -/
theorem gmAffineTildeSchwartz_apply_sub
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    gmAffineTildeSchwartz T hT f x =
      ∫ u' : ℝ, T * gmCubicLocalBump (T * (x - u')) * f u' := by
  rw [gmAffineTildeSchwartz_apply]
  let q : ℝ → ℝ := fun t => T * gmCubicLocalBump (T * t) * f (x - t)
  simpa only [q, sub_sub_cancel] using
    (integral_sub_left_eq_self q volume x).symm

/-- A retained width-`1/T` neighborhood is majorized by the actual
normalized smoother, with no informal "almost constant" step. -/
theorem setIntegral_gmAffineUnitInterval_le_tilde
    {T : ℝ} (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ u, 0 ≤ f u) (x : ℝ) :
    (∫ u' in gmAffineUnitInterval T x, T * f u') ≤
      gmAffineTildeSchwartz T hT f x := by
  let G : ℝ → ℝ := fun u' =>
    T * gmCubicLocalBump (T * (x - u')) * f u'
  have hGint : Integrable G := by
    apply (f.integrable.norm.const_mul T).mono'
    · have hbcont : Continuous gmCubicLocalBump := by
        simpa only [gmAffineLocalBumpSchwartz_apply, Complex.ofReal_re] using
          (Complex.continuous_re.comp gmAffineLocalBumpSchwartz.continuous)
      exact ((continuous_const.mul
        (hbcont.comp (continuous_const.mul
          (continuous_const.sub continuous_id)))).mul f.continuous).aestronglyMeasurable
    · filter_upwards with u'
      dsimp only [G]
      simp only [Real.norm_eq_abs]
      have hb := gmCubicLocalBump_le_one (T * (x - u'))
      calc
        |T * gmCubicLocalBump (T * (x - u')) * f u'| =
            T * gmCubicLocalBump (T * (x - u')) * |f u'| := by
          rw [abs_mul, abs_mul, abs_of_pos hT,
            abs_of_nonneg (gmCubicLocalBump_nonneg _)]
        _ ≤ T * 1 * |f u'| := by gcongr
        _ = T * |f u'| := by ring
  calc
    (∫ u' in gmAffineUnitInterval T x, T * f u') =
        ∫ u' in gmAffineUnitInterval T x, G u' := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro u' hu'
      have hwidth : |T * (x - u')| ≤ 1 := by
        have hdiff : |x - u'| ≤ 1 / T := by
          rw [abs_le]
          constructor <;> linarith [hu'.1, hu'.2]
        calc
          |T * (x - u')| = T * |x - u'| := by rw [abs_mul, abs_of_pos hT]
          _ ≤ T * (1 / T) := mul_le_mul_of_nonneg_left hdiff hT.le
          _ = 1 := by field_simp [hT.ne']
      dsimp only [G]
      rw [gmCubicLocalBump_one hwidth]
      ring
    _ ≤ ∫ u' : ℝ, G u' :=
      setIntegral_le_integral hGint
        (Eventually.of_forall fun u' => by
          dsimp only [G]
          exact mul_nonneg
            (mul_nonneg hT.le (gmCubicLocalBump_nonneg _)) (hf u'))
    _ = gmAffineTildeSchwartz T hT f x := by
      rw [gmAffineTildeSchwartz_apply_sub]

/-! ### The exact finite `J(tilde f)` entry in equation (9.8) -/

/-- The fixed source support used in Section 9.  Guth--Maynard may choose
the bump around `u = 1` this narrowly before starting the iteration. -/
def GMAffineSourceSupported (f : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, u ∉ Set.Icc (1 / 2 : ℝ) 2 → f u = 0

/-- Smoothing at width `1/T` enlarges `[1/2,2]` only to `[1/4,9/4]`
once `T ≥ 8`.  This is the support assertion needed to make the
integer shift in (9.8) a member of the finite central shell. -/
theorem gmAffineTildeSchwartz_eq_zero_of_not_mem_support
    {T : ℝ} (hT : 8 ≤ T) (f : SchwartzMap ℝ ℝ)
    (hsupp : GMAffineSourceSupported f)
    {u : ℝ} (hu : u ∉ Set.Icc (1 / 4 : ℝ) (9 / 4 : ℝ)) :
    gmAffineTildeSchwartz T (by positivity) f u = 0 := by
  rw [gmAffineTildeSchwartz_apply]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases hb : gmCubicLocalBump (T * t) = 0
  · simp [hb]
  · have hBt : |T * t| < 2 := by
      exact lt_of_not_ge fun hge =>
        hb (gmCubicLocalBump_eq_zero_of_two_le_abs hge)
    have hTpos : 0 < T := by linarith
    have ht : |t| < 1 / 4 := by
      rw [abs_mul, abs_of_pos hTpos] at hBt
      have ht' : |t| < 2 / T := (lt_div_iff₀ hTpos).mpr (by
        simpa only [mul_comm] using hBt)
      exact ht'.trans_le (by
        rw [div_le_iff₀ hTpos]
        nlinarith)
    have hut : u - t ∉ Set.Icc (1 / 2 : ℝ) 2 := by
      intro hut
      have htLower : -(1 / 4 : ℝ) < t := (neg_lt_of_abs_lt ht)
      have htUpper : t < (1 / 4 : ℝ) := (lt_of_abs_lt ht)
      have huLower : (1 / 4 : ℝ) < u := by linarith [hut.1]
      have huUpper : u < (9 / 4 : ℝ) := by linarith [hut.2]
      exact hu ⟨huLower.le, huUpper.le⟩
    simp [hsupp (u - t) hut]

/-- The shift selected by two positive dyadic variables and two points in
the source/smoothed support lies in the actual finite central shell. -/
theorem mem_gmAffineCentralShell_of_affine_support
    {M : ℕ} (hM : 0 < M) {m m' j : ℤ}
    (hm : m ∈ gmAffinePositiveShell M)
    (hm' : m' ∈ gmAffinePositiveShell M)
    {u x : ℝ} (hu : u ∈ Set.Icc (1 / 2 : ℝ) 2)
    (hx : x ∈ Set.Icc (1 / 4 : ℝ) (9 / 4 : ℝ))
    (heq : x = (((m : ℝ) * u + (j : ℝ)) / (m' : ℝ))) :
    j ∈ gmAffineCentralShell M := by
  have hmBounds := mem_gmAffinePositiveShell.mp hm
  have hm'Bounds := mem_gmAffinePositiveShell.mp hm'
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hmLower : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmBounds.1
  have hmUpper : (m : ℝ) ≤ 2 * M := by exact_mod_cast hmBounds.2
  have hm'Lower : (M : ℝ) ≤ (m' : ℝ) := by exact_mod_cast hm'Bounds.1
  have hm'Upper : (m' : ℝ) ≤ 2 * M := by exact_mod_cast hm'Bounds.2
  have hm'Ne : (m' : ℝ) ≠ 0 := by
    exact_mod_cast gmAffinePositiveShell_ne_zero hM hm'
  have hjEq : (j : ℝ) = (m' : ℝ) * x - (m : ℝ) * u := by
    field_simp [hm'Ne] at heq
    linarith
  rw [mem_gmAffineCentralShell]
  have hjLowerReal : (-(8 * M : ℝ)) ≤ (j : ℝ) := by
    rw [hjEq]
    nlinarith [hu.1, hu.2, hx.1, hx.2]
  have hjUpperReal : (j : ℝ) ≤ 8 * M := by
    rw [hjEq]
    nlinarith [hu.1, hu.2, hx.1, hx.2]
  constructor
  · exact_mod_cast hjLowerReal
  · exact_mod_cast hjUpperReal

/-- The positive-sign affine subfamily appearing after Cauchy--Schwarz in
(9.8).  Its shift range is the same finite shell as the project `J`. -/
noncomputable def gmAffinePositiveTransformSum
    (f : ℝ → ℝ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ gmAffinePositiveShell M,
    ∑ m' ∈ gmAffinePositiveShell M,
      ∑ j ∈ gmAffineCentralShell M, gmAffineTerm f m m' j u

theorem gmAffinePositiveTransformSum_nonneg
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (M : ℕ) (u : ℝ) :
    0 ≤ gmAffinePositiveTransformSum f M u := by
  unfold gmAffinePositiveTransformSum
  apply Finset.sum_nonneg
  intro m hm
  apply Finset.sum_nonneg
  intro m' hm'
  apply Finset.sum_nonneg
  intro j hj
  exact hf _

/-- The positive-sign family is a literal subfamily of the sharp affine
sum defining `J`, not a separately assumed surrogate. -/
theorem gmAffinePositiveTransformSum_le_transformSum
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (M : ℕ) (u : ℝ) :
    gmAffinePositiveTransformSum f M u ≤
      gmAffineTransformSum f M M M u := by
  unfold gmAffinePositiveTransformSum gmAffineTransformSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    rw [mem_gmAffineSignedShell]
    exact Or.inr (mem_gmAffinePositiveShell.mp hm)
  · intro m hmSigned hmPositive
    apply Finset.sum_nonneg
    intro m' hm'
    apply Finset.sum_nonneg
    intro j hj
    exact hf _

theorem integrable_gmAffinePositiveTransformSum_sq
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M : ℕ} (hM : 0 < M) :
    Integrable (fun u : ℝ => gmAffinePositiveTransformSum f M u ^ 2) := by
  have hsmoothInt := integrable_gmAffineSmoothTransformSum_sq
    (M₃ := M) f hM hM
  apply hsmoothInt.mono'
  · exact ((show Continuous (gmAffinePositiveTransformSum f M) by
      unfold gmAffinePositiveTransformSum gmAffineTerm
      fun_prop).pow 2).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hpos := gmAffinePositiveTransformSum_nonneg hf M u
    have hmajor := gmAffineTransformSum_le_smooth
      (M₁ := M) (M₂ := M) hf hM u
    exact (sq_le_sq₀ hpos
      (gmAffineSmoothTransformSum_nonneg hf M M M u)).mpr
        ((gmAffinePositiveTransformSum_le_transformSum hf M u).trans hmajor)

/-- Exact square-integral entry into the finite supremum `J`.  This is the
last step in Guth--Maynard (9.8) after support has restricted `j` to the
central shell. -/
theorem integral_gmAffinePositiveTransformSum_sq_le_J
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M : ℕ} (hM : 0 < M) :
    (∫ u : ℝ, gmAffinePositiveTransformSum f M u ^ 2) ≤
      gmAffineJ f M := by
  have hsmooth : ∀ u : ℝ,
      gmAffinePositiveTransformSum f M u ^ 2 ≤
        gmAffineTransformSum f M M M u ^ 2 := by
    intro u
    exact (sq_le_sq₀ (gmAffinePositiveTransformSum_nonneg hf M u)
      (gmAffineTransformSum_nonneg hf M M M u)).mpr
        (gmAffinePositiveTransformSum_le_transformSum hf M u)
  have hright : Integrable (fun u : ℝ =>
      gmAffineTransformSum f M M M u ^ 2) := by
    have hsmoothInt := integrable_gmAffineSmoothTransformSum_sq
      (M₃ := M) f hM hM
    apply hsmoothInt.mono'
    · exact ((continuous_gmAffineTransformSum f.continuous M M M).pow 2).aestronglyMeasurable
    · filter_upwards with u
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (gmAffineTransformSum_nonneg hf M M M u)
        (gmAffineSmoothTransformSum_nonneg hf M M M u)).mpr
          (gmAffineTransformSum_le_smooth hf hM u)
  exact (integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
    hright (Eventually.of_forall hsmooth)).trans
      (gmAffineTransformIntegral_le_J f hM
        (mem_gmAffineScaleTriples.mpr ⟨by omega, le_rfl, by omega, le_rfl,
          by omega, le_rfl⟩))

/-- The exact Cauchy--Schwarz step (9.8), already connected to the finite
`J` defined by the source affine family. -/
theorem integral_mul_gmAffinePositiveTransformSum_le
    {T : ℝ} (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ x, 0 ≤ f x) {M : ℕ} (hM : 0 < M) :
    (∫ u : ℝ, f u *
        gmAffinePositiveTransformSum
          (gmAffineTildeSchwartz T hT f) M u) ≤
      Real.sqrt (∫ u : ℝ, f u ^ 2) *
        Real.sqrt (gmAffineJ (gmAffineTildeSchwartz T hT f) M) := by
  let ft := gmAffineTildeSchwartz T hT f
  let A : ℝ → ℝ := fun u => gmAffinePositiveTransformSum ft M u
  have hft : ∀ u, 0 ≤ ft u := gmAffineTildeSchwartz_nonneg T hT f hf
  have hA : ∀ u, 0 ≤ A u := gmAffinePositiveTransformSum_nonneg hft M
  have hfLp : MemLp f 2 volume := by
    simpa using f.memLp (2 : ENNReal)
  have hALp : MemLp A 2 volume := by
    apply (memLp_two_iff_integrable_sq (by
      exact (show Continuous A by
        unfold A gmAffinePositiveTransformSum gmAffineTerm
        fun_prop).aestronglyMeasurable)).2
    exact integrable_gmAffinePositiveTransformSum_sq ft hft hM
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.HolderConjugate.two_two) (Eventually.of_forall hf)
      (Eventually.of_forall hA)
      (show MemLp f (ENNReal.ofReal 2) volume by simpa using hfLp)
      (show MemLp A (ENNReal.ofReal 2) volume by simpa using hALp)
  have hAJ := integral_gmAffinePositiveTransformSum_sq_le_J ft hft hM
  have hJnonneg : 0 ≤ gmAffineJ ft M := by
    have hIntegralNonneg :
        0 ≤ ∫ u : ℝ, gmAffinePositiveTransformSum ft M u ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    exact hIntegralNonneg.trans hAJ
  calc
    (∫ u : ℝ, f u * gmAffinePositiveTransformSum ft M u) ≤
        (∫ u : ℝ, f u ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ u : ℝ, A u ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hHolder
    _ = Real.sqrt (∫ u : ℝ, f u ^ 2) *
          Real.sqrt (∫ u : ℝ, A u ^ 2) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
      norm_num
    _ ≤ Real.sqrt (∫ u : ℝ, f u ^ 2) *
          Real.sqrt (gmAffineJ ft M) := by
      gcongr

/-- The exact finite retained-neighborhood expression produced by the
second Poisson window in (9.7). -/
noncomputable def gmAffineRetainedNeighborhoodSum
    (f : ℝ → ℝ) (T : ℝ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ gmAffinePositiveShell M,
    ∑ m' ∈ gmAffinePositiveShell M,
      ∑ j ∈ gmAffineCentralShell M,
        ∫ u' in gmAffineUnitInterval T
          (((m : ℝ) * u + (j : ℝ)) / (m' : ℝ)), T * f u'

theorem gmAffineRetainedNeighborhoodSum_nonneg
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x)
    {T : ℝ} (hT : 0 ≤ T) (M : ℕ) (u : ℝ) :
    0 ≤ gmAffineRetainedNeighborhoodSum f T M u := by
  unfold gmAffineRetainedNeighborhoodSum
  apply Finset.sum_nonneg
  intro m hm
  apply Finset.sum_nonneg
  intro m' hm'
  apply Finset.sum_nonneg
  intro j hj
  exact integral_nonneg fun u' => mul_nonneg hT (hf u')

/-- Every retained `1/T`-neighborhood is bounded by the actual convolution
defining `f_tilde`; summing gives the literal affine family in `J`. -/
theorem gmAffineRetainedNeighborhoodSum_le_positiveTransform
    {T : ℝ} (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ x, 0 ≤ f x) (M : ℕ) (u : ℝ) :
    gmAffineRetainedNeighborhoodSum f T M u ≤
      gmAffinePositiveTransformSum
        (gmAffineTildeSchwartz T hT f) M u := by
  unfold gmAffineRetainedNeighborhoodSum gmAffinePositiveTransformSum
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro m' hm'
  apply Finset.sum_le_sum
  intro j hj
  exact setIntegral_gmAffineUnitInterval_le_tilde hT f hf
    (((m : ℝ) * u + (j : ℝ)) / (m' : ℝ))

/-- Equation (9.8) for the exact finite retained-neighborhood sum. -/
theorem integral_mul_gmAffineRetainedNeighborhoodSum_le
    {T : ℝ} (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ x, 0 ≤ f x) {M : ℕ} (hM : 0 < M) :
    (∫ u : ℝ, f u * gmAffineRetainedNeighborhoodSum f T M u) ≤
      Real.sqrt (∫ u : ℝ, f u ^ 2) *
        Real.sqrt (gmAffineJ (gmAffineTildeSchwartz T hT f) M) := by
  let ft := gmAffineTildeSchwartz T hT f
  let A : ℝ → ℝ := fun u => gmAffinePositiveTransformSum ft M u
  have hft : ∀ u, 0 ≤ ft u := gmAffineTildeSchwartz_nonneg T hT f hf
  have hfLp : MemLp f 2 volume := by simpa using f.memLp (2 : ENNReal)
  have hALp : MemLp A 2 volume := by
    apply (memLp_two_iff_integrable_sq (by
      exact (show Continuous A by
        unfold A gmAffinePositiveTransformSum gmAffineTerm
        fun_prop).aestronglyMeasurable)).2
    exact integrable_gmAffinePositiveTransformSum_sq ft hft hM
  have hright : Integrable (fun u : ℝ => f u * A u) :=
    hfLp.integrable_mul hALp
  have hpoint : ∀ u : ℝ,
      f u * gmAffineRetainedNeighborhoodSum f T M u ≤ f u * A u := by
    intro u
    exact mul_le_mul_of_nonneg_left
      (gmAffineRetainedNeighborhoodSum_le_positiveTransform hT f hf M u) (hf u)
  calc
    (∫ u : ℝ, f u * gmAffineRetainedNeighborhoodSum f T M u) ≤
        ∫ u : ℝ, f u * A u := by
      apply integral_mono_of_nonneg
        (Eventually.of_forall fun u => mul_nonneg (hf u)
          (gmAffineRetainedNeighborhoodSum_nonneg hf hT.le M u))
        hright (Eventually.of_forall hpoint)
    _ ≤ Real.sqrt (∫ u : ℝ, f u ^ 2) *
        Real.sqrt (gmAffineJ ft M) := by
      simpa only [A, ft] using
        integral_mul_gmAffinePositiveTransformSum_le hT f hf hM

/-! ### Finite replacement for the paper's downward induction in `epsilon` -/

/-- A positive exponent can be raised past the crude exponent `100` by
finitely many multiplications by `3/2`.  This is the natural-number
termination certificate used in Proposition 9.1. -/
theorem exists_nat_three_halves_pow_mul_ge_hundred
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ j : ℕ, (100 : ℝ) ≤ (3 / 2 : ℝ) ^ j * epsilon := by
  have htend : Tendsto (fun j : ℕ => (3 / 2 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent : ∀ᶠ j : ℕ in atTop, 100 / epsilon < (3 / 2 : ℝ) ^ j :=
    htend.eventually_gt_atTop (100 / epsilon)
  rw [eventually_atTop] at hevent
  obtain ⟨j, hj⟩ := hevent
  refine ⟨j, ?_⟩
  have hquot : 100 / epsilon < (3 / 2 : ℝ) ^ j := hj j le_rfl
  rw [div_lt_iff₀ hepsilon] at hquot
  exact hquot.le

/-- Iterating a `3/2` exponent-improvement step a finite number of times
descends from exponent `(3/2)^j epsilon` to `epsilon`.  No induction on
real numbers is involved. -/
theorem gmAffine_finite_exponent_descent
    (P : ℝ → Prop)
    (hstep : ∀ {delta : ℝ}, 0 < delta → P (3 * delta / 2) → P delta)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (j : ℕ)
    (hhigh : P ((3 / 2 : ℝ) ^ j * epsilon)) :
    P epsilon := by
  induction j with
  | zero => simpa using hhigh
  | succ j ih =>
      have hdelta : 0 < (3 / 2 : ℝ) ^ j * epsilon := by positivity
      apply ih
      apply hstep hdelta
      convert hhigh using 1
      rw [pow_succ]
      ring

/-- Source-faithful finite induction principle for Proposition 9.1: a
crude bound at every exponent at least `100`, together with Lemma 9.2's
`3/2` improvement, proves the requested positive exponent. -/
theorem gmAffine_proposition9_finite_induction
    (P : ℝ → Prop)
    (hbase : ∀ {delta : ℝ}, (100 : ℝ) ≤ delta → P delta)
    (hstep : ∀ {delta : ℝ}, 0 < delta → P (3 * delta / 2) → P delta)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    P epsilon := by
  obtain ⟨j, hj⟩ :=
    exists_nat_three_halves_pow_mul_ge_hundred hepsilon
  exact gmAffine_finite_exponent_descent P hstep hepsilon j (hbase hj)

/-! ### The first-Poisson product fibers in the middle region -/

/-- The exact finite set of retained first-Poisson pairs `(m₁, ℓ)`.
The product map on this set is the source variable `s = m₁ℓ` used to
avoid paying separately for every `m₁`. -/
noncomputable def gmAffineFirstPoissonPairs
    (M₁ M₃ : ℕ) (Q xi : ℝ) : Finset (ℤ × ℤ) :=
  (gmAffineSignedShell M₁).biUnion fun m₁ =>
    (gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q).image
      fun ell => (m₁, ell)

theorem mem_gmAffineFirstPoissonPairs
    {M₁ M₃ : ℕ} {Q xi : ℝ} {p : ℤ × ℤ} :
    p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi ↔
      p.1 ∈ gmAffineSignedShell M₁ ∧
        p.2 ∈ gmAffinePoissonNearSet M₃ (xi / (p.1 : ℝ)) Q := by
  classical
  simp only [gmAffineFirstPoissonPairs, Finset.mem_biUnion,
    Finset.mem_image]
  constructor
  · rintro ⟨m₁, hm₁, ell, hell, hp⟩
    rw [← hp]
    exact ⟨hm₁, hell⟩
  · rintro ⟨hp₁, hp₂⟩
    exact ⟨p.1, hp₁, p.2, hp₂, Prod.ext rfl rfl⟩

/-- The finite product image of the retained first-Poisson pairs. -/
noncomputable def gmAffineFirstPoissonProducts
    (M₁ M₃ : ℕ) (Q xi : ℝ) : Finset ℤ :=
  (gmAffineFirstPoissonPairs M₁ M₃ Q xi).image
    fun p => p.1 * p.2

/-- A nonzero product fiber injects into the signed divisor
antidiagonal.  This is the exact finite form of the divisor-bound step
in the proof of Lemma 9.2. -/
theorem card_gmAffineFirstPoissonPair_fiber_le_divisorsAntidiag
    (M₁ M₃ : ℕ) (Q xi : ℝ) {s : ℤ} (hs : s ≠ 0) :
    ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).filter
        fun p => p.1 * p.2 = s).card ≤ s.divisorsAntidiag.card := by
  classical
  apply Finset.card_le_card
  intro p hp
  rw [Int.mem_divisorsAntidiag]
  exact ⟨(Finset.mem_filter.mp hp).2, hs⟩

/-- The signed divisor antidiagonal has exactly twice the ordinary
positive-divisor cardinality. -/
theorem card_int_divisorsAntidiag_eq_two_mul_natAbs_divisors
    (s : ℤ) :
    s.divisorsAntidiag.card = 2 * s.natAbs.divisors.card := by
  cases s with
  | ofNat n =>
      change ((n : ℤ).divisorsAntidiag).card = 2 * n.divisors.card
      rw [Int.divisorsAntidiag_natCast, Finset.card_disjUnion]
      simp only [Finset.card_map]
      rw [show n.divisorsAntidiagonal.card = n.divisors.card by
        rw [← Nat.map_div_right_divisors]
        simp]
      omega
  | negSucc n =>
      change ((-((n + 1 : ℕ) : ℤ)).divisorsAntidiag).card =
        2 * (n + 1).divisors.card
      rw [Int.divisorsAntidiag_neg_natCast, Finset.card_disjUnion]
      simp only [Finset.card_map]
      rw [show (n + 1).divisorsAntidiagonal.card = (n + 1).divisors.card by
        rw [← Nat.map_div_right_divisors]
        simp]
      omega

/-- Fiberwise divisor estimate for the complete retained pair set.  The
nonzero-product hypothesis will be discharged from the lower boundary
of the middle-frequency region. -/
theorem card_gmAffineFirstPoissonPairs_le_sum_divisors
    (M₁ M₃ : ℕ) (Q xi : ℝ)
    (hnonzero : ∀ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
      p.1 * p.2 ≠ 0) :
    (gmAffineFirstPoissonPairs M₁ M₃ Q xi).card ≤
      ∑ s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
        2 * s.natAbs.divisors.card := by
  classical
  rw [Finset.card_eq_sum_card_image
    (fun p : ℤ × ℤ => p.1 * p.2)
    (gmAffineFirstPoissonPairs M₁ M₃ Q xi)]
  unfold gmAffineFirstPoissonProducts
  apply Finset.sum_le_sum
  intro s hs
  rw [← card_int_divisorsAntidiag_eq_two_mul_natAbs_divisors]
  apply card_gmAffineFirstPoissonPair_fiber_le_divisorsAntidiag
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
  exact hnonzero p hp

/-- The exact product-window radius following from the retained
first-Poisson cutoff. -/
noncomputable def gmAffineFirstPoissonRadius
    (M₁ M₃ : ℕ) (Q : ℝ) : ℝ :=
  Q * (2 * M₁ : ℝ) / (8 * M₃ : ℝ)

/-- Every retained product lies in the narrow real window centered at
`-xi`.  This is the algebraic content of the passage from `(m₁,ℓ)`
to `s = m₁ℓ`. -/
theorem abs_add_product_lt_gmAffineFirstPoissonRadius
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) {p : ℤ × ℤ}
    (hp : p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi) :
    |xi + ((p.1 * p.2 : ℤ) : ℝ)| <
      gmAffineFirstPoissonRadius M₁ M₃ Q := by
  obtain ⟨hm₁, hell⟩ := mem_gmAffineFirstPoissonPairs.mp hp
  have hm₁neZ : p.1 ≠ 0 := gmAffineSignedShell_ne_zero hM₁ hm₁
  have hm₁neR : (p.1 : ℝ) ≠ 0 := by exact_mod_cast hm₁neZ
  have hnear : |(8 * M₃ : ℝ) *
      (xi / (p.1 : ℝ) + (p.2 : ℝ))| < Q := by
    unfold gmAffinePoissonNearSet at hell
    exact (Finset.mem_filter.mp hell).2
  have hrewrite : xi / (p.1 : ℝ) + (p.2 : ℝ) =
      (xi + (p.1 : ℝ) * (p.2 : ℝ)) / (p.1 : ℝ) := by
    field_simp [hm₁neR]
  rw [hrewrite, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 8 * M₃), abs_div] at hnear
  have hmabs : 0 < |(p.1 : ℝ)| := abs_pos.mpr hm₁neR
  have hscale : (0 : ℝ) < 8 * M₃ := by positivity
  have hdiv : |xi + (p.1 : ℝ) * (p.2 : ℝ)| / |(p.1 : ℝ)| <
      Q / (8 * M₃ : ℝ) := by
    rw [lt_div_iff₀ hscale]
    simpa only [mul_comm] using hnear
  have hmul : |xi + (p.1 : ℝ) * (p.2 : ℝ)| <
      (Q / (8 * M₃ : ℝ)) * |(p.1 : ℝ)| := by
    rw [div_lt_iff₀ hmabs] at hdiv
    exact hdiv
  calc
    |xi + ((p.1 * p.2 : ℤ) : ℝ)| =
        |xi + (p.1 : ℝ) * (p.2 : ℝ)| := by push_cast; rfl
    _ < (Q / (8 * M₃ : ℝ)) * |(p.1 : ℝ)| := hmul
    _ ≤ (Q / (8 * M₃ : ℝ)) * (2 * M₁ : ℝ) := by
      gcongr
      exact abs_gmAffineSignedShell_le_scale hm₁
    _ = gmAffineFirstPoissonRadius M₁ M₃ Q := by
      unfold gmAffineFirstPoissonRadius
      ring

/-- The lower boundary of Region II excludes the zero product. -/
theorem gmAffineFirstPoissonPair_product_ne_zero
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q)
    (hxi : gmAffineFirstPoissonRadius M₁ M₃ Q ≤ |xi|)
    {p : ℤ × ℤ} (hp : p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi) :
    p.1 * p.2 ≠ 0 := by
  intro hz
  have hdev := abs_add_product_lt_gmAffineFirstPoissonRadius
    hM₁ hM₃ hQ hp
  rw [hz, Int.cast_zero, add_zero] at hdev
  exact (not_lt_of_ge hxi) hdev

/-- Integer interval containing the product image of all retained
first-Poisson pairs. -/
noncomputable def gmAffineFirstPoissonProductRange
    (M₁ M₃ : ℕ) (Q xi : ℝ) : Finset ℤ :=
  Finset.Icc ⌊-xi - gmAffineFirstPoissonRadius M₁ M₃ Q⌋
    ⌈-xi + gmAffineFirstPoissonRadius M₁ M₃ Q⌉

theorem gmAffineFirstPoissonProducts_subset_range
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) :
    gmAffineFirstPoissonProducts M₁ M₃ Q xi ⊆
      gmAffineFirstPoissonProductRange M₁ M₃ Q xi := by
  intro s hs
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
  have hdev := abs_add_product_lt_gmAffineFirstPoissonRadius
    hM₁ hM₃ hQ hp
  rw [abs_lt] at hdev
  rw [gmAffineFirstPoissonProductRange, Finset.mem_Icc]
  constructor
  · have hfloor := Int.floor_mono
      (show -xi - gmAffineFirstPoissonRadius M₁ M₃ Q ≤
        ((p.1 * p.2 : ℤ) : ℝ) by linarith [hdev.1])
    rw [Int.floor_intCast] at hfloor
    simpa using hfloor
  · have hceil := Int.ceil_mono
      (show ((p.1 * p.2 : ℤ) : ℝ) ≤
        -xi + gmAffineFirstPoissonRadius M₁ M₃ Q by linarith [hdev.2])
    rw [Int.ceil_intCast] at hceil
    simpa using hceil

/-- The containing integer interval has the source-size bound
`2 * radius + 3`, including both endpoint roundings. -/
theorem card_gmAffineFirstPoissonProductRange_real_le
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) :
    ((gmAffineFirstPoissonProductRange M₁ M₃ Q xi).card : ℝ) ≤
      2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3 := by
  let R := gmAffineFirstPoissonRadius M₁ M₃ Q
  let a : ℤ := ⌊-xi - R⌋
  let b : ℤ := ⌈-xi + R⌉
  have hR : 0 ≤ R := by
    unfold R gmAffineFirstPoissonRadius
    positivity
  have haReal : (a : ℝ) ≤ -xi - R := Int.floor_le (-xi - R)
  have hbReal : -xi + R ≤ (b : ℝ) := Int.le_ceil (-xi + R)
  have habReal : (a : ℝ) ≤ (b : ℝ) := by linarith
  have hab : a ≤ b := by exact_mod_cast habReal
  have hdiff : 0 ≤ b + 1 - a := by omega
  have htoNat : (((b + 1 - a).toNat : ℕ) : ℤ) = b + 1 - a :=
    Int.toNat_of_nonneg hdiff
  have hcast : (((b + 1 - a).toNat : ℕ) : ℝ) =
      (b : ℝ) + 1 - (a : ℝ) := by
    exact_mod_cast htoNat
  have haClose := Int.lt_floor_add_one (-xi - R)
  have hbClose := Int.ceil_lt_add_one (-xi + R)
  rw [gmAffineFirstPoissonProductRange, Int.card_Icc]
  change (((b + 1 - a).toNat : ℕ) : ℝ) ≤ _
  rw [hcast]
  dsimp only [R] at haClose hbClose ⊢
  linarith

/-- Consequently the number of distinct product values has the same
source-size bound. -/
theorem card_gmAffineFirstPoissonProducts_real_le
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) :
    ((gmAffineFirstPoissonProducts M₁ M₃ Q xi).card : ℝ) ≤
      2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3 := by
  have hcard := Finset.card_le_card
    (gmAffineFirstPoissonProducts_subset_range hM₁ hM₃ (xi := xi) hQ)
  have hcardReal :
      ((gmAffineFirstPoissonProducts M₁ M₃ Q xi).card : ℝ) ≤
        ((gmAffineFirstPoissonProductRange M₁ M₃ Q xi).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardReal.trans
    (card_gmAffineFirstPoissonProductRange_real_le hM₁ hM₃ hQ)

/-- The complete retained-pair estimate after the divisor bound.  The
constant depends only on `epsilon`; `B` is any uniform upper bound for
the absolute product variable. -/
theorem exists_card_gmAffineFirstPoissonPairs_real_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi B : ℝ} (hQ : 0 < Q)
    (hxi : gmAffineFirstPoissonRadius M₁ M₃ Q ≤ |xi|)
    (hB : 0 ≤ B)
    (hprod : ∀ s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
      (s.natAbs : ℝ) ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
        C * B ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) := by
  obtain ⟨C, hC, hdiv⟩ := divisorCountBound_native epsilon hepsilon
  refine ⟨2 * C, by positivity, ?_⟩
  have hnonzero : ∀ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
      p.1 * p.2 ≠ 0 := by
    intro p hp
    exact gmAffineFirstPoissonPair_product_ne_zero hM₁ hM₃ hQ hxi hp
  have hnat := card_gmAffineFirstPoissonPairs_le_sum_divisors
    M₁ M₃ Q xi hnonzero
  have hreal : ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
      ∑ s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
        2 * (s.natAbs.divisors.card : ℝ) := by
    exact_mod_cast hnat
  calc
    ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
        ∑ s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
          2 * (s.natAbs.divisors.card : ℝ) := hreal
    _ ≤ ∑ _s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi,
          2 * (C * B ^ epsilon) := by
      apply Finset.sum_le_sum
      intro s hs
      have hs₀ : s ≠ 0 := by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
        exact hnonzero p hp
      have hdivs := hdiv s.natAbs (Int.natAbs_pos.mpr hs₀)
      have hpow : (s.natAbs : ℝ) ^ epsilon ≤ B ^ epsilon :=
        Real.rpow_le_rpow (by positivity) (hprod s hs) hepsilon.le
      nlinarith [mul_le_mul_of_nonneg_left hpow hC.le]
    _ = (2 * C * B ^ epsilon) *
          ((gmAffineFirstPoissonProducts M₁ M₃ Q xi).card : ℝ) := by
      simp
      ring
    _ ≤ (2 * C) * B ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) := by
      have hcard := card_gmAffineFirstPoissonProducts_real_le
        hM₁ hM₃ (xi := xi) hQ
      have hcoef : 0 ≤ 2 * C * B ^ epsilon := by positivity
      nlinarith

/-- Absolute size of every product in the first-Poisson image. -/
theorem natAbs_le_abs_add_gmAffineFirstPoissonRadius
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q)
    {s : ℤ} (hs : s ∈ gmAffineFirstPoissonProducts M₁ M₃ Q xi) :
    (s.natAbs : ℝ) ≤ |xi| + gmAffineFirstPoissonRadius M₁ M₃ Q := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
  have hdev := abs_add_product_lt_gmAffineFirstPoissonRadius
    hM₁ hM₃ hQ hp
  rw [Nat.cast_natAbs, Int.cast_abs]
  calc
    |((p.1 * p.2 : ℤ) : ℝ)| =
        |(xi + ((p.1 * p.2 : ℤ) : ℝ)) - xi| := by ring_nf
    _ ≤ |xi + ((p.1 * p.2 : ℤ) : ℝ)| + |xi| := abs_sub _ _
    _ ≤ |xi| + gmAffineFirstPoissonRadius M₁ M₃ Q := by
      linarith

/-- Source-facing middle-region pair count before specializing
`Y = T^6` and `Q = T^eta`. -/
theorem exists_card_gmAffineFirstPoissonPairs_middle_real_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {M₁ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {Q xi Y : ℝ} (hQ : 0 < Q) (hY : 0 ≤ Y)
    (hxiLower : gmAffineFirstPoissonRadius M₁ M₃ Q ≤ |xi|)
    (hxiUpper : |xi| ≤ Y) :
    ∃ C : ℝ, 0 < C ∧
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) ≤
        C * (Y + gmAffineFirstPoissonRadius M₁ M₃ Q) ^ epsilon *
          (2 * gmAffineFirstPoissonRadius M₁ M₃ Q + 3) := by
  apply exists_card_gmAffineFirstPoissonPairs_real_le hepsilon hM₁ hM₃
    hQ hxiLower (by
      have hR : 0 ≤ gmAffineFirstPoissonRadius M₁ M₃ Q := by
        unfold gmAffineFirstPoissonRadius
        positivity
      linarith)
  intro s hs
  exact (natAbs_le_abs_add_gmAffineFirstPoissonRadius hM₁ hM₃ hQ hs).trans
    (by simpa only [add_comm] using
      (add_le_add_right hxiUpper (gmAffineFirstPoissonRadius M₁ M₃ Q)))

/-- The product-pair finset counts exactly the nested `(m₁,ℓ)` sum;
there is no hidden multiplicity in the finite reindexing. -/
theorem card_gmAffineFirstPoissonPairs_eq_sum
    (M₁ M₃ : ℕ) (Q xi : ℝ) :
    (gmAffineFirstPoissonPairs M₁ M₃ Q xi).card =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        (gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q).card := by
  classical
  have hdis : Set.PairwiseDisjoint (↑(gmAffineSignedShell M₁))
      (fun m₁ : ℤ =>
        (gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q).image
          fun ell => (m₁, ell)) := by
    intro a ha b hb hab
    change Disjoint
      ((gmAffinePoissonNearSet M₃ (xi / (a : ℝ)) Q).image
        fun ell => (a, ell))
      ((gmAffinePoissonNearSet M₃ (xi / (b : ℝ)) Q).image
        fun ell => (b, ell))
    rw [Finset.disjoint_left]
    intro p hpa hpb
    obtain ⟨ella, hella, hpaEq⟩ := Finset.mem_image.mp hpa
    obtain ⟨ellb, hellb, hpbEq⟩ := Finset.mem_image.mp hpb
    apply hab
    have hfirst : (a, ella).1 = (b, ellb).1 := by rw [hpaEq, hpbEq]
    simpa using hfirst
  unfold gmAffineFirstPoissonPairs
  rw [Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  rw [Finset.card_image_iff.mpr]
  intro a ha b hb hab
  exact congrArg Prod.snd hab

/-- Exact finite reindexing of the nested first-Poisson sum by retained
`(m₁, ℓ)` pairs.  This is the sum-level companion to the cardinality
identity above and carries the actual Fourier summands into the divisor
counting argument. -/
theorem sum_gmAffineFirstPoissonPairs
    {A : Type*} [AddCommMonoid A]
    (M₁ M₃ : ℕ) (Q xi : ℝ) (F : ℤ × ℤ → A) :
    ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi, F p =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ ell ∈ gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q,
          F (m₁, ell) := by
  classical
  have hdis : Set.PairwiseDisjoint (↑(gmAffineSignedShell M₁))
      (fun m₁ : ℤ =>
        (gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q).image
          fun ell => (m₁, ell)) := by
    intro a ha b hb hab
    change Disjoint
      ((gmAffinePoissonNearSet M₃ (xi / (a : ℝ)) Q).image
        fun ell => (a, ell))
      ((gmAffinePoissonNearSet M₃ (xi / (b : ℝ)) Q).image
        fun ell => (b, ell))
    rw [Finset.disjoint_left]
    intro p hpa hpb
    obtain ⟨ella, hella, hpaEq⟩ := Finset.mem_image.mp hpa
    obtain ⟨ellb, hellb, hpbEq⟩ := Finset.mem_image.mp hpb
    apply hab
    have hfirst : (a, ella).1 = (b, ellb).1 := by rw [hpaEq, hpbEq]
    simpa using hfirst
  unfold gmAffineFirstPoissonPairs
  rw [Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  rw [Finset.sum_image]
  intro a ha b hb hab
  exact congrArg Prod.snd hab

/-- The complete `m₂` Fourier block attached to a retained first-Poisson
frequency.  It is kept intact when `(m₁, ℓ)` is reindexed by the product
`m₁ℓ`. -/
noncomputable def gmAffineM₂FourierBlock
    (f : SchwartzMap ℝ ℝ) (M₂ : ℕ) (m₁ : ℤ) (xi : ℝ) : ℂ :=
  ∑ m₂ ∈ gmAffinePositiveShell M₂,
    (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
      fourier (gmAffineComplexify f)
        (((m₂ : ℝ) / (m₁ : ℝ)) * xi))

/-- A single retained `(m₁, ℓ)` summand of the first-Poisson main term. -/
noncomputable def gmAffineFirstPoissonPairTerm
    (f : SchwartzMap ℝ ℝ) (M₂ M₃ : ℕ) (hM₃ : 0 < M₃)
    (xi : ℝ) (p : ℤ × ℤ) : ℂ :=
  gmAffineM₂FourierBlock f M₂ p.1 xi *
    gmAffineCentralPoissonKernel M₃ hM₃
      (xi / (p.1 : ℝ) + p.2)

/-- The retained main term in equation (9.3), reindexed by the exact
finite pair set used in the divisor-counting argument. -/
theorem gmAffinePoissonMainFourier_eq_sum_pairs
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (hM₃ : 0 < M₃)
    (Q xi : ℝ) :
    gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi =
      ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
        gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi p := by
  rw [sum_gmAffineFirstPoissonPairs]
  unfold gmAffinePoissonMainFourier gmAffineFirstPoissonPairTerm
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  unfold gmAffineM₂FourierBlock
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- Pointwise Cauchy--Schwarz after the source-faithful pair reindexing.
The outer factor is now exactly the pair count controlled by the divisor
bound, rather than the much larger product of the two shell sizes. -/
theorem norm_gmAffinePoissonMainFourier_sq_le_pairs
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (hM₃ : 0 < M₃)
    (Q xi : ℝ) :
    ‖gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi‖ ^ 2 ≤
      ((gmAffineFirstPoissonPairs M₁ M₃ Q xi).card : ℝ) *
        ∑ p ∈ gmAffineFirstPoissonPairs M₁ M₃ Q xi,
          ‖gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi p‖ ^ 2 := by
  rw [gmAffinePoissonMainFourier_eq_sum_pairs]
  exact norm_sum_sq_le_card_mul_sum_norm_sq
    (gmAffineFirstPoissonPairs M₁ M₃ Q xi)
    (gmAffineFirstPoissonPairTerm f M₂ M₃ hM₃ xi)

/-- Exact ordered-pair expansion of the squared norm of a finite complex
sum.  The ordering agrees with the conjugated/unconjugated Fourier factors
used in equation (9.7). -/
theorem ofReal_norm_finset_sum_sq_expand
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) :
    ((‖∑ i ∈ s, a i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ s, ∑ j ∈ s, star (a i) * a j := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

/-- Source-normalized integral formula for the Fourier transform of a
real Schwartz function.  The displayed sign and `2π` normalization are
the ones used in the phases `Z₁` and `Z₂` of equation (9.7). -/
theorem fourier_gmAffineComplexify_eq_integral
    (f : SchwartzMap ℝ ℝ) (xi : ℝ) :
    fourier (gmAffineComplexify f) xi =
      ∫ u : ℝ, Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I) *
        (f u : ℂ) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with u
  rw [gmAffineComplexify_apply]
  simp only [Real.inner_apply, smul_eq_mul]
  congr 2
  push_cast
  ring

/-- Conjugated form of the source-normalized Fourier integral. -/
theorem conj_fourier_gmAffineComplexify_eq_integral
    (f : SchwartzMap ℝ ℝ) (xi : ℝ) :
    (starRingEnd ℂ) (fourier (gmAffineComplexify f) xi) =
      ∫ u : ℝ, Complex.exp ((((2 * Real.pi * u * xi) : ℝ) : ℂ) * I) *
        (f u : ℂ) := by
  rw [fourier_gmAffineComplexify_eq_integral]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with u
  have hexp :
      (starRingEnd ℂ)
          (Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I)) =
        Complex.exp ((((2 * Real.pi * u * xi) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I]
    push_cast
    ring
  rw [map_mul, hexp]
  simp

/-! ### Exact equation (9.7) source objects -/

/-- The inner `m₂`-sum in the source definition of `Σ_II`. -/
noncomputable def gmAffineMiddleFourierBlock
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ : ℕ) (ell : ℤ) (tau : ℝ) : ℂ :=
  ∑ m₂ ∈ gmAffinePositiveShell M₂,
    (m₂ : ℂ) * fourier (gmAffineComplexify f)
      ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / M₁) * tau)

/-- A finite-frequency version of the `Z₂` factor in equation (9.7).
The full source cutoff is recovered once its compact integer support is
identified. -/
noncomputable def gmAffineMiddleZ₂Finite
    (L : Finset ℤ) (T : ℝ) (M₂ : ℕ)
    (m₂ m₂' : ℤ) (u u' : ℝ) : ℂ :=
  ∑ ell ∈ L,
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
      Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
        gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I)

/-- The finite-frequency form of `Σ_II` before expanding the Fourier
square. -/
noncomputable def gmAffineSigmaIIFinite
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ)
    (T : ℝ) (M₁ M₂ : ℕ) : ℂ :=
  ∑ ell ∈ L,
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
      ∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
        ((‖gmAffineMiddleFourierBlock f M₁ M₂ ell tau‖ ^ 2 : ℝ) : ℂ)

/-- Exact ordered-pair expansion of the Fourier block in `Σ_II`; no
frequency, coefficient, or conjugation is discarded. -/
theorem ofReal_norm_gmAffineMiddleFourierBlock_sq_expand
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ : ℕ) (ell : ℤ) (tau : ℝ) :
    ((‖gmAffineMiddleFourierBlock f M₁ M₂ ell tau‖ ^ 2 : ℝ) : ℂ) =
      ∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          star ((m₂' : ℂ) * fourier (gmAffineComplexify f)
            ((ell : ℝ) * (m₂' : ℝ) + ((m₂' : ℝ) / M₁) * tau)) *
          ((m₂ : ℂ) * fourier (gmAffineComplexify f)
            ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / M₁) * tau)) := by
  unfold gmAffineMiddleFourierBlock
  exact ofReal_norm_finset_sum_sq_expand
    (gmAffinePositiveShell M₂)
    (fun m₂ => (m₂ : ℂ) * fourier (gmAffineComplexify f)
      ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / M₁) * tau))

/-- Exact two-variable integral expansion of one conjugated Fourier pair.
This is the Fubini kernel from which the phases `Z₁` and `Z₂` in (9.7)
are obtained. -/
theorem gmAffineFourierPair_eq_iteratedIntegral
    (f : SchwartzMap ℝ ℝ) (m₂ m₂' : ℤ) (xi xi' : ℝ) :
    (starRingEnd ℂ) ((m₂' : ℂ) * fourier (gmAffineComplexify f) xi') *
        ((m₂ : ℂ) * fourier (gmAffineComplexify f) xi) =
      ∫ u' : ℝ, ∫ u : ℝ,
        (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
          Complex.exp ((((2 * Real.pi * (u' * xi' - u * xi)) : ℝ) : ℂ) * I) := by
  rw [map_mul, conj_fourier_gmAffineComplexify_eq_integral,
    fourier_gmAffineComplexify_eq_integral]
  simp only [map_intCast]
  let A : ℝ → ℂ := fun u' =>
    Complex.exp ((((2 * Real.pi * u' * xi') : ℝ) : ℂ) * I) * (f u' : ℂ)
  let B : ℝ → ℂ := fun u =>
    Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I) * (f u : ℂ)
  change ((m₂' : ℂ) * ∫ u', A u') * ((m₂ : ℂ) * ∫ u, B u) = _
  calc
    ((m₂' : ℂ) * ∫ u', A u') * ((m₂ : ℂ) * ∫ u, B u) =
        (∫ u', A u') * (((m₂' * m₂ : ℤ) : ℂ) * ∫ u, B u) := by
      push_cast
      ring
    _ = ∫ u' : ℝ, A u' * (((m₂' * m₂ : ℤ) : ℂ) * ∫ u, B u) := by
      rw [integral_mul_const]
    _ = ∫ u' : ℝ, ∫ u : ℝ, A u' * (((m₂' * m₂ : ℤ) : ℂ) * B u) := by
      apply integral_congr_ae
      filter_upwards with u'
      rw [integral_const_mul]
      rw [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u'
      apply integral_congr_ae
      filter_upwards with u
      dsimp only [A, B]
      calc
        Complex.exp ((((2 * Real.pi * u' * xi') : ℝ) : ℂ) * I) * (f u' : ℂ) *
            (((m₂' * m₂ : ℤ) : ℂ) *
              (Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I) * (f u : ℂ))) =
            (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
              (Complex.exp ((((2 * Real.pi * u' * xi') : ℝ) : ℂ) * I) *
                Complex.exp (((-(2 * Real.pi * u * xi) : ℝ) : ℂ) * I)) := by ring
        _ = _ := by
          rw [← Complex.exp_add]
          congr 2
          push_cast
          ring

/-- First exact expansion of finite `Σ_II`: the Fourier square is replaced
by its ordered `(m₂',m₂)` double sum and each Fourier pair by the literal
two-variable integral.  This is equation (9.7) before commuting the finite
sums and compact `τ` integral. -/
theorem gmAffineSigmaIIFinite_eq_expandedFourierPairs
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ)
    (T : ℝ) (M₁ M₂ : ℕ) :
    gmAffineSigmaIIFinite L f T M₁ M₂ =
      ∑ ell ∈ L,
        (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
          ∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
            ∑ m₂' ∈ gmAffinePositiveShell M₂,
              ∑ m₂ ∈ gmAffinePositiveShell M₂,
                ∫ u' : ℝ, ∫ u : ℝ,
                  (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
                    Complex.exp ((((2 * Real.pi *
                      (u' * ((ell : ℝ) * (m₂' : ℝ) +
                          ((m₂' : ℝ) / M₁) * tau) -
                        u * ((ell : ℝ) * (m₂ : ℝ) +
                          ((m₂ : ℝ) / M₁) * tau))) : ℝ) : ℂ) * I) := by
  unfold gmAffineSigmaIIFinite
  apply Finset.sum_congr rfl
  intro ell hell
  congr 1
  apply integral_congr_ae
  filter_upwards with tau
  congr 1
  rw [ofReal_norm_gmAffineMiddleFourierBlock_sq_expand]
  apply Finset.sum_congr rfl
  intro m₂' hm₂'
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  exact gmAffineFourierPair_eq_iteratedIntegral f m₂ m₂'
    ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / M₁) * tau)
    ((ell : ℝ) * (m₂' : ℝ) + ((m₂' : ℝ) / M₁) * tau)

/-- The expanded Fourier-pair phase splits exactly into the compact
`τ` phase `Z₁` and the integer-frequency phase `Z₂` from equation (9.7). -/
theorem gmAffineMiddlePairPhase_exp_eq_Z₁_mul_Z₂
    (M₁ : ℕ) (ell m₂ m₂' : ℤ) (u u' tau : ℝ) :
    Complex.exp ((((2 * Real.pi *
        (u' * ((ell : ℝ) * (m₂' : ℝ) + ((m₂' : ℝ) / M₁) * tau) -
          u * ((ell : ℝ) * (m₂ : ℝ) + ((m₂ : ℝ) / M₁) * tau))) : ℝ) : ℂ) * I) =
      Complex.exp ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
        Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
          gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]
  congr 1
  unfold gmAffineMiddleTauPhase gmAffineMiddleDisplacement
  push_cast
  ring

/-- Equation (9.7) with the phase already separated into its `Z₁` and
`Z₂` factors, still in the original finite-sum/integral order. -/
theorem gmAffineSigmaIIFinite_eq_expanded_Z₁_Z₂_integrands
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ)
    (T : ℝ) (M₁ M₂ : ℕ) :
    gmAffineSigmaIIFinite L f T M₁ M₂ =
      ∑ ell ∈ L,
        (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
          ∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
            ∑ m₂' ∈ gmAffinePositiveShell M₂,
              ∑ m₂ ∈ gmAffinePositiveShell M₂,
                ∫ u' : ℝ, ∫ u : ℝ,
                  (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
                    (Complex.exp
                      ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
                    Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
                      gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I)) := by
  rw [gmAffineSigmaIIFinite_eq_expandedFourierPairs]
  apply Finset.sum_congr rfl
  intro ell hell
  congr 1
  apply integral_congr_ae
  filter_upwards with tau
  congr 1
  apply Finset.sum_congr rfl
  intro m₂' hm₂'
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  apply integral_congr_ae
  filter_upwards with u'
  apply integral_congr_ae
  filter_upwards with u
  rw [gmAffineMiddlePairPhase_exp_eq_Z₁_mul_Z₂]

/-- The two-variable Fourier-pair kernel underlying equation (9.7). -/
noncomputable def gmAffineFourierPairKernel
    (f : SchwartzMap ℝ ℝ) (m₂ m₂' : ℤ) (xi xi' : ℝ)
    (q : ℝ × ℝ) : ℂ :=
  (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
    Complex.exp ((((2 * Real.pi * (q.1 * xi' - q.2 * xi)) : ℝ) : ℂ) * I)

/-- Absolute integrability of the exact Fourier-pair kernel on the product
space.  This is the Tonelli/Fubini justification needed to commute the
`u'` and `u` integrals in (9.7). -/
theorem integrable_gmAffineFourierPairKernel
    (f : SchwartzMap ℝ ℝ) (m₂ m₂' : ℤ) (xi xi' : ℝ) :
    Integrable (gmAffineFourierPairKernel f m₂ m₂' xi xi')
      (volume.prod volume) := by
  have hf : Integrable (fun u : ℝ => ‖gmAffineComplexify f u‖) :=
    (gmAffineComplexify f).integrable.norm
  have hprod : Integrable (fun q : ℝ × ℝ =>
      ‖gmAffineComplexify f q.1‖ * ‖gmAffineComplexify f q.2‖)
      (volume.prod volume) := hf.mul_prod hf
  have hmajor : Integrable (fun q : ℝ × ℝ =>
      ‖((m₂' * m₂ : ℤ) : ℂ)‖ *
        (‖gmAffineComplexify f q.1‖ * ‖gmAffineComplexify f q.2‖))
      (volume.prod volume) := hprod.const_mul _
  apply hmajor.mono'
  · unfold gmAffineFourierPairKernel
    fun_prop
  · filter_upwards with q
    unfold gmAffineFourierPairKernel
    rw [norm_mul, Complex.norm_exp]
    simp only [mul_re, ofReal_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, Real.exp_zero]
    simp [gmAffineComplexify_apply, mul_assoc]

/-- Product-measure form of one conjugated Fourier pair, with Fubini
justified by the absolute-integrability theorem above. -/
theorem gmAffineFourierPair_eq_prodIntegral
    (f : SchwartzMap ℝ ℝ) (m₂ m₂' : ℤ) (xi xi' : ℝ) :
    (starRingEnd ℂ) ((m₂' : ℂ) * fourier (gmAffineComplexify f) xi') *
        ((m₂ : ℂ) * fourier (gmAffineComplexify f) xi) =
      ∫ q : ℝ × ℝ, gmAffineFourierPairKernel f m₂ m₂' xi xi' q := by
  rw [gmAffineFourierPair_eq_iteratedIntegral]
  change (∫ u' : ℝ, ∫ u : ℝ,
      gmAffineFourierPairKernel f m₂ m₂' xi xi' (u', u)) = _
  exact (MeasureTheory.integral_prod _
    (integrable_gmAffineFourierPairKernel f m₂ m₂' xi xi')).symm

/-- The full `(τ,(u',u))` kernel after splitting the equation-(9.7)
phase. -/
noncomputable def gmAffineMiddleTripleKernel
    (f : SchwartzMap ℝ ℝ) (M₁ : ℕ) (ell m₂ m₂' : ℤ)
    (z : ℝ × (ℝ × ℝ)) : ℂ :=
  (gmCubicLocalBump z.1 : ℂ) *
    ((((m₂' * m₂ : ℤ) : ℂ) * (f z.2.1 : ℂ) * (f z.2.2 : ℂ)) *
      (Complex.exp
          ((gmAffineMiddleTauPhase M₁ m₂ m₂' z.2.2 z.2.1 z.1 : ℂ) * I) *
        Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
          gmAffineMiddleDisplacement m₂ m₂' z.2.2 z.2.1) : ℝ) : ℂ) * I)))

/-- Absolute integrability of the complete equation-(9.7) triple kernel. -/
theorem integrable_gmAffineMiddleTripleKernel
    (f : SchwartzMap ℝ ℝ) (M₁ : ℕ) (ell m₂ m₂' : ℤ) :
    Integrable (gmAffineMiddleTripleKernel f M₁ ell m₂ m₂')
      (volume.prod (volume.prod volume)) := by
  have hb : Integrable (fun tau : ℝ => ‖(gmCubicLocalBump tau : ℂ)‖) := by
    simpa only [gmAffineLocalBumpSchwartz_apply] using
      gmAffineLocalBumpSchwartz.integrable.norm
  have hf : Integrable (fun u : ℝ => ‖gmAffineComplexify f u‖) :=
    (gmAffineComplexify f).integrable.norm
  have hpair : Integrable (fun q : ℝ × ℝ =>
      ‖gmAffineComplexify f q.1‖ * ‖gmAffineComplexify f q.2‖)
      (volume.prod volume) := hf.mul_prod hf
  have hprod : Integrable (fun z : ℝ × (ℝ × ℝ) =>
      ‖(gmCubicLocalBump z.1 : ℂ)‖ *
        (‖gmAffineComplexify f z.2.1‖ * ‖gmAffineComplexify f z.2.2‖))
      (volume.prod (volume.prod volume)) := hb.mul_prod hpair
  have hmajor : Integrable (fun z : ℝ × (ℝ × ℝ) =>
      ‖((m₂' * m₂ : ℤ) : ℂ)‖ *
        (‖(gmCubicLocalBump z.1 : ℂ)‖ *
          (‖gmAffineComplexify f z.2.1‖ * ‖gmAffineComplexify f z.2.2‖)))
      (volume.prod (volume.prod volume)) := hprod.const_mul _
  apply hmajor.mono'
  · unfold gmAffineMiddleTripleKernel
    change AEStronglyMeasurable (fun z : ℝ × (ℝ × ℝ) =>
      gmAffineLocalBumpSchwartz z.1 *
        ((((m₂' * m₂ : ℤ) : ℂ) * gmAffineComplexify f z.2.1 *
            gmAffineComplexify f z.2.2) *
          (Complex.exp
              ((gmAffineMiddleTauPhase M₁ m₂ m₂' z.2.2 z.2.1 z.1 : ℂ) * I) *
            Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
              gmAffineMiddleDisplacement m₂ m₂' z.2.2 z.2.1) : ℝ) : ℂ) * I))))
    apply Continuous.aestronglyMeasurable
    have hbcont : Continuous (fun z : ℝ × (ℝ × ℝ) =>
        gmAffineLocalBumpSchwartz z.1) :=
      gmAffineLocalBumpSchwartz.continuous.comp continuous_fst
    have hfcont₁ : Continuous (fun z : ℝ × (ℝ × ℝ) =>
        gmAffineComplexify f z.2.1) :=
      (gmAffineComplexify f).continuous.comp (continuous_fst.comp continuous_snd)
    have hfcont₂ : Continuous (fun z : ℝ × (ℝ × ℝ) =>
        gmAffineComplexify f z.2.2) :=
      (gmAffineComplexify f).continuous.comp (continuous_snd.comp continuous_snd)
    have hphase : Continuous (fun z : ℝ × (ℝ × ℝ) =>
        Complex.exp
            ((gmAffineMiddleTauPhase M₁ m₂ m₂' z.2.2 z.2.1 z.1 : ℂ) * I) *
          Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
            gmAffineMiddleDisplacement m₂ m₂' z.2.2 z.2.1) : ℝ) : ℂ) * I)) := by
      unfold gmAffineMiddleTauPhase gmAffineMiddleDisplacement
      fun_prop
    exact hbcont.mul
      (((continuous_const.mul hfcont₁).mul hfcont₂).mul hphase)
  · filter_upwards with z
    unfold gmAffineMiddleTripleKernel
    simp only [norm_mul, Complex.norm_exp, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, Real.exp_zero]
    simp only [gmAffineComplexify_apply, norm_real]
    ring_nf
    exact le_rfl

/-- Exact Fubini interchange from the source order `(τ,u',u)` to the
equation-(9.7) order `(u',u,τ)`. -/
theorem integral_tau_u'_u_gmAffineMiddleTripleKernel_eq_u'_u_tau
    (f : SchwartzMap ℝ ℝ) (M₁ : ℕ) (ell m₂ m₂' : ℤ) :
    (∫ tau : ℝ, ∫ u' : ℝ, ∫ u : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) =
      ∫ u' : ℝ, ∫ u : ℝ, ∫ tau : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u)) := by
  let F : ℝ × (ℝ × ℝ) → ℂ :=
    gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  have hF : Integrable F (volume.prod (volume.prod volume)) :=
    integrable_gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  calc
    (∫ tau : ℝ, ∫ u' : ℝ, ∫ u : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) =
      ∫ tau : ℝ, ∫ q : ℝ × ℝ, F (tau, q) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hF.prod_right_ae] with tau htau
        exact (MeasureTheory.integral_prod _ htau).symm
    _ = ∫ z : ℝ × (ℝ × ℝ), F z ∂(volume.prod (volume.prod volume)) :=
      (MeasureTheory.integral_prod _ hF).symm
    _ = ∫ q : ℝ × ℝ, ∫ tau : ℝ, F (tau, q) :=
      MeasureTheory.integral_prod_symm _ hF
    _ = ∫ u' : ℝ, ∫ u : ℝ, ∫ tau : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u)) := by
      simpa [F] using MeasureTheory.integral_prod
        (fun q : ℝ × ℝ => ∫ tau : ℝ, F (tau, q)) hF.integral_prod_right

/-- The inner `τ`-integral of the full kernel is exactly the compact
factor `Z₁`, with the integer-frequency phase retained. -/
theorem integral_gmAffineMiddleTripleKernel_eq_Z₁
    (f : SchwartzMap ℝ ℝ) (M₁ : ℕ) (ell m₂ m₂' : ℤ) (u u' : ℝ) :
    (∫ tau : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) =
      (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
        gmAffineMiddleZ₁ M₁ m₂ m₂' u u' *
        Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
          gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I) := by
  let A : ℂ := ((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)
  let E : ℂ := Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
    gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I)
  calc
    (∫ tau : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) =
      ∫ tau : ℝ, A *
          ((gmCubicLocalBump tau : ℂ) *
            Complex.exp
              ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I)) * E := by
        apply integral_congr_ae
        filter_upwards with tau
        unfold gmAffineMiddleTripleKernel
        dsimp only [A, E]
        ring
    _ = A * (∫ tau : ℝ,
          (gmCubicLocalBump tau : ℂ) *
            Complex.exp
              ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I)) * E := by
      rw [integral_mul_const, integral_const_mul]
    _ = _ := by
      rfl

/-- Moving the compact `τ` cutoff through the two Fourier variables gives
the literal triple kernel. -/
theorem gmCubicLocalBump_mul_fourierPairIntegral_eq_tripleKernel
    (f : SchwartzMap ℝ ℝ) (M₁ : ℕ) (ell m₂ m₂' : ℤ) (tau : ℝ) :
    (gmCubicLocalBump tau : ℂ) *
        (∫ u' : ℝ, ∫ u : ℝ,
          (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
            (Complex.exp
                ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
              Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
                gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I))) =
      ∫ u' : ℝ, ∫ u : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u'
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  unfold gmAffineMiddleTripleKernel
  ring

/-- One fixed `(ell,m₂',m₂)` contribution in the source order is exactly
its equation-(9.7) `Z₁` contribution in the Fourier-analysis order. -/
theorem gmAffineMiddleWeightedComponent_eq_Z₁
    (f : SchwartzMap ℝ ℝ) (T : ℝ) (M₁ M₂ : ℕ)
    (ell m₂ m₂' : ℤ) :
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
        (∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
          ∫ u' : ℝ, ∫ u : ℝ,
            (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
              (Complex.exp
                  ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
                Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
                  gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I))) =
      ∫ u' : ℝ, ∫ u : ℝ,
        (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
          gmAffineMiddleZ₁ M₁ m₂ m₂' u u' *
          ((gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
            Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
              gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I)) := by
  let c : ℂ :=
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ)
  calc
    c * (∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
          ∫ u' : ℝ, ∫ u : ℝ,
            (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
              (Complex.exp
                  ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
                Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
                  gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I))) =
      c * (∫ tau : ℝ, ∫ u' : ℝ, ∫ u : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with tau
          exact gmCubicLocalBump_mul_fourierPairIntegral_eq_tripleKernel
            f M₁ ell m₂ m₂' tau
    _ = c * (∫ u' : ℝ, ∫ u : ℝ, ∫ tau : ℝ,
        gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) := by
          rw [integral_tau_u'_u_gmAffineMiddleTripleKernel_eq_u'_u_tau]
    _ = ∫ u' : ℝ, ∫ u : ℝ, c *
        (∫ tau : ℝ,
          gmAffineMiddleTripleKernel f M₁ ell m₂ m₂' (tau, (u', u))) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with u'
          rw [← integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u'
      apply integral_congr_ae
      filter_upwards with u
      rw [integral_gmAffineMiddleTripleKernel_eq_Z₁]
      dsimp only [c]
      ring

/-- The source-order contribution of one fixed middle frequency pair. -/
noncomputable def gmAffineMiddleSourceTerm
    (f : SchwartzMap ℝ ℝ) (M₁ : ℕ) (ell m₂ m₂' : ℤ) (tau : ℝ) : ℂ :=
  (gmCubicLocalBump tau : ℂ) *
    ∫ u' : ℝ, ∫ u : ℝ,
      (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
        (Complex.exp
            ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
          Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
            gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I))

/-- The equation-(9.7) contribution of one fixed integer frequency and
one fixed middle-shell pair. -/
noncomputable def gmAffineMiddleEquation97Term
    (f : SchwartzMap ℝ ℝ) (T : ℝ) (M₁ M₂ : ℕ)
    (ell m₂ m₂' : ℤ) (q : ℝ × ℝ) : ℂ :=
  (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
    gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1 *
    ((gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
      Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
        gmAffineMiddleDisplacement m₂ m₂' q.2 q.1) : ℝ) : ℂ) * I))

theorem integrable_gmAffineMiddleSourceTerm
    (f : SchwartzMap ℝ ℝ) (M₁ : ℕ) (ell m₂ m₂' : ℤ) :
    Integrable (gmAffineMiddleSourceTerm f M₁ ell m₂ m₂') := by
  let F : ℝ × (ℝ × ℝ) → ℂ :=
    gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  have hF : Integrable F (volume.prod (volume.prod volume)) :=
    integrable_gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  refine hF.integral_prod_left.congr ?_
  filter_upwards [hF.prod_right_ae] with tau htau
  unfold gmAffineMiddleSourceTerm
  rw [gmCubicLocalBump_mul_fourierPairIntegral_eq_tripleKernel]
  exact MeasureTheory.integral_prod _ htau

theorem integrable_gmAffineMiddleEquation97Term
    (f : SchwartzMap ℝ ℝ) (T : ℝ) (M₁ M₂ : ℕ)
    (ell m₂ m₂' : ℤ) :
    Integrable (gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂')
      (volume.prod volume) := by
  let F : ℝ × (ℝ × ℝ) → ℂ :=
    gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  let c : ℂ :=
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ)
  have hF : Integrable F (volume.prod (volume.prod volume)) :=
    integrable_gmAffineMiddleTripleKernel f M₁ ell m₂ m₂'
  have hc : Integrable (fun q : ℝ × ℝ =>
      c * ∫ tau : ℝ, F (tau, q)) (volume.prod volume) :=
    hF.integral_prod_right.const_mul c
  refine hc.congr ?_
  filter_upwards with q
  rw [integral_gmAffineMiddleTripleKernel_eq_Z₁]
  unfold gmAffineMiddleEquation97Term
  dsimp only [F, c]
  ring

/-- Exact equation-(9.7) rearrangement for one fixed integer frequency,
including both ordered middle-shell sums. -/
theorem gmAffineMiddleEllSource_eq_equation97
    (f : SchwartzMap ℝ ℝ) (T : ℝ) (M₁ M₂ : ℕ) (ell : ℤ) :
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
        (∫ tau : ℝ,
          ∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∑ m₂ ∈ gmAffinePositiveShell M₂,
              gmAffineMiddleSourceTerm f M₁ ell m₂ m₂' tau) =
      ∫ q : ℝ × ℝ,
        ∑ m₂' ∈ gmAffinePositiveShell M₂,
          ∑ m₂ ∈ gmAffinePositiveShell M₂,
            gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q := by
  let c : ℂ :=
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ)
  calc
    c * (∫ tau : ℝ,
          ∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∑ m₂ ∈ gmAffinePositiveShell M₂,
              gmAffineMiddleSourceTerm f M₁ ell m₂ m₂' tau) =
      c * (∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ∫ tau : ℝ, gmAffineMiddleSourceTerm f M₁ ell m₂ m₂' tau) := by
        congr 1
        rw [MeasureTheory.integral_finsetSum _ (fun m₂' _ =>
          integrable_finsetSum _ (fun m₂ _ =>
            integrable_gmAffineMiddleSourceTerm f M₁ ell m₂ m₂'))]
        apply Finset.sum_congr rfl
        intro m₂' hm₂'
        rw [MeasureTheory.integral_finsetSum _ (fun m₂ _ =>
          integrable_gmAffineMiddleSourceTerm f M₁ ell m₂ m₂')]
    _ = ∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          c * (∫ tau : ℝ,
            gmAffineMiddleSourceTerm f M₁ ell m₂ m₂' tau) := by
      simp only [Finset.mul_sum]
    _ = ∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ∫ u' : ℝ, ∫ u : ℝ,
            gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' (u', u) := by
      apply Finset.sum_congr rfl
      intro m₂' hm₂'
      apply Finset.sum_congr rfl
      intro m₂ hm₂
      unfold gmAffineMiddleSourceTerm gmAffineMiddleEquation97Term
      exact gmAffineMiddleWeightedComponent_eq_Z₁ f T M₁ M₂ ell m₂ m₂'
    _ = ∑ m₂' ∈ gmAffinePositiveShell M₂,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ∫ q : ℝ × ℝ,
            gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q := by
      apply Finset.sum_congr rfl
      intro m₂' hm₂'
      apply Finset.sum_congr rfl
      intro m₂ hm₂
      exact (MeasureTheory.integral_prod _
        (integrable_gmAffineMiddleEquation97Term
          f T M₁ M₂ ell m₂ m₂')).symm
    _ = _ := by
      calc
        (∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∑ m₂ ∈ gmAffinePositiveShell M₂,
              ∫ q : ℝ × ℝ,
                gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q) =
          ∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∫ q : ℝ × ℝ,
              ∑ m₂ ∈ gmAffinePositiveShell M₂,
                gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q := by
            apply Finset.sum_congr rfl
            intro m₂' hm₂'
            exact (MeasureTheory.integral_finsetSum _ (fun m₂ _ =>
              integrable_gmAffineMiddleEquation97Term
                f T M₁ M₂ ell m₂ m₂')).symm
        _ = _ := (MeasureTheory.integral_finsetSum _ (fun m₂' _ =>
          integrable_finsetSum _ (fun m₂ _ =>
            integrable_gmAffineMiddleEquation97Term
              f T M₁ M₂ ell m₂ m₂'))).symm

/-- Summing the fixed-frequency equation-(9.7) terms produces exactly the
finite `Z₂` factor. -/
theorem sum_gmAffineMiddleEquation97Term_eq_Z₂Finite
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ) (T : ℝ) (M₁ M₂ : ℕ)
    (m₂ m₂' : ℤ) (q : ℝ × ℝ) :
    (∑ ell ∈ L,
        gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q) =
      (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
        gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1 *
        gmAffineMiddleZ₂Finite L T M₂ m₂ m₂' q.2 q.1 := by
  unfold gmAffineMiddleEquation97Term gmAffineMiddleZ₂Finite
  simp only [Finset.mul_sum]

/-- The finite-frequency right side of Guth--Maynard equation (9.7). -/
noncomputable def gmAffineSigmaIIEquation97Finite
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ)
    (T : ℝ) (M₁ M₂ : ℕ) : ℂ :=
  ∫ q : ℝ × ℝ,
    ∑ m₂' ∈ gmAffinePositiveShell M₂,
      ∑ m₂ ∈ gmAffinePositiveShell M₂,
        (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
          gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1 *
          gmAffineMiddleZ₂Finite L T M₂ m₂ m₂' q.2 q.1

/-- Exact finite-frequency form of Guth--Maynard equation (9.7), with all
three finite sums, both real integrals, and the `Z₁ Z₂` factors retained. -/
theorem gmAffineSigmaIIFinite_eq_equation97
    (L : Finset ℤ) (f : SchwartzMap ℝ ℝ)
    (T : ℝ) (M₁ M₂ : ℕ) :
    gmAffineSigmaIIFinite L f T M₁ M₂ =
      gmAffineSigmaIIEquation97Finite L f T M₁ M₂ := by
  rw [gmAffineSigmaIIFinite_eq_expanded_Z₁_Z₂_integrands]
  unfold gmAffineSigmaIIEquation97Finite
  calc
    (∑ ell ∈ L,
        (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
          ∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
            ∑ m₂' ∈ gmAffinePositiveShell M₂,
              ∑ m₂ ∈ gmAffinePositiveShell M₂,
                ∫ u' : ℝ, ∫ u : ℝ,
                  (((m₂' * m₂ : ℤ) : ℂ) * (f u' : ℂ) * (f u : ℂ)) *
                    (Complex.exp
                      ((gmAffineMiddleTauPhase M₁ m₂ m₂' u u' tau : ℂ) * I) *
                    Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
                      gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I))) =
      ∑ ell ∈ L,
        (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
          ∫ tau : ℝ,
            ∑ m₂' ∈ gmAffinePositiveShell M₂,
              ∑ m₂ ∈ gmAffinePositiveShell M₂,
                gmAffineMiddleSourceTerm f M₁ ell m₂ m₂' tau := by
          apply Finset.sum_congr rfl
          intro ell hell
          congr 1
          apply integral_congr_ae
          filter_upwards with tau
          unfold gmAffineMiddleSourceTerm
          simp only [Finset.mul_sum]
    _ = ∑ ell ∈ L,
        ∫ q : ℝ × ℝ,
          ∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∑ m₂ ∈ gmAffinePositiveShell M₂,
              gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q := by
          apply Finset.sum_congr rfl
          intro ell hell
          exact gmAffineMiddleEllSource_eq_equation97 f T M₁ M₂ ell
    _ = ∫ q : ℝ × ℝ,
        ∑ ell ∈ L,
          ∑ m₂' ∈ gmAffinePositiveShell M₂,
            ∑ m₂ ∈ gmAffinePositiveShell M₂,
              gmAffineMiddleEquation97Term f T M₁ M₂ ell m₂ m₂' q := by
          exact (MeasureTheory.integral_finsetSum L (fun ell _ =>
            integrable_finsetSum _ (fun m₂' _ =>
              integrable_finsetSum _ (fun m₂ _ =>
                integrable_gmAffineMiddleEquation97Term
                  f T M₁ M₂ ell m₂ m₂')))).symm
    _ = ∫ q : ℝ × ℝ,
        ∑ m₂' ∈ gmAffinePositiveShell M₂,
          ∑ m₂ ∈ gmAffinePositiveShell M₂,
            (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
              gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1 *
              gmAffineMiddleZ₂Finite L T M₂ m₂ m₂' q.2 q.1 := by
          apply integral_congr_ae
          filter_upwards with q
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro m₂' hm₂'
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro m₂ hm₂
          exact sum_gmAffineMiddleEquation97Term_eq_Z₂Finite
            L f T M₁ M₂ m₂ m₂' q

/-- A symmetric integer window containing the complete support of the
source cutoff `ψ₂(M₂ ell / T)`.  The extra unit makes the endpoint
comparison strict and avoids any convention at `|x| = 2`. -/
noncomputable def gmAffineMiddleFrequencySupport (T : ℝ) (M₂ : ℕ) : Finset ℤ :=
  let B : ℕ := ⌈2 * T / (M₂ : ℝ)⌉₊ + 1
  Finset.Icc (-(B : ℤ)) (B : ℤ)

theorem gmCubicLocalBump_middleFrequency_eq_zero_of_not_mem
    {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    {ell : ℤ} (hell : ell ∉ gmAffineMiddleFrequencySupport T M₂) :
    gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) = 0 := by
  let B : ℕ := ⌈2 * T / (M₂ : ℝ)⌉₊ + 1
  have hceil : 2 * T / (M₂ : ℝ) ≤
      (⌈2 * T / (M₂ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hB : 2 * T / (M₂ : ℝ) < (B : ℝ) := by
    dsimp only [B]
    push_cast
    linarith
  have hell' : ell < -(B : ℤ) ∨ (B : ℤ) < ell := by
    simpa only [gmAffineMiddleFrequencySupport, B, Finset.mem_Icc,
      not_and_or, not_le] using hell
  have hellAbs : (B : ℝ) < |(ell : ℝ)| := by
    rcases hell' with hleft | hright
    · have hleft' : (ell : ℝ) < -(B : ℝ) := by exact_mod_cast hleft
      rw [abs_of_neg (by linarith)]
      linarith
    · have hright' : (B : ℝ) < (ell : ℝ) := by exact_mod_cast hright
      rw [abs_of_pos (by linarith)]
      exact hright'
  apply gmCubicLocalBump_eq_zero_of_two_le_abs
  rw [abs_div, abs_mul, abs_of_pos hT, abs_of_pos (by positivity : (0 : ℝ) < M₂)]
  apply (le_div_iff₀ hT).2
  have hscale : 2 * T < (M₂ : ℝ) * |(ell : ℝ)| := by
    have hM₂real : (0 : ℝ) < M₂ := by positivity
    have := mul_lt_mul_of_pos_left (lt_trans hB hellAbs) hM₂real
    calc
      2 * T = (M₂ : ℝ) * (2 * T / (M₂ : ℝ)) := by field_simp
      _ < (M₂ : ℝ) * |(ell : ℝ)| := this
  linarith

/-- The finite source-support sum is exactly the complete integer lattice
sum `Z₂`; no tail is being discarded before Poisson summation. -/
theorem gmAffineMiddleZ₂Finite_support_eq_Z₂
    {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    (m₂ m₂' : ℤ) (u u' : ℝ) :
    gmAffineMiddleZ₂Finite (gmAffineMiddleFrequencySupport T M₂)
        T M₂ m₂ m₂' u u' =
      gmAffineMiddleZ₂ T M₂ m₂ m₂' u u' := by
  unfold gmAffineMiddleZ₂Finite gmAffineMiddleZ₂
  rw [tsum_eq_sum (s := gmAffineMiddleFrequencySupport T M₂)]
  intro ell hell
  rw [gmCubicLocalBump_middleFrequency_eq_zero_of_not_mem hT hM₂ hell]
  simp

/-- Guth--Maynard's complete middle-frequency quantity `Σ_II`, written as
the source integer lattice sum rather than a preselected finite window. -/
noncomputable def gmAffineSigmaII
    (f : SchwartzMap ℝ ℝ) (T : ℝ) (M₁ M₂ : ℕ) : ℂ :=
  ∑' ell : ℤ,
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
      ∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
        ((‖gmAffineMiddleFourierBlock f M₁ M₂ ell tau‖ ^ 2 : ℝ) : ℂ)

theorem gmAffineSigmaII_eq_finiteSupport
    {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    (f : SchwartzMap ℝ ℝ) (M₁ : ℕ) :
    gmAffineSigmaII f T M₁ M₂ =
      gmAffineSigmaIIFinite (gmAffineMiddleFrequencySupport T M₂)
        f T M₁ M₂ := by
  unfold gmAffineSigmaII gmAffineSigmaIIFinite
  rw [tsum_eq_sum (s := gmAffineMiddleFrequencySupport T M₂)]
  intro ell hell
  rw [gmCubicLocalBump_middleFrequency_eq_zero_of_not_mem hT hM₂ hell]
  simp

/-- The complete, source-faithful right side of equation (9.7). -/
noncomputable def gmAffineSigmaIIEquation97
    (f : SchwartzMap ℝ ℝ) (T : ℝ) (M₁ M₂ : ℕ) : ℂ :=
  ∫ q : ℝ × ℝ,
    ∑ m₂' ∈ gmAffinePositiveShell M₂,
      ∑ m₂ ∈ gmAffinePositiveShell M₂,
        (((m₂' * m₂ : ℤ) : ℂ) * (f q.1 : ℂ) * (f q.2 : ℂ)) *
          gmAffineMiddleZ₁ M₁ m₂ m₂' q.2 q.1 *
          gmAffineMiddleZ₂ T M₂ m₂ m₂' q.2 q.1

/-- Exact Guth--Maynard equation (9.7) for the complete integer-frequency
sum.  Compact support, both Fubini steps, and both shell sums are proved in
the theorem chain above. -/
theorem gmAffineSigmaII_eq_equation97
    {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    (f : SchwartzMap ℝ ℝ) (M₁ : ℕ) :
    gmAffineSigmaII f T M₁ M₂ =
      gmAffineSigmaIIEquation97 f T M₁ M₂ := by
  rw [gmAffineSigmaII_eq_finiteSupport hT hM₂,
    gmAffineSigmaIIFinite_eq_equation97]
  unfold gmAffineSigmaIIEquation97Finite gmAffineSigmaIIEquation97
  apply integral_congr_ae
  filter_upwards with q
  apply Finset.sum_congr rfl
  intro m₂' hm₂'
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  rw [gmAffineMiddleZ₂Finite_support_eq_Z₂ hT hM₂]

/-- Zeroth-order uniform bound for one second-Poisson kernel value. -/
theorem norm_gmAffineScaledBumpDual_le
    {S : ℝ} (hS : 0 < S) (y : ℝ) :
    ‖gmAffineScaledBumpDual S hS y‖ ≤
      S * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual := by
  simpa using gmAffineScaledBumpDual_polynomial_decay 0 hS y

/-- The affine center associated with the Poisson integer `j`.  The sign
is chosen so that replacing `j` by `-j` gives the source affine shift. -/
noncomputable def gmAffineMiddleCenter (m₂ m₂' j : ℤ) (u : ℝ) : ℝ :=
  ((m₂ : ℝ) * u - (j : ℝ)) / (m₂' : ℝ)

/-- Membership in the retained second-Poisson window forces `u'` into the
physical interval of radius `Q/T` about the corresponding affine center. -/
theorem mem_gmAffineUnitInterval_div_of_mem_scaledNear
    {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {m₂ m₂' j : ℤ}
    (hm₂' : m₂' ∈ gmAffinePositiveShell M₂) {u u' : ℝ}
    (hj : j ∈ gmAffineScaledNearSet (T / M₂)
      (-gmAffineMiddleDisplacement m₂ m₂' u u') Q) :
    u' ∈ gmAffineUnitInterval (T / Q)
      (gmAffineMiddleCenter m₂ m₂' j u) := by
  have hnear := (Finset.mem_filter.mp hj).2
  have hm₂'Bounds := mem_gmAffinePositiveShell.mp hm₂'
  have hM₂Int : (0 : ℤ) < (M₂ : ℤ) := by exact_mod_cast hM₂
  have hm₂'PosInt : (0 : ℤ) < m₂' :=
    lt_of_lt_of_le hM₂Int hm₂'Bounds.1
  have hm₂'Pos : (0 : ℝ) < m₂' := by
    exact_mod_cast hm₂'PosInt
  have hS : 0 < T / (M₂ : ℝ) := by positivity
  have hM₂real : (0 : ℝ) < M₂ := by positivity
  have hraw :
      |u' - gmAffineMiddleCenter m₂ m₂' j u| < Q / T := by
    have hfactor :
        (T / (M₂ : ℝ)) *
            ((j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u') =
          ((T * (m₂' : ℝ)) / (M₂ : ℝ)) *
            (u' - gmAffineMiddleCenter m₂ m₂' j u) := by
      unfold gmAffineMiddleDisplacement gmAffineMiddleCenter
      field_simp [show (m₂' : ℝ) ≠ 0 by positivity,
        show (M₂ : ℝ) ≠ 0 by positivity]
      ring
    rw [show -gmAffineMiddleDisplacement m₂ m₂' u u' + (j : ℝ) =
        (j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u' by ring,
      hfactor, abs_mul, abs_of_pos (by positivity :
      (0 : ℝ) < (T * (m₂' : ℝ)) / (M₂ : ℝ))] at hnear
    have hscale : T ≤ (T * (m₂' : ℝ)) / (M₂ : ℝ) := by
      rw [le_div_iff₀ hM₂real]
      nlinarith [show (M₂ : ℝ) ≤ m₂' by exact_mod_cast hm₂'Bounds.1]
    have hTmul : T * |u' - gmAffineMiddleCenter m₂ m₂' j u| < Q :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hscale (abs_nonneg _)) hnear
    exact (lt_div_iff₀ hT).mpr (by simpa [mul_comm] using hTmul)
  rw [gmAffineUnitInterval, Set.mem_Icc]
  have hHQ : 0 < T / Q := by positivity
  have hradius : 1 / (T / Q) = Q / T := by field_simp
  rw [hradius]
  rw [abs_lt] at hraw
  constructor <;> linarith

/-- On the source support and for `Q ≤ T`, every retained Poisson integer
maps (after the sign change in (9.5)) into the actual finite affine-shift
shell used by `J`. -/
theorem neg_mem_gmAffineCentralShell_of_mem_scaledNear
    {T Q : ℝ} (hT : 0 < T) (hQT : Q ≤ T)
    {M₂ : ℕ} (hM₂ : 0 < M₂) {m₂ m₂' j : ℤ}
    (hm₂ : m₂ ∈ gmAffinePositiveShell M₂)
    (hm₂' : m₂' ∈ gmAffinePositiveShell M₂)
    {u u' : ℝ} (hu : u ∈ Set.Icc (1 / 2 : ℝ) 2)
    (hu' : u' ∈ Set.Icc (1 / 2 : ℝ) 2)
    (hj : j ∈ gmAffineScaledNearSet (T / M₂)
      (-gmAffineMiddleDisplacement m₂ m₂' u u') Q) :
    -j ∈ gmAffineCentralShell M₂ := by
  have hm₂Bounds := mem_gmAffinePositiveShell.mp hm₂
  have hm₂'Bounds := mem_gmAffinePositiveShell.mp hm₂'
  have hM₂real : (0 : ℝ) < M₂ := by positivity
  have hm₂Lower : (M₂ : ℝ) ≤ m₂ := by exact_mod_cast hm₂Bounds.1
  have hm₂Upper : (m₂ : ℝ) ≤ 2 * M₂ := by exact_mod_cast hm₂Bounds.2
  have hm₂'Lower : (M₂ : ℝ) ≤ m₂' := by exact_mod_cast hm₂'Bounds.1
  have hm₂'Upper : (m₂' : ℝ) ≤ 2 * M₂ := by exact_mod_cast hm₂'Bounds.2
  have hm₂Nonneg : (0 : ℝ) ≤ m₂ := hM₂real.le.trans hm₂Lower
  have hm₂'Nonneg : (0 : ℝ) ≤ m₂' := hM₂real.le.trans hm₂'Lower
  have hmuLower : (M₂ : ℝ) / 2 ≤ (m₂ : ℝ) * u := by
    calc
      (M₂ : ℝ) / 2 = (M₂ : ℝ) * (1 / 2 : ℝ) := by ring
      _ ≤ (m₂ : ℝ) * u :=
        mul_le_mul hm₂Lower hu.1 (by norm_num) hm₂Nonneg
  have hmuUpper : (m₂ : ℝ) * u ≤ 4 * M₂ := by
    calc
      (m₂ : ℝ) * u ≤ (2 * M₂ : ℝ) * 2 :=
        mul_le_mul hm₂Upper hu.2 (by linarith [hu.1]) (by positivity)
      _ = 4 * M₂ := by ring
  have hm'u'Lower : (M₂ : ℝ) / 2 ≤ (m₂' : ℝ) * u' := by
    calc
      (M₂ : ℝ) / 2 = (M₂ : ℝ) * (1 / 2 : ℝ) := by ring
      _ ≤ (m₂' : ℝ) * u' :=
        mul_le_mul hm₂'Lower hu'.1 (by norm_num) hm₂'Nonneg
  have hm'u'Upper : (m₂' : ℝ) * u' ≤ 4 * M₂ := by
    calc
      (m₂' : ℝ) * u' ≤ (2 * M₂ : ℝ) * 2 :=
        mul_le_mul hm₂'Upper hu'.2 (by linarith [hu'.1]) (by positivity)
      _ = 4 * M₂ := by ring
  have hnear := (Finset.mem_filter.mp hj).2
  have hS : 0 < T / (M₂ : ℝ) := by positivity
  rw [abs_mul, abs_of_pos hS] at hnear
  have herrScaled : (T / (M₂ : ℝ)) *
      |(j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u'| < T := by
    simpa [sub_eq_add_neg, add_comm] using hnear.trans_le hQT
  have herr :
      |(j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u'| < M₂ := by
    have hmul : T *
        |(j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u'| <
          T * M₂ := by
      apply (div_lt_iff₀ hM₂real).mp
      simpa [div_mul_eq_mul_div] using herrScaled
    nlinarith
  rw [abs_lt] at herr
  unfold gmAffineMiddleDisplacement at herr
  have hjLower : (-(8 * M₂ : ℝ)) ≤ -(j : ℝ) := by
    linarith
  have hjUpper : -(j : ℝ) ≤ (8 * M₂ : ℝ) := by
    linarith
  rw [mem_gmAffineCentralShell]
  constructor
  · have hcast : ((-(8 * (M₂ : ℤ)) : ℤ) : ℝ) ≤ ((-j : ℤ) : ℝ) := by
      push_cast
      simpa using hjLower
    exact_mod_cast hcast
  · have hcast : ((-j : ℤ) : ℝ) ≤ (((8 * M₂ : ℕ) : ℤ) : ℝ) := by
      push_cast
      simpa using hjUpper
    exact_mod_cast hcast

end RiemannZeta.GuthMaynard
