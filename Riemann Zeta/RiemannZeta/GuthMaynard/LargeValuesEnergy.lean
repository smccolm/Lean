import RiemannZeta.GuthMaynard.LargeValuesS3Refined
import RiemannZeta.GuthMaynard.HeathBrownReflection
import RiemannZeta.GuthMaynard.ClassicalEndpointSlab

open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap

namespace RiemannZeta.GuthMaynard

/-!
# Guth--Maynard Section 11: energy estimates

This module starts the source-facing Section 11 consumer chain.  It uses the
native Heath--Brown difference-set theorem proved in
`HeathBrownReflection`, rather than introducing a Section 11 estimate as an
independent premise.
-/

/-! ## A coefficient-preserving Fourier reproducing formula -/

/-- Fourier deweighting with arbitrary fixed coefficients.  The existing
coefficient-one theorem is sufficient for Type I; Guth--Maynard Lemma 11.3
requires the same exact identity without discarding the source coefficients.
-/
theorem fourierDeweightFiniteBlock_logShift_coeffs_native
    (f : SchwartzMap ℝ ℂ) (S : Finset ℕ) (b : ℕ → ℂ) (t a : ℝ)
    (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S, b n * f (Real.log n - a) *
        (n : ℂ) ^ (-(t : ℂ) * I)) =
      ∫ ξ : ℝ, 𝓕 f ξ *
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
          ∑ n ∈ S, b n *
            (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
  have hinversion (u : ℝ) :
      f u = ∫ ξ : ℝ,
        Complex.exp (((2 * Real.pi * (ξ * u) : ℝ) : ℂ) * I) * 𝓕 f ξ := by
    have hpairMap : 𝓕⁻ (𝓕 f) = f := FourierTransform.fourierInv_fourier_eq f
    have hpair := congrArg (fun g : SchwartzMap ℝ ℂ ↦ g u) hpairMap
    change (𝓕⁻ (𝓕 f)) u = f u at hpair
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hpair
    simpa only [Real.inner_apply, smul_eq_mul] using hpair.symm
  have hbaseIntegrable (n : ℕ) (hn : 0 < n) : Integrable
      (fun ξ : ℝ ↦ 𝓕 f ξ *
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)) := by
    have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hcontinuous : Continuous (fun ξ : ℝ ↦
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)) := by
      apply Continuous.mul
      · fun_prop
      · apply Continuous.const_cpow
        · fun_prop
        · exact Or.inl hnNe
    have hbound : ∀ᵐ ξ : ℝ ∂volume,
        ‖Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
          (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)‖ ≤ 1 := by
      filter_upwards with ξ
      rw [norm_mul, Complex.norm_exp, Complex.norm_natCast_cpow_of_pos hn]
      simp
    have hInt := (𝓕 f).integrable.mul_bdd (c := 1)
      hcontinuous.aestronglyMeasurable hbound
    simpa only [mul_assoc] using hInt
  have hintegrable (n : ℕ) (hn : 0 < n) : Integrable
      (fun ξ : ℝ ↦ 𝓕 f ξ *
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
          (b n * (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I))) := by
    have h := (hbaseIntegrable n hn).mul_const (b n)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ n ∈ S, b n * f (Real.log n - a) *
        (n : ℂ) ^ (-(t : ℂ) * I)) =
      ∑ n ∈ S, ∫ ξ : ℝ, 𝓕 f ξ *
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
          (b n * (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)) := by
      apply Finset.sum_congr rfl
      intro n hnS
      have hn := hS n hnS
      have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [hinversion]
      rw [← MeasureTheory.integral_const_mul,
        ← MeasureTheory.integral_mul_const]
      apply integral_congr_ae
      filter_upwards with ξ
      have hphase :
          Complex.exp (((2 * Real.pi *
              (ξ * (Real.log n - a)) : ℝ) : ℂ) * I) *
              (n : ℂ) ^ (-(t : ℂ) * I) =
            Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
              (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
        rw [Complex.cpow_def_of_ne_zero hnNe,
          Complex.cpow_def_of_ne_zero hnNe]
        have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
        have hlog : Complex.log (n : ℂ) =
            (Real.log (n : ℝ) : ℂ) := (Complex.ofReal_log hnReal.le).symm
        rw [hlog, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      calc
        b n *
              (Complex.exp (((2 * Real.pi *
                  (ξ * (Real.log n - a)) : ℝ) : ℂ) * I) * 𝓕 f ξ) *
              (n : ℂ) ^ (-(t : ℂ) * I) =
            b n * 𝓕 f ξ *
              (Complex.exp (((2 * Real.pi *
                  (ξ * (Real.log n - a)) : ℝ) : ℂ) * I) *
                (n : ℂ) ^ (-(t : ℂ) * I)) := by ring
        _ = b n * 𝓕 f ξ *
              (Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
                (n : ℂ) ^
                  (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)) := by
              rw [hphase]
        _ = 𝓕 f ξ *
              Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
                (b n * (n : ℂ) ^
                  (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)) := by ring
    _ = ∫ ξ : ℝ, ∑ n ∈ S, 𝓕 f ξ *
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
          (b n * (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)) := by
      rw [integral_finsetSum]
      intro n hn
      exact hintegrable n (hS n hn)
    _ = ∫ ξ : ℝ, 𝓕 f ξ *
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)) *
          ∑ n ∈ S, b n *
            (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := by
      apply integral_congr_ae
      filter_upwards with ξ
      simpa only [mul_assoc] using
        (Finset.mul_sum S
          (fun n : ℕ ↦ b n *
            (n : ℂ) ^ (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * I))
          (𝓕 f ξ * Complex.exp
            (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * I)))).symm

/-- The fixed affine bump is identically one on the complete logarithmic
image of the source interval `(M,2M]`. -/
theorem gmAffineLocalBumpSchwartz_one_on_dyadicLog
    {M n : ℕ} (hM : 0 < M) (hn : n ∈ dyadicInterval M) :
    gmAffineLocalBumpSchwartz (Real.log n - Real.log M) = 1 := by
  have hnBounds := Finset.mem_Ioc.mp hn
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hnr : (0 : ℝ) < n := by exact_mod_cast (hM.trans hnBounds.1)
  have hLowerCast : (M : ℝ) ≤ n := by exact_mod_cast hnBounds.1.le
  have hUpperCast : (n : ℝ) ≤ 2 * M := by
    exact_mod_cast hnBounds.2
  have hlogLower : Real.log (M : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hMr hLowerCast
  have hlogUpperRaw : Real.log (n : ℝ) ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_le_log hnr hUpperCast
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hMr.ne'] at hlogUpperRaw
  have habs : |Real.log (n : ℝ) - Real.log (M : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hlogLower)]
    linarith [Real.log_two_lt_d9]
  rw [gmAffineLocalBumpSchwartz_apply, gmCubicLocalBump_one habs]
  norm_num

/-- Exact band-limited reproducing formula for the actual source polynomial.
This is the equality underlying Guth--Maynard Lemma 11.3; later estimates
split this integral into its local part and a rapidly decaying far tail. -/
theorem sourceDirichletPoly_energyFourier_reproduction
    {M : ℕ} (hM : 0 < M) (b : ℕ → ℂ) (t : ℝ) :
    sourceDirichletPoly M b t =
      ∫ ξ : ℝ, 𝓕 gmAffineLocalBumpSchwartz ξ *
        Complex.exp
          (-(((2 * Real.pi * ξ * Real.log (M : ℝ) : ℝ) : ℂ) * I)) *
        sourceDirichletPoly M b (t + 2 * Real.pi * ξ) := by
  have hPositive : ∀ n ∈ dyadicInterval M, 0 < n := by
    intro n hn
    exact hM.trans (Finset.mem_Ioc.mp hn).1
  have hFourier := fourierDeweightFiniteBlock_logShift_coeffs_native
    gmAffineLocalBumpSchwartz (dyadicInterval M) b (-t)
      (Real.log (M : ℝ)) hPositive
  calc
    sourceDirichletPoly M b t =
        ∑ n ∈ dyadicInterval M,
          b n * gmAffineLocalBumpSchwartz
              (Real.log n - Real.log (M : ℝ)) *
            (n : ℂ) ^ (-((-t : ℝ) : ℂ) * I) := by
      unfold sourceDirichletPoly
      apply Finset.sum_congr rfl
      intro n hn
      rw [gmAffineLocalBumpSchwartz_one_on_dyadicLog hM hn]
      have hexp : ((t : ℝ) : ℂ) * I = -(((-t : ℝ) : ℂ)) * I := by
        push_cast
        ring
      rw [hexp]
      ring
    _ = ∫ ξ : ℝ, 𝓕 gmAffineLocalBumpSchwartz ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * Real.log (M : ℝ) : ℝ) : ℂ) * I)) *
          ∑ n ∈ dyadicInterval M, b n *
            (n : ℂ) ^
              (-((((-t) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I) := hFourier
    _ = ∫ ξ : ℝ, 𝓕 gmAffineLocalBumpSchwartz ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * Real.log (M : ℝ) : ℝ) : ℂ) * I)) *
          sourceDirichletPoly M b (t + 2 * Real.pi * ξ) := by
      apply integral_congr_ae
      filter_upwards with ξ
      congr 1
      change (∑ n ∈ dyadicInterval M, b n *
          (n : ℂ) ^ (-((((-t) - 2 * Real.pi * ξ : ℝ) : ℂ)) * I)) =
        ∑ n ∈ dyadicInterval M, b n *
          (n : ℂ) ^ ((((t + 2 * Real.pi * ξ : ℝ) : ℂ)) * I)
      apply Finset.sum_congr rfl
      intro n hn
      congr 1
      push_cast
      ring

/-- Arbitrary polynomial decay of the fixed Fourier profile used in
Guth--Maynard Lemma 11.3.  The constant is absolute because the bump itself
is fixed once and for all. -/
theorem gmAffineLocalBumpFourier_polynomial_decay (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ,
      |ξ| ^ q * ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ ≤ C := by
  let F : SchwartzMap ℝ ℂ := 𝓕 gmAffineLocalBumpSchwartz
  let C : ℝ := SchwartzMap.seminorm ℝ q 0 F
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ξ
  have hSem := SchwartzMap.le_seminorm' (𝕜 := ℝ) q 0 F ξ
  rw [iteratedDeriv_zero] at hSem
  simpa only [F, C, Real.norm_eq_abs] using hSem

/-- A fixed global bound for the Fourier profile in Lemma 11.3. -/
noncomputable def gmAffineLocalBumpFourierSup : ℝ :=
  max 1 (Classical.choose (gmAffineLocalBumpFourier_polynomial_decay 0))

theorem gmAffineLocalBumpFourierSup_pos :
    0 < gmAffineLocalBumpFourierSup :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem norm_gmAffineLocalBumpFourier_le (ξ : ℝ) :
    ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ ≤ gmAffineLocalBumpFourierSup := by
  have hChoose := (Classical.choose_spec
    (gmAffineLocalBumpFourier_polynomial_decay 0)).2 ξ
  have hBase : ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ ≤
      Classical.choose (gmAffineLocalBumpFourier_polynomial_decay 0) := by
    simpa only [pow_zero, one_mul] using hChoose
  exact hBase.trans (le_max_right _ _)

/-- Quantitative `L¹` tail of the fixed Section 11 Fourier profile, at any
integer order at least two. -/
theorem exists_gmAffineLocalBumpFourier_tail_bound (q : ℕ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H →
      ∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ,
          ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ ≤
        C * H ^ (1 - (q : ℝ)) := by
  obtain ⟨C₀, hC₀, hDecay⟩ :=
    gmAffineLocalBumpFourier_polynomial_decay q
  let C : ℝ := max 1 (2 * C₀ / ((q : ℝ) - 1))
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro H hH
  have hHPos : 0 < H := zero_lt_one.trans_le hH
  let F : SchwartzMap ℝ ℂ := 𝓕 gmAffineLocalBumpSchwartz
  have hqReal : (1 : ℝ) < q := by exact_mod_cast hq
  have hExp : -(q : ℝ) < -1 := by linarith
  have hFInt : Integrable (fun ξ : ℝ => ‖F ξ‖) := F.integrable.norm
  have hDomInt : IntegrableOn (fun ξ : ℝ => C₀ * |ξ| ^ (-(q : ℝ)))
      (Set.Icc (-H) H)ᶜ := by
    exact (integrableOn_abs_rpow_compl_Icc hExp hHPos).const_mul C₀
  have hPoint : ∀ᵐ ξ : ℝ ∂volume.restrict (Set.Icc (-H) H)ᶜ,
      ‖F ξ‖ ≤ C₀ * |ξ| ^ (-(q : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with ξ hξ
    have hAbs : H < |ξ| := by
      by_contra hnot
      exact hξ (abs_le.mp (le_of_not_gt hnot))
    have hAbsPos : 0 < |ξ| := hHPos.trans hAbs
    have hRaw := hDecay ξ
    change |ξ| ^ q * ‖F ξ‖ ≤ C₀ at hRaw
    rw [show |ξ| ^ (-(q : ℝ)) = (|ξ| ^ q)⁻¹ by
      rw [Real.rpow_neg hAbsPos.le, Real.rpow_natCast]]
    rw [le_mul_inv_iff₀ (pow_pos hAbsPos q)]
    simpa only [mul_comm] using hRaw
  calc
    ∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ,
        ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ ≤
      ∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ,
        C₀ * |ξ| ^ (-(q : ℝ)) := by
          exact integral_mono_ae hFInt.integrableOn hDomInt hPoint
    _ = (2 * C₀ / ((q : ℝ) - 1)) * H ^ (1 - (q : ℝ)) := by
      rw [integral_const_mul, integral_abs_rpow_compl_Icc hExp hHPos]
      have hexp : -(q : ℝ) + 1 = 1 - (q : ℝ) := by ring
      rw [hexp]
      have hden : (q : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hqReal)
      have hden' : 1 - (q : ℝ) ≠ 0 := by linarith
      field_simp [hden, hden']
      ring
    _ ≤ C * H ^ (1 - (q : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg hHPos.le _)

/-- A single proved Schwartz-tail constant, fixed once for a decay order.
Its proof argument is propositionally irrelevant, so every later ordinate
and multiplicity-class estimate uses the same mathematical constant. -/
noncomputable def gmAffineLocalBumpFourierTailConstant
    (q : ℕ) (hq : 2 ≤ q) : ℝ :=
  Classical.choose (exists_gmAffineLocalBumpFourier_tail_bound q hq)

theorem gmAffineLocalBumpFourierTailConstant_pos
    (q : ℕ) (hq : 2 ≤ q) :
    0 < gmAffineLocalBumpFourierTailConstant q hq :=
  (Classical.choose_spec
    (exists_gmAffineLocalBumpFourier_tail_bound q hq)).1

theorem gmAffineLocalBumpFourierTailConstant_bound
    (q : ℕ) (hq : 2 ≤ q) (H : ℝ) (hH : 1 ≤ H) :
    ∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ,
        ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ ≤
      gmAffineLocalBumpFourierTailConstant q hq *
        H ^ (1 - (q : ℝ)) :=
  (Classical.choose_spec
    (exists_gmAffineLocalBumpFourier_tail_bound q hq)).2 H hH

/-- Trivial source-polynomial bound with the exact dyadic cardinality.  It
is used only on the omitted Fourier tail in Lemma 11.3. -/
theorem norm_sourceDirichletPoly_le_scale
    {M : ℕ} (b : ℕ → ℂ) (t : ℝ)
    (hb : ∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) :
    ‖sourceDirichletPoly M b t‖ ≤ M := by
  unfold sourceDirichletPoly
  calc
    ‖∑ n ∈ dyadicInterval M,
        b n * (n : ℂ) ^ (((t : ℂ)) * I)‖ ≤
      ∑ n ∈ dyadicInterval M,
        ‖b n * (n : ℂ) ^ (((t : ℂ)) * I)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ dyadicInterval M, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos
        (by exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1))]
      simpa using hb n hn
    _ = M := by simp [dyadicInterval, Nat.card_Ioc]; omega

/-- The complete reproducing integrand is integrable uniformly in its
ordinate.  This justifies the exact central/tail split used below. -/
theorem integrable_sourceDirichletPoly_energyFourier
    {M : ℕ} (hM : 0 < M) (b : ℕ → ℂ) (t : ℝ)
    (hb : ∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) :
    Integrable (fun ξ : ℝ => 𝓕 gmAffineLocalBumpSchwartz ξ *
      Complex.exp
        (-(((2 * Real.pi * ξ * Real.log (M : ℝ) : ℝ) : ℂ) * I)) *
      sourceDirichletPoly M b (t + 2 * Real.pi * ξ)) := by
  let g : ℝ → ℂ := fun ξ =>
    Complex.exp
        (-(((2 * Real.pi * ξ * Real.log (M : ℝ) : ℝ) : ℂ) * I)) *
      sourceDirichletPoly M b (t + 2 * Real.pi * ξ)
  have hgContinuous : Continuous g := by
    dsimp only [g]
    apply Continuous.mul
    · fun_prop
    · dsimp only [sourceDirichletPoly]
      apply continuous_finsetSum
      intro n hn
      apply Continuous.const_mul
      apply Continuous.const_cpow
      · fun_prop
      · left
        exact_mod_cast (hM.trans (Finset.mem_Ioc.mp hn).1).ne'
  have hexpNorm (ξ : ℝ) :
      ‖Complex.exp
        (-(((2 * Real.pi * ξ * Real.log (M : ℝ) : ℝ) : ℂ) * I))‖ = 1 := by
    rw [show -(((2 * Real.pi * ξ * Real.log (M : ℝ) : ℝ) : ℂ) * I) =
        ((-(2 * Real.pi * ξ * Real.log (M : ℝ)) : ℝ) : ℂ) * I by
      push_cast
      ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hgBound : ∀ᵐ ξ : ℝ ∂volume, ‖g ξ‖ ≤ M := by
    filter_upwards with ξ
    rw [norm_mul, hexpNorm, one_mul]
    exact norm_sourceDirichletPoly_le_scale b _ hb
  have h := (𝓕 gmAffineLocalBumpSchwartz).integrable.mul_bdd
    hgContinuous.aestronglyMeasurable hgBound
  simpa only [g, mul_assoc] using h

/-- Quantitative local-shift form of Guth--Maynard Lemma 11.3.  The first
term contains only shifts `|2πξ| ≤ 2πH`; the second is the complete omitted
Fourier tail, with arbitrary polynomial decay and no untracked term. -/
theorem sourceDirichletPoly_norm_le_localFourier_add_tail
    {M : ℕ} (hM : 0 < M) (b : ℕ → ℂ) (t H : ℝ)
    (hb : ∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1)
    (hH : 1 ≤ H) (q : ℕ) (hq : 2 ≤ q) :
    ‖sourceDirichletPoly M b t‖ ≤
      (∫ ξ : ℝ in Set.Icc (-H) H,
        ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
          ‖sourceDirichletPoly M b (t + 2 * Real.pi * ξ)‖) +
        (M : ℝ) * gmAffineLocalBumpFourierTailConstant q hq *
          H ^ (1 - (q : ℝ)) := by
  let C := gmAffineLocalBumpFourierTailConstant q hq
  have hC : 0 < C := gmAffineLocalBumpFourierTailConstant_pos q hq
  have hTail := gmAffineLocalBumpFourierTailConstant_bound q hq
  let f : ℝ → ℂ := fun ξ => 𝓕 gmAffineLocalBumpSchwartz ξ *
    Complex.exp
      (-(((2 * Real.pi * ξ * Real.log (M : ℝ) : ℝ) : ℂ) * I)) *
    sourceDirichletPoly M b (t + 2 * Real.pi * ξ)
  have hf : Integrable f := by
    simpa only [f] using
      integrable_sourceDirichletPoly_energyFourier hM b t hb
  have hrepr := sourceDirichletPoly_energyFourier_reproduction hM b t
  have hsplit := integral_add_compl
    (s := Set.Icc (-H) H) measurableSet_Icc hf
  have hexpNorm (ξ : ℝ) :
      ‖Complex.exp
        (-(((2 * Real.pi * ξ * Real.log (M : ℝ) : ℝ) : ℂ) * I))‖ = 1 := by
    rw [show -(((2 * Real.pi * ξ * Real.log (M : ℝ) : ℝ) : ℂ) * I) =
        ((-(2 * Real.pi * ξ * Real.log (M : ℝ)) : ℝ) : ℂ) * I by
      push_cast
      ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hTailNorm : ‖∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, f ξ‖ ≤
      (M : ℝ) * C * H ^ (1 - (q : ℝ)) := by
    calc
      ‖∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, f ξ‖ ≤
          ∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, ‖f ξ‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ,
          (M : ℝ) * ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ := by
        apply integral_mono_ae hf.norm.integrableOn
          ((𝓕 gmAffineLocalBumpSchwartz).integrable.norm.const_mul M).integrableOn
        filter_upwards with ξ
        dsimp only [f]
        rw [norm_mul, norm_mul, hexpNorm]
        simp only [mul_one]
        have hp := norm_sourceDirichletPoly_le_scale b
          (t + 2 * Real.pi * ξ) hb
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_of_nonneg_left hp
            (norm_nonneg (𝓕 gmAffineLocalBumpSchwartz ξ))
      _ = (M : ℝ) * (∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ,
          ‖𝓕 gmAffineLocalBumpSchwartz ξ‖) := by
        rw [integral_const_mul]
      _ ≤ (M : ℝ) * (C * H ^ (1 - (q : ℝ))) := by
        gcongr
        exact hTail H hH
      _ = (M : ℝ) * C * H ^ (1 - (q : ℝ)) := by ring
  calc
    ‖sourceDirichletPoly M b t‖ =
        ‖(∫ ξ : ℝ in Set.Icc (-H) H, f ξ) +
          (∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, f ξ)‖ := by
      have hrepr' : sourceDirichletPoly M b t = ∫ ξ : ℝ, f ξ := by
        simpa only [f] using hrepr
      exact (congrArg norm hrepr').trans (congrArg norm hsplit.symm)
    _ ≤ ‖(∫ ξ : ℝ in Set.Icc (-H) H, f ξ)‖ +
          ‖(∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, f ξ)‖ := by
      simpa using norm_add_le
        (∫ ξ : ℝ in Set.Icc (-H) H, f ξ)
        (∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, f ξ)
    _ ≤ (∫ ξ : ℝ in Set.Icc (-H) H, ‖f ξ‖) +
          (M : ℝ) * C * H ^ (1 - (q : ℝ)) := by
      gcongr
      exact norm_integral_le_integral_norm _
    _ = (∫ ξ : ℝ in Set.Icc (-H) H,
          ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
            ‖sourceDirichletPoly M b (t + 2 * Real.pi * ξ)‖) +
          (M : ℝ) * C * H ^ (1 - (q : ℝ)) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      intro ξ hξ
      dsimp only [f]
      rw [norm_mul, norm_mul, hexpNorm]
      simp only [mul_one]

/-- The arbitrary-order Fourier tail in Lemma 11.3 is `O(T⁻ᴬ)` once the
polynomial length is at most the ambient height.  The decay order and its
epsilon dependence are the same audited choices used by the quantitative
smooth-reflection module. -/
theorem gmLemma11ThreeFourierError_le
    {A ε C T : ℝ} {M : ℕ}
    (hA : 0 < A) (hε : 0 < ε) (hC : 0 ≤ C)
    (hT : 1 ≤ T) (hMT : (M : ℝ) ≤ T) :
    (M : ℝ) * C * gmReflectionHeight T ε ^
        (1 - (gmReflectionDecayOrder A ε : ℝ)) ≤ C / T ^ A := by
  let η := gmReflectionEta ε
  let q := gmReflectionDecayOrder A ε
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hBudget := gmReflectionDecayOrder_budget hA hε
  have hExponent : 1 + η * (1 - (q : ℝ)) ≤ -A := by
    dsimp only [η, q]
    nlinarith
  have hHeight : gmReflectionHeight T ε ^ (1 - (q : ℝ)) =
      T ^ (η * (1 - (q : ℝ))) := by
    dsimp only [gmReflectionHeight, η]
    rw [Real.rpow_mul hTpos.le]
  have hHeightNonneg : 0 ≤
      gmReflectionHeight T ε ^ (1 - (q : ℝ)) := by
    rw [hHeight]
    exact Real.rpow_nonneg hTpos.le _
  calc
    (M : ℝ) * C * gmReflectionHeight T ε ^ (1 - (q : ℝ)) ≤
        T * C * gmReflectionHeight T ε ^ (1 - (q : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMT hC) hHeightNonneg
    _ = C * T ^ (1 + η * (1 - (q : ℝ))) := by
      rw [hHeight]
      calc
        T * C * T ^ (η * (1 - (q : ℝ))) =
            C * (T ^ (1 : ℝ) * T ^ (η * (1 - (q : ℝ)))) := by
          rw [Real.rpow_one]
          ring
        _ = C * T ^ (1 + η * (1 - (q : ℝ))) := by
          rw [← Real.rpow_add hTpos]
    _ ≤ C * T ^ (-A) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT hExponent) hC
    _ = C / T ^ A := by
      rw [Real.rpow_neg hTpos.le]
      ring

/-- Source-form Lemma 11.3 with its paper-level `T^{-A}` remainder and a
fully explicit `T^η` shift window. -/
theorem sourceDirichletPoly_norm_le_gmReflectionWindow_add_error
    {A ε T : ℝ} {M : ℕ}
    (hA : 0 < A) (hε : 0 < ε) (hT : 1 ≤ T)
    (hM : 0 < M) (hMT : (M : ℝ) ≤ T)
    (b : ℕ → ℂ) (t : ℝ)
    (hb : ∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) :
    ‖sourceDirichletPoly M b t‖ ≤
      (∫ ξ : ℝ in Set.Icc
          (-(gmReflectionHeight T ε)) (gmReflectionHeight T ε),
        ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
          ‖sourceDirichletPoly M b (t + 2 * Real.pi * ξ)‖) +
        gmAffineLocalBumpFourierTailConstant
            (gmReflectionDecayOrder A ε)
            (gmReflectionDecayOrder_two_le A ε) /
          T ^ A := by
  let q := gmReflectionDecayOrder A ε
  have hq : 2 ≤ q := gmReflectionDecayOrder_two_le A ε
  have hH : 1 ≤ gmReflectionHeight T ε := by
    unfold gmReflectionHeight
    exact Real.one_le_rpow hT (gmReflectionEta_pos hε).le
  let C := gmAffineLocalBumpFourierTailConstant q hq
  have hC : 0 < C := gmAffineLocalBumpFourierTailConstant_pos q hq
  have hlocal := sourceDirichletPoly_norm_le_localFourier_add_tail
    hM b t (gmReflectionHeight T ε) hb hH q hq
  exact hlocal.trans (by
    gcongr
    exact gmLemma11ThreeFourierError_le hA hε hC.le hT hMT)

/-- Uniform quantifier order for Lemma 11.3.  The same absolute tail
constant works for every height, length, coefficient sequence, and
ordinate, which is essential before summing a dyadic multiplicity class. -/
theorem sourceDirichletPoly_norm_le_gmReflectionWindow_add_error_uniform
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ} {M : ℕ},
      1 ≤ T → 0 < M → (M : ℝ) ≤ T →
      ∀ (b : ℕ → ℂ) (t : ℝ),
        (∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) →
        ‖sourceDirichletPoly M b t‖ ≤
          (∫ ξ : ℝ in Set.Icc
              (-(gmReflectionHeight T ε)) (gmReflectionHeight T ε),
            ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
              ‖sourceDirichletPoly M b (t + 2 * Real.pi * ξ)‖) +
            C / T ^ A := by
  let q := gmReflectionDecayOrder A ε
  let C := gmAffineLocalBumpFourierTailConstant q
    (gmReflectionDecayOrder_two_le A ε)
  refine ⟨C, gmAffineLocalBumpFourierTailConstant_pos q
      (gmReflectionDecayOrder_two_le A ε), ?_⟩
  intro T M hT hM hMT b t hb
  simpa only [C, q] using
    sourceDirichletPoly_norm_le_gmReflectionWindow_add_error
      hA hε hT hM hMT b t hb

/-- The common displacement radius after a nearest-integer error of at
most one and a Fourier shift of size `H`. -/
noncomputable def gmSection11CommonRadius (H : ℝ) : ℝ :=
  1 + 2 * Real.pi * H

theorem setIntegral_Icc_comp_mul_add
    (f : ℝ → ℝ) {a b c s : ℝ} (hab : a ≤ b) (hc : 0 < c) :
    (∫ x : ℝ in Set.Icc a b, f (c * x + s)) =
      c⁻¹ * ∫ y : ℝ in Set.Icc (c * a + s) (c * b + s), f y := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_mul_add (f := f) hc.ne' s]
  have hcb : c * a + s ≤ c * b + s := by gcongr
  rw [intervalIntegral.integral_of_le hcb,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rfl

/-- A local Fourier integral centered at any displacement `|s| ≤ 1` is
dominated by one common interval.  This is the rigorous replacement for
the paper's `sup_{|s| ≪ 1}` before applying Heath--Brown. -/
theorem sourceDirichletPoly_localFourier_le_commonInterval
    {M : ℕ} (hM : 0 < M) (b : ℕ → ℂ) (base s H : ℝ)
    (hs : |s| ≤ 1) (hH : 0 ≤ H) :
    (∫ ξ : ℝ in Set.Icc (-H) H,
        ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
          ‖sourceDirichletPoly M b (base + s + 2 * Real.pi * ξ)‖) ≤
      gmAffineLocalBumpFourierSup / (2 * Real.pi) *
        ∫ t : ℝ in Set.Icc (-(gmSection11CommonRadius H))
            (gmSection11CommonRadius H),
          ‖sourceDirichletPoly M b (base + t)‖ := by
  let f : ℝ → ℝ := fun t => ‖sourceDirichletPoly M b (base + t)‖
  have hf : Continuous f := by
    dsimp only [f, sourceDirichletPoly]
    apply Continuous.norm
    apply continuous_finsetSum
    intro n hn
    apply Continuous.const_mul
    apply Continuous.const_cpow
    · fun_prop
    · left
      exact_mod_cast (hM.trans (Finset.mem_Ioc.mp hn).1).ne'
  have hOrder : -H ≤ H := by linarith
  have hLocalSource : Continuous (fun ξ : ℝ =>
      ‖sourceDirichletPoly M b (base + s + 2 * Real.pi * ξ)‖) := by
    have harg : Continuous (fun ξ : ℝ => s + 2 * Real.pi * ξ) := by
      fun_prop
    have hcomp := hf.comp harg
    convert hcomp using 1
    funext ξ
    dsimp only [f]
    congr 2
    ring
  have hLocalInt : IntegrableOn
      (fun ξ : ℝ => ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
        ‖sourceDirichletPoly M b (base + s + 2 * Real.pi * ξ)‖)
      (Set.Icc (-H) H) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    apply Continuous.mul
    · exact (𝓕 gmAffineLocalBumpSchwartz).continuous.norm
    · exact hLocalSource
  have hMajorInt : IntegrableOn
      (fun ξ : ℝ => gmAffineLocalBumpFourierSup *
        f (2 * Real.pi * ξ + s)) (Set.Icc (-H) H) := by
    apply ContinuousOn.integrableOn_Icc
    have harg : Continuous (fun ξ : ℝ => 2 * Real.pi * ξ + s) := by
      fun_prop
    exact (continuous_const.mul (hf.comp harg)).continuousOn
  have hPoint (ξ : ℝ) :
      ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
          ‖sourceDirichletPoly M b (base + s + 2 * Real.pi * ξ)‖ ≤
        gmAffineLocalBumpFourierSup * f (2 * Real.pi * ξ + s) := by
    have hw := norm_gmAffineLocalBumpFourier_le ξ
    have hn : 0 ≤ ‖sourceDirichletPoly M b
        (base + s + 2 * Real.pi * ξ)‖ := norm_nonneg _
    have := mul_le_mul_of_nonneg_right hw hn
    dsimp only [f]
    convert this using 1
    all_goals ring
  have hFirst :
      (∫ ξ : ℝ in Set.Icc (-H) H,
          ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
            ‖sourceDirichletPoly M b (base + s + 2 * Real.pi * ξ)‖) ≤
        ∫ ξ : ℝ in Set.Icc (-H) H,
          gmAffineLocalBumpFourierSup * f (2 * Real.pi * ξ + s) := by
    exact setIntegral_mono hLocalInt hMajorInt hPoint
  have hScale :
      (∫ ξ : ℝ in Set.Icc (-H) H, f (2 * Real.pi * ξ + s)) =
        (2 * Real.pi)⁻¹ *
          ∫ t : ℝ in Set.Icc (2 * Real.pi * (-H) + s)
              (2 * Real.pi * H + s), f t := by
    exact setIntegral_Icc_comp_mul_add f hOrder
      (mul_pos (by norm_num) Real.pi_pos)
  have hsBounds := abs_le.mp hs
  have hSubset : Set.Icc (2 * Real.pi * (-H) + s)
      (2 * Real.pi * H + s) ⊆
      Set.Icc (-(gmSection11CommonRadius H))
        (gmSection11CommonRadius H) := by
    intro t ht
    rw [Set.mem_Icc] at ht ⊢
    dsimp only [gmSection11CommonRadius]
    constructor <;> linarith [Real.pi_pos]
  have hSmallInt : IntegrableOn f
      (Set.Icc (2 * Real.pi * (-H) + s) (2 * Real.pi * H + s)) :=
    hf.continuousOn.integrableOn_Icc
  have hBigInt : IntegrableOn f
      (Set.Icc (-(gmSection11CommonRadius H))
        (gmSection11CommonRadius H)) := hf.continuousOn.integrableOn_Icc
  have hIntegralMono :
      (∫ t : ℝ in Set.Icc (2 * Real.pi * (-H) + s)
          (2 * Real.pi * H + s), f t) ≤
        ∫ t : ℝ in Set.Icc (-(gmSection11CommonRadius H))
            (gmSection11CommonRadius H), f t := by
    exact setIntegral_mono_set hBigInt
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun t ht => hSubset ht)
  calc
    _ ≤ ∫ ξ : ℝ in Set.Icc (-H) H,
          gmAffineLocalBumpFourierSup * f (2 * Real.pi * ξ + s) := hFirst
    _ = gmAffineLocalBumpFourierSup *
          ((2 * Real.pi)⁻¹ *
            ∫ t : ℝ in Set.Icc (2 * Real.pi * (-H) + s)
              (2 * Real.pi * H + s), f t) := by
      rw [MeasureTheory.integral_const_mul, hScale]
    _ ≤ gmAffineLocalBumpFourierSup *
          ((2 * Real.pi)⁻¹ *
            ∫ t : ℝ in Set.Icc (-(gmSection11CommonRadius H))
              (gmSection11CommonRadius H), f t) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hIntegralMono
          (inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)))
        gmAffineLocalBumpFourierSup_pos.le
    _ = _ := by
      dsimp only [f]
      field_simp [Real.pi_ne_zero]

/-- Cauchy--Schwarz on the common Section 11 displacement interval. -/
theorem sq_setIntegral_norm_sourceDirichletPoly_le
    {M : ℕ} (hM : 0 < M) (b : ℕ → ℂ) (base H : ℝ) (hH : 0 ≤ H) :
    (∫ t : ℝ in Set.Icc (-(gmSection11CommonRadius H))
        (gmSection11CommonRadius H),
        ‖sourceDirichletPoly M b (base + t)‖) ^ 2 ≤
      (2 * gmSection11CommonRadius H) *
        ∫ t : ℝ in Set.Icc (-(gmSection11CommonRadius H))
            (gmSection11CommonRadius H),
          ‖sourceDirichletPoly M b (base + t)‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => ‖sourceDirichletPoly M b (base + t)‖
  have hf : Continuous f := by
    dsimp only [f, sourceDirichletPoly]
    apply Continuous.norm
    apply continuous_finsetSum
    intro n hn
    apply Continuous.const_mul
    apply Continuous.const_cpow
    · fun_prop
    · left
      exact_mod_cast (hM.trans (Finset.mem_Ioc.mp hn).1).ne'
  have hRadius : 0 ≤ gmSection11CommonRadius H := by
    dsimp only [gmSection11CommonRadius]
    positivity
  have hCS := sq_intervalIntegral_le_length_mul_intervalIntegral_sq
    f (gmSection11CommonRadius H) hRadius hf (fun _ => norm_nonneg _)
  rw [intervalIntegral.integral_of_le (neg_le_self hRadius),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (neg_le_self hRadius),
    ← MeasureTheory.integral_Icc_eq_integral_Ioc] at hCS
  simpa only [f] using hCS

/-- Squared common-interval form of Lemma 11.3, uniform in the bounded
nearest-integer displacement and with the complete `T^{-A}` error. -/
theorem sourceDirichletPoly_norm_sq_le_commonInterval_add_error
    {A ε T : ℝ} {M : ℕ}
    (hA : 0 < A) (hε : 0 < ε) (hT : 1 ≤ T)
    (hM : 0 < M) (hMT : (M : ℝ) ≤ T)
    (b : ℕ → ℂ) (base s : ℝ) (hs : |s| ≤ 1)
    (hb : ∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) :
    ‖sourceDirichletPoly M b (base + s)‖ ^ 2 ≤
      2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
          (2 * gmSection11CommonRadius (gmReflectionHeight T ε)) *
          (∫ t : ℝ in Set.Icc
              (-(gmSection11CommonRadius (gmReflectionHeight T ε)))
              (gmSection11CommonRadius (gmReflectionHeight T ε)),
            ‖sourceDirichletPoly M b (base + t)‖ ^ 2) +
        2 * (gmAffineLocalBumpFourierTailConstant
            (gmReflectionDecayOrder A ε)
            (gmReflectionDecayOrder_two_le A ε) / T ^ A) ^ 2 := by
  let H := gmReflectionHeight T ε
  let K := gmAffineLocalBumpFourierSup / (2 * Real.pi)
  let E := gmAffineLocalBumpFourierTailConstant
    (gmReflectionDecayOrder A ε)
    (gmReflectionDecayOrder_two_le A ε) / T ^ A
  let J := ∫ t : ℝ in Set.Icc (-(gmSection11CommonRadius H))
      (gmSection11CommonRadius H),
    ‖sourceDirichletPoly M b (base + t)‖
  have hH : 0 ≤ H := by
    dsimp only [H, gmReflectionHeight]
    positivity
  have hRaw := sourceDirichletPoly_norm_le_gmReflectionWindow_add_error
    hA hε hT hM hMT b (base + s) hb
  have hLocal := sourceDirichletPoly_localFourier_le_commonInterval
    hM b base s H hs hH
  have hRaw' : ‖sourceDirichletPoly M b (base + s)‖ ≤ K * J + E := by
    have hsum := add_le_add hLocal (le_refl E)
    exact hRaw.trans (by
      simpa only [H, K, J, E] using hsum)
  have hRhsNonneg : 0 ≤ K * J + E := (norm_nonneg _).trans hRaw'
  have hSq := pow_le_pow_left₀ (norm_nonneg _) hRaw' 2
  have hSplit : (K * J + E) ^ 2 ≤ 2 * K ^ 2 * J ^ 2 + 2 * E ^ 2 := by
    nlinarith [sq_nonneg (K * J - E)]
  have hCS := sq_setIntegral_norm_sourceDirichletPoly_le
    hM b base H hH
  calc
    ‖sourceDirichletPoly M b (base + s)‖ ^ 2 ≤ (K * J + E) ^ 2 := hSq
    _ ≤ 2 * K ^ 2 * J ^ 2 + 2 * E ^ 2 := hSplit
    _ ≤ 2 * K ^ 2 *
          ((2 * gmSection11CommonRadius H) *
            ∫ t : ℝ in Set.Icc (-(gmSection11CommonRadius H))
                (gmSection11CommonRadius H),
              ‖sourceDirichletPoly M b (base + t)‖ ^ 2) +
          2 * E ^ 2 := by
      gcongr
    _ = _ := by
      dsimp only [K, J, E, H]
      ring

/-- The discrete ratio moment occurring throughout Guth--Maynard Section 11.
Keeping it as one sum over the Cartesian product makes the Hölder step an
ordinary finite Cauchy--Schwarz inequality. -/
noncomputable def gmDiscreteRatioMoment (p M : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ nm ∈ dyadicInterval M ×ˢ dyadicInterval M,
    ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ p

theorem gmDiscreteRatioMoment_eq_iterated (p M : ℕ) (W : Finset ℝ) :
    gmDiscreteRatioMoment p M W =
      ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        ‖gmR W ((n : ℝ) / m)‖ ^ p := by
  unfold gmDiscreteRatioMoment
  rw [Finset.sum_product]

/-- The exact finite Hölder interpolation used immediately before the GCD
split in Section 11. -/
theorem gmDiscreteThirdMoment_sq_le_second_mul_fourth
    (M : ℕ) (W : Finset ℝ) :
    gmDiscreteRatioMoment 3 M W ^ 2 ≤
      gmDiscreteRatioMoment 2 M W * gmDiscreteRatioMoment 4 M W := by
  let S := dyadicInterval M ×ˢ dyadicInterval M
  let a : ℕ × ℕ → ℝ := fun nm ↦ ‖gmR W ((nm.1 : ℝ) / nm.2)‖
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S a (fun nm ↦ a nm ^ 2)
  have hthree :
      (∑ nm ∈ S, a nm ^ 3) = ∑ nm ∈ S, a nm * a nm ^ 2 := by
    apply Finset.sum_congr rfl
    intro nm hnm
    ring
  have hfour :
      (∑ nm ∈ S, a nm ^ 4) = ∑ nm ∈ S, (a nm ^ 2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro nm hnm
    ring
  change (∑ nm ∈ S, a nm ^ 3) ^ 2 ≤
    (∑ nm ∈ S, a nm ^ 2) * ∑ nm ∈ S, a nm ^ 4
  rw [hthree, hfour]
  exact hCS

/-- Square-root form of the finite Hölder step. -/
theorem gmDiscreteThirdMoment_le_sqrt
    (M : ℕ) (W : Finset ℝ) :
    gmDiscreteRatioMoment 3 M W ≤
      Real.sqrt (gmDiscreteRatioMoment 2 M W) *
        Real.sqrt (gmDiscreteRatioMoment 4 M W) := by
  unfold gmDiscreteRatioMoment
  have h := Real.sum_mul_le_sqrt_mul_sqrt
    (dyadicInterval M ×ˢ dyadicInterval M)
    (fun nm ↦ ‖gmR W ((nm.1 : ℝ) / nm.2)‖)
    (fun nm ↦ ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 2)
  have hthree :
      (∑ nm ∈ dyadicInterval M ×ˢ dyadicInterval M,
          ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 3) =
        ∑ nm ∈ dyadicInterval M ×ˢ dyadicInterval M,
          ‖gmR W ((nm.1 : ℝ) / nm.2)‖ *
            ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro nm hnm
    ring
  have hfour :
      (∑ nm ∈ dyadicInterval M ×ˢ dyadicInterval M,
          ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 4) =
        ∑ nm ∈ dyadicInterval M ×ˢ dyadicInterval M,
          (‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 2) ^ 2 := by
    apply Finset.sum_congr rfl
    intro nm hnm
    ring
  rw [hthree, hfour]
  exact h

/-- The elementary fallback used in Lemma 1.7: one pointwise factor is
bounded by `|W|`.  The refined Section 11 argument replaces this loss with
the dyadic fourth-moment analysis below. -/
theorem gmDiscreteThirdMoment_le_card_mul_second (M : ℕ) (W : Finset ℝ) :
    gmDiscreteRatioMoment 3 M W ≤
      (W.card : ℝ) * gmDiscreteRatioMoment 2 M W := by
  unfold gmDiscreteRatioMoment
  calc
    ∑ nm ∈ dyadicInterval M ×ˢ dyadicInterval M,
        ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 3 ≤
      ∑ nm ∈ dyadicInterval M ×ˢ dyadicInterval M,
        (W.card : ℝ) * ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro nm hnm
      have hR := norm_gmR_le_card_all W ((nm.1 : ℝ) / nm.2)
      nlinarith [sq_nonneg ‖gmR W ((nm.1 : ℝ) / nm.2)‖]
    _ = (W.card : ℝ) *
        ∑ nm ∈ dyadicInterval M ×ˢ dyadicInterval M,
          ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 2 := by
      rw [Finset.mul_sum]

theorem gmDiscreteFourthMoment_le_card_sq_mul_second (M : ℕ) (W : Finset ℝ) :
    gmDiscreteRatioMoment 4 M W ≤
      (W.card : ℝ) ^ 2 * gmDiscreteRatioMoment 2 M W := by
  unfold gmDiscreteRatioMoment
  calc
    ∑ nm ∈ dyadicInterval M ×ˢ dyadicInterval M,
        ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 4 ≤
      ∑ nm ∈ dyadicInterval M ×ˢ dyadicInterval M,
        (W.card : ℝ) ^ 2 * ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro nm hnm
      have hR := norm_gmR_le_card_all W ((nm.1 : ℝ) / nm.2)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hR 2
      nlinarith [sq_nonneg ‖gmR W ((nm.1 : ℝ) / nm.2)‖]
    _ = (W.card : ℝ) ^ 2 *
        ∑ nm ∈ dyadicInterval M ×ˢ dyadicInterval M,
          ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 2 := by
      rw [Finset.mul_sum]

/-- Guth--Maynard Lemma 11.5.  The equality between the discrete ratio
moment and Heath--Brown's coefficient-one difference moment is exact; only
the final estimate carries the arbitrary epsilon loss. -/
theorem gmDiscreteSecondMoment_native :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ),
          0 < M → T₀ ≤ T → IsSeparated 1 W → InBaseInterval T W →
          (∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
              ‖gmR W ((n : ℝ) / m)‖ ^ 2) ≤
            C * T ^ epsilon *
              (((W.card : ℝ) ^ 2 * M) +
                ((W.card : ℝ) * M ^ 2) +
                ((W.card : ℝ) ^ (5 / 4 : ℝ) *
                  T ^ (1 / 2 : ℝ) * M)) := by
  intro epsilon hepsilon
  obtain ⟨C, T₀, hC, hT₀, hHB⟩ :=
    heathBrownCoefficientOneMeanSquare_native epsilon hepsilon
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T W hM hT hSep hBase
  rw [← sourceCoefficientOne_differenceMoment_eq_gmR_ratioMoment]
  exact hHB M T W hM hT hSep hBase

/-- Lemma 11.5 in the one-sum notation consumed by the later Hölder and
GCD decompositions. -/
theorem gmDiscreteRatioSecondMoment_native :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ),
          0 < M → T₀ ≤ T → IsSeparated 1 W → InBaseInterval T W →
          gmDiscreteRatioMoment 2 M W ≤
            C * T ^ epsilon *
              (((W.card : ℝ) ^ 2 * M) +
                ((W.card : ℝ) * M ^ 2) +
                ((W.card : ℝ) ^ (5 / 4 : ℝ) *
                  T ^ (1 / 2 : ℝ) * M)) := by
  intro epsilon hepsilon
  obtain ⟨C, T₀, hC, hT₀, h⟩ := gmDiscreteSecondMoment_native epsilon hepsilon
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T W hM hT hSep hBase
  rw [gmDiscreteRatioMoment_eq_iterated]
  exact h M T W hM hT hSep hBase

/-! ## The exact difference-multiplicity layer for Lemma 11.6 -/

/-- A nearest-integer difference bin.  Equality of these bins forces two
real differences to be within one unit, exactly the tolerance used by
`ApproxAddEnergy 1`, while the bin labels themselves remain one-separated
for the Heath--Brown consumer. -/
noncomputable def gmHalfDifferenceBin (p : ℝ × ℝ) : ℤ :=
  ⌊(p.1 - p.2) + 1 / 2⌋

noncomputable def gmHalfDifferenceMatchedPairs (W : Finset ℝ) :
    Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((W ×ˢ W) ×ˢ (W ×ˢ W)).filter fun q ↦
    gmHalfDifferenceBin q.1 = gmHalfDifferenceBin q.2

noncomputable def gmHalfMatchedToEnergy
    (q : (ℝ × ℝ) × (ℝ × ℝ)) : (ℝ × ℝ) × (ℝ × ℝ) :=
  ((q.1.1, q.2.2), (q.1.2, q.2.1))

theorem gmHalfMatchedToEnergy_mem (W : Finset ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ))
    (hq : q ∈ gmHalfDifferenceMatchedPairs W) :
    gmHalfMatchedToEnergy q ∈ approximateAdditiveQuadruples 1 W := by
  simp only [gmHalfDifferenceMatchedPairs, Finset.mem_filter,
    Finset.mem_product] at hq
  simp only [gmHalfMatchedToEnergy, approximateAdditiveQuadruples,
    Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨⟨hq.1.1.1, hq.1.2.2⟩, hq.1.1.2, hq.1.2.1⟩, ?_⟩
  have hfloor := hq.2
  have hleftLower := Int.floor_le ((q.1.1 - q.1.2) + 1 / 2)
  have hleftUpper := Int.lt_floor_add_one ((q.1.1 - q.1.2) + 1 / 2)
  have hrightLower := Int.floor_le ((q.2.1 - q.2.2) + 1 / 2)
  have hrightUpper := Int.lt_floor_add_one ((q.2.1 - q.2.2) + 1 / 2)
  unfold gmHalfDifferenceBin at hfloor
  rw [hfloor] at hleftLower hleftUpper
  rw [abs_le]
  constructor <;> linarith

theorem card_gmHalfDifferenceMatchedPairs_le_energy (W : Finset ℝ) :
    (gmHalfDifferenceMatchedPairs W).card ≤ ApproxAddEnergy 1 W := by
  unfold ApproxAddEnergy
  apply Finset.card_le_card_of_injOn gmHalfMatchedToEnergy
  · intro q hq
    exact gmHalfMatchedToEnergy_mem W q hq
  · intro q hq q' hq' heq
    rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rcases q' with ⟨⟨a', b'⟩, ⟨c', d'⟩⟩
    simp only [gmHalfMatchedToEnergy, Prod.mk.injEq] at heq
    rcases heq with ⟨⟨ha, hd⟩, hb, hc⟩
    subst a'
    subst b'
    subst c'
    subst d'
    rfl

/-- The multiplicity of one half-unit difference bin. -/
noncomputable def gmHalfDifferenceMultiplicity (W : Finset ℝ) (u : ℤ) : ℕ :=
  ((W ×ˢ W).filter fun p ↦ gmHalfDifferenceBin p = u).card

/-- Exact fiber-square identity: the sum of squared bin multiplicities is
the cardinality of the matched-pair set. -/
theorem sum_gmHalfDifferenceMultiplicity_sq (W : Finset ℝ) :
    ∑ u ∈ (W ×ˢ W).image gmHalfDifferenceBin,
        gmHalfDifferenceMultiplicity W u ^ 2 =
      (gmHalfDifferenceMatchedPairs W).card := by
  classical
  let P := W ×ˢ W
  let f := gmHalfDifferenceBin
  calc
    ∑ u ∈ P.image f, gmHalfDifferenceMultiplicity W u ^ 2 =
        ∑ u ∈ P.image f,
          (((P.filter fun p ↦ f p = u).card) *
            ((P.filter fun p ↦ f p = u).card)) := by
          apply Finset.sum_congr rfl
          intro u hu
          simp only [gmHalfDifferenceMultiplicity, P, f, pow_two]
    _ = ∑ u ∈ P.image f,
          ((P.filter fun p ↦ f p = u) ×ˢ
            (P.filter fun p ↦ f p = u)).card := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.card_product]
    _ = (gmHalfDifferenceMatchedPairs W).card := by
          rw [← Finset.card_biUnion]
          · congr 1
            ext q
            simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product,
              Finset.mem_filter, gmHalfDifferenceMatchedPairs, P, f]
            constructor
            · rintro ⟨u, ⟨p, hp, rfl⟩, hq1, hq2⟩
              exact ⟨⟨hq1.1, hq2.1⟩, hq1.2.trans hq2.2.symm⟩
            · rintro ⟨⟨hq1, hq2⟩, heq⟩
              refine ⟨f q.1, ⟨q.1, hq1, rfl⟩, ⟨hq1, rfl⟩, hq2, ?_⟩
              exact heq.symm
          · intro u hu v hv huv
            apply Finset.disjoint_left.2
            intro q hqu hqv
            simp only [Finset.mem_product, Finset.mem_filter] at hqu hqv
            exact huv (hqu.1.2.symm.trans hqv.1.2)

/-- Source inequality `∑ B(u)^2 ≤ E(W)` used in Lemma 11.6, now with
the half-unit bin convention that proves the tolerance-one bridge exactly. -/
theorem sum_gmHalfDifferenceMultiplicity_sq_le_energy (W : Finset ℝ) :
    ∑ u ∈ (W ×ˢ W).image gmHalfDifferenceBin,
        gmHalfDifferenceMultiplicity W u ^ 2 ≤ ApproxAddEnergy 1 W := by
  rw [sum_gmHalfDifferenceMultiplicity_sq]
  exact card_gmHalfDifferenceMatchedPairs_le_energy W

/-- In a one-separated set a half-unit difference bin contains at most one
second ordinate for each first ordinate.  This is the exact finite form of
the source assertion `B ≤ |W|`. -/
theorem gmHalfDifferenceMultiplicity_le_card (W : Finset ℝ)
    (hSep : IsSeparated 1 W) (u : ℤ) :
    gmHalfDifferenceMultiplicity W u ≤ W.card := by
  unfold gmHalfDifferenceMultiplicity
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    change p ∈ (W ×ˢ W).filter (fun p ↦ gmHalfDifferenceBin p = u) at hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact hp.1.1
  · intro p hp q hq hpq
    change p ∈ (W ×ˢ W).filter (fun p ↦ gmHalfDifferenceBin p = u) at hp
    change q ∈ (W ×ˢ W).filter (fun p ↦ gmHalfDifferenceBin p = u) at hq
    simp only [Finset.mem_filter, Finset.mem_product] at hp hq
    have hpMem := hp
    have hqMem := hq
    have hfloor : gmHalfDifferenceBin p = gmHalfDifferenceBin q :=
      hpMem.2.trans hqMem.2.symm
    have hfirst : p.1 = q.1 := hpq
    by_cases hsecond : p.2 = q.2
    · exact Prod.ext hfirst hsecond
    · have hseparation : 1 ≤ |p.2 - q.2| := by
        simpa [Real.dist_eq] using
          hSep p.2 hpMem.1.2 q.2 hqMem.1.2 hsecond
      have hpLower := Int.floor_le ((p.1 - p.2) + 1 / 2)
      have hpUpper := Int.lt_floor_add_one ((p.1 - p.2) + 1 / 2)
      have hqLower := Int.floor_le ((q.1 - q.2) + 1 / 2)
      have hqUpper := Int.lt_floor_add_one ((q.1 - q.2) + 1 / 2)
      unfold gmHalfDifferenceBin at hfloor
      rw [hfloor, hfirst] at hpLower hpUpper
      have hdiff : |p.2 - q.2| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      exact False.elim ((not_lt_of_ge hseparation) hdiff)

/-- The total mass of all difference-bin multiplicities is exactly the
number of ordered pairs in `W`. -/
theorem sum_gmHalfDifferenceMultiplicity (W : Finset ℝ) :
    ∑ u ∈ (W ×ˢ W).image gmHalfDifferenceBin,
        gmHalfDifferenceMultiplicity W u = W.card ^ 2 := by
  classical
  calc
    ∑ u ∈ (W ×ˢ W).image gmHalfDifferenceBin,
        gmHalfDifferenceMultiplicity W u = (W ×ˢ W).card := by
      exact (Finset.card_eq_sum_card_image gmHalfDifferenceBin (W ×ˢ W)).symm
    _ = W.card ^ 2 := by simp [pow_two]

/-- The source dyadic multiplicity class `U_B`, with `B = 2^j`. -/
noncomputable def gmHalfDifferenceDyadicClass (W : Finset ℝ) (j : ℕ) : Finset ℤ :=
  ((W ×ˢ W).image gmHalfDifferenceBin).filter fun u ↦
    2 ^ j ≤ gmHalfDifferenceMultiplicity W u ∧
      gmHalfDifferenceMultiplicity W u < 2 ^ (j + 1)

theorem mem_gmHalfDifferenceDyadicClass {W : Finset ℝ} {j : ℕ} {u : ℤ} :
    u ∈ gmHalfDifferenceDyadicClass W j ↔
      u ∈ (W ×ˢ W).image gmHalfDifferenceBin ∧
        2 ^ j ≤ gmHalfDifferenceMultiplicity W u ∧
        gmHalfDifferenceMultiplicity W u < 2 ^ (j + 1) := by
  simp [gmHalfDifferenceDyadicClass]

/-- Exact `B |U_B| ≤ |W|^2`. -/
theorem twoPow_mul_card_gmHalfDifferenceDyadicClass_le
    (W : Finset ℝ) (j : ℕ) :
    2 ^ j * (gmHalfDifferenceDyadicClass W j).card ≤ W.card ^ 2 := by
  let U := gmHalfDifferenceDyadicClass W j
  let S := (W ×ˢ W).image gmHalfDifferenceBin
  have hUS : U ⊆ S := by
    intro u hu
    exact (mem_gmHalfDifferenceDyadicClass.mp hu).1
  have hpoint : ∀ u ∈ U, 2 ^ j ≤ gmHalfDifferenceMultiplicity W u := by
    intro u hu
    exact (mem_gmHalfDifferenceDyadicClass.mp hu).2.1
  calc
    2 ^ j * U.card = ∑ _u ∈ U, 2 ^ j := by simp [Nat.mul_comm]
    _ ≤ ∑ u ∈ U, gmHalfDifferenceMultiplicity W u := by
      exact Finset.sum_le_sum fun u hu ↦ hpoint u hu
    _ ≤ ∑ u ∈ S, gmHalfDifferenceMultiplicity W u := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hUS (fun _ _ _ ↦ Nat.zero_le _)
    _ = W.card ^ 2 := by
      simpa only [S] using sum_gmHalfDifferenceMultiplicity W

/-- Exact `B² |U_B| ≤ E(W)`. -/
theorem twoPow_sq_mul_card_gmHalfDifferenceDyadicClass_le_energy
    (W : Finset ℝ) (j : ℕ) :
    (2 ^ j) ^ 2 * (gmHalfDifferenceDyadicClass W j).card ≤
      ApproxAddEnergy 1 W := by
  let U := gmHalfDifferenceDyadicClass W j
  let S := (W ×ˢ W).image gmHalfDifferenceBin
  have hUS : U ⊆ S := by
    intro u hu
    exact (mem_gmHalfDifferenceDyadicClass.mp hu).1
  have hpoint : ∀ u ∈ U,
      (2 ^ j) ^ 2 ≤ gmHalfDifferenceMultiplicity W u ^ 2 := by
    intro u hu
    exact Nat.pow_le_pow_left (mem_gmHalfDifferenceDyadicClass.mp hu).2.1 2
  calc
    (2 ^ j) ^ 2 * U.card = ∑ _u ∈ U, (2 ^ j) ^ 2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ u ∈ U, gmHalfDifferenceMultiplicity W u ^ 2 := by
      exact Finset.sum_le_sum fun u hu ↦ hpoint u hu
    _ ≤ ∑ u ∈ S, gmHalfDifferenceMultiplicity W u ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hUS (fun _ _ _ ↦ Nat.zero_le _)
    _ ≤ ApproxAddEnergy 1 W := by
      simpa only [S] using sum_gmHalfDifferenceMultiplicity_sq_le_energy W

/-- Every occupied difference bin has positive multiplicity.  This is the
finite nonvanishing fact needed before taking its base-two logarithm. -/
theorem gmHalfDifferenceMultiplicity_pos_of_mem {W : Finset ℝ} {u : ℤ}
    (hu : u ∈ (W ×ˢ W).image gmHalfDifferenceBin) :
    0 < gmHalfDifferenceMultiplicity W u := by
  classical
  rw [Finset.mem_image] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  unfold gmHalfDifferenceMultiplicity
  exact Finset.card_pos.mpr ⟨p, by simp only [Finset.mem_filter, hp, true_and]⟩

/-- Nearest-integer error for the actual Section 11 difference bin. -/
theorem abs_sub_gmHalfDifferenceBin_le_half (p : ℝ × ℝ) :
    |(p.1 - p.2) - (gmHalfDifferenceBin p : ℝ)| ≤ 1 / 2 := by
  have hlower := Int.floor_le ((p.1 - p.2) + 1 / 2)
  have hupper := Int.lt_floor_add_one ((p.1 - p.2) + 1 / 2)
  unfold gmHalfDifferenceBin
  rw [abs_le]
  constructor <;> linarith

/-- The two nearest-integer errors combine to a displacement of absolute
value at most one, and reconstruct the original pair difference exactly. -/
theorem gmHalfDifference_pair_displacement
    (p q : ℝ × ℝ) :
    let s := ((p.1 - p.2) - (gmHalfDifferenceBin p : ℝ)) -
      ((q.1 - q.2) - (gmHalfDifferenceBin q : ℝ))
    |s| ≤ 1 ∧
      (p.1 - p.2) - (q.1 - q.2) =
        ((gmHalfDifferenceBin p : ℝ) - gmHalfDifferenceBin q) + s := by
  dsimp only
  constructor
  · calc
      |((p.1 - p.2) - (gmHalfDifferenceBin p : ℝ)) -
          ((q.1 - q.2) - (gmHalfDifferenceBin q : ℝ))| ≤
          |(p.1 - p.2) - (gmHalfDifferenceBin p : ℝ)| +
            |(q.1 - q.2) - (gmHalfDifferenceBin q : ℝ)| := abs_sub _ _
      _ ≤ 1 / 2 + 1 / 2 := add_le_add
        (abs_sub_gmHalfDifferenceBin_le_half p)
        (abs_sub_gmHalfDifferenceBin_le_half q)
      _ = 1 := by norm_num
  · ring

/-- The source dyadic selection is total: the class indexed by the base-two
logarithm of an occupied fiber contains that fiber. -/
theorem mem_gmHalfDifferenceDyadicClass_log {W : Finset ℝ} {u : ℤ}
    (hu : u ∈ (W ×ˢ W).image gmHalfDifferenceBin) :
    u ∈ gmHalfDifferenceDyadicClass W
      (Nat.log 2 (gmHalfDifferenceMultiplicity W u)) := by
  rw [mem_gmHalfDifferenceDyadicClass]
  refine ⟨hu, ?_, ?_⟩
  · exact Nat.pow_log_le_self 2
      (Nat.ne_of_gt (gmHalfDifferenceMultiplicity_pos_of_mem hu))
  · simpa [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
        (gmHalfDifferenceMultiplicity W u)

/-- Every pair in the `j`th logarithmic multiplicity block maps to the
corresponding integer-bin class `U_{2^j}`. -/
theorem gmHalfDifferenceBin_mem_dyadicClass_of_pair
    {W : Finset ℝ} {j : ℕ} {p : ℝ × ℝ}
    (hp : p ∈ (W ×ˢ W).filter (fun p ↦
      Nat.log 2 (gmHalfDifferenceMultiplicity W
        (gmHalfDifferenceBin p)) = j)) :
    gmHalfDifferenceBin p ∈ gmHalfDifferenceDyadicClass W j := by
  have hp' := Finset.mem_filter.mp hp
  have hu : gmHalfDifferenceBin p ∈ (W ×ˢ W).image gmHalfDifferenceBin :=
    Finset.mem_image.mpr ⟨p, hp'.1, rfl⟩
  have hmpos : 0 < gmHalfDifferenceMultiplicity W (gmHalfDifferenceBin p) :=
    gmHalfDifferenceMultiplicity_pos_of_mem hu
  rw [mem_gmHalfDifferenceDyadicClass]
  refine ⟨hu, ?_, ?_⟩
  · rw [← hp'.2]
    exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hmpos)
  · rw [← hp'.2]
    simpa [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
        (gmHalfDifferenceMultiplicity W (gmHalfDifferenceBin p))

/-- A pair fiber inside the `j`th block has fewer than `2^(j+1)` members. -/
theorem card_gmHalfDifferenceDyadicPairFiber_lt
    {W : Finset ℝ} {j : ℕ} {u : ℤ}
    (hu : u ∈ gmHalfDifferenceDyadicClass W j) :
    (((W ×ˢ W).filter (fun p ↦
        Nat.log 2 (gmHalfDifferenceMultiplicity W
          (gmHalfDifferenceBin p)) = j)).filter (fun p ↦
          gmHalfDifferenceBin p = u)).card < 2 ^ (j + 1) := by
  have hcard :
      (((W ×ˢ W).filter (fun p ↦
          Nat.log 2 (gmHalfDifferenceMultiplicity W
            (gmHalfDifferenceBin p)) = j)).filter (fun p ↦
            gmHalfDifferenceBin p = u)).card ≤
        gmHalfDifferenceMultiplicity W u := by
    unfold gmHalfDifferenceMultiplicity
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1.1, hp.2⟩
  exact hcard.trans_lt (mem_gmHalfDifferenceDyadicClass.mp hu).2.2

/-- For a one-separated set, no occupied dyadic class has index beyond
`log₂ |W|`.  Thus the source's dyadic selection ranges over a genuinely
finite, explicitly bounded family. -/
theorem log_gmHalfDifferenceMultiplicity_le_log_card
    (W : Finset ℝ) (hSep : IsSeparated 1 W) (u : ℤ) :
    Nat.log 2 (gmHalfDifferenceMultiplicity W u) ≤ Nat.log 2 W.card := by
  exact Nat.log_mono_right (gmHalfDifferenceMultiplicity_le_card W hSep u)

/-- Every occupied half-difference bin lies in one of the explicit classes
`0, ..., log₂ |W|`. -/
theorem exists_bounded_gmHalfDifferenceDyadicClass
    (W : Finset ℝ) (hSep : IsSeparated 1 W) {u : ℤ}
    (hu : u ∈ (W ×ˢ W).image gmHalfDifferenceBin) :
    ∃ j ∈ Finset.range (Nat.log 2 W.card + 1),
      u ∈ gmHalfDifferenceDyadicClass W j := by
  refine ⟨Nat.log 2 (gmHalfDifferenceMultiplicity W u), ?_,
    mem_gmHalfDifferenceDyadicClass_log hu⟩
  simp only [Finset.mem_range]
  exact Nat.lt_succ_of_le (log_gmHalfDifferenceMultiplicity_le_log_card W hSep u)

/-! ## Exact dyadic decomposition of the fourth-moment phase -/

/-- The pair phase whose sum is `|R(e^x)|²`. -/
noncomputable def gmHalfDifferencePairPhase (p : ℝ × ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((((p.1 - p.2) * x : ℝ) : ℂ) * I)

/-- One base-two multiplicity block in the exact pair expansion. -/
noncomputable def gmHalfDifferenceDyadicPairBlock
    (W : Finset ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  ∑ p ∈ (W ×ˢ W).filter (fun p ↦
      Nat.log 2 (gmHalfDifferenceMultiplicity W (gmHalfDifferenceBin p)) = j),
    gmHalfDifferencePairPhase p x

/-- Every pair is assigned to an index in `0, ..., log₂ |W|`. -/
theorem gmHalfDifferencePairScale_mem_range
    (W : Finset ℝ) (hSep : IsSeparated 1 W) (p : ℝ × ℝ) :
    Nat.log 2 (gmHalfDifferenceMultiplicity W (gmHalfDifferenceBin p)) ∈
      Finset.range (Nat.log 2 W.card + 1) := by
  rw [Finset.mem_range]
  apply Nat.lt_succ_of_le
  exact log_gmHalfDifferenceMultiplicity_le_log_card W hSep
    (gmHalfDifferenceBin p)

/-- Exact source decomposition before Cauchy--Schwarz: no pair is dropped
and no dyadic multiplicity class is duplicated. -/
theorem norm_gmRPhase_sq_eq_sum_halfDifferenceDyadicPairBlock
    (W : Finset ℝ) (hSep : IsSeparated 1 W) (x : ℝ) :
    ((‖gmRPhase W x‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
        gmHalfDifferenceDyadicPairBlock W j x := by
  let P := W ×ˢ W
  let scale : ℝ × ℝ → ℕ := fun p ↦
    Nat.log 2 (gmHalfDifferenceMultiplicity W (gmHalfDifferenceBin p))
  let phase : ℝ × ℝ → ℂ := fun p ↦ gmHalfDifferencePairPhase p x
  have hmaps : ∀ p ∈ P, scale p ∈ Finset.range (Nat.log 2 W.card + 1) := by
    intro p hp
    exact gmHalfDifferencePairScale_mem_range W hSep p
  calc
    ((‖gmRPhase W x‖ ^ 2 : ℝ) : ℂ) =
        ∑ p ∈ P, phase p := by
      rw [norm_gmRPhase_sq_expand]
      simp only [P, phase, gmHalfDifferencePairPhase, Finset.sum_product]
    _ = ∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
          ∑ p ∈ P with scale p = j, phase p := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps phase).symm
    _ = ∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
          gmHalfDifferenceDyadicPairBlock W j x := by
      apply Finset.sum_congr rfl
      intro j hj
      rfl

/-- Cauchy--Schwarz across the exact finite dyadic decomposition.  The
factor `log₂ |W| + 1` is kept explicit for the later epsilon budget. -/
theorem norm_gmRPhase_fourth_le_dyadicPairBlocks
    (W : Finset ℝ) (hSep : IsSeparated 1 W) (x : ℝ) :
    ‖gmRPhase W x‖ ^ 4 ≤
      ((Nat.log 2 W.card + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
          ‖gmHalfDifferenceDyadicPairBlock W j x‖ ^ 2 := by
  have hdecomp :=
    norm_gmRPhase_sq_eq_sum_halfDifferenceDyadicPairBlock W hSep x
  have hnorm : ‖gmRPhase W x‖ ^ 2 =
      ‖∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
        gmHalfDifferenceDyadicPairBlock W j x‖ := by
    rw [← hdecomp]
    simp
  calc
    ‖gmRPhase W x‖ ^ 4 = (‖gmRPhase W x‖ ^ 2) ^ 2 := by ring
    _ = ‖∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
          gmHalfDifferenceDyadicPairBlock W j x‖ ^ 2 := by rw [hnorm]
    _ ≤ ((Finset.range (Nat.log 2 W.card + 1)).card : ℝ) *
          ∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
            ‖gmHalfDifferenceDyadicPairBlock W j x‖ ^ 2 :=
      norm_sum_sq_le_card_mul_sum_norm_sq _ _
    _ = ((Nat.log 2 W.card + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
            ‖gmHalfDifferenceDyadicPairBlock W j x‖ ^ 2 := by simp

/-- The phase carried by the complete fiber of one integer difference bin. -/
noncomputable def gmHalfDifferenceFiberPhase
    (W : Finset ℝ) (u : ℤ) (x : ℝ) : ℂ :=
  ∑ p ∈ (W ×ˢ W).filter (fun p ↦ gmHalfDifferenceBin p = u),
    gmHalfDifferencePairPhase p x

/-- The dyadic pair block is exactly the sum of its occupied integer-bin
fibers.  This is the formal counterpart of the inner two sums defining
`U_B` in Guth--Maynard Lemma 11.6. -/
theorem gmHalfDifferenceDyadicPairBlock_eq_sum_fibers
    (W : Finset ℝ) (j : ℕ) (x : ℝ) :
    gmHalfDifferenceDyadicPairBlock W j x =
      ∑ u ∈ gmHalfDifferenceDyadicClass W j,
        gmHalfDifferenceFiberPhase W u x := by
  let P := W ×ˢ W
  let Pj := P.filter (fun p ↦
    Nat.log 2 (gmHalfDifferenceMultiplicity W (gmHalfDifferenceBin p)) = j)
  let phase : ℝ × ℝ → ℂ := fun p ↦ gmHalfDifferencePairPhase p x
  have hmaps : ∀ p ∈ Pj,
      gmHalfDifferenceBin p ∈ gmHalfDifferenceDyadicClass W j := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hu : gmHalfDifferenceBin p ∈ P.image gmHalfDifferenceBin :=
      Finset.mem_image.mpr ⟨p, hp'.1, rfl⟩
    have hmpos : 0 <
        gmHalfDifferenceMultiplicity W (gmHalfDifferenceBin p) :=
      gmHalfDifferenceMultiplicity_pos_of_mem hu
    rw [mem_gmHalfDifferenceDyadicClass]
    refine ⟨hu, ?_, ?_⟩
    · rw [← hp'.2]
      exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hmpos)
    · rw [← hp'.2]
      simpa [Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (by norm_num : 1 < 2)
          (gmHalfDifferenceMultiplicity W (gmHalfDifferenceBin p))
  have hfiber (u : ℤ) (hu : u ∈ gmHalfDifferenceDyadicClass W j) :
      ∑ p ∈ Pj with gmHalfDifferenceBin p = u, phase p =
        gmHalfDifferenceFiberPhase W u x := by
    apply Finset.sum_congr
    · ext p
      simp only [Pj, P, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp, hscale⟩, hbin⟩
        exact ⟨hp, hbin⟩
      · rintro ⟨hp, hbin⟩
        have hclass := (mem_gmHalfDifferenceDyadicClass.mp hu).2
        have hmpos : 0 < gmHalfDifferenceMultiplicity W u :=
          gmHalfDifferenceMultiplicity_pos_of_mem
            (mem_gmHalfDifferenceDyadicClass.mp hu).1
        have hlog : Nat.log 2 (gmHalfDifferenceMultiplicity W u) = j := by
          apply Nat.le_antisymm
          · have hlt :=
              Nat.log_lt_of_lt_pow (Nat.ne_of_gt hmpos) hclass.2
            omega
          · exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) hclass.1
        exact ⟨⟨hp, by simpa only [hbin] using hlog⟩, hbin⟩
    · intro p hp
      rfl
  change (∑ p ∈ Pj, phase p) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps phase]
  apply Finset.sum_congr rfl
  intro u hu
  exact hfiber u hu

/-- Exact two-variable fiber decomposition of a dyadic pair block.  It is
stated for an arbitrary summand so that the source-polynomial moment can
be grouped by the two integer difference labels without changing any
phase or coefficient. -/
theorem sum_gmHalfDifferenceDyadicPairs_eq_sum_fibers
    (W : Finset ℝ) (j : ℕ) (F : (ℝ × ℝ) → (ℝ × ℝ) → ℝ) :
    (∑ p ∈ (W ×ˢ W).filter (fun p ↦
        Nat.log 2 (gmHalfDifferenceMultiplicity W
          (gmHalfDifferenceBin p)) = j),
      ∑ q ∈ (W ×ˢ W).filter (fun q ↦
        Nat.log 2 (gmHalfDifferenceMultiplicity W
          (gmHalfDifferenceBin q)) = j), F p q) =
      ∑ u ∈ gmHalfDifferenceDyadicClass W j,
        ∑ v ∈ gmHalfDifferenceDyadicClass W j,
          ∑ p ∈ (W ×ˢ W).filter (fun p ↦
              Nat.log 2 (gmHalfDifferenceMultiplicity W
                (gmHalfDifferenceBin p)) = j) with
                gmHalfDifferenceBin p = u,
            ∑ q ∈ (W ×ˢ W).filter (fun q ↦
                Nat.log 2 (gmHalfDifferenceMultiplicity W
                  (gmHalfDifferenceBin q)) = j) with
                  gmHalfDifferenceBin q = v,
              F p q := by
  let Pj := (W ×ˢ W).filter (fun p ↦
    Nat.log 2 (gmHalfDifferenceMultiplicity W
      (gmHalfDifferenceBin p)) = j)
  have hmaps : ∀ p ∈ Pj,
      gmHalfDifferenceBin p ∈ gmHalfDifferenceDyadicClass W j := by
    intro p hp
    exact gmHalfDifferenceBin_mem_dyadicClass_of_pair hp
  calc
    (∑ p ∈ Pj, ∑ q ∈ Pj, F p q) =
        ∑ u ∈ gmHalfDifferenceDyadicClass W j,
          ∑ p ∈ Pj with gmHalfDifferenceBin p = u,
            ∑ q ∈ Pj, F p q := by
      rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    _ = ∑ u ∈ gmHalfDifferenceDyadicClass W j,
          ∑ v ∈ gmHalfDifferenceDyadicClass W j,
            ∑ p ∈ Pj with gmHalfDifferenceBin p = u,
              ∑ q ∈ Pj with gmHalfDifferenceBin q = v, F p q := by
      apply Finset.sum_congr rfl
      intro u hu
      calc
        (∑ p ∈ Pj with gmHalfDifferenceBin p = u,
            ∑ q ∈ Pj, F p q) =
            ∑ p ∈ Pj with gmHalfDifferenceBin p = u,
              ∑ v ∈ gmHalfDifferenceDyadicClass W j,
                ∑ q ∈ Pj with gmHalfDifferenceBin q = v, F p q := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [← Finset.sum_fiberwise_of_maps_to hmaps]
        _ = _ := by rw [Finset.sum_comm]

/-- A fiber contains exactly its multiplicity many unit complex phases. -/
theorem norm_gmHalfDifferenceFiberPhase_le_multiplicity
    (W : Finset ℝ) (u : ℤ) (x : ℝ) :
    ‖gmHalfDifferenceFiberPhase W u x‖ ≤
      gmHalfDifferenceMultiplicity W u := by
  unfold gmHalfDifferenceFiberPhase gmHalfDifferenceMultiplicity
  calc
    ‖∑ p ∈ (W ×ˢ W).filter (fun p ↦ gmHalfDifferenceBin p = u),
        gmHalfDifferencePairPhase p x‖ ≤
        ∑ p ∈ (W ×ˢ W).filter (fun p ↦ gmHalfDifferenceBin p = u),
          ‖gmHalfDifferencePairPhase p x‖ := norm_sum_le _ _
    _ = ((W ×ˢ W).filter (fun p ↦ gmHalfDifferenceBin p = u)).card := by
      have hunit (p : ℝ × ℝ) : ‖gmHalfDifferencePairPhase p x‖ = 1 := by
        rw [gmHalfDifferencePairPhase, Complex.norm_exp]
        simp
      simp_rw [hunit]
      simp
    _ = _ := by norm_cast

/-- Uniform source bound for every fiber in `U_{2^j}`. -/
theorem norm_gmHalfDifferenceFiberPhase_lt_twoPow_succ
    {W : Finset ℝ} {j : ℕ} {u : ℤ}
    (hu : u ∈ gmHalfDifferenceDyadicClass W j) (x : ℝ) :
    ‖gmHalfDifferenceFiberPhase W u x‖ < (2 ^ (j + 1) : ℕ) := by
  have hmult := (mem_gmHalfDifferenceDyadicClass.mp hu).2.2
  exact (norm_gmHalfDifferenceFiberPhase_le_multiplicity W u x).trans_lt
    (by exact_mod_cast hmult)

/-! ## Translation of the dyadic difference classes for Heath--Brown -/

/-- Translate an integer difference class into a nonnegative real interval.
Differences are unchanged by this translation, which is exactly what the
Heath--Brown mean-square theorem uses. -/
noncomputable def gmHalfDifferenceTranslatedClass
    (T : ℝ) (W : Finset ℝ) (j : ℕ) : Finset ℝ :=
  (gmHalfDifferenceDyadicClass W j).image fun u : ℤ =>
    (u : ℝ) + (2 * T + 1)

theorem card_gmHalfDifferenceTranslatedClass
    (T : ℝ) (W : Finset ℝ) (j : ℕ) :
    (gmHalfDifferenceTranslatedClass T W j).card =
      (gmHalfDifferenceDyadicClass W j).card := by
  unfold gmHalfDifferenceTranslatedClass
  rw [Finset.card_image_of_injective]
  intro u v huv
  have hcast : (u : ℝ) = (v : ℝ) := by linarith
  exact_mod_cast hcast

theorem gmHalfDifferenceTranslatedClass_separated
    (T : ℝ) (W : Finset ℝ) (j : ℕ) :
    IsSeparated 1 (gmHalfDifferenceTranslatedClass T W j) := by
  intro x hx y hy hxy
  rw [gmHalfDifferenceTranslatedClass, Finset.mem_image] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rw [Real.dist_eq]
  have huv : u ≠ v := by
    intro huv
    apply hxy
    rw [huv]
  have hInt : (1 : ℤ) ≤ |u - v| := by
    have hpos : (0 : ℤ) < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
    omega
  have hCast : (1 : ℝ) ≤ |(u : ℝ) - (v : ℝ)| := by
    exact_mod_cast hInt
  simpa only [add_sub_add_right_eq_sub] using hCast

/-- Every occupied half-difference bin lies in the interval forced by the
original base interval. -/
theorem gmHalfDifferenceBin_bounds_of_base
    {T : ℝ} {W : Finset ℝ} (hBase : InBaseInterval T W)
    {u : ℤ} (hu : u ∈ (W ×ˢ W).image gmHalfDifferenceBin) :
    -(T + 1) ≤ (u : ℝ) ∧ (u : ℝ) ≤ T + 1 := by
  rw [Finset.mem_image] at hu
  obtain ⟨p, hp, rfl⟩ := hu
  rw [Finset.mem_product] at hp
  have hp1 := hBase p.1 hp.1
  have hp2 := hBase p.2 hp.2
  rw [Set.mem_Icc] at hp1 hp2
  have hlower := Int.lt_floor_add_one ((p.1 - p.2) + 1 / 2)
  have hupper := Int.floor_le ((p.1 - p.2) + 1 / 2)
  unfold gmHalfDifferenceBin
  constructor <;> linarith

/-- The translated dyadic class lies in one explicit interval of length
`4T+2`, so the source Heath--Brown theorem applies without any hidden
recentering convention. -/
theorem gmHalfDifferenceTranslatedClass_inBase
    {T : ℝ} {W : Finset ℝ} (hBase : InBaseInterval T W) (j : ℕ) :
    InBaseInterval (4 * T + 2)
      (gmHalfDifferenceTranslatedClass T W j) := by
  intro x hx
  rw [gmHalfDifferenceTranslatedClass, Finset.mem_image] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  have huImage := (mem_gmHalfDifferenceDyadicClass.mp hu).1
  have hb := gmHalfDifferenceBin_bounds_of_base hBase huImage
  have hTnonneg : 0 ≤ T := by
    rw [Finset.mem_image] at huImage
    obtain ⟨p, hp, hpbin⟩ := huImage
    have hpMem := (Finset.mem_product.mp hp).1
    exact (hBase p.1 hpMem).1.trans (hBase p.1 hpMem).2
  rw [Set.mem_Icc]
  constructor <;> linarith

/-- Translation cancels in every two-ordinate difference. -/
theorem gmHalfDifferenceTranslated_sub
    (T : ℝ) (u v : ℤ) :
    ((u : ℝ) + (2 * T + 1)) - ((v : ℝ) + (2 * T + 1)) =
      (u : ℝ) - v := by
  ring

/-- Heath--Brown's native theorem applied to one translated multiplicity
class, with an arbitrary common frequency shift absorbed into unit-modulus
coefficients.  This is the analytic input in Guth--Maynard Lemma 11.6. -/
theorem gmHalfDifferenceTranslatedMeanSquare_native :
    ∀ ε : ℝ, 0 < ε →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ) (j : ℕ) (s : ℝ),
          0 < M → T₀ ≤ T → IsSeparated 1 W → InBaseInterval T W →
          (∑ x ∈ gmHalfDifferenceTranslatedClass T W j,
            ∑ y ∈ gmHalfDifferenceTranslatedClass T W j,
              ‖sourceDirichletPoly M
                (fun n => (n : ℂ) ^ (((s : ℂ)) * I)) (x - y)‖ ^ 2) ≤
            C * (4 * T + 2) ^ ε *
              ((((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 * M) +
                (((gmHalfDifferenceDyadicClass W j).card : ℝ) * M ^ 2) +
                (((gmHalfDifferenceDyadicClass W j).card : ℝ) ^
                    (5 / 4 : ℝ) *
                  (4 * T + 2) ^ (1 / 2 : ℝ) * M)) := by
  intro ε hε
  obtain ⟨C, T₀, hC, hT₀, hHB⟩ :=
    heathBrownDifferenceSetMeanSquare_native ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T W j s hM hT hSep hBase
  have hTnonneg : 0 ≤ T := hT₀.trans hT |>.trans' (by norm_num)
  have hHeight : T₀ ≤ 4 * T + 2 := by linarith
  have hCoeff : ∀ n ∈ dyadicInterval M,
      ‖(n : ℂ) ^ (((s : ℂ)) * I)‖ ≤ 1 := by
    intro n hn
    have hnpos : 0 < n := hM.trans (Finset.mem_Ioc.mp hn).1
    rw [Complex.norm_natCast_cpow_of_pos hnpos]
    simp
  have hApplied := hHB M (4 * T + 2)
    (gmHalfDifferenceTranslatedClass T W j)
    (fun n => (n : ℂ) ^ (((s : ℂ)) * I)) hM hHeight
    (gmHalfDifferenceTranslatedClass_separated T W j)
    (gmHalfDifferenceTranslatedClass_inBase hBase j) hCoeff
  simpa only [card_gmHalfDifferenceTranslatedClass] using hApplied

/-- Exact reindexing of the translated Heath--Brown moment back to the
integer bin labels. -/
theorem sum_gmHalfDifferenceTranslatedClass_eq_bins
    (M : ℕ) (T : ℝ) (W : Finset ℝ) (j : ℕ) (a : ℕ → ℂ) :
    (∑ x ∈ gmHalfDifferenceTranslatedClass T W j,
      ∑ y ∈ gmHalfDifferenceTranslatedClass T W j,
        ‖sourceDirichletPoly M a (x - y)‖ ^ 2) =
      ∑ u ∈ gmHalfDifferenceDyadicClass W j,
        ∑ v ∈ gmHalfDifferenceDyadicClass W j,
          ‖sourceDirichletPoly M a ((u : ℝ) - v)‖ ^ 2 := by
  unfold gmHalfDifferenceTranslatedClass
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro v hv
      rw [gmHalfDifferenceTranslated_sub]
    · intro v₁ hv₁ v₂ hv₂ heq
      have hcast : (v₁ : ℝ) = (v₂ : ℝ) := by linarith
      exact_mod_cast hcast
  · intro u₁ hu₁ u₂ hu₂ heq
    have hcast : (u₁ : ℝ) = (u₂ : ℝ) := by linarith
    exact_mod_cast hcast

/-- A common real frequency shift is exactly a unit-modulus coefficient
twist. -/
theorem sourceDirichletPoly_shift_eq_twisted
    {M : ℕ} (hM : 0 < M) (s u : ℝ) :
    sourceDirichletPoly M (fun n => (n : ℂ) ^ (((s : ℂ)) * I)) u =
      sourceDirichletPoly M (fun _ => (1 : ℂ)) (u + s) := by
  unfold sourceDirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := hM.trans (Finset.mem_Ioc.mp hn).1
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  rw [one_mul, ← Complex.cpow_add _ _ hnne]
  congr 1
  push_cast
  ring

/-- Integer-bin form of the native Heath--Brown estimate, uniformly in the
bounded displacement appearing in Lemma 11.3. -/
theorem gmHalfDifferenceBinShiftedMeanSquare_native :
    ∀ ε : ℝ, 0 < ε →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ) (j : ℕ) (s : ℝ),
          0 < M → T₀ ≤ T → IsSeparated 1 W → InBaseInterval T W →
          (∑ u ∈ gmHalfDifferenceDyadicClass W j,
            ∑ v ∈ gmHalfDifferenceDyadicClass W j,
              ‖sourceDirichletPoly M (fun _ => (1 : ℂ))
                ((u : ℝ) - v + s)‖ ^ 2) ≤
            C * (4 * T + 2) ^ ε *
              ((((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 * M) +
                (((gmHalfDifferenceDyadicClass W j).card : ℝ) * M ^ 2) +
                (((gmHalfDifferenceDyadicClass W j).card : ℝ) ^
                    (5 / 4 : ℝ) *
                  (4 * T + 2) ^ (1 / 2 : ℝ) * M)) := by
  intro ε hε
  obtain ⟨C, T₀, hC, hT₀, hHB⟩ :=
    gmHalfDifferenceTranslatedMeanSquare_native ε hε
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T W j s hM hT hSep hBase
  have hApplied := hHB M T W j s hM hT hSep hBase
  rw [sum_gmHalfDifferenceTranslatedClass_eq_bins] at hApplied
  simpa only [sourceDirichletPoly_shift_eq_twisted hM] using hApplied

/-- Exact ordered-pair expansion of a coefficient-one source polynomial.
This fixes the sign convention needed when the dyadic pair blocks are
summed over numerator/denominator pairs. -/
theorem ofReal_norm_sourceDirichletPoly_one_sq_expand
    {M : ℕ} (hM : 0 < M) (a : ℝ) :
    ((‖sourceDirichletPoly M (fun _ => (1 : ℂ)) a‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        Complex.exp ((((a * (Real.log m - Real.log n) : ℝ) : ℂ) * I)) := by
  rw [sourceDirichletPoly]
  simp only [one_mul]
  rw [ofReal_norm_finset_sum_sq_expand]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hnpos : 0 < n := hM.trans (Finset.mem_Ioc.mp hn).1
  have hmpos : 0 < m := hM.trans (Finset.mem_Ioc.mp hm).1
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hmne : (m : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'
  rw [Complex.cpow_def_of_ne_zero hnne, Complex.cpow_def_of_ne_zero hmne]
  have hnCast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  have hmCast : (m : ℂ) = ((m : ℝ) : ℂ) := by norm_num
  rw [hnCast, hmCast,
    ← Complex.ofReal_log (by exact_mod_cast hnpos.le),
    ← Complex.ofReal_log (by exact_mod_cast hmpos.le),
    Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I]
  push_cast
  ring

/-- Ordered-pair expansion of one dyadic difference block. -/
theorem ofReal_norm_gmHalfDifferenceDyadicPairBlock_sq_expand
    (W : Finset ℝ) (j : ℕ) (x : ℝ) :
    ((‖gmHalfDifferenceDyadicPairBlock W j x‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ (W ×ˢ W).filter (fun p ↦
          Nat.log 2 (gmHalfDifferenceMultiplicity W
            (gmHalfDifferenceBin p)) = j),
        ∑ q ∈ (W ×ˢ W).filter (fun q ↦
          Nat.log 2 (gmHalfDifferenceMultiplicity W
            (gmHalfDifferenceBin q)) = j),
          Complex.exp (((((q.1 - q.2) - (p.1 - p.2)) * x : ℝ) : ℂ) * I) := by
  unfold gmHalfDifferenceDyadicPairBlock
  rw [ofReal_norm_finset_sum_sq_expand]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  unfold gmHalfDifferencePairPhase
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I]
  push_cast
  ring

/-- The block phase and the coefficient-one source-polynomial phase are
identical after substituting `x = log (n / m)`.  Keeping this as an exact
identity prevents a sign convention from being hidden in the Section 11
moment comparison. -/
theorem gmHalfDifferencePairPhase_log_div_eq_sourcePhase
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (p q : ℝ × ℝ) :
    Complex.exp
        (((((q.1 - q.2) - (p.1 - p.2)) * Real.log ((n : ℝ) / m) : ℝ) : ℂ) * I) =
      Complex.exp
        (((((p.1 - p.2) - (q.1 - q.2)) *
          (Real.log m - Real.log n) : ℝ) : ℂ) * I) := by
  rw [Real.log_div (by positivity : (n : ℝ) ≠ 0) (by positivity : (m : ℝ) ≠ 0)]
  congr 1
  push_cast
  ring

theorem ofReal_norm_sourceDirichletPoly_one_sq_expand'
    {M : ℕ} (hM : 0 < M) (a : ℝ) :
    ((‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ)) a‖ : ℂ) ^ 2) =
      ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        Complex.exp ((((a * (Real.log m - Real.log n) : ℝ) : ℂ) * I)) := by
  rw [← ofReal_norm_sourceDirichletPoly_one_sq_expand hM a]
  push_cast
  rfl

theorem ofReal_norm_gmHalfDifferenceDyadicPairBlock_sq_expand'
    (W : Finset ℝ) (j : ℕ) (x : ℝ) :
    ((‖gmHalfDifferenceDyadicPairBlock W j x‖ : ℂ) ^ 2) =
      ∑ p ∈ (W ×ˢ W).filter (fun p ↦
          Nat.log 2 (gmHalfDifferenceMultiplicity W
            (gmHalfDifferenceBin p)) = j),
        ∑ q ∈ (W ×ˢ W).filter (fun q ↦
          Nat.log 2 (gmHalfDifferenceMultiplicity W
            (gmHalfDifferenceBin q)) = j),
          Complex.exp (((((q.1 - q.2) - (p.1 - p.2)) * x : ℝ) : ℂ) * I) := by
  rw [← ofReal_norm_gmHalfDifferenceDyadicPairBlock_sq_expand W j x]
  push_cast
  rfl

theorem sum_four_comm_middle_to_front
    {α β γ δ R : Type*} [AddCommMonoid R]
    (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → R) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d) =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  calc
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D, f a b c d := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ D, f a b c d := by
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]

/-- Exact discrete-moment identity for one multiplicity block.  This is
the finite bridge from the fourth moment of the `R`-sum to the source
Dirichlet-polynomial moment to which Lemma 11.3 and Heath--Brown apply. -/
theorem sum_norm_gmHalfDifferenceDyadicPairBlock_sq_eq_sourceMoment
    (M : ℕ) (hM : 0 < M) (W : Finset ℝ) (j : ℕ) :
    (∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        ‖gmHalfDifferenceDyadicPairBlock W j
          (Real.log ((n : ℝ) / m))‖ ^ 2) =
      ∑ p ∈ (W ×ˢ W).filter (fun p ↦
          Nat.log 2 (gmHalfDifferenceMultiplicity W
            (gmHalfDifferenceBin p)) = j),
        ∑ q ∈ (W ×ˢ W).filter (fun q ↦
          Nat.log 2 (gmHalfDifferenceMultiplicity W
            (gmHalfDifferenceBin q)) = j),
          ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
            ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_norm_gmHalfDifferenceDyadicPairBlock_sq_expand',
    ofReal_norm_sourceDirichletPoly_one_sq_expand' hM]
  rw [sum_four_comm_middle_to_front]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro n hnMem
  apply Finset.sum_congr rfl
  intro m hmMem
  exact gmHalfDifferencePairPhase_log_div_eq_sourcePhase
    (hM.trans (Finset.mem_Ioc.mp hnMem).1)
    (hM.trans (Finset.mem_Ioc.mp hmMem).1) p q

/-- Pointwise Lemma 11.3 bound for two pairs in prescribed integer
difference bins.  The displacement is derived from the actual pairs and
then removed into the common interval; it is not a theorem parameter. -/
theorem sourceDirichletPoly_pairDifference_sq_le_commonInterval
    {A ε T : ℝ} {M : ℕ}
    (hA : 0 < A) (hε : 0 < ε) (hT : 1 ≤ T)
    (hM : 0 < M) (hMT : (M : ℝ) ≤ T)
    {p q : ℝ × ℝ} {u v : ℤ}
    (hp : gmHalfDifferenceBin p = u)
    (hq : gmHalfDifferenceBin q = v) :
    ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
        ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2 ≤
      2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
          (2 * gmSection11CommonRadius (gmReflectionHeight T ε)) *
          (∫ t : ℝ in Set.Icc
              (-(gmSection11CommonRadius (gmReflectionHeight T ε)))
              (gmSection11CommonRadius (gmReflectionHeight T ε)),
            ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
              (((u : ℝ) - v) + t)‖ ^ 2) +
        2 * (gmAffineLocalBumpFourierTailConstant
            (gmReflectionDecayOrder A ε)
            (gmReflectionDecayOrder_two_le A ε) / T ^ A) ^ 2 := by
  let s := ((p.1 - p.2) - (gmHalfDifferenceBin p : ℝ)) -
    ((q.1 - q.2) - (gmHalfDifferenceBin q : ℝ))
  have hdisp := gmHalfDifference_pair_displacement p q
  have hs : |s| ≤ 1 := hdisp.1
  have heq : (p.1 - p.2) - (q.1 - q.2) = ((u : ℝ) - v) + s := by
    simpa only [s, hp, hq] using hdisp.2
  rw [heq]
  exact sourceDirichletPoly_norm_sq_le_commonInterval_add_error
    hA hε hT hM hMT (fun _ ↦ (1 : ℂ)) ((u : ℝ) - v) s hs
    (by intro n hn; simp)

/-- Common-interval majorant attached to one ordered pair of integer
difference bins in Lemma 11.6. -/
noncomputable def gmSection11PairMajorant
    (A ε T : ℝ) (M : ℕ) (u v : ℤ) : ℝ :=
  2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
      (2 * gmSection11CommonRadius (gmReflectionHeight T ε)) *
      (∫ t : ℝ in Set.Icc
          (-(gmSection11CommonRadius (gmReflectionHeight T ε)))
          (gmSection11CommonRadius (gmReflectionHeight T ε)),
        ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
          (((u : ℝ) - v) + t)‖ ^ 2) +
    2 * (gmAffineLocalBumpFourierTailConstant
        (gmReflectionDecayOrder A ε)
        (gmReflectionDecayOrder_two_le A ε) / T ^ A) ^ 2

theorem gmSection11PairMajorant_nonneg
    {A ε T : ℝ} {M : ℕ} {u v : ℤ} (hT : 0 ≤ T) :
    0 ≤ gmSection11PairMajorant A ε T M u v := by
  unfold gmSection11PairMajorant
  have hIntegral : 0 ≤
      ∫ t : ℝ in Set.Icc
          (-(gmSection11CommonRadius (gmReflectionHeight T ε)))
          (gmSection11CommonRadius (gmReflectionHeight T ε)),
        ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
          (((u : ℝ) - v) + t)‖ ^ 2 :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  have hHeight : 0 ≤ gmReflectionHeight T ε := by
    unfold gmReflectionHeight
    exact Real.rpow_nonneg hT _
  have hRadius : 0 ≤ gmSection11CommonRadius (gmReflectionHeight T ε) := by
    unfold gmSection11CommonRadius
    positivity
  have hCoeff : 0 ≤
      2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
        (2 * gmSection11CommonRadius (gmReflectionHeight T ε)) := by
    positivity
  exact add_nonneg (mul_nonneg hCoeff hIntegral) (by positivity)

theorem sourceDirichletPoly_pairDifference_sq_le_majorant
    {A ε T : ℝ} {M : ℕ}
    (hA : 0 < A) (hε : 0 < ε) (hT : 1 ≤ T)
    (hM : 0 < M) (hMT : (M : ℝ) ≤ T)
    {p q : ℝ × ℝ} {u v : ℤ}
    (hp : gmHalfDifferenceBin p = u)
    (hq : gmHalfDifferenceBin q = v) :
    ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
        ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2 ≤
      gmSection11PairMajorant A ε T M u v := by
  exact sourceDirichletPoly_pairDifference_sq_le_commonInterval
    hA hε hT hM hMT hp hq

/-- Sum over all actual pairs in one multiplicity block, bounded by the
common-bin majorants with the exact `2^(j+1)` fiber loss. -/
theorem sum_sourceMoment_dyadicPairs_le_binMajorants
    {A ε T : ℝ} {M : ℕ}
    (hA : 0 < A) (hε : 0 < ε) (hT : 1 ≤ T)
    (hM : 0 < M) (hMT : (M : ℝ) ≤ T)
    (W : Finset ℝ) (j : ℕ) :
    (∑ p ∈ (W ×ˢ W).filter (fun p ↦
        Nat.log 2 (gmHalfDifferenceMultiplicity W
          (gmHalfDifferenceBin p)) = j),
      ∑ q ∈ (W ×ˢ W).filter (fun q ↦
        Nat.log 2 (gmHalfDifferenceMultiplicity W
          (gmHalfDifferenceBin q)) = j),
        ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
          ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2) ≤
      ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
        ∑ u ∈ gmHalfDifferenceDyadicClass W j,
          ∑ v ∈ gmHalfDifferenceDyadicClass W j,
            gmSection11PairMajorant A ε T M u v := by
  let Pj := (W ×ˢ W).filter (fun p ↦
    Nat.log 2 (gmHalfDifferenceMultiplicity W
      (gmHalfDifferenceBin p)) = j)
  let U := gmHalfDifferenceDyadicClass W j
  rw [sum_gmHalfDifferenceDyadicPairs_eq_sum_fibers]
  calc
    (∑ u ∈ U, ∑ v ∈ U,
        ∑ p ∈ Pj with gmHalfDifferenceBin p = u,
          ∑ q ∈ Pj with gmHalfDifferenceBin q = v,
            ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
              ((p.1 - p.2) - (q.1 - q.2))‖ ^ 2) ≤
      ∑ u ∈ U, ∑ v ∈ U,
        ∑ _p ∈ Pj with gmHalfDifferenceBin _p = u,
          ∑ _q ∈ Pj with gmHalfDifferenceBin _q = v,
            gmSection11PairMajorant A ε T M u v := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      exact sourceDirichletPoly_pairDifference_sq_le_majorant
        hA hε hT hM hMT (Finset.mem_filter.mp hp).2
          (Finset.mem_filter.mp hq).2
    _ = ∑ u ∈ U, ∑ v ∈ U,
        ((((Pj.filter fun p ↦ gmHalfDifferenceBin p = u).card : ℕ) : ℝ) *
          (((Pj.filter fun q ↦ gmHalfDifferenceBin q = v).card : ℕ) : ℝ)) *
            gmSection11PairMajorant A ε T M u v := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      simp
      ring
    _ ≤ ∑ u ∈ U, ∑ v ∈ U,
        ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
          gmSection11PairMajorant A ε T M u v := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      apply mul_le_mul_of_nonneg_right
      · have huCard := card_gmHalfDifferenceDyadicPairFiber_lt
          (W := W) (j := j) (u := u) hu
        have hvCard := card_gmHalfDifferenceDyadicPairFiber_lt
          (W := W) (j := j) (u := v) hv
        have huReal : ((Pj.filter fun p ↦ gmHalfDifferenceBin p = u).card : ℝ) ≤
            ((2 ^ (j + 1) : ℕ) : ℝ) := by
          exact_mod_cast huCard.le
        have hvReal : ((Pj.filter fun p ↦ gmHalfDifferenceBin p = v).card : ℝ) ≤
            ((2 ^ (j + 1) : ℕ) : ℝ) := by
          exact_mod_cast hvCard.le
        nlinarith
      · exact gmSection11PairMajorant_nonneg (zero_le_one.trans hT)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]

/-- Finite Fubini identity for the common-bin source moment. -/
theorem integral_sum_gmHalfDifferenceBin_sourceMoment
    {M : ℕ} (hM : 0 < M) (W : Finset ℝ) (j : ℕ) (L : ℝ) :
    (∫ t : ℝ in Set.Icc (-L) L,
        ∑ u ∈ gmHalfDifferenceDyadicClass W j,
          ∑ v ∈ gmHalfDifferenceDyadicClass W j,
            ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
              (((u : ℝ) - v) + t)‖ ^ 2) =
      ∑ u ∈ gmHalfDifferenceDyadicClass W j,
        ∑ v ∈ gmHalfDifferenceDyadicClass W j,
          ∫ t : ℝ in Set.Icc (-L) L,
            ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
              (((u : ℝ) - v) + t)‖ ^ 2 := by
  let U := gmHalfDifferenceDyadicClass W j
  have hInt (u v : ℤ) : IntegrableOn (fun t : ℝ =>
      ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
        (((u : ℝ) - v) + t)‖ ^ 2) (Set.Icc (-L) L) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    apply Continuous.pow
    apply Continuous.norm
    unfold sourceDirichletPoly
    apply continuous_finsetSum
    intro n hn
    apply Continuous.const_mul
    apply Continuous.const_cpow
    · fun_prop
    · left
      exact_mod_cast (hM.trans (Finset.mem_Ioc.mp hn).1).ne'
  change (∫ t : ℝ in Set.Icc (-L) L,
      ∑ u ∈ U, ∑ v ∈ U,
        ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
          (((u : ℝ) - v) + t)‖ ^ 2) = _
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [MeasureTheory.integral_finsetSum]
    intro v hv
    exact hInt u v
  · intro u hu
    exact integrable_finsetSum U (fun v hv => hInt u v)

/-- Heath--Brown integrated over the common displacement interval.  The
shift is now genuinely common at each integration point, so this theorem
does not make the invalid varying-shift substitution that the preceding
common-interval bridge was designed to avoid. -/
theorem gmHalfDifferenceBinCommonIntervalMeanSquare_native :
    ∀ η : ℝ, 0 < η →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ) (j : ℕ) (L : ℝ),
          0 < M → T₀ ≤ T → IsSeparated 1 W → InBaseInterval T W →
          0 ≤ L →
          (∑ u ∈ gmHalfDifferenceDyadicClass W j,
            ∑ v ∈ gmHalfDifferenceDyadicClass W j,
              ∫ t : ℝ in Set.Icc (-L) L,
                ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
                  (((u : ℝ) - v) + t)‖ ^ 2) ≤
            (2 * L) * C * (4 * T + 2) ^ η *
              ((((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 * M) +
                (((gmHalfDifferenceDyadicClass W j).card : ℝ) * M ^ 2) +
                (((gmHalfDifferenceDyadicClass W j).card : ℝ) ^
                    (5 / 4 : ℝ) *
                  (4 * T + 2) ^ (1 / 2 : ℝ) * M)) := by
  intro η hη
  obtain ⟨C, T₀, hC, hT₀, hHB⟩ :=
    gmHalfDifferenceBinShiftedMeanSquare_native η hη
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T W j L hM hT hSep hBase hL
  let U := gmHalfDifferenceDyadicClass W j
  let B : ℝ := C * (4 * T + 2) ^ η *
    ((((U.card : ℝ) ^ 2 * M) + ((U.card : ℝ) * M ^ 2) +
      ((U.card : ℝ) ^ (5 / 4 : ℝ) *
        (4 * T + 2) ^ (1 / 2 : ℝ) * M)))
  have hPoint (t : ℝ) :
      (∑ u ∈ U, ∑ v ∈ U,
        ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
          (((u : ℝ) - v) + t)‖ ^ 2) ≤ B := by
    simpa only [U, B, add_assoc] using
      hHB M T W j t hM hT hSep hBase
  have hSingleInt (u v : ℤ) : IntegrableOn (fun t : ℝ =>
      ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
        (((u : ℝ) - v) + t)‖ ^ 2) (Set.Icc (-L) L) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    apply Continuous.pow
    apply Continuous.norm
    unfold sourceDirichletPoly
    apply continuous_finsetSum
    intro n hn
    apply Continuous.const_mul
    apply Continuous.const_cpow
    · fun_prop
    · left
      exact_mod_cast (hM.trans (Finset.mem_Ioc.mp hn).1).ne'
  have hSumInt : IntegrableOn (fun t : ℝ =>
      ∑ u ∈ U, ∑ v ∈ U,
        ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
          (((u : ℝ) - v) + t)‖ ^ 2) (Set.Icc (-L) L) := by
    exact integrable_finsetSum U (fun u hu =>
      integrable_finsetSum U (fun v hv => hSingleInt u v))
  have hConstInt : IntegrableOn (fun _ : ℝ => B) (Set.Icc (-L) L) :=
    integrableOn_const (ne_of_lt isCompact_Icc.measure_lt_top)
  calc
    (∑ u ∈ U, ∑ v ∈ U,
        ∫ t : ℝ in Set.Icc (-L) L,
          ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
            (((u : ℝ) - v) + t)‖ ^ 2) =
      ∫ t : ℝ in Set.Icc (-L) L,
        ∑ u ∈ U, ∑ v ∈ U,
          ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
            (((u : ℝ) - v) + t)‖ ^ 2 := by
      exact (integral_sum_gmHalfDifferenceBin_sourceMoment
        hM W j L).symm
    _ ≤ ∫ _t : ℝ in Set.Icc (-L) L, B :=
      setIntegral_mono hSumInt hConstInt hPoint
    _ = (2 * L) * B := by
      rw [MeasureTheory.setIntegral_const]
      change volume.real (Set.Icc (-L) L) * B = _
      rw [Real.volume_real_Icc_of_le (by linarith)]
      ring
    _ = _ := by
      dsimp only [B, U]
      ring

/-- Complete bin-majorant sum after the native Heath--Brown input. -/
theorem sum_gmSection11PairMajorant_native :
    ∀ A ε η : ℝ, 0 < A → 0 < ε → 0 < η →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ) (j : ℕ),
          0 < M → T₀ ≤ T → (M : ℝ) ≤ T →
          IsSeparated 1 W → InBaseInterval T W →
          (∑ u ∈ gmHalfDifferenceDyadicClass W j,
            ∑ v ∈ gmHalfDifferenceDyadicClass W j,
              gmSection11PairMajorant A ε T M u v) ≤
            (2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
              (2 * gmSection11CommonRadius (gmReflectionHeight T ε))) *
              ((2 * gmSection11CommonRadius (gmReflectionHeight T ε)) *
                C * (4 * T + 2) ^ η *
                ((((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 * M) +
                  (((gmHalfDifferenceDyadicClass W j).card : ℝ) * M ^ 2) +
                  (((gmHalfDifferenceDyadicClass W j).card : ℝ) ^
                      (5 / 4 : ℝ) *
                    (4 * T + 2) ^ (1 / 2 : ℝ) * M))) +
              ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 *
                (2 * (gmAffineLocalBumpFourierTailConstant
                  (gmReflectionDecayOrder A ε)
                  (gmReflectionDecayOrder_two_le A ε) / T ^ A) ^ 2) := by
  intro A ε η hA hε hη
  obtain ⟨C, T₀, hC, hT₀, hHB⟩ :=
    gmHalfDifferenceBinCommonIntervalMeanSquare_native η hη
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T W j hM hT hMT hSep hBase
  let U := gmHalfDifferenceDyadicClass W j
  let H := gmReflectionHeight T ε
  let L := gmSection11CommonRadius H
  let K : ℝ := 2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
    (2 * L)
  let E : ℝ := 2 * (gmAffineLocalBumpFourierTailConstant
    (gmReflectionDecayOrder A ε)
    (gmReflectionDecayOrder_two_le A ε) / T ^ A) ^ 2
  let Iuv : ℤ → ℤ → ℝ := fun u v =>
    ∫ t : ℝ in Set.Icc (-L) L,
      ‖sourceDirichletPoly M (fun _ ↦ (1 : ℂ))
        (((u : ℝ) - v) + t)‖ ^ 2
  have hTnonneg : 0 ≤ T := (zero_le_one.trans hT₀).trans hT
  have hH : 0 ≤ H := by
    dsimp only [H, gmReflectionHeight]
    exact Real.rpow_nonneg hTnonneg _
  have hL : 0 ≤ L := by
    dsimp only [L, gmSection11CommonRadius]
    positivity
  have hApplied := hHB M T W j L hM hT hSep hBase hL
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hMain :
      (∑ u ∈ U, ∑ v ∈ U, K * Iuv u v) =
        K * ∑ u ∈ U, ∑ v ∈ U, Iuv u v := by
    calc
      _ = ∑ u ∈ U, K * (∑ v ∈ U, Iuv u v) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.mul_sum]
  have hMaj (u v : ℤ) :
      gmSection11PairMajorant A ε T M u v = K * Iuv u v + E := by
    rfl
  calc
    (∑ u ∈ U, ∑ v ∈ U, gmSection11PairMajorant A ε T M u v) =
      K * (∑ u ∈ U, ∑ v ∈ U, Iuv u v) + (U.card : ℝ) ^ 2 * E := by
      simp_rw [hMaj]
      simp_rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hMain]
      ring
    _ ≤ K * ((2 * L) * C * (4 * T + 2) ^ η *
          ((((U.card : ℝ) ^ 2 * M) + ((U.card : ℝ) * M ^ 2) +
            ((U.card : ℝ) ^ (5 / 4 : ℝ) *
              (4 * T + 2) ^ (1 / 2 : ℝ) * M)))) +
        (U.card : ℝ) ^ 2 * E := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (by simpa only [U, L, Iuv] using hApplied) hK
      · exact le_rfl
    _ = _ := by
      dsimp only [U, H, L, K, E]

/-- Native dyadic-block fourth-moment estimate before the elementary
`B|U_B|` and `B²|U_B|` simplifications. -/
theorem gmDyadicPairBlockMoment_native :
    ∀ A ε η : ℝ, 0 < A → 0 < ε → 0 < η →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ) (j : ℕ),
          0 < M → T₀ ≤ T → (M : ℝ) ≤ T →
          IsSeparated 1 W → InBaseInterval T W →
          (∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
            ‖gmHalfDifferenceDyadicPairBlock W j
              (Real.log ((n : ℝ) / m))‖ ^ 2) ≤
            ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
              ((2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
                (2 * gmSection11CommonRadius (gmReflectionHeight T ε))) *
                ((2 * gmSection11CommonRadius (gmReflectionHeight T ε)) *
                  C * (4 * T + 2) ^ η *
                  ((((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 * M) +
                    (((gmHalfDifferenceDyadicClass W j).card : ℝ) * M ^ 2) +
                    (((gmHalfDifferenceDyadicClass W j).card : ℝ) ^
                        (5 / 4 : ℝ) *
                      (4 * T + 2) ^ (1 / 2 : ℝ) * M))) +
                ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 *
                  (2 * (gmAffineLocalBumpFourierTailConstant
                    (gmReflectionDecayOrder A ε)
                    (gmReflectionDecayOrder_two_le A ε) / T ^ A) ^ 2)) := by
  intro A ε η hA hε hη
  obtain ⟨C, T₀, hC, hT₀, hMaj⟩ :=
    sum_gmSection11PairMajorant_native A ε η hA hε hη
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T W j hM hT hMT hSep hBase
  rw [sum_norm_gmHalfDifferenceDyadicPairBlock_sq_eq_sourceMoment M hM W j]
  have hPairs := sum_sourceMoment_dyadicPairs_le_binMajorants
    hA hε (hT₀.trans hT) hM hMT W j
  have hMajorants := hMaj M T W j hM hT hMT hSep hBase
  exact hPairs.trans (mul_le_mul_of_nonneg_left hMajorants (sq_nonneg _))

/-! ### Elementary multiplicity algebra for the Lemma 11.6 source shape -/

theorem twoPowSucc_sq_mul_dyadicClass_card_sq_le_card_four
    (W : Finset ℝ) (j : ℕ) :
    ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
        ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 ≤
      4 * (W.card : ℝ) ^ 4 := by
  have hBU := twoPow_mul_card_gmHalfDifferenceDyadicClass_le W j
  have hBUr : ((2 ^ j : ℕ) : ℝ) *
      ((gmHalfDifferenceDyadicClass W j).card : ℝ) ≤ (W.card : ℝ) ^ 2 := by
    exact_mod_cast hBU
  have hQ : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * ((2 ^ j : ℕ) : ℝ) := by
    push_cast
    rw [pow_succ]
    ring
  have hSq := mul_self_le_mul_self
    (mul_nonneg (by positivity : 0 ≤ ((2 ^ j : ℕ) : ℝ))
      (by positivity : 0 ≤ ((gmHalfDifferenceDyadicClass W j).card : ℝ)))
    hBUr
  have hSq' : ((((2 ^ j : ℕ) : ℝ) *
        ((gmHalfDifferenceDyadicClass W j).card : ℝ)) ^ 2) ≤
      ((W.card : ℝ) ^ 2) ^ 2 := by
    simpa [pow_two] using hSq
  rw [hQ]
  calc
    (2 * ((2 ^ j : ℕ) : ℝ)) ^ 2 *
        ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 =
      4 * ((((2 ^ j : ℕ) : ℝ) *
        ((gmHalfDifferenceDyadicClass W j).card : ℝ)) ^ 2) := by ring
    _ ≤ 4 * ((W.card : ℝ) ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hSq' (by norm_num)
    _ = 4 * (W.card : ℝ) ^ 4 := by ring

theorem twoPowSucc_sq_mul_dyadicClass_card_le_energy
    (W : Finset ℝ) (j : ℕ) :
    ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
        ((gmHalfDifferenceDyadicClass W j).card : ℝ) ≤
      4 * (ApproxAddEnergy 1 W : ℝ) := by
  have hB2U := twoPow_sq_mul_card_gmHalfDifferenceDyadicClass_le_energy W j
  have hB2Ur : ((2 ^ j : ℕ) : ℝ) ^ 2 *
      ((gmHalfDifferenceDyadicClass W j).card : ℝ) ≤
        (ApproxAddEnergy 1 W : ℝ) := by
    exact_mod_cast hB2U
  have hQ : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * ((2 ^ j : ℕ) : ℝ) := by
    push_cast
    rw [pow_succ]
    ring
  rw [hQ]
  nlinarith

theorem mul_sq_mul_rpow_five_four_factor
    {B U : ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U) :
    B ^ 2 * U ^ (5 / 4 : ℝ) =
      (B ^ 2 * U) ^ (3 / 4 : ℝ) *
        (B * U) ^ (1 / 2 : ℝ) := by
  rcases hB.eq_or_lt with hB0 | hBpos
  · subst B
    norm_num
  rcases hU.eq_or_lt with hU0 | hUpos
  · subst U
    norm_num
  rw [Real.mul_rpow (pow_nonneg hB 2) hU,
    Real.mul_rpow hB hU,
    ← Real.rpow_natCast_mul hB 2 (3 / 4 : ℝ)]
  calc
    B ^ 2 * U ^ (5 / 4 : ℝ) =
        (B ^ (2 * (3 / 4 : ℝ)) * B ^ (1 / 2 : ℝ)) *
          (U ^ (3 / 4 : ℝ) * U ^ (1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hBpos, ← Real.rpow_add hUpos]
      norm_num [Real.rpow_natCast]
    _ = B ^ (2 * (3 / 4 : ℝ)) * U ^ (3 / 4 : ℝ) *
        (B ^ (1 / 2 : ℝ) * U ^ (1 / 2 : ℝ)) := by ring

theorem twoPowSucc_sq_mul_dyadicClass_card_five_four_le
    (W : Finset ℝ) (j : ℕ) :
    ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
        ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ (5 / 4 : ℝ) ≤
      4 * (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
        (W.card : ℝ) := by
  let B : ℝ := ((2 ^ j : ℕ) : ℝ)
  let U : ℝ := ((gmHalfDifferenceDyadicClass W j).card : ℝ)
  let E : ℝ := (ApproxAddEnergy 1 W : ℝ)
  let R : ℝ := (W.card : ℝ)
  have hB : 0 ≤ B := by positivity
  have hU : 0 ≤ U := by positivity
  have hE : 0 ≤ E := by positivity
  have hR : 0 ≤ R := by positivity
  have hB2U : B ^ 2 * U ≤ E := by
    dsimp only [B, U, E]
    exact_mod_cast
      twoPow_sq_mul_card_gmHalfDifferenceDyadicClass_le_energy W j
  have hBU : B * U ≤ R ^ 2 := by
    dsimp only [B, U, R]
    exact_mod_cast twoPow_mul_card_gmHalfDifferenceDyadicClass_le W j
  have hFirst : (B ^ 2 * U) ^ (3 / 4 : ℝ) ≤ E ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (mul_nonneg (pow_nonneg hB 2) hU) hB2U (by norm_num)
  have hSecond : (B * U) ^ (1 / 2 : ℝ) ≤ R := by
    have hRaw := Real.rpow_le_rpow (mul_nonneg hB hU) hBU
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      (B * U) ^ (1 / 2 : ℝ) ≤ (R ^ 2) ^ (1 / 2 : ℝ) := hRaw
      _ = R := by
        rw [← Real.rpow_natCast_mul hR 2 (1 / 2 : ℝ)]
        norm_num
  have hProduct : B ^ 2 * U ^ (5 / 4 : ℝ) ≤
      E ^ (3 / 4 : ℝ) * R := by
    rw [mul_sq_mul_rpow_five_four_factor hB hU]
    exact mul_le_mul hFirst hSecond
      (Real.rpow_nonneg (mul_nonneg hB hU) _) (Real.rpow_nonneg hE _)
  have hQ : ((2 ^ (j + 1) : ℕ) : ℝ) = 2 * B := by
    dsimp only [B]
    push_cast
    rw [pow_succ]
    ring
  rw [hQ]
  nlinarith

/-- The three elementary multiplicity inequalities assembled in exactly the
shape needed after the native Heath--Brown estimate for one dyadic class. -/
theorem gmDyadicMultiplicitySourceShape
    (W : Finset ℝ) (j : ℕ) {K L S X : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hS : 0 ≤ S) (hX : 0 ≤ X) :
    ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
        (K *
          (((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 * X +
            ((gmHalfDifferenceDyadicClass W j).card : ℝ) * X ^ 2 +
            ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ (5 / 4 : ℝ) *
              S * X) +
          ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 * L) ≤
      4 * K *
          ((W.card : ℝ) ^ 4 * X +
            (ApproxAddEnergy 1 W : ℝ) * X ^ 2 +
            (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
              (W.card : ℝ) * S * X) +
        4 * (W.card : ℝ) ^ 4 * L := by
  have hOne := twoPowSucc_sq_mul_dyadicClass_card_sq_le_card_four W j
  have hTwo := twoPowSucc_sq_mul_dyadicClass_card_le_energy W j
  have hThree := twoPowSucc_sq_mul_dyadicClass_card_five_four_le W j
  calc
    ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
        (K *
          (((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 * X +
            ((gmHalfDifferenceDyadicClass W j).card : ℝ) * X ^ 2 +
            ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ (5 / 4 : ℝ) *
              S * X) +
          ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2 * L) =
      K *
          ((((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
              ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2) * X +
            (((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
              ((gmHalfDifferenceDyadicClass W j).card : ℝ)) * X ^ 2 +
            (((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
              ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ (5 / 4 : ℝ)) *
                S * X) +
        (((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 *
          ((gmHalfDifferenceDyadicClass W j).card : ℝ) ^ 2) * L := by ring
    _ ≤ K *
          ((4 * (W.card : ℝ) ^ 4) * X +
            (4 * (ApproxAddEnergy 1 W : ℝ)) * X ^ 2 +
            (4 * (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
              (W.card : ℝ)) * S * X) +
        (4 * (W.card : ℝ) ^ 4) * L := by
      gcongr
    _ = 4 * K *
          ((W.card : ℝ) ^ 4 * X +
            (ApproxAddEnergy 1 W : ℝ) * X ^ 2 +
            (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
              (W.card : ℝ) * S * X) +
        4 * (W.card : ℝ) ^ 4 * L := by ring

/-- Guth--Maynard Lemma 11.6 for one occupied dyadic multiplicity class,
after the source inequalities `B|U_B| ≤ |W|²` and
`B²|U_B| ≤ E(W)` have been applied.  The common smoothing radius and
the rapidly decreasing Fourier tail are still displayed explicitly here;
they are absorbed only in the full fourth-moment consumer below. -/
theorem gmDyadicPairBlockMoment_sourceShape_native :
    ∀ A ε η : ℝ, 0 < A → 0 < ε → 0 < η →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ) (j : ℕ),
          0 < M → T₀ ≤ T → (M : ℝ) ≤ T →
          IsSeparated 1 W → InBaseInterval T W →
          (∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
            ‖gmHalfDifferenceDyadicPairBlock W j
              (Real.log ((n : ℝ) / m))‖ ^ 2) ≤
            4 *
              ((2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
                (2 * gmSection11CommonRadius (gmReflectionHeight T ε))) *
                ((2 * gmSection11CommonRadius (gmReflectionHeight T ε)) *
                  C * (4 * T + 2) ^ η)) *
              ((W.card : ℝ) ^ 4 * M +
                (ApproxAddEnergy 1 W : ℝ) * M ^ 2 +
                (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
                  (W.card : ℝ) * (4 * T + 2) ^ (1 / 2 : ℝ) * M) +
            4 * (W.card : ℝ) ^ 4 *
              (2 * (gmAffineLocalBumpFourierTailConstant
                (gmReflectionDecayOrder A ε)
                (gmReflectionDecayOrder_two_le A ε) / T ^ A) ^ 2) := by
  intro A ε η hA hε hη
  obtain ⟨C, T₀, hC, hT₀, hBlock⟩ :=
    gmDyadicPairBlockMoment_native A ε η hA hε hη
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T W j hM hT hMT hSep hBase
  have hRaw := hBlock M T W j hM hT hMT hSep hBase
  let K : ℝ :=
    (2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
      (2 * gmSection11CommonRadius (gmReflectionHeight T ε))) *
      ((2 * gmSection11CommonRadius (gmReflectionHeight T ε)) *
        C * (4 * T + 2) ^ η)
  let L : ℝ := 2 * (gmAffineLocalBumpFourierTailConstant
    (gmReflectionDecayOrder A ε)
    (gmReflectionDecayOrder_two_le A ε) / T ^ A) ^ 2
  let S : ℝ := (4 * T + 2) ^ (1 / 2 : ℝ)
  have hTone : 1 ≤ T := hT₀.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hHeight : 0 ≤ gmReflectionHeight T ε := by
    unfold gmReflectionHeight
    exact Real.rpow_nonneg hTpos.le _
  have hRadius : 0 ≤
      gmSection11CommonRadius (gmReflectionHeight T ε) := by
    unfold gmSection11CommonRadius
    positivity
  have hBase : 0 ≤ 4 * T + 2 := by positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hL : 0 ≤ L := by
    dsimp only [L]
    positivity
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact Real.rpow_nonneg hBase _
  have hShape := gmDyadicMultiplicitySourceShape W j hK hL hS
    (by positivity : 0 ≤ (M : ℝ))
  exact hRaw.trans (by
    dsimp only [K, L, S] at hShape
    convert hShape using 1
    all_goals ring_nf)

/-- The exact Cauchy--Schwarz reduction of the discrete fourth moment to
the occupied multiplicity blocks.  This is the finite, source-facing first
line of Guth--Maynard Lemma 11.6. -/
theorem gmDiscreteFourthMoment_le_dyadicPairBlockMoments
    (M : ℕ) (W : Finset ℝ) (hSep : IsSeparated 1 W) :
    gmDiscreteRatioMoment 4 M W ≤
      ((Nat.log 2 W.card + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
          ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
            ‖gmHalfDifferenceDyadicPairBlock W j
              (Real.log ((n : ℝ) / m))‖ ^ 2 := by
  rw [gmDiscreteRatioMoment_eq_iterated]
  calc
    (∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        ‖gmR W ((n : ℝ) / m)‖ ^ 4) ≤
      ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        ((Nat.log 2 W.card + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
            ‖gmHalfDifferenceDyadicPairBlock W j
              (Real.log ((n : ℝ) / m))‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      have hnNat : 0 < n := by
        rw [dyadicInterval, Finset.mem_Ioc] at hn
        omega
      have hmNat : 0 < m := by
        rw [dyadicInterval, Finset.mem_Ioc] at hm
        omega
      have hratio : 0 < (n : ℝ) / m := by positivity
      rw [gmR_eq_gmRPhase_log hratio.ne', abs_of_pos hratio]
      exact norm_gmRPhase_fourth_le_dyadicPairBlocks W hSep
        (Real.log ((n : ℝ) / m))
    _ = ((Nat.log 2 W.card + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
          ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
            ‖gmHalfDifferenceDyadicPairBlock W j
              (Real.log ((n : ℝ) / m))‖ ^ 2 := by
      simp_rw [Finset.mul_sum]
      apply Eq.trans
      · apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_comm]
      · rw [Finset.sum_comm]

/-- Full finite Lemma 11.6 before epsilon absorption.  The only factors not
yet in the three-term source bound are the square of the number of occupied
dyadic multiplicity scales, the common smoothing radius, and the displayed
Schwartz tail. -/
theorem gmDiscreteFourthMoment_raw_native :
    ∀ A ε η : ℝ, 0 < A → 0 < ε → 0 < η →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ),
          0 < M → T₀ ≤ T → (M : ℝ) ≤ T →
          IsSeparated 1 W → InBaseInterval T W →
          gmDiscreteRatioMoment 4 M W ≤
            ((Nat.log 2 W.card + 1 : ℕ) : ℝ) ^ 2 *
              (4 *
                ((2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
                  (2 * gmSection11CommonRadius (gmReflectionHeight T ε))) *
                  ((2 * gmSection11CommonRadius (gmReflectionHeight T ε)) *
                    C * (4 * T + 2) ^ η)) *
                ((W.card : ℝ) ^ 4 * M +
                  (ApproxAddEnergy 1 W : ℝ) * M ^ 2 +
                  (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
                    (W.card : ℝ) * (4 * T + 2) ^ (1 / 2 : ℝ) * M) +
              4 * (W.card : ℝ) ^ 4 *
                (2 * (gmAffineLocalBumpFourierTailConstant
                  (gmReflectionDecayOrder A ε)
                  (gmReflectionDecayOrder_two_le A ε) / T ^ A) ^ 2)) := by
  intro A ε η hA hε hη
  obtain ⟨C, T₀, hC, hT₀, hBlock⟩ :=
    gmDyadicPairBlockMoment_sourceShape_native A ε η hA hε hη
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro M T W hM hT hMT hSep hBase
  let J : ℝ := ((Nat.log 2 W.card + 1 : ℕ) : ℝ)
  let B : ℝ :=
    4 *
      ((2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
        (2 * gmSection11CommonRadius (gmReflectionHeight T ε))) *
        ((2 * gmSection11CommonRadius (gmReflectionHeight T ε)) *
          C * (4 * T + 2) ^ η)) *
      ((W.card : ℝ) ^ 4 * M +
        (ApproxAddEnergy 1 W : ℝ) * M ^ 2 +
        (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
          (W.card : ℝ) * (4 * T + 2) ^ (1 / 2 : ℝ) * M) +
    4 * (W.card : ℝ) ^ 4 *
      (2 * (gmAffineLocalBumpFourierTailConstant
        (gmReflectionDecayOrder A ε)
        (gmReflectionDecayOrder_two_le A ε) / T ^ A) ^ 2)
  have hReduce := gmDiscreteFourthMoment_le_dyadicPairBlockMoments M W hSep
  have hSum :
      (∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
        ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
          ‖gmHalfDifferenceDyadicPairBlock W j
            (Real.log ((n : ℝ) / m))‖ ^ 2) ≤
        J * B := by
    calc
      (∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
          ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
            ‖gmHalfDifferenceDyadicPairBlock W j
              (Real.log ((n : ℝ) / m))‖ ^ 2) ≤
        ∑ _j ∈ Finset.range (Nat.log 2 W.card + 1), B := by
          apply Finset.sum_le_sum
          intro j hj
          dsimp only [B]
          exact hBlock M T W j hM hT hMT hSep hBase
      _ = J * B := by simp [J]
  calc
    gmDiscreteRatioMoment 4 M W ≤ J *
        ∑ j ∈ Finset.range (Nat.log 2 W.card + 1),
          ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
            ‖gmHalfDifferenceDyadicPairBlock W j
              (Real.log ((n : ℝ) / m))‖ ^ 2 := by
      simpa only [J] using hReduce
    _ ≤ J * (J * B) := mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = J ^ 2 * B := by ring
    _ = _ := by rfl

/-- The number of multiplicity scales is logarithmic in the physical
height, uniformly for the actual one-separated source set. -/
theorem gmHalfDifferenceDyadicCount_le_six_log
    {T : ℝ} {W : Finset ℝ}
    (hT : Real.exp 1 ≤ T) (hSep : IsSeparated 1 W)
    (hBase : InBaseInterval T W) :
    ((Nat.log 2 W.card + 1 : ℕ) : ℝ) ≤ 6 * Real.log T := by
  have hTone : 1 ≤ T := by
    calc
      1 = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ T := hT
  have hlogTone : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) hT
  by_cases hWzero : W.card = 0
  · rw [hWzero]
    norm_num
    linarith
  have hWone : 1 ≤ W.card := Nat.one_le_iff_ne_zero.mpr hWzero
  have hCard := gmSeparated_card_le_two_height hTone hSep hBase
  have hLogCard := natCast_log_two_le_log W.card hWone
  have hCardPos : (0 : ℝ) < W.card := by exact_mod_cast (Nat.pos_of_ne_zero hWzero)
  have hTwoTPos : 0 < 2 * T := by positivity
  have hLogMono : Real.log (W.card : ℝ) ≤ Real.log (2 * T) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hCardPos) (Set.mem_Ioi.mpr hTwoTPos) hCard
  have hLogProduct : Real.log (2 * T) = Real.log 2 + Real.log T := by
    rw [Real.log_mul (by norm_num) (by positivity : T ≠ 0)]
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  push_cast
  calc
    (Nat.log 2 W.card : ℝ) + 1 ≤
        Real.log (W.card : ℝ) / Real.log 2 + 1 := by linarith
    _ ≤ Real.log (2 * T) / Real.log 2 + 1 := by gcongr
    _ = (Real.log 2 + Real.log T) / Real.log 2 + 1 := by
      rw [hLogProduct]
    _ ≤ 6 * Real.log T := by
      have hdiv :
          (Real.log 2 + Real.log T) / Real.log 2 ≤
            6 * Real.log T - 1 := by
        rw [div_le_iff₀ hlogTwoPos]
        nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
      linarith

theorem four_mul_add_two_rpow_le_six_mul
    {T a : ℝ} (hT : 1 ≤ T) (ha : 0 ≤ a) :
    (4 * T + 2) ^ a ≤ 6 ^ a * T ^ a := by
  have hBase : 0 ≤ 4 * T + 2 := by positivity
  have hSixT : 4 * T + 2 ≤ 6 * T := by linarith
  calc
    (4 * T + 2) ^ a ≤ (6 * T) ^ a :=
      Real.rpow_le_rpow hBase hSixT ha
    _ = 6 ^ a * T ^ a := by rw [Real.mul_rpow (by norm_num) (by positivity)]

theorem gmSection11CommonRadius_le_epsilonPower
    {ε T : ℝ} (hε : 0 < ε) (hT : 1 ≤ T) :
    gmSection11CommonRadius (gmReflectionHeight T ε) ≤
      (1 + 2 * Real.pi) * T ^ (ε / 16) := by
  have hEta : gmReflectionEta ε ≤ ε / 16 := by
    unfold gmReflectionEta
    exact min_le_left _ _
  have hHeight : gmReflectionHeight T ε ≤ T ^ (ε / 16) := by
    unfold gmReflectionHeight
    exact Real.rpow_le_rpow_of_exponent_le hT hEta
  have hPowOne : 1 ≤ T ^ (ε / 16) :=
    Real.one_le_rpow hT (by positivity)
  unfold gmSection11CommonRadius
  calc
    1 + 2 * Real.pi * gmReflectionHeight T ε ≤
        1 + 2 * Real.pi * T ^ (ε / 16) := by gcongr
    _ ≤ (1 + 2 * Real.pi) * T ^ (ε / 16) := by
      nlinarith [Real.pi_pos]

theorem gmSection11RawCore_le_sqrtSix
    {T : ℝ} {M : ℕ} (W : Finset ℝ) (hT : 1 ≤ T) :
    (W.card : ℝ) ^ 4 * M +
        (ApproxAddEnergy 1 W : ℝ) * M ^ 2 +
        (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
          (W.card : ℝ) * (4 * T + 2) ^ (1 / 2 : ℝ) * M ≤
      Real.sqrt 6 *
        ((W.card : ℝ) ^ 4 * M +
          (ApproxAddEnergy 1 W : ℝ) * M ^ 2 +
          (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
            (W.card : ℝ) * T ^ (1 / 2 : ℝ) * M) := by
  have hSix : (0 : ℝ) ≤ 6 := by norm_num
  have hSqrtSixOne : 1 ≤ Real.sqrt 6 :=
    (Real.one_le_sqrt).2 (by norm_num)
  have hRoot := four_mul_add_two_rpow_le_six_mul hT
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hSqrtSix : 6 ^ (1 / 2 : ℝ) = Real.sqrt 6 := by
    rw [Real.sqrt_eq_rpow]
  rw [hSqrtSix] at hRoot
  have hFirst :
      (W.card : ℝ) ^ 4 * M ≤
        Real.sqrt 6 * ((W.card : ℝ) ^ 4 * M) := by
    nlinarith [show 0 ≤ (W.card : ℝ) ^ 4 * M by positivity]
  have hSecond :
      (ApproxAddEnergy 1 W : ℝ) * M ^ 2 ≤
        Real.sqrt 6 * ((ApproxAddEnergy 1 W : ℝ) * M ^ 2) := by
    nlinarith [show 0 ≤ (ApproxAddEnergy 1 W : ℝ) * M ^ 2 by positivity]
  have hThird :
      (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
          (W.card : ℝ) * (4 * T + 2) ^ (1 / 2 : ℝ) * M ≤
        Real.sqrt 6 *
          ((ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
            (W.card : ℝ) * T ^ (1 / 2 : ℝ) * M) := by
    calc
      _ ≤ (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
          (W.card : ℝ) * (Real.sqrt 6 * T ^ (1 / 2 : ℝ)) * M := by
        gcongr
      _ = _ := by ring
  linarith

set_option maxHeartbeats 1000000 in
/-- Guth--Maynard Lemma 11.6 in its paper-level epsilon form.  This theorem
assembles the exact dyadic pair decomposition, common-shift smoothing,
native Heath--Brown mean square, multiplicity/energy inequalities, and all
logarithmic and smoothing losses. -/
theorem gmDiscreteFourthMoment_native :
    ∀ ε : ℝ, 0 < ε →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ (M : ℕ) (T : ℝ) (W : Finset ℝ),
          0 < M → T₀ ≤ T → (M : ℝ) ≤ T →
          IsSeparated 1 W → InBaseInterval T W →
          gmDiscreteRatioMoment 4 M W ≤
            C * T ^ ε *
              ((W.card : ℝ) ^ 4 * M +
                (ApproxAddEnergy 1 W : ℝ) * M ^ 2 +
                (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
                  (W.card : ℝ) * T ^ (1 / 2 : ℝ) * M) := by
  intro ε hε
  let η : ℝ := ε / 16
  let δ : ℝ := ε / 4
  have hη : 0 < η := by dsimp only [η]; positivity
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨C₁, T₁, hC₁, hT₁, hRaw⟩ :=
    gmDiscreteFourthMoment_raw_native 100 ε η (by norm_num) hε hη
  have hLogEventually := eventually_log_nat_power_le_rpow 2 δ hδ
  rw [eventually_atTop] at hLogEventually
  obtain ⟨Tlog, hTlog⟩ := hLogEventually
  let T₀ : ℝ := max T₁ (max (Real.exp 1) Tlog)
  let A₀ : ℝ := 2 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2
  let D₀ : ℝ := 1 + 2 * Real.pi
  let E₀ : ℝ := gmAffineLocalBumpFourierTailConstant
    (gmReflectionDecayOrder 100 ε) (gmReflectionDecayOrder_two_le 100 ε)
  let Cmain : ℝ :=
    576 * A₀ * D₀ ^ 2 * C₁ * 6 ^ η * Real.sqrt 6
  let Ctail : ℝ := 288 * E₀ ^ 2
  let C : ℝ := Cmain + Ctail
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  have hA₀pos : 0 < A₀ := by
    dsimp only [A₀]
    have hSup : 0 < gmAffineLocalBumpFourierSup :=
      gmAffineLocalBumpFourierSup_pos
    positivity
  have hD₀ : 0 < D₀ := by dsimp only [D₀]; nlinarith [Real.pi_pos]
  have hE₀ : 0 < E₀ := by
    dsimp only [E₀]
    exact gmAffineLocalBumpFourierTailConstant_pos _ _
  have hCmain : 0 < Cmain := by
    dsimp only [Cmain]
    positivity
  have hCtail : 0 < Ctail := by dsimp only [Ctail]; positivity
  refine ⟨C, T₀, by dsimp only [C]; positivity,
    le_trans hT₁ (le_max_left _ _), ?_⟩
  intro M T W hM hT hMT hSep hBase
  have hT₁' : T₁ ≤ T := (le_max_left _ _).trans hT
  have hTexp : Real.exp 1 ≤ T :=
    (le_max_left (Real.exp 1) Tlog).trans
      ((le_max_right T₁ (max (Real.exp 1) Tlog)).trans hT)
  have hTlog' : Tlog ≤ T :=
    (le_max_right (Real.exp 1) Tlog).trans
      ((le_max_right T₁ (max (Real.exp 1) Tlog)).trans hT)
  have hTone : 1 ≤ T := by
    calc
      1 = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ T := hTexp
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hLogPow : (Real.log T) ^ 2 ≤ T ^ δ := hTlog T hTlog'
  let J : ℝ := ((Nat.log 2 W.card + 1 : ℕ) : ℝ)
  let R : ℝ := gmSection11CommonRadius (gmReflectionHeight T ε)
  let S : ℝ := (4 * T + 2) ^ (1 / 2 : ℝ)
  let Core : ℝ :=
    (W.card : ℝ) ^ 4 * M +
      (ApproxAddEnergy 1 W : ℝ) * M ^ 2 +
      (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
        (W.card : ℝ) * T ^ (1 / 2 : ℝ) * M
  let RawCore : ℝ :=
    (W.card : ℝ) ^ 4 * M +
      (ApproxAddEnergy 1 W : ℝ) * M ^ 2 +
      (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
        (W.card : ℝ) * S * M
  have hJ : J ≤ 6 * Real.log T := by
    simpa only [J] using gmHalfDifferenceDyadicCount_le_six_log hTexp hSep hBase
  have hJ0 : 0 ≤ J := by dsimp only [J]; positivity
  have hLog0 : 0 ≤ Real.log T := Real.log_nonneg hTone
  have hJSq : J ^ 2 ≤ 36 * T ^ δ := by
    calc
      J ^ 2 ≤ (6 * Real.log T) ^ 2 := pow_le_pow_left₀ hJ0 hJ 2
      _ = 36 * (Real.log T) ^ 2 := by ring
      _ ≤ 36 * T ^ δ := by gcongr
  have hR : R ≤ D₀ * T ^ (ε / 16) := by
    simpa only [R, D₀] using gmSection11CommonRadius_le_epsilonPower hε hTone
  have hR0 : 0 ≤ R := by
    dsimp only [R, gmSection11CommonRadius, gmReflectionHeight]
    positivity
  have hRSq : R ^ 2 ≤ D₀ ^ 2 * T ^ (ε / 8) := by
    calc
      R ^ 2 ≤ (D₀ * T ^ (ε / 16)) ^ 2 :=
        pow_le_pow_left₀ hR0 hR 2
      _ = D₀ ^ 2 * T ^ (ε / 8) := by
        rw [mul_pow]
        congr 1
        calc
          (T ^ (ε / 16)) ^ 2 = (T ^ (ε / 16)) ^ (2 : ℝ) := by
            rw [Real.rpow_two]
          _ = T ^ ((ε / 16) * 2) := by
            rw [Real.rpow_mul hTpos.le]
          _ = T ^ (ε / 8) := by
            congr 1
            ring_nf
  have hScale : (4 * T + 2) ^ η ≤ 6 ^ η * T ^ η :=
    four_mul_add_two_rpow_le_six_mul hTone hη.le
  have hCore : RawCore ≤ Real.sqrt 6 * Core := by
    simpa only [RawCore, Core, S] using gmSection11RawCore_le_sqrtSix W hTone
  have hCore0 : 0 ≤ Core := by dsimp only [Core]; positivity
  have hRawCore0 : 0 ≤ RawCore := by dsimp only [RawCore, S]; positivity
  have hExponent : δ + ε / 8 + η ≤ ε := by
    dsimp only [δ, η]
    linarith
  have hPowCombine :
      T ^ δ * T ^ (ε / 8) * T ^ η ≤ T ^ ε := by
    rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
    exact Real.rpow_le_rpow_of_exponent_le hTone hExponent
  have hMainPrefactor :
      J ^ 2 *
          (4 * ((A₀ * (2 * R)) * ((2 * R) * C₁ * (4 * T + 2) ^ η))) ≤
        (Cmain / Real.sqrt 6) * T ^ ε := by
    have hSqrtSixPos : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
    calc
      J ^ 2 *
          (4 * ((A₀ * (2 * R)) * ((2 * R) * C₁ * (4 * T + 2) ^ η))) ≤
        (36 * T ^ δ) *
          (4 * ((A₀ * (2 * R)) * ((2 * R) * C₁ * (4 * T + 2) ^ η))) := by
            gcongr
      _ = 576 * A₀ * C₁ * T ^ δ * R ^ 2 * (4 * T + 2) ^ η := by ring
      _ ≤ 576 * A₀ * C₁ * T ^ δ *
          (D₀ ^ 2 * T ^ (ε / 8)) * (6 ^ η * T ^ η) := by
            gcongr
      _ = (576 * A₀ * D₀ ^ 2 * C₁ * 6 ^ η) *
          (T ^ δ * T ^ (ε / 8) * T ^ η) := by ring
      _ ≤ (576 * A₀ * D₀ ^ 2 * C₁ * 6 ^ η) * T ^ ε := by
            gcongr
      _ = (Cmain / Real.sqrt 6) * T ^ ε := by
        dsimp only [Cmain]
        field_simp [hSqrtSixPos.ne']
  have hMain :
      J ^ 2 *
          (4 * ((A₀ * (2 * R)) * ((2 * R) * C₁ * (4 * T + 2) ^ η)) *
            RawCore) ≤
        Cmain * T ^ ε * Core := by
    calc
      _ = (J ^ 2 *
          (4 * ((A₀ * (2 * R)) * ((2 * R) * C₁ * (4 * T + 2) ^ η)))) *
            RawCore := by ring
      _ ≤ ((Cmain / Real.sqrt 6) * T ^ ε) *
            (Real.sqrt 6 * Core) := by gcongr
      _ = Cmain * T ^ ε * Core := by
        have hsqrt : Real.sqrt 6 ≠ 0 :=
          Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 6)
        field_simp [hsqrt]
  have hTailFrac : E₀ / T ^ (100 : ℝ) ≤ E₀ := by
    apply div_le_self hE₀.le
    exact Real.one_le_rpow hTone (by norm_num)
  have hTailFrac0 : 0 ≤ E₀ / T ^ (100 : ℝ) := by positivity
  have hTailSq : (E₀ / T ^ (100 : ℝ)) ^ 2 ≤ E₀ ^ 2 :=
    pow_le_pow_left₀ hTailFrac0 hTailFrac 2
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hRfourM : (W.card : ℝ) ^ 4 ≤ Core := by
    dsimp only [Core]
    have : (W.card : ℝ) ^ 4 ≤ (W.card : ℝ) ^ 4 * M := by
      nlinarith [show 0 ≤ (W.card : ℝ) ^ 4 by positivity]
    have hSecondNonneg :
        0 ≤ (ApproxAddEnergy 1 W : ℝ) * (M : ℝ) ^ 2 := by positivity
    have hThirdNonneg :
        0 ≤ (ApproxAddEnergy 1 W : ℝ) ^ (3 / 4 : ℝ) *
          (W.card : ℝ) * T ^ (1 / 2 : ℝ) * M := by positivity
    linarith
  have hDeltaEps : δ ≤ ε := by dsimp only [δ]; linarith
  have hPowDelta : T ^ δ ≤ T ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hTone hDeltaEps
  have hTail :
      J ^ 2 * (4 * (W.card : ℝ) ^ 4 *
        (2 * (E₀ / T ^ (100 : ℝ)) ^ 2)) ≤
        Ctail * T ^ ε * Core := by
    calc
      _ ≤ (36 * T ^ δ) *
          (4 * (W.card : ℝ) ^ 4 * (2 * E₀ ^ 2)) := by gcongr
      _ = Ctail * T ^ δ * (W.card : ℝ) ^ 4 := by
        dsimp only [Ctail]
        ring
      _ ≤ Ctail * T ^ ε * Core := by gcongr
  have hApplied := hRaw M T W hM hT₁' hMT hSep hBase
  change gmDiscreteRatioMoment 4 M W ≤
      J ^ 2 *
        (4 * ((A₀ * (2 * R)) * ((2 * R) * C₁ * (4 * T + 2) ^ η)) *
          RawCore +
        4 * (W.card : ℝ) ^ 4 *
          (2 * (E₀ / T ^ (100 : ℝ)) ^ 2)) at hApplied
  calc
    gmDiscreteRatioMoment 4 M W ≤ _ := hApplied
    _ = J ^ 2 *
          (4 * ((A₀ * (2 * R)) * ((2 * R) * C₁ * (4 * T + 2) ^ η)) *
            RawCore) +
        J ^ 2 * (4 * (W.card : ℝ) ^ 4 *
          (2 * (E₀ / T ^ (100 : ℝ)) ^ 2)) := by ring
    _ ≤ Cmain * T ^ ε * Core + Ctail * T ^ ε * Core := add_le_add hMain hTail
    _ = C * T ^ ε * Core := by dsimp only [C]; ring
    _ = _ := by rfl

/-! ## The large-value input: Guth--Maynard Lemma 11.4 -/

/-- Exact finite expansion of the squared source polynomial, with the
coefficient ordering chosen to match the three copies of `R` in Lemma 11.4.
This is the arbitrary-coefficient analogue of
`ofReal_norm_sourceDirichletPoly_one_sq_expand`. -/
theorem ofReal_norm_sourceDirichletPoly_sq_expand
    {M : ℕ} (hM : 0 < M) (b : ℕ → ℂ) (a : ℝ) :
    ((‖sourceDirichletPoly M b a‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        star (b n) * b m *
          Complex.exp ((((a * (Real.log m - Real.log n) : ℝ) : ℂ) * I)) := by
  rw [sourceDirichletPoly, ofReal_norm_finset_sum_sq_expand]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  have hnpos : 0 < n := hM.trans (Finset.mem_Ioc.mp hn).1
  have hmpos : 0 < m := hM.trans (Finset.mem_Ioc.mp hm).1
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hmne : (m : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'
  rw [star_mul, Complex.cpow_def_of_ne_zero hnne,
    Complex.cpow_def_of_ne_zero hmne]
  rw [Complex.star_def, ← Complex.exp_conj]
  have hnCast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  have hmCast : (m : ℂ) = ((m : ℝ) : ℂ) := by norm_num
  rw [hnCast, hmCast,
    ← Complex.ofReal_log (by exact_mod_cast hnpos.le),
    ← Complex.ofReal_log (by exact_mod_cast hmpos.le)]
  have hstarPhase :
      star (((Real.log n : ℝ) : ℂ) * ((a : ℂ) * I)) =
        -(((Real.log n : ℝ) : ℂ) * ((a : ℂ) * I)) := by
    rw [Complex.star_def]
    simp only [map_mul, conj_ofReal, conj_I]
    ring
  have hphase :
      Complex.exp (star (((Real.log n : ℝ) : ℂ) * ((a : ℂ) * I))) *
          Complex.exp (((Real.log m : ℝ) : ℂ) * ((a : ℂ) * I)) =
        Complex.exp ((((a * (Real.log m - Real.log n) : ℝ) : ℂ) * I)) := by
    rw [hstarPhase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = star (b n) * b m *
        (Complex.exp
            (star ((((Real.log n : ℝ) : ℂ) * ((a : ℂ) * I)))) *
          Complex.exp ((((Real.log m : ℝ) : ℂ) * ((a : ℂ) * I)))) := by
      ac_rfl
    _ = _ := by
      rw [hphase]
      rfl

theorem ofReal_norm_sourceDirichletPoly_sq_expand'
    {M : ℕ} (hM : 0 < M) (b : ℕ → ℂ) (a : ℝ) :
    ((‖sourceDirichletPoly M b a‖ : ℂ) ^ 2) =
      ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        star (b n) * b m *
          Complex.exp ((((a * (Real.log m - Real.log n) : ℝ) : ℂ) * I)) := by
  rw [← ofReal_norm_sourceDirichletPoly_sq_expand hM b a]
  push_cast
  rfl

theorem sum_three_swap_first_third
    {A B C R : Type*} [AddCommMonoid R]
    (U : Finset A) (V : Finset B) (W : Finset C)
    (f : A → B → C → R) :
    (∑ a ∈ U, ∑ b ∈ V, ∑ c ∈ W, f a b c) =
      ∑ c ∈ W, ∑ b ∈ V, ∑ a ∈ U, f a b c := by
  calc
    _ = ∑ a ∈ U, ∑ c ∈ W, ∑ b ∈ V, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c ∈ W, ∑ a ∈ U, ∑ b ∈ V, f a b c := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]

theorem sum_five_last_two_to_front
    {A B C D E R : Type*} [AddCommMonoid R]
    (U : Finset A) (V : Finset B) (W : Finset C)
    (X : Finset D) (Y : Finset E)
    (f : A → B → C → D → E → R) :
    (∑ a ∈ U, ∑ b ∈ V, ∑ c ∈ W, ∑ d ∈ X, ∑ e ∈ Y,
        f a b c d e) =
      ∑ d ∈ X, ∑ e ∈ Y, ∑ a ∈ U, ∑ b ∈ V, ∑ c ∈ W,
        f a b c d e := by
  calc
    _ = ∑ a ∈ U, ∑ b ∈ V, ∑ d ∈ X, ∑ c ∈ W, ∑ e ∈ Y,
        f a b c d e := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    _ = ∑ a ∈ U, ∑ d ∈ X, ∑ b ∈ V, ∑ c ∈ W, ∑ e ∈ Y,
        f a b c d e := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ d ∈ X, ∑ a ∈ U, ∑ b ∈ V, ∑ c ∈ W, ∑ e ∈ Y,
        f a b c d e := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ X, ∑ a ∈ U, ∑ b ∈ V, ∑ e ∈ Y, ∑ c ∈ W,
        f a b c d e := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    _ = ∑ d ∈ X, ∑ a ∈ U, ∑ e ∈ Y, ∑ b ∈ V, ∑ c ∈ W,
        f a b c d e := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]

/-- The three ordinate sums in Lemma 11.4 are exactly two positive-frequency
copies and one negative-frequency copy of the source exponential sum. -/
theorem sum_three_source_phases_eq_gmRPhase
    (W : Finset ℝ) (x s : ℝ) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        Complex.exp ((((t₁ + t₂ - t₃ + s) * x : ℝ) : ℂ) * I) =
      Complex.exp ((((s * x : ℝ) : ℂ) * I)) *
        gmRPhase W x ^ 2 * gmRPhase W (-x) := by
  unfold gmRPhase
  rw [pow_two]
  calc
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        Complex.exp ((((t₁ + t₂ - t₃ + s) * x : ℝ) : ℂ) * I) =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        Complex.exp ((((s * x : ℝ) : ℂ) * I)) *
          Complex.exp ((((t₁ * x : ℝ) : ℂ) * I)) *
          Complex.exp ((((t₂ * x : ℝ) : ℂ) * I)) *
          Complex.exp ((((t₃ * (-x) : ℝ) : ℂ) * I)) := by
      apply Finset.sum_congr rfl
      intro t₁ ht₁
      apply Finset.sum_congr rfl
      intro t₂ ht₂
      apply Finset.sum_congr rfl
      intro t₃ ht₃
      rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = Complex.exp ((((s * x : ℝ) : ℂ) * I)) *
        (∑ t ∈ W, Complex.exp ((((t * x : ℝ) : ℂ) * I))) *
        (∑ t ∈ W, Complex.exp ((((t * x : ℝ) : ℂ) * I))) *
        (∑ t ∈ W, Complex.exp ((((t * (-x) : ℝ) : ℂ) * I))) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact sum_three_swap_first_third W W W _
    _ = _ := by ring

/-- Exact triple-moment identity behind Guth--Maynard Lemma 11.4.  No
absolute value or coefficient estimate has yet been used. -/
theorem ofReal_sum_triple_sourceMoment_eq
    {M : ℕ} (hM : 0 < M) (W : Finset ℝ) (b : ℕ → ℂ) (s : ℝ) :
    (((∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2) : ℝ) : ℂ) =
      ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        star (b n) * b m *
          (Complex.exp ((((s * (Real.log m - Real.log n) : ℝ) : ℂ) * I)) *
            gmRPhase W (Real.log m - Real.log n) ^ 2 *
              gmRPhase W (-(Real.log m - Real.log n))) := by
  push_cast
  simp_rw [ofReal_norm_sourceDirichletPoly_sq_expand' hM]
  rw [sum_five_last_two_to_front]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  calc
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        star (b n) * b m *
          Complex.exp ((((t₁ + t₂ - t₃ + s) *
            (Real.log m - Real.log n) : ℝ) : ℂ) * I) =
      star (b n) * b m *
        (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          Complex.exp ((((t₁ + t₂ - t₃ + s) *
            (Real.log m - Real.log n) : ℝ) : ℂ) * I)) := by
      simp only [Finset.mul_sum]
    _ = _ := by
      rw [sum_three_source_phases_eq_gmRPhase]
      have hnpos : 0 < n := hM.trans (Finset.mem_Ioc.mp hn).1
      have hmpos : 0 < m := hM.trans (Finset.mem_Ioc.mp hm).1
      have hmLog : Complex.log (m : ℂ) = ((Real.log m : ℝ) : ℂ) := by
        symm
        exact Complex.ofReal_log (by exact_mod_cast hmpos.le)
      have hnLog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
        symm
        exact Complex.ofReal_log (by exact_mod_cast hnpos.le)
      rw [hmLog, hnLog]
      push_cast
      rfl

/-- The coefficient-uniform form of the triple-moment calculation in
Guth--Maynard Lemma 11.4.  The three ordinate sums are bounded by the
actual discrete third moment of `R`; no replacement moment or independent
cardinality hypothesis is introduced. -/
theorem sum_triple_sourceMoment_le_discreteThirdMoment
    {M : ℕ} (hM : 0 < M) (W : Finset ℝ) (b : ℕ → ℂ) (s : ℝ)
    (hb : ∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) :
    (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2) ≤
      gmDiscreteRatioMoment 3 M W := by
  let S : ℝ := ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
    ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    positivity
  have hSnorm : S = ‖((S : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
  have hExpand := ofReal_sum_triple_sourceMoment_eq hM W b s
  change S ≤ gmDiscreteRatioMoment 3 M W
  rw [hSnorm, hExpand, gmDiscreteRatioMoment_eq_iterated]
  calc
    ‖∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        star (b n) * b m *
          (Complex.exp ((((s * (Real.log m - Real.log n) : ℝ) : ℂ) * I)) *
            gmRPhase W (Real.log m - Real.log n) ^ 2 *
              gmRPhase W (-(Real.log m - Real.log n)))‖ ≤
      ∑ n ∈ dyadicInterval M, ‖∑ m ∈ dyadicInterval M,
        star (b n) * b m *
          (Complex.exp ((((s * (Real.log m - Real.log n) : ℝ) : ℂ) * I)) *
            gmRPhase W (Real.log m - Real.log n) ^ 2 *
              gmRPhase W (-(Real.log m - Real.log n)))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        ‖star (b n) * b m *
          (Complex.exp ((((s * (Real.log m - Real.log n) : ℝ) : ℂ) * I)) *
            gmRPhase W (Real.log m - Real.log n) ^ 2 *
              gmRPhase W (-(Real.log m - Real.log n)))‖ := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_sum_le _ _
    _ ≤ ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        ‖gmR W ((n : ℝ) / m)‖ ^ 3 := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      have hnpos : 0 < n := hM.trans (Finset.mem_Ioc.mp hn).1
      have hmpos : 0 < m := hM.trans (Finset.mem_Ioc.mp hm).1
      have hmn : 0 < (m : ℝ) / n := by positivity
      have hnm : (n : ℝ) / m ≠ 0 := by positivity
      have hlog : Real.log ((m : ℝ) / n) = Real.log m - Real.log n := by
        rw [Real.log_div (by positivity) (by positivity)]
      have hRphase :
          ‖gmRPhase W (Real.log m - Real.log n)‖ =
            ‖gmR W ((n : ℝ) / m)‖ := by
        have hrecip : (m : ℝ) / n = 1 / ((n : ℝ) / m) := by
          field_simp
        calc
          ‖gmRPhase W (Real.log m - Real.log n)‖ =
              ‖gmR W ((m : ℝ) / n)‖ := by
            rw [gmR_eq_gmRPhase_log hmn.ne', abs_of_pos hmn, hlog]
          _ = ‖gmR W ((n : ℝ) / m)‖ := by
            rw [hrecip, norm_gmR_reciprocal W ((n : ℝ) / m) hnm]
      have hbn := hb n hn
      have hbm := hb m hm
      have hR0 : 0 ≤ ‖gmR W ((n : ℝ) / m)‖ := norm_nonneg _
      calc
        ‖star (b n) * b m *
            (Complex.exp ((((s * (Real.log m - Real.log n) : ℝ) : ℂ) * I)) *
              gmRPhase W (Real.log m - Real.log n) ^ 2 *
                gmRPhase W (-(Real.log m - Real.log n)))‖ =
            ‖b n‖ * ‖b m‖ * ‖gmR W ((n : ℝ) / m)‖ ^ 3 := by
          simp only [norm_mul, norm_star, Complex.norm_exp_ofReal_mul_I,
            norm_pow, norm_gmRPhase_neg, hRphase, one_mul]
          ring
        _ ≤ 1 * 1 * ‖gmR W ((n : ℝ) / m)‖ ^ 3 := by
          gcongr
        _ = _ := by ring
    _ = _ := rfl

/-- The possible fourth ordinates completing one tolerance-one additive
quadruple form a one-separated subset of an interval of length two, hence
there are at most three of them.  This is the finite packing fact used (and
usually suppressed) in Guth--Maynard Lemma 11.4. -/
theorem card_filter_abs_sub_le_one_le_three
    (W : Finset ℝ) (hSep : IsSeparated 1 W) (center : ℝ) :
    (W.filter fun t => |t - center| ≤ 1).card ≤ 3 := by
  let F := W.filter fun t => |t - center| ≤ 1
  let f : ℝ → ℤ := fun t => ⌊t - center⌋
  have hinj : Set.InjOn f (F : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hxF : x ∈ F := hx
    have hyF : y ∈ F := hy
    have hxW : x ∈ W := (Finset.mem_filter.mp hxF).1
    have hyW : y ∈ W := (Finset.mem_filter.mp hyF).1
    have hdist := hSep x hxW y hyW hne
    have hfloorX := Int.floor_le (x - center)
    have hfloorY := Int.floor_le (y - center)
    have hfloorX' := Int.lt_floor_add_one (x - center)
    have hfloorY' := Int.lt_floor_add_one (y - center)
    change ⌊x - center⌋ = ⌊y - center⌋ at hxy
    rw [hxy] at hfloorX hfloorX'
    have hxylt : |x - y| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    rw [Real.dist_eq] at hdist
    exact (not_lt_of_ge hdist) hxylt
  have hcardImage : F.card = (F.image f).card := by
    symm
    exact Finset.card_image_iff.mpr hinj
  have hsub : F.image f ⊆ Finset.Icc (-1 : ℤ) 1 := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨t, htF, rfl⟩ := hz
    have htAbs := (Finset.mem_filter.mp htF).2
    rw [abs_le] at htAbs
    rw [Finset.mem_Icc]
    constructor
    · apply Int.le_floor.mpr
      norm_num
      linarith
    · rw [Int.floor_le_iff]
      norm_num
      linarith
  calc
    F.card = (F.image f).card := hcardImage
    _ ≤ (Finset.Icc (-1 : ℤ) 1).card := Finset.card_le_card hsub
    _ = 3 := by rw [Int.card_Icc]; rfl

/-- Fiberwise summation form of the preceding packing lemma.  It converts a
sum over approximate additive quadruples into three times the corresponding
sum over the first three ordinates whenever the summand is independent of the
fourth ordinate. -/
theorem sum_approximateAdditiveQuadruples_le_three_mul_sum_triples
    (W : Finset ℝ) (hSep : IsSeparated 1 W) (g : ℝ → ℝ → ℝ → ℝ)
    (hg : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ∀ t₃ ∈ W, 0 ≤ g t₁ t₂ t₃) :
    (∑ q ∈ approximateAdditiveQuadruples 1 W,
        g q.1.1 q.1.2 q.2.1) ≤
      3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, g t₁ t₂ t₃ := by
  have hinner (t₁ t₂ t₃ : ℝ)
      (ht₁ : t₁ ∈ W) (ht₂ : t₂ ∈ W) (ht₃ : t₃ ∈ W) :
      (∑ t₄ ∈ W,
          if |t₁ + t₂ - t₃ - t₄| ≤ 1 then g t₁ t₂ t₃ else 0) ≤
        3 * g t₁ t₂ t₃ := by
    have hpred (t₄ : ℝ) :
        |t₁ + t₂ - t₃ - t₄| ≤ 1 ↔ |t₄ - (t₁ + t₂ - t₃)| ≤ 1 := by
      rw [abs_sub_comm]
    simp_rw [hpred]
    rw [← Finset.sum_filter]
    calc
      (∑ _t ∈ W.filter (fun t₄ => |t₄ - (t₁ + t₂ - t₃)| ≤ 1),
          g t₁ t₂ t₃) =
          ((W.filter fun t₄ => |t₄ - (t₁ + t₂ - t₃)| ≤ 1).card : ℝ) *
            g t₁ t₂ t₃ := by simp
      _ ≤ 3 * g t₁ t₂ t₃ := by
        gcongr
        · exact hg t₁ ht₁ t₂ ht₂ t₃ ht₃
        exact_mod_cast card_filter_abs_sub_le_one_le_three W hSep
          (t₁ + t₂ - t₃)
  unfold approximateAdditiveQuadruples
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [Finset.sum_product]
  calc
    (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ t₄ ∈ W,
        if |t₁ + t₂ - t₃ - t₄| ≤ 1 then g t₁ t₂ t₃ else 0) ≤
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, 3 * g t₁ t₂ t₃ := by
      apply Finset.sum_le_sum
      intro t₁ ht₁
      apply Finset.sum_le_sum
      intro t₂ ht₂
      apply Finset.sum_le_sum
      intro t₃ ht₃
      exact hinner t₁ t₂ t₃ ht₁ ht₂ ht₃
    _ = 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, g t₁ t₂ t₃ := by
      simp only [Finset.mul_sum]

/-- Finite Fubini for the three source-polynomial copies in Lemma 11.4. -/
theorem integral_sum_triple_sourceMoment
    {M : ℕ} (hM : 0 < M) (W : Finset ℝ) (b : ℕ → ℂ) (L : ℝ) :
    (∫ s : ℝ in Set.Icc (-L) L,
        ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2) =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ∫ s : ℝ in Set.Icc (-L) L,
          ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2 := by
  have hInt (t₁ t₂ t₃ : ℝ) : IntegrableOn (fun s : ℝ =>
      ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2)
      (Set.Icc (-L) L) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    apply Continuous.pow
    apply Continuous.norm
    unfold sourceDirichletPoly
    apply continuous_finsetSum
    intro n hn
    apply Continuous.const_mul
    apply Continuous.const_cpow
    · fun_prop
    · left
      exact_mod_cast (hM.trans (Finset.mem_Ioc.mp hn).1).ne'
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t₁ ht₁
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro t₂ ht₂
      rw [MeasureTheory.integral_finsetSum]
      intro t₃ ht₃
      exact hInt t₁ t₂ t₃
    · intro t₂ ht₂
      exact MeasureTheory.integrable_finsetSum _
        (fun t₃ _ => hInt t₁ t₂ t₃)
  · intro t₁ ht₁
    exact MeasureTheory.integrable_finsetSum _ fun t₂ _ =>
      MeasureTheory.integrable_finsetSum _ fun t₃ _ => hInt t₁ t₂ t₃

/-- Integrating the coefficient-uniform triple-moment bound over the common
reflection interval costs exactly its length `2L`. -/
theorem sum_triple_integral_sourceMoment_le
    {M : ℕ} (hM : 0 < M) (W : Finset ℝ) (b : ℕ → ℂ) (L : ℝ)
    (hL : 0 ≤ L) (hb : ∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) :
    (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ∫ s : ℝ in Set.Icc (-L) L,
          ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2) ≤
      (2 * L) * gmDiscreteRatioMoment 3 M W := by
  rw [← integral_sum_triple_sourceMoment hM W b L]
  have hPoint (s : ℝ) :
      (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2) ≤
        gmDiscreteRatioMoment 3 M W :=
    sum_triple_sourceMoment_le_discreteThirdMoment hM W b s hb
  have hSourceInt : IntegrableOn (fun s : ℝ =>
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
        ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2)
      (Set.Icc (-L) L) := by
    apply MeasureTheory.integrable_finsetSum
    intro t₁ ht₁
    apply MeasureTheory.integrable_finsetSum
    intro t₂ ht₂
    apply MeasureTheory.integrable_finsetSum
    intro t₃ ht₃
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    apply Continuous.pow
    apply Continuous.norm
    unfold sourceDirichletPoly
    apply continuous_finsetSum
    intro n hn
    apply Continuous.const_mul
    apply Continuous.const_cpow
    · fun_prop
    · left
      exact_mod_cast (hM.trans (Finset.mem_Ioc.mp hn).1).ne'
  calc
    (∫ s : ℝ in Set.Icc (-L) L,
        ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
          ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2) ≤
      ∫ _s : ℝ in Set.Icc (-L) L, gmDiscreteRatioMoment 3 M W := by
        apply MeasureTheory.setIntegral_mono_on
        · exact hSourceInt
        · exact MeasureTheory.integrableOn_const
            (hs := ne_of_lt (measure_Icc_lt_top :
              volume (Set.Icc (-L) L) < (⊤ : ENNReal)))
        · exact measurableSet_Icc
        · intro s hs
          exact hPoint s
    _ = (2 * L) * gmDiscreteRatioMoment 3 M W := by
      rw [MeasureTheory.setIntegral_const]
      simp only [smul_eq_mul]
      rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
      · ring
      · linarith

/-- Exact pre-asymptotic form of Guth--Maynard Lemma 11.4.  It starts from
the literal approximate-additive quadruples, uses the actual large-value
condition at their fourth ordinate, applies the common-interval smoothing
lemma, and ends at the genuine discrete third moment of `R`. -/
theorem approxAddEnergy_mul_largeValue_sq_le_thirdMoment_raw
    {A ε T V : ℝ} {M : ℕ} (W : Finset ℝ) (b : ℕ → ℂ)
    (hA : 0 < A) (hε : 0 < ε) (hT : 1 ≤ T) (hM : 0 < M)
    (hMT : (M : ℝ) ≤ T) (hV : 0 ≤ V) (hSep : IsSeparated 1 W)
    (hb : ∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1)
    (hLarge : ∀ t ∈ W, V ≤ ‖sourceDirichletPoly M b t‖) :
    (ApproxAddEnergy 1 W : ℝ) * V ^ 2 ≤
      6 * (gmAffineLocalBumpFourierSup / (2 * Real.pi)) ^ 2 *
          (2 * gmSection11CommonRadius (gmReflectionHeight T ε)) ^ 2 *
          gmDiscreteRatioMoment 3 M W +
        6 * (W.card : ℝ) ^ 3 *
          (gmAffineLocalBumpFourierTailConstant
            (gmReflectionDecayOrder A ε)
            (gmReflectionDecayOrder_two_le A ε) / T ^ A) ^ 2 := by
  let K : ℝ := gmAffineLocalBumpFourierSup / (2 * Real.pi)
  let L : ℝ := gmSection11CommonRadius (gmReflectionHeight T ε)
  let E : ℝ := gmAffineLocalBumpFourierTailConstant
    (gmReflectionDecayOrder A ε)
    (gmReflectionDecayOrder_two_le A ε) / T ^ A
  let g : ℝ → ℝ → ℝ → ℝ := fun t₁ t₂ t₃ =>
    2 * K ^ 2 * (2 * L) *
        (∫ s : ℝ in Set.Icc (-L) L,
          ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2) +
      2 * E ^ 2
  have hL : 0 ≤ L := by
    dsimp only [L, gmSection11CommonRadius, gmReflectionHeight]
    positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact (div_pos gmAffineLocalBumpFourierSup_pos (by positivity)).le
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact div_nonneg
      (gmAffineLocalBumpFourierTailConstant_pos _ _).le
      (Real.rpow_nonneg (zero_lt_one.trans_le hT).le _)
  have hEnergyLower :
      (ApproxAddEnergy 1 W : ℝ) * V ^ 2 ≤
        ∑ q ∈ approximateAdditiveQuadruples 1 W,
          ‖sourceDirichletPoly M b q.2.2‖ ^ 2 := by
    unfold ApproxAddEnergy
    calc
      ((approximateAdditiveQuadruples 1 W).card : ℝ) * V ^ 2 =
          ∑ _q ∈ approximateAdditiveQuadruples 1 W, V ^ 2 := by simp
      _ ≤ ∑ q ∈ approximateAdditiveQuadruples 1 W,
          ‖sourceDirichletPoly M b q.2.2‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hmem : q ∈ (W ×ˢ W) ×ˢ (W ×ˢ W) :=
          (Finset.mem_filter.mp hq).1
        have ht4 : q.2.2 ∈ W :=
          (Finset.mem_product.mp (Finset.mem_product.mp hmem).2).2
        exact pow_le_pow_left₀ hV (hLarge q.2.2 ht4) 2
  have hSmoothSum :
      (∑ q ∈ approximateAdditiveQuadruples 1 W,
          ‖sourceDirichletPoly M b q.2.2‖ ^ 2) ≤
        ∑ q ∈ approximateAdditiveQuadruples 1 W,
          g q.1.1 q.1.2 q.2.1 := by
    apply Finset.sum_le_sum
    intro q hq
    have hdefect := (Finset.mem_filter.mp hq).2
    have hs : |q.2.2 - (q.1.1 + q.1.2 - q.2.1)| ≤ 1 := by
      rw [abs_sub_comm]
      simpa only [sub_eq_add_neg, add_assoc] using hdefect
    have hRaw := sourceDirichletPoly_norm_sq_le_commonInterval_add_error
      hA hε hT hM hMT b (q.1.1 + q.1.2 - q.2.1)
        (q.2.2 - (q.1.1 + q.1.2 - q.2.1)) hs hb
    dsimp only [g, K, L, E]
    convert hRaw using 1
    ring
  have hg : ∀ t₁ ∈ W, ∀ t₂ ∈ W, ∀ t₃ ∈ W, 0 ≤ g t₁ t₂ t₃ := by
    intro t₁ ht₁ t₂ ht₂ t₃ ht₃
    dsimp only [g]
    have hInt : 0 ≤ ∫ s : ℝ in Set.Icc (-L) L,
        ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2 := by
      apply MeasureTheory.setIntegral_nonneg measurableSet_Icc
      intro s hs
      positivity
    positivity
  have hFiber := sum_approximateAdditiveQuadruples_le_three_mul_sum_triples
    W hSep g hg
  have hTriple := sum_triple_integral_sourceMoment_le hM W b L hL hb
  calc
    (ApproxAddEnergy 1 W : ℝ) * V ^ 2 ≤
        ∑ q ∈ approximateAdditiveQuadruples 1 W,
          ‖sourceDirichletPoly M b q.2.2‖ ^ 2 := hEnergyLower
    _ ≤ ∑ q ∈ approximateAdditiveQuadruples 1 W,
          g q.1.1 q.1.2 q.2.1 := hSmoothSum
    _ ≤ 3 * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, g t₁ t₂ t₃ := hFiber
    _ = 3 * (2 * K ^ 2 * (2 * L) *
          (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
            ∫ s : ℝ in Set.Icc (-L) L,
              ‖sourceDirichletPoly M b (t₁ + t₂ - t₃ + s)‖ ^ 2) +
          2 * E ^ 2 * (W.card : ℝ) ^ 3) := by
      dsimp only [g]
      simp only [Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 3 * (2 * K ^ 2 * (2 * L) *
          ((2 * L) * gmDiscreteRatioMoment 3 M W) +
          2 * E ^ 2 * (W.card : ℝ) ^ 3) := by
      gcongr
    _ = 6 * K ^ 2 * (2 * L) ^ 2 * gmDiscreteRatioMoment 3 M W +
          6 * (W.card : ℝ) ^ 3 * E ^ 2 := by ring
    _ = _ := by rfl

/-- The diagonal pair `n=m=M+1` already contributes `|W|^3` to the
discrete third moment.  This absorbs the complete smoothing tail in the
epsilon form of Lemma 11.4. -/
theorem card_cubed_le_gmDiscreteRatioMoment_three
    {M : ℕ} (hM : 0 < M) (W : Finset ℝ) :
    (W.card : ℝ) ^ 3 ≤ gmDiscreteRatioMoment 3 M W := by
  let n₀ : ℕ := M + 1
  have hn₀ : n₀ ∈ dyadicInterval M := by
    dsimp only [n₀, dyadicInterval]
    rw [Finset.mem_Ioc]
    omega
  rw [gmDiscreteRatioMoment_eq_iterated]
  have hdiag :
      ‖gmR W ((n₀ : ℝ) / n₀)‖ ^ 3 = (W.card : ℝ) ^ 3 := by
    have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast (Nat.zero_lt_succ M)
    rw [div_self hn₀pos.ne', gmR_one]
    norm_num
  calc
    (W.card : ℝ) ^ 3 = ‖gmR W ((n₀ : ℝ) / n₀)‖ ^ 3 := hdiag.symm
    _ ≤ ∑ m ∈ dyadicInterval M, ‖gmR W ((n₀ : ℝ) / m)‖ ^ 3 := by
      exact Finset.single_le_sum (s := dyadicInterval M)
        (f := fun m : ℕ => ‖gmR W ((n₀ : ℝ) / (m : ℝ))‖ ^ 3)
        (fun m hm => pow_nonneg (norm_nonneg _) 3) hn₀
    _ ≤ ∑ n ∈ dyadicInterval M, ∑ m ∈ dyadicInterval M,
        ‖gmR W ((n : ℝ) / m)‖ ^ 3 := by
      exact Finset.single_le_sum (s := dyadicInterval M)
        (f := fun n : ℕ => ∑ m ∈ dyadicInterval M,
          ‖gmR W ((n : ℝ) / (m : ℝ))‖ ^ 3)
        (fun n hn => Finset.sum_nonneg fun m hm =>
          pow_nonneg (norm_nonneg _) 3) hn₀

/-- Guth--Maynard Lemma 11.4 in its epsilon-uniform native form.  The
large-value threshold remains explicit on the left, which is equivalent to
the paper's `N^{-2σ}` formulation after setting `V=N^σ`. -/
theorem gmApproxAddEnergy_largeValues_native :
    ∀ ε : ℝ, 0 < ε →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ (M : ℕ) (T V : ℝ) (W : Finset ℝ) (b : ℕ → ℂ),
          0 < M → T₀ ≤ T → (M : ℝ) ≤ T → 0 ≤ V →
          IsSeparated 1 W →
          (∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) →
          (∀ t ∈ W, V ≤ ‖sourceDirichletPoly M b t‖) →
          (ApproxAddEnergy 1 W : ℝ) * V ^ 2 ≤
            C * T ^ ε * gmDiscreteRatioMoment 3 M W := by
  intro ε hε
  let K : ℝ := gmAffineLocalBumpFourierSup / (2 * Real.pi)
  let D : ℝ := 1 + 2 * Real.pi
  let E₀ : ℝ := gmAffineLocalBumpFourierTailConstant
    (gmReflectionDecayOrder 100 ε)
    (gmReflectionDecayOrder_two_le 100 ε)
  let Cmain : ℝ := 6 * K ^ 2 * (2 * D) ^ 2
  let Ctail : ℝ := 6 * E₀ ^ 2
  let C : ℝ := Cmain + Ctail
  refine ⟨C, 1, ?_, le_rfl, ?_⟩
  · dsimp only [C, Cmain, Ctail, K, D, E₀]
    have hSup := gmAffineLocalBumpFourierSup_pos
    have hTail := gmAffineLocalBumpFourierTailConstant_pos
      (gmReflectionDecayOrder 100 ε) (gmReflectionDecayOrder_two_le 100 ε)
    positivity
  intro M T V W b hM hT hMT hV hSep hb hLarge
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hRaw := approxAddEnergy_mul_largeValue_sq_le_thirdMoment_raw
    W b (A := (100 : ℝ)) (ε := ε) (T := T) (V := V)
      (by norm_num) hε hT hM hMT hV hSep hb hLarge
  let L : ℝ := gmSection11CommonRadius (gmReflectionHeight T ε)
  have hL0 : 0 ≤ L := by
    dsimp only [L, gmSection11CommonRadius, gmReflectionHeight]
    positivity
  have hL : L ≤ D * T ^ (ε / 16) := by
    simpa only [L, D] using gmSection11CommonRadius_le_epsilonPower hε hT
  have hTwoLSq :
      (2 * L) ^ 2 ≤ (2 * D) ^ 2 * T ^ (ε / 8) := by
    calc
      (2 * L) ^ 2 ≤ (2 * (D * T ^ (ε / 16))) ^ 2 := by
        gcongr
      _ = (2 * D) ^ 2 * (T ^ (ε / 16)) ^ 2 := by ring
      _ = (2 * D) ^ 2 * T ^ (ε / 8) := by
        congr 1
        calc
          (T ^ (ε / 16)) ^ 2 = (T ^ (ε / 16)) ^ (2 : ℝ) := by
            rw [Real.rpow_two]
          _ = T ^ ((ε / 16) * 2) := by rw [Real.rpow_mul hTpos.le]
          _ = T ^ (ε / 8) := by congr 1; ring
  have hPowEighth : T ^ (ε / 8) ≤ T ^ ε := by
    apply Real.rpow_le_rpow_of_exponent_le hT
    linarith
  have hMoment0 : 0 ≤ gmDiscreteRatioMoment 3 M W := by
    unfold gmDiscreteRatioMoment
    positivity
  have hMain :
      6 * K ^ 2 * (2 * L) ^ 2 * gmDiscreteRatioMoment 3 M W ≤
        Cmain * T ^ ε * gmDiscreteRatioMoment 3 M W := by
    have hScale : (2 * L) ^ 2 ≤ (2 * D) ^ 2 * T ^ ε :=
      hTwoLSq.trans (mul_le_mul_of_nonneg_left hPowEighth (by positivity))
    dsimp only [Cmain]
    calc
      6 * K ^ 2 * (2 * L) ^ 2 * gmDiscreteRatioMoment 3 M W ≤
          6 * K ^ 2 * ((2 * D) ^ 2 * T ^ ε) *
            gmDiscreteRatioMoment 3 M W := by gcongr
      _ = 6 * K ^ 2 * (2 * D) ^ 2 * T ^ ε *
            gmDiscreteRatioMoment 3 M W := by ring
  have hTpow100 : 1 ≤ T ^ (100 : ℝ) :=
    Real.one_le_rpow hT (by norm_num)
  have hTailFrac : E₀ / T ^ (100 : ℝ) ≤ E₀ := by
    apply div_le_self
    · dsimp only [E₀]
      exact (gmAffineLocalBumpFourierTailConstant_pos _ _).le
    · exact hTpow100
  have hTailFrac0 : 0 ≤ E₀ / T ^ (100 : ℝ) := by
    dsimp only [E₀]
    exact div_nonneg
      (gmAffineLocalBumpFourierTailConstant_pos _ _).le
      (Real.rpow_nonneg hTpos.le _)
  have hTailSq : (E₀ / T ^ (100 : ℝ)) ^ 2 ≤ E₀ ^ 2 :=
    pow_le_pow_left₀ hTailFrac0 hTailFrac 2
  have hCard := card_cubed_le_gmDiscreteRatioMoment_three hM W
  have hOnePow : 1 ≤ T ^ ε := Real.one_le_rpow hT hε.le
  have hTail :
      6 * (W.card : ℝ) ^ 3 * (E₀ / T ^ (100 : ℝ)) ^ 2 ≤
        Ctail * T ^ ε * gmDiscreteRatioMoment 3 M W := by
    dsimp only [Ctail]
    calc
      _ ≤ 6 * (W.card : ℝ) ^ 3 * E₀ ^ 2 := by gcongr
      _ ≤ 6 * gmDiscreteRatioMoment 3 M W * E₀ ^ 2 := by gcongr
      _ ≤ 6 * (T ^ ε * gmDiscreteRatioMoment 3 M W) * E₀ ^ 2 := by
        gcongr
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hOnePow hMoment0)
      _ = 6 * E₀ ^ 2 * T ^ ε * gmDiscreteRatioMoment 3 M W := by ring
  change (ApproxAddEnergy 1 W : ℝ) * V ^ 2 ≤
      6 * K ^ 2 * (2 * L) ^ 2 * gmDiscreteRatioMoment 3 M W +
        6 * (W.card : ℝ) ^ 3 * (E₀ / T ^ (100 : ℝ)) ^ 2 at hRaw
  calc
    (ApproxAddEnergy 1 W : ℝ) * V ^ 2 ≤ _ := hRaw
    _ ≤ Cmain * T ^ ε * gmDiscreteRatioMoment 3 M W +
        Ctail * T ^ ε * gmDiscreteRatioMoment 3 M W := add_le_add hMain hTail
    _ = C * T ^ ε * gmDiscreteRatioMoment 3 M W := by
      dsimp only [C]
      ring

/-! ## Local sampling for the small-GCD part of Section 11 -/

noncomputable def gmFiniteExpSum
    {α : Type*} (S : Finset α) (c : α → ℂ) (freq : α → ℝ) (x : ℝ) : ℂ :=
  ∑ a ∈ S, c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I)

theorem continuous_gmFiniteExpSum
    {α : Type*} (S : Finset α) (c : α → ℂ) (freq : α → ℝ) :
    Continuous (gmFiniteExpSum S c freq) := by
  unfold gmFiniteExpSum
  fun_prop

theorem norm_gmFiniteExpSum_le_coeffMass
    {α : Type*} (S : Finset α) (c : α → ℂ) (freq : α → ℝ) (x : ℝ) :
    ‖gmFiniteExpSum S c freq x‖ ≤ ∑ a ∈ S, ‖c a‖ := by
  unfold gmFiniteExpSum
  calc
    ‖∑ a ∈ S, c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I)‖ ≤
        ∑ a ∈ S, ‖c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I)‖ :=
      norm_sum_le _ _
    _ = ∑ a ∈ S, ‖c a‖ := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- A finite exponential polynomial whose frequencies lie in `[-B*T,B*T]`
is reproduced exactly from translates on the physical scale `(B*T)⁻¹`.
This is the additive-coordinate form of the Fourier identity in the proof
of Guth--Maynard Lemma 11.7. -/
theorem finiteExpSum_fourier_reproduction
    {α : Type*} [DecidableEq α] (S : Finset α) (c : α → ℂ)
    (freq : α → ℝ) {B T : ℝ} (hBT : 0 < B * T)
    (hfreq : ∀ a ∈ S, |freq a| ≤ B * T) (x : ℝ) :
    (∑ a ∈ S, c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I)) =
      ∫ ξ : ℝ, 𝓕 gmAffineLocalBumpSchwartz ξ *
        ∑ a ∈ S, c a *
          Complex.exp ((((freq a) *
            (x + 2 * Real.pi * ξ / (B * T)) : ℝ) : ℂ) * I) := by
  have hinversion (u : ℝ) :
      gmAffineLocalBumpSchwartz u =
        ∫ ξ : ℝ,
          Complex.exp (((2 * Real.pi * (ξ * u) : ℝ) : ℂ) * I) *
            𝓕 gmAffineLocalBumpSchwartz ξ := by
    have hpairMap : 𝓕⁻ (𝓕 gmAffineLocalBumpSchwartz) =
        gmAffineLocalBumpSchwartz :=
      FourierTransform.fourierInv_fourier_eq gmAffineLocalBumpSchwartz
    have hpair := congrArg
      (fun g : SchwartzMap ℝ ℂ => g u) hpairMap
    change (𝓕⁻ (𝓕 gmAffineLocalBumpSchwartz)) u =
      gmAffineLocalBumpSchwartz u at hpair
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hpair
    simpa only [Real.inner_apply, smul_eq_mul] using hpair.symm
  have hone (a : α) (ha : a ∈ S) :
      gmAffineLocalBumpSchwartz (freq a / (B * T)) = 1 := by
    rw [gmAffineLocalBumpSchwartz_apply]
    have habs : |freq a / (B * T)| ≤ 1 := by
      rw [abs_div, abs_of_pos hBT]
      exact (div_le_one hBT).2 (hfreq a ha)
    rw [gmCubicLocalBump_one habs]
    norm_num
  have hInt (a : α) : Integrable (fun ξ : ℝ =>
      c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I) *
        (Complex.exp (((2 * Real.pi *
          (ξ * (freq a / (B * T))) : ℝ) : ℂ) * I) *
          𝓕 gmAffineLocalBumpSchwartz ξ)) := by
    let g : ℝ → ℂ := fun ξ =>
      c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I) *
        Complex.exp (((2 * Real.pi *
          (ξ * (freq a / (B * T))) : ℝ) : ℂ) * I)
    have hg : Continuous g := by
      dsimp only [g]
      fun_prop
    have hbounded : ∀ᵐ ξ : ℝ ∂volume, ‖g ξ‖ ≤ ‖c a‖ := by
      filter_upwards with ξ
      dsimp only [g]
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact le_rfl
    have hbase := (𝓕 gmAffineLocalBumpSchwartz).integrable.mul_bdd
      (c := ‖c a‖) hg.aestronglyMeasurable hbounded
    simpa only [g, mul_assoc, mul_left_comm, mul_comm] using hbase
  calc
    (∑ a ∈ S, c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I)) =
        ∑ a ∈ S, c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I) *
          gmAffineLocalBumpSchwartz (freq a / (B * T)) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hone a ha, mul_one]
    _ = ∑ a ∈ S, c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I) *
          (∫ ξ : ℝ,
            Complex.exp (((2 * Real.pi *
              (ξ * (freq a / (B * T))) : ℝ) : ℂ) * I) *
              𝓕 gmAffineLocalBumpSchwartz ξ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hinversion]
    _ = ∑ a ∈ S, ∫ ξ : ℝ,
          c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I) *
            (Complex.exp (((2 * Real.pi *
              (ξ * (freq a / (B * T))) : ℝ) : ℂ) * I) *
              𝓕 gmAffineLocalBumpSchwartz ξ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [MeasureTheory.integral_const_mul]
    _ = ∫ ξ : ℝ, ∑ a ∈ S,
          c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I) *
            (Complex.exp (((2 * Real.pi *
              (ξ * (freq a / (B * T))) : ℝ) : ℂ) * I) *
              𝓕 gmAffineLocalBumpSchwartz ξ) := by
      rw [MeasureTheory.integral_finsetSum]
      intro a ha
      exact hInt a
    _ = ∫ ξ : ℝ, 𝓕 gmAffineLocalBumpSchwartz ξ *
        ∑ a ∈ S, c a *
          Complex.exp ((((freq a) *
            (x + 2 * Real.pi * ξ / (B * T)) : ℝ) : ℂ) * I) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      calc
        c a * Complex.exp ((((freq a) * x : ℝ) : ℂ) * I) *
              (Complex.exp (((2 * Real.pi *
                (ξ * (freq a / (B * T))) : ℝ) : ℂ) * I) *
                𝓕 gmAffineLocalBumpSchwartz ξ) =
            𝓕 gmAffineLocalBumpSchwartz ξ *
              (c a * (Complex.exp ((((freq a) * x : ℝ) : ℂ) * I) *
                Complex.exp (((2 * Real.pi *
                  (ξ * (freq a / (B * T))) : ℝ) : ℂ) * I))) := by ring
        _ = 𝓕 gmAffineLocalBumpSchwartz ξ *
              (c a * Complex.exp
                (((freq a * (x + 2 * Real.pi * ξ / (B * T)) : ℝ) : ℂ) * I)) := by
          congr 2
          rw [← Complex.exp_add]
          congr 1
          push_cast
          field_simp [hBT.ne']

theorem integrable_finiteExpSum_fourier_kernel
    {α : Type*} [DecidableEq α] (S : Finset α) (c : α → ℂ)
    (freq : α → ℝ) {B T : ℝ} (_hBT : 0 < B * T) (x : ℝ) :
    Integrable (fun ξ : ℝ => 𝓕 gmAffineLocalBumpSchwartz ξ *
      gmFiniteExpSum S c freq (x + 2 * Real.pi * ξ / (B * T))) := by
  let mass : ℝ := ∑ a ∈ S, ‖c a‖
  have hcont : Continuous (fun ξ : ℝ =>
      gmFiniteExpSum S c freq (x + 2 * Real.pi * ξ / (B * T))) :=
    (continuous_gmFiniteExpSum S c freq).comp (by fun_prop)
  have hbound : ∀ᵐ ξ : ℝ ∂volume,
      ‖gmFiniteExpSum S c freq (x + 2 * Real.pi * ξ / (B * T))‖ ≤ mass := by
    filter_upwards with ξ
    exact norm_gmFiniteExpSum_le_coeffMass S c freq _
  exact (𝓕 gmAffineLocalBumpSchwartz).integrable.mul_bdd
    hcont.aestronglyMeasurable hbound

/-- Complete local-plus-tail estimate for a finite band-limited
exponential polynomial.  No asymptotic notation is hidden: the omitted
Fourier mass is the explicit fixed Schwartz-tail constant. -/
theorem norm_gmFiniteExpSum_le_localFourier_add_tail
    {α : Type*} [DecidableEq α] (S : Finset α) (c : α → ℂ)
    (freq : α → ℝ) {B T : ℝ} (hBT : 0 < B * T)
    (hfreq : ∀ a ∈ S, |freq a| ≤ B * T) (x H : ℝ)
    (hH : 1 ≤ H) (q : ℕ) (hq : 2 ≤ q) :
    ‖gmFiniteExpSum S c freq x‖ ≤
      (∫ ξ : ℝ in Set.Icc (-H) H,
        ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
          ‖gmFiniteExpSum S c freq
            (x + 2 * Real.pi * ξ / (B * T))‖) +
      (∑ a ∈ S, ‖c a‖) *
        gmAffineLocalBumpFourierTailConstant q hq *
          H ^ (1 - (q : ℝ)) := by
  let mass : ℝ := ∑ a ∈ S, ‖c a‖
  let C : ℝ := gmAffineLocalBumpFourierTailConstant q hq
  let f : ℝ → ℂ := fun ξ => 𝓕 gmAffineLocalBumpSchwartz ξ *
    gmFiniteExpSum S c freq (x + 2 * Real.pi * ξ / (B * T))
  have hf : Integrable f := by
    simpa only [f] using
      integrable_finiteExpSum_fourier_kernel S c freq hBT x
  have hrepr : gmFiniteExpSum S c freq x = ∫ ξ : ℝ, f ξ := by
    simpa only [gmFiniteExpSum, f] using
      finiteExpSum_fourier_reproduction S c freq hBT hfreq x
  have hsplit := integral_add_compl
    (s := Set.Icc (-H) H) measurableSet_Icc hf
  have hTailNorm : ‖∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, f ξ‖ ≤
      mass * C * H ^ (1 - (q : ℝ)) := by
    calc
      ‖∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, f ξ‖ ≤
          ∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, ‖f ξ‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ,
          mass * ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ := by
        apply integral_mono_ae hf.norm.integrableOn
          ((𝓕 gmAffineLocalBumpSchwartz).integrable.norm.const_mul mass).integrableOn
        filter_upwards with ξ
        dsimp only [f]
        rw [norm_mul]
        have hp := norm_gmFiniteExpSum_le_coeffMass S c freq
          (x + 2 * Real.pi * ξ / (B * T))
        simpa only [mass, mul_comm] using
          mul_le_mul_of_nonneg_left hp
            (norm_nonneg (𝓕 gmAffineLocalBumpSchwartz ξ))
      _ = mass * (∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ,
          ‖𝓕 gmAffineLocalBumpSchwartz ξ‖) := by
        rw [integral_const_mul]
      _ ≤ mass * (C * H ^ (1 - (q : ℝ))) := by
        gcongr
        exact gmAffineLocalBumpFourierTailConstant_bound q hq H hH
      _ = mass * C * H ^ (1 - (q : ℝ)) := by ring
  calc
    ‖gmFiniteExpSum S c freq x‖ =
        ‖(∫ ξ : ℝ in Set.Icc (-H) H, f ξ) +
          (∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, f ξ)‖ := by
      exact (congrArg norm hrepr).trans (congrArg norm hsplit.symm)
    _ ≤ ‖∫ ξ : ℝ in Set.Icc (-H) H, f ξ‖ +
          ‖∫ ξ : ℝ in (Set.Icc (-H) H)ᶜ, f ξ‖ := by
      exact norm_add_le _ _
    _ ≤ (∫ ξ : ℝ in Set.Icc (-H) H, ‖f ξ‖) +
          mass * C * H ^ (1 - (q : ℝ)) := by
      exact add_le_add (norm_integral_le_integral_norm _) hTailNorm
    _ = (∫ ξ : ℝ in Set.Icc (-H) H,
          ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
            ‖gmFiniteExpSum S c freq
              (x + 2 * Real.pi * ξ / (B * T))‖) +
          mass * C * H ^ (1 - (q : ℝ)) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      intro ξ hξ
      dsimp only [f]
      rw [norm_mul]
    _ = _ := rfl

/-- Physical-neighbourhood form of the preceding Fourier estimate.  The
Jacobian `B*T/(2π)` is explicit, as is the radius `2πH/(B*T)`. -/
theorem norm_gmFiniteExpSum_le_localIntegral_add_tail
    {α : Type*} [DecidableEq α] (S : Finset α) (c : α → ℂ)
    (freq : α → ℝ) {B T : ℝ} (hBT : 0 < B * T)
    (hfreq : ∀ a ∈ S, |freq a| ≤ B * T) (x H : ℝ)
    (hH : 1 ≤ H) (q : ℕ) (hq : 2 ≤ q) :
    ‖gmFiniteExpSum S c freq x‖ ≤
      gmAffineLocalBumpFourierSup * (B * T / (2 * Real.pi)) *
        (∫ y : ℝ in Set.Icc
          (x - 2 * Real.pi * H / (B * T))
          (x + 2 * Real.pi * H / (B * T)),
          ‖gmFiniteExpSum S c freq y‖) +
      (∑ a ∈ S, ‖c a‖) *
        gmAffineLocalBumpFourierTailConstant q hq *
          H ^ (1 - (q : ℝ)) := by
  let scale : ℝ := 2 * Real.pi / (B * T)
  let g : ℝ → ℝ := fun y => ‖gmFiniteExpSum S c freq y‖
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact div_pos (mul_pos (by norm_num) Real.pi_pos) hBT
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hLocalInt : IntegrableOn (fun ξ : ℝ =>
      ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
        ‖gmFiniteExpSum S c freq
          (x + 2 * Real.pi * ξ / (B * T))‖) (Set.Icc (-H) H) := by
    apply ContinuousOn.integrableOn_Icc
    apply Continuous.continuousOn
    apply Continuous.mul
    · exact (𝓕 gmAffineLocalBumpSchwartz).continuous.norm
    · exact (continuous_gmFiniteExpSum S c freq).norm.comp (by fun_prop)
  have hMajorInt : IntegrableOn (fun ξ : ℝ =>
      gmAffineLocalBumpFourierSup * g (scale * ξ + x))
      (Set.Icc (-H) H) := by
    apply ContinuousOn.integrableOn_Icc
    exact (continuous_const.mul
      ((continuous_gmFiniteExpSum S c freq).norm.comp (by fun_prop))).continuousOn
  have hPoint (ξ : ℝ) :
      ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
          ‖gmFiniteExpSum S c freq
            (x + 2 * Real.pi * ξ / (B * T))‖ ≤
        gmAffineLocalBumpFourierSup * g (scale * ξ + x) := by
    have hw := norm_gmAffineLocalBumpFourier_le ξ
    have hn : 0 ≤ ‖gmFiniteExpSum S c freq
        (x + 2 * Real.pi * ξ / (B * T))‖ := norm_nonneg _
    have hm := mul_le_mul_of_nonneg_right hw hn
    dsimp only [g, scale]
    have harg : 2 * Real.pi / (B * T) * ξ + x =
        x + 2 * Real.pi * ξ / (B * T) := by ring
    rw [harg]
    exact hm
  have hLocal :
      (∫ ξ : ℝ in Set.Icc (-H) H,
        ‖𝓕 gmAffineLocalBumpSchwartz ξ‖ *
          ‖gmFiniteExpSum S c freq
            (x + 2 * Real.pi * ξ / (B * T))‖) ≤
        gmAffineLocalBumpFourierSup *
          (B * T / (2 * Real.pi)) *
            (∫ y : ℝ in Set.Icc
              (x - 2 * Real.pi * H / (B * T))
              (x + 2 * Real.pi * H / (B * T)),
              ‖gmFiniteExpSum S c freq y‖) := by
    calc
      _ ≤ ∫ ξ : ℝ in Set.Icc (-H) H,
          gmAffineLocalBumpFourierSup * g (scale * ξ + x) :=
        setIntegral_mono hLocalInt hMajorInt hPoint
      _ = gmAffineLocalBumpFourierSup *
          (∫ ξ : ℝ in Set.Icc (-H) H, g (scale * ξ + x)) := by
        rw [integral_const_mul]
      _ = gmAffineLocalBumpFourierSup *
          (scale⁻¹ * ∫ y : ℝ in Set.Icc
            (scale * (-H) + x) (scale * H + x), g y) := by
        rw [setIntegral_Icc_comp_mul_add g (by linarith) hscale]
      _ = gmAffineLocalBumpFourierSup *
          (B * T / (2 * Real.pi)) *
            (∫ y : ℝ in Set.Icc
              (x - 2 * Real.pi * H / (B * T))
              (x + 2 * Real.pi * H / (B * T)),
              ‖gmFiniteExpSum S c freq y‖) := by
        dsimp only [scale, g]
        have hpi : (2 * Real.pi : ℝ) ≠ 0 :=
          mul_ne_zero (by norm_num) Real.pi_ne_zero
        have hbt : B * T ≠ 0 := hBT.ne'
        field_simp [hpi, hbt]
        ring
  have hRaw := norm_gmFiniteExpSum_le_localFourier_add_tail
    S c freq hBT hfreq x H hH q hq
  exact hRaw.trans (add_le_add hLocal le_rfl)

theorem gmRPhase_sq_eq_gmFiniteExpSum (W : Finset ℝ) (x : ℝ) :
    ((‖gmRPhase W x‖ ^ 2 : ℝ) : ℂ) =
      gmFiniteExpSum (W ×ˢ W) (fun _ => (1 : ℂ))
        (fun p => p.1 - p.2) x := by
  rw [norm_gmRPhase_sq_expand]
  unfold gmFiniteExpSum
  rw [Finset.sum_product]
  simp

theorem gmRPhase_fourth_eq_gmFiniteExpSum (W : Finset ℝ) (x : ℝ) :
    ((‖gmRPhase W x‖ ^ 4 : ℝ) : ℂ) =
      gmFiniteExpSum ((W ×ˢ W) ×ˢ (W ×ˢ W)) (fun _ => (1 : ℂ))
        (fun q => q.1.1 + q.1.2 - q.2.1 - q.2.2) x := by
  rw [norm_gmRPhase_fourth_expand]
  unfold gmFiniteExpSum
  simp_rw [Finset.sum_product]
  simp

theorem gmRPhase_pair_frequency_le
    {T : ℝ} {W : Finset ℝ} (hBase : InBaseInterval T W)
    (p : ℝ × ℝ) (hp : p ∈ W ×ˢ W) : |p.1 - p.2| ≤ T := by
  have hp' := Finset.mem_product.mp hp
  have h₁ := hBase p.1 hp'.1
  have h₂ := hBase p.2 hp'.2
  rw [abs_le]
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

theorem gmRPhase_quad_frequency_le
    {T : ℝ} {W : Finset ℝ} (hBase : InBaseInterval T W)
    (q : (ℝ × ℝ) × (ℝ × ℝ)) (hq : q ∈ (W ×ˢ W) ×ˢ (W ×ˢ W)) :
    |q.1.1 + q.1.2 - q.2.1 - q.2.2| ≤ 2 * T := by
  have hq' := Finset.mem_product.mp hq
  have h₁₂ := Finset.mem_product.mp hq'.1
  have h₃₄ := Finset.mem_product.mp hq'.2
  have h₁ := hBase q.1.1 h₁₂.1
  have h₂ := hBase q.1.2 h₁₂.2
  have h₃ := hBase q.2.1 h₃₄.1
  have h₄ := hBase q.2.2 h₃₄.2
  rw [abs_le]
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2,
    h₃.1, h₃.2, h₄.1, h₄.2]

/-- Lemma 11.7 specialized to the literal second moment of `R`. -/
theorem norm_gmRPhase_sq_le_localIntegral_add_tail
    {T : ℝ} (hT : 0 < T) {W : Finset ℝ} (hBase : InBaseInterval T W)
    (x H : ℝ) (hH : 1 ≤ H) (q : ℕ) (hq : 2 ≤ q) :
    ‖gmRPhase W x‖ ^ 2 ≤
      gmAffineLocalBumpFourierSup * (T / (2 * Real.pi)) *
        (∫ y : ℝ in Set.Icc
          (x - 2 * Real.pi * H / T) (x + 2 * Real.pi * H / T),
          ‖gmRPhase W y‖ ^ 2) +
      (W.card : ℝ) ^ 2 *
        gmAffineLocalBumpFourierTailConstant q hq *
          H ^ (1 - (q : ℝ)) := by
  have hRaw := norm_gmFiniteExpSum_le_localIntegral_add_tail
    (W ×ˢ W) (fun _ => (1 : ℂ)) (fun p : ℝ × ℝ => p.1 - p.2)
      (B := (1 : ℝ)) (T := T) (by simpa using hT)
      (by intro p hp; simpa using gmRPhase_pair_frequency_le hBase p hp)
      x H hH q hq
  have hpoint (y : ℝ) :
      ‖gmFiniteExpSum (W ×ˢ W) (fun _ => (1 : ℂ))
        (fun p : ℝ × ℝ => p.1 - p.2) y‖ = ‖gmRPhase W y‖ ^ 2 := by
    rw [← gmRPhase_sq_eq_gmFiniteExpSum]
    simp
  simp_rw [hpoint] at hRaw
  simp only [Finset.card_product, Nat.cast_mul, norm_one,
    Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at hRaw
  have hcard : (W.card : ℝ) * W.card = (W.card : ℝ) ^ 2 := by ring
  rw [hcard] at hRaw
  exact hRaw

/-- Lemma 11.7 specialized to the literal fourth moment of `R`. -/
theorem norm_gmRPhase_fourth_le_localIntegral_add_tail
    {T : ℝ} (hT : 0 < T) {W : Finset ℝ} (hBase : InBaseInterval T W)
    (x H : ℝ) (hH : 1 ≤ H) (q : ℕ) (hq : 2 ≤ q) :
    ‖gmRPhase W x‖ ^ 4 ≤
      gmAffineLocalBumpFourierSup * (2 * T / (2 * Real.pi)) *
        (∫ y : ℝ in Set.Icc
          (x - 2 * Real.pi * H / (2 * T))
          (x + 2 * Real.pi * H / (2 * T)),
          ‖gmRPhase W y‖ ^ 4) +
      (W.card : ℝ) ^ 4 *
        gmAffineLocalBumpFourierTailConstant q hq *
          H ^ (1 - (q : ℝ)) := by
  have hRaw := norm_gmFiniteExpSum_le_localIntegral_add_tail
    ((W ×ˢ W) ×ˢ (W ×ˢ W)) (fun _ => (1 : ℂ))
      (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        q.1.1 + q.1.2 - q.2.1 - q.2.2)
      (B := (2 : ℝ)) (T := T) (by positivity)
      (by intro z hz; simpa using gmRPhase_quad_frequency_le hBase z hz)
      x H hH q hq
  have hpoint (y : ℝ) :
      ‖gmFiniteExpSum ((W ×ˢ W) ×ˢ (W ×ˢ W))
        (fun _ => (1 : ℂ))
        (fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
          z.1.1 + z.1.2 - z.2.1 - z.2.2) y‖ =
        ‖gmRPhase W y‖ ^ 4 := by
    rw [← gmRPhase_fourth_eq_gmFiniteExpSum]
    simp
  simp_rw [hpoint] at hRaw
  simp only [Finset.card_product, Nat.cast_mul, norm_one,
    Finset.sum_const, nsmul_eq_mul, mul_one] at hRaw
  have hcard : (W.card : ℝ) * W.card * ((W.card : ℝ) * W.card) =
      (W.card : ℝ) ^ 4 := by ring
  rw [hcard] at hRaw
  exact hRaw

/-! ### One-dimensional packing on the logarithmic ratio line -/

/-- A finite `δ`-separated subset of an interval of radius `r` has at most
`2 * ceil (r / δ) + 1` elements.  The proof records the floor-bin injection
used implicitly in Guth--Maynard Lemma 11.8. -/
theorem card_filter_abs_sub_le_two_mul_ceil_add_one
    (S : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hSep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|)
    (center r : ℝ) (_hr : 0 ≤ r) :
    (S.filter fun x => |x - center| ≤ r).card ≤
      2 * Nat.ceil (r / δ) + 1 := by
  let F := S.filter fun x => |x - center| ≤ r
  let f : ℝ → ℤ := fun x => ⌊(x - center) / δ⌋
  let K : ℕ := Nat.ceil (r / δ)
  have hinj : Set.InjOn f (F : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hxF : x ∈ F := hx
    have hyF : y ∈ F := hy
    have hxS : x ∈ S := (Finset.mem_filter.mp hxF).1
    have hyS : y ∈ S := (Finset.mem_filter.mp hyF).1
    have hdist := hSep x hxS y hyS hne
    have hfloorX := Int.floor_le ((x - center) / δ)
    have hfloorY := Int.floor_le ((y - center) / δ)
    have hfloorX' := Int.lt_floor_add_one ((x - center) / δ)
    have hfloorY' := Int.lt_floor_add_one ((y - center) / δ)
    change ⌊(x - center) / δ⌋ = ⌊(y - center) / δ⌋ at hxy
    rw [hxy] at hfloorX hfloorX'
    have hxylt : |x - y| < δ := by
      rw [abs_lt]
      constructor
      · have h₁ : (y - center) / δ < (x - center) / δ + 1 := by
          linarith
        have h₂ : y - center < x - center + δ := by
          have h := (div_lt_iff₀ hδ).mp h₁
          calc
            y - center < ((x - center) / δ + 1) * δ := h
            _ = x - center + δ := by field_simp
        linarith
      · have h₁ : (x - center) / δ < (y - center) / δ + 1 := by
          linarith
        have h₂ : x - center < y - center + δ := by
          have h := (div_lt_iff₀ hδ).mp h₁
          calc
            x - center < ((y - center) / δ + 1) * δ := h
            _ = y - center + δ := by field_simp
        linarith
    exact (not_lt_of_ge hdist) hxylt
  have hcardImage : F.card = (F.image f).card := by
    symm
    exact Finset.card_image_iff.mpr hinj
  have hsub : F.image f ⊆ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hxF, rfl⟩ := hz
    have hxAbs := (Finset.mem_filter.mp hxF).2
    rw [abs_le] at hxAbs
    have hceil : r / δ ≤ (K : ℝ) := by
      dsimp only [K]
      exact Nat.le_ceil (r / δ)
    rw [Finset.mem_Icc]
    constructor
    · apply Int.le_floor.mpr
      have hdiv : -(K : ℝ) ≤ (x - center) / δ := by
        apply (le_div_iff₀ hδ).2
        have : -(K : ℝ) * δ ≤ -r := by
          have hm : r ≤ (K : ℝ) * δ := (div_le_iff₀ hδ).mp hceil
          linarith
        linarith
      exact_mod_cast hdiv
    · rw [Int.floor_le_iff]
      have hdiv : (x - center) / δ < (K : ℝ) + 1 := by
        have hxle : (x - center) / δ ≤ r / δ :=
          (div_le_div_iff_of_pos_right hδ).2 hxAbs.2
        exact hxle.trans_lt (hceil.trans_lt (lt_add_one _))
      exact_mod_cast hdiv
  calc
    F.card = (F.image f).card := hcardImage
    _ ≤ (Finset.Icc (-(K : ℤ)) (K : ℤ)).card := Finset.card_le_card hsub
    _ = 2 * K + 1 := by
      rw [Int.card_Icc]
      omega

/-- Real-valued version of the logarithmic packing bound. -/
theorem cast_card_filter_abs_sub_le_ratio
    (S : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hSep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|)
    (center r : ℝ) (hr : 0 ≤ r) :
    ((S.filter fun x => |x - center| ≤ r).card : ℝ) ≤
      2 * (r / δ) + 3 := by
  have hcard := card_filter_abs_sub_le_two_mul_ceil_add_one
    S hδ hSep center r hr
  have hceil : (Nat.ceil (r / δ) : ℝ) < r / δ + 1 := by
    exact Nat.ceil_lt_add_one (div_nonneg hr hδ.le)
  have hcardR : ((S.filter fun x => |x - center| ≤ r).card : ℝ) ≤
      2 * (Nat.ceil (r / δ) : ℝ) + 1 := by
    exact_mod_cast hcard
  exact hcardR.trans (by linarith)

/-! ### Reduced rational slices -/

/-- The exact reduced pairs arising from the `gcd = d` slice of
`(N,2N]²`.  Retaining the dilated inequalities avoids every floor/ceiling
ambiguity in the paper's shorthand `n₁',n₂' ∼ N/d`. -/
def gmReducedRatioPairs (N d : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (2 * N)) ×ˢ (Finset.Icc 1 (2 * N))).filter fun p =>
    N < d * p.1 ∧ d * p.1 ≤ 2 * N ∧
      N < d * p.2 ∧ d * p.2 ≤ 2 * N ∧ Nat.Coprime p.1 p.2

noncomputable def gmReducedLogRatios (N d : ℕ) : Finset ℝ :=
  (gmReducedRatioPairs N d).image fun p =>
    Real.log (p.1 : ℝ) - Real.log (p.2 : ℝ)

theorem gmReducedRatioPairs_fst_pos
    {N d : ℕ} {p : ℕ × ℕ} (hp : p ∈ gmReducedRatioPairs N d) :
    0 < p.1 := by
  have hcond := (Finset.mem_filter.mp hp).2
  exact Nat.pos_of_mul_pos_right (by
    simpa [mul_comm] using (lt_of_le_of_lt (Nat.zero_le N) hcond.1))

theorem gmReducedRatioPairs_snd_pos
    {N d : ℕ} {p : ℕ × ℕ} (hp : p ∈ gmReducedRatioPairs N d) :
    0 < p.2 := by
  have hcond := (Finset.mem_filter.mp hp).2
  exact Nat.pos_of_mul_pos_right
    (by simpa [mul_comm] using
      (lt_of_le_of_lt (Nat.zero_le N) hcond.2.2.1))

theorem gmReducedRatioPairs_coprime
    {N d : ℕ} {p : ℕ × ℕ} (hp : p ∈ gmReducedRatioPairs N d) :
    Nat.Coprime p.1 p.2 :=
  (Finset.mem_filter.mp hp).2.2.2.2.2

theorem gmReducedRatioPairs_dilate_snd_le
    {N d : ℕ} {p : ℕ × ℕ} (hp : p ∈ gmReducedRatioPairs N d) :
    d * p.2 ≤ 2 * N :=
  (Finset.mem_filter.mp hp).2.2.2.2.1

/-- A reduced positive fraction has a unique numerator/denominator pair. -/
theorem reduced_nat_ratio_injective
    {p q : ℕ × ℕ} (_hp₁ : 0 < p.1) (hp₂ : 0 < p.2)
    (hq₁ : 0 < q.1) (hq₂ : 0 < q.2)
    (hpCoprime : Nat.Coprime p.1 p.2)
    (hqCoprime : Nat.Coprime q.1 q.2)
    (hratio : (p.1 : ℝ) / p.2 = (q.1 : ℝ) / q.2) : p = q := by
  have hcrossR : (p.1 : ℝ) * q.2 = (q.1 : ℝ) * p.2 := by
    field_simp at hratio
    simpa [mul_comm] using hratio
  have hcross : p.1 * q.2 = q.1 * p.2 := by exact_mod_cast hcrossR
  have hpDvdQ : p.1 ∣ q.1 := by
    apply (hpCoprime.dvd_mul_right).mp
    exact ⟨q.2, by simpa [mul_comm] using hcross.symm⟩
  have hqDvdP : q.1 ∣ p.1 := by
    apply (hqCoprime.dvd_mul_right).mp
    exact ⟨p.2, by simpa [mul_comm] using hcross⟩
  have hfst : p.1 = q.1 := Nat.dvd_antisymm hpDvdQ hqDvdP
  have hsnd : p.2 = q.2 := by
    rw [hfst] at hcross
    exact Nat.mul_left_cancel hq₁ hcross.symm
  exact Prod.ext hfst hsnd

theorem gmReducedLogRatios_image_injective
    {N d : ℕ} : Set.InjOn
      (fun p : ℕ × ℕ => Real.log (p.1 : ℝ) - Real.log (p.2 : ℝ))
      (gmReducedRatioPairs N d : Set (ℕ × ℕ)) := by
  intro p hp q hq heq
  have hp₁ := gmReducedRatioPairs_fst_pos hp
  have hp₂ := gmReducedRatioPairs_snd_pos hp
  have hq₁ := gmReducedRatioPairs_fst_pos hq
  have hq₂ := gmReducedRatioPairs_snd_pos hq
  have hratio : (p.1 : ℝ) / p.2 = (q.1 : ℝ) / q.2 := by
    have hlog : Real.log ((p.1 : ℝ) / p.2) =
        Real.log ((q.1 : ℝ) / q.2) := by
      rw [Real.log_div (by exact_mod_cast hp₁.ne')
        (by exact_mod_cast hp₂.ne'),
        Real.log_div (by exact_mod_cast hq₁.ne')
          (by exact_mod_cast hq₂.ne')]
      exact heq
    have hp₁R : (0 : ℝ) < p.1 := by exact_mod_cast hp₁
    have hp₂R : (0 : ℝ) < p.2 := by exact_mod_cast hp₂
    have hq₁R : (0 : ℝ) < q.1 := by exact_mod_cast hq₁
    have hq₂R : (0 : ℝ) < q.2 := by exact_mod_cast hq₂
    exact Real.strictMonoOn_log.injOn
      (div_pos hp₁R hp₂R) (div_pos hq₁R hq₂R) hlog
  exact reduced_nat_ratio_injective hp₁ hp₂ hq₁ hq₂
    (gmReducedRatioPairs_coprime hp) (gmReducedRatioPairs_coprime hq) hratio

theorem card_gmReducedLogRatios (N d : ℕ) :
    (gmReducedLogRatios N d).card = (gmReducedRatioPairs N d).card := by
  unfold gmReducedLogRatios
  exact Finset.card_image_iff.mpr gmReducedLogRatios_image_injective

theorem half_abs_sub_le_abs_log_sub
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxTwo : x ≤ 2) (hyTwo : y ≤ 2) :
    |x - y| / 2 ≤ |Real.log x - Real.log y| := by
  rcases le_total x y with hxy | hyx
  · have hlog : Real.log x ≤ Real.log y := Real.strictMonoOn_log.monotoneOn hx hy hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hxy), abs_of_nonpos (sub_nonpos.mpr hlog)]
    have hbase := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
    rw [Real.log_div hy.ne' hx.ne'] at hbase
    have hcompare : (y - x) / 2 ≤ 1 - (y / x)⁻¹ := by
      rw [inv_div]
      have hid : 1 - x / y = (y - x) / y := by field_simp
      rw [hid]
      apply (le_div_iff₀ hy).2
      have hprod := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hyTwo)
      nlinarith
    linarith
  · have hlog : Real.log y ≤ Real.log x := Real.strictMonoOn_log.monotoneOn hy hx hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg (sub_nonneg.mpr hlog)]
    have hbase := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
    rw [Real.log_div hx.ne' hy.ne'] at hbase
    have hcompare : (x - y) / 2 ≤ 1 - (x / y)⁻¹ := by
      rw [inv_div]
      have hid : 1 - y / x = (x - y) / x := by field_simp
      rw [hid]
      apply (le_div_iff₀ hx).2
      have hprod := mul_nonneg (sub_nonneg.mpr hyx) (sub_nonneg.mpr hxTwo)
      nlinarith
    linarith

theorem gmReducedRatioPairs_ratio_bounds
    {N d : ℕ} (_hN : 0 < N) (hd : 0 < d) {p : ℕ × ℕ}
    (hp : p ∈ gmReducedRatioPairs N d) :
    (1 / 2 : ℝ) < (p.1 : ℝ) / p.2 ∧ (p.1 : ℝ) / p.2 < 2 := by
  have hcond := (Finset.mem_filter.mp hp).2
  have hp₁ := gmReducedRatioPairs_fst_pos hp
  have hp₂ := gmReducedRatioPairs_snd_pos hp
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have haLower : (N : ℝ) < d * p.1 := by exact_mod_cast hcond.1
  have haUpper : (d : ℝ) * p.1 ≤ 2 * N := by exact_mod_cast hcond.2.1
  have hbLower : (N : ℝ) < d * p.2 := by exact_mod_cast hcond.2.2.1
  have hbUpper : (d : ℝ) * p.2 ≤ 2 * N := by exact_mod_cast hcond.2.2.2.1
  have hp₂R : (0 : ℝ) < p.2 := by exact_mod_cast hp₂
  constructor
  · apply (lt_div_iff₀ hp₂R).2
    have hmul : (d : ℝ) * p.2 < (d : ℝ) * (2 * p.1) := by
      nlinarith
    by_contra hnot
    have hle : (2 : ℝ) * p.1 ≤ p.2 := by
      have := le_of_not_gt hnot
      nlinarith
    have := mul_le_mul_of_nonneg_left hle hdR.le
    linarith
  · apply (div_lt_iff₀ hp₂R).2
    have hmul : (d : ℝ) * p.1 < (d : ℝ) * (2 * p.2) := by
      nlinarith
    by_contra hnot
    have hle : (2 : ℝ) * p.2 ≤ p.1 := le_of_not_gt hnot
    have := mul_le_mul_of_nonneg_left hle hdR.le
    linarith

/-- Distinct reduced fractions in the `d`-slice are separated by
`d²/(4N²)`.  This is the exact arithmetic spacing statement in the proof
of Lemma 11.8. -/
theorem gmReducedRatioPairs_ratio_separated
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {p q : ℕ × ℕ} (hp : p ∈ gmReducedRatioPairs N d)
    (hq : q ∈ gmReducedRatioPairs N d) (hne : p ≠ q) :
    (d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2) ≤
      |(p.1 : ℝ) / p.2 - (q.1 : ℝ) / q.2| := by
  have hp₁ := gmReducedRatioPairs_fst_pos hp
  have hp₂ := gmReducedRatioPairs_snd_pos hp
  have hq₁ := gmReducedRatioPairs_fst_pos hq
  have hq₂ := gmReducedRatioPairs_snd_pos hq
  have hcrossNe : p.1 * q.2 ≠ q.1 * p.2 := by
    intro hcross
    apply hne
    apply reduced_nat_ratio_injective hp₁ hp₂ hq₁ hq₂
      (gmReducedRatioPairs_coprime hp) (gmReducedRatioPairs_coprime hq)
    field_simp
    have hcrossR : (p.1 : ℝ) * q.2 = (q.1 : ℝ) * p.2 := by
      exact_mod_cast hcross
    simpa [mul_comm] using hcrossR
  have hnum : (1 : ℝ) ≤
      |(p.1 : ℝ) * q.2 - (q.1 : ℝ) * p.2| := by
    by_cases hle : p.1 * q.2 ≤ q.1 * p.2
    · have hdiff : 1 ≤ q.1 * p.2 - p.1 * q.2 := by omega
      have hdiffR : (1 : ℝ) ≤
          (q.1 * p.2 - p.1 * q.2 : ℕ) := by exact_mod_cast hdiff
      rw [Nat.cast_sub hle, Nat.cast_mul, Nat.cast_mul] at hdiffR
      rw [abs_of_nonpos]
      · linarith
      · exact sub_nonpos.mpr (by exact_mod_cast hle)
    · have hlt : q.1 * p.2 < p.1 * q.2 := lt_of_not_ge hle
      have hdiff : 1 ≤ p.1 * q.2 - q.1 * p.2 := by omega
      have hdiffR : (1 : ℝ) ≤
          (p.1 * q.2 - q.1 * p.2 : ℕ) := by exact_mod_cast hdiff
      rw [Nat.cast_sub hlt.le, Nat.cast_mul, Nat.cast_mul] at hdiffR
      rw [abs_of_nonneg]
      · exact hdiffR
      · exact sub_nonneg.mpr (by exact_mod_cast hlt.le)
  have hpDen := gmReducedRatioPairs_dilate_snd_le hp
  have hqDen := gmReducedRatioPairs_dilate_snd_le hq
  have hpDenR : (d : ℝ) * p.2 ≤ 2 * N := by exact_mod_cast hpDen
  have hqDenR : (d : ℝ) * q.2 ≤ 2 * N := by exact_mod_cast hqDen
  have hdenPos : (0 : ℝ) < (p.2 : ℝ) * q.2 := mul_pos (by exact_mod_cast hp₂) (by exact_mod_cast hq₂)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : (d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2) ≤
      1 / ((p.2 : ℝ) * q.2) := by
    apply (div_le_div_iff₀ (by positivity) hdenPos).2
    have hprod := mul_le_mul hpDenR hqDenR (by positivity) (by positivity)
    nlinarith
  have hratio :
      |(p.1 : ℝ) / p.2 - (q.1 : ℝ) / q.2| =
        |(p.1 : ℝ) * q.2 - (q.1 : ℝ) * p.2| /
          ((p.2 : ℝ) * q.2) := by
    rw [div_sub_div _ _ (by exact_mod_cast hp₂.ne')
      (by exact_mod_cast hq₂.ne'), abs_div, abs_of_pos hdenPos]
    congr 2
    ring
  rw [hratio]
  exact hscale.trans (div_le_div_of_nonneg_right hnum hdenPos.le)

/-- Logarithmic version of the reduced-fraction spacing, the form consumed
by the band-limited local sampling lemma. -/
theorem gmReducedLogRatios_separated
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    {x y : ℝ} (hx : x ∈ gmReducedLogRatios N d)
    (hy : y ∈ gmReducedLogRatios N d) (hne : x ≠ y) :
    (d : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2) ≤ |x - y| := by
  rw [gmReducedLogRatios, Finset.mem_image] at hx hy
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨q, hq, hlogNe⟩ := hy
  have hp₁ := gmReducedRatioPairs_fst_pos hp
  have hp₂ := gmReducedRatioPairs_snd_pos hp
  have hq₁ := gmReducedRatioPairs_fst_pos hq
  have hq₂ := gmReducedRatioPairs_snd_pos hq
  have hpBounds := gmReducedRatioPairs_ratio_bounds hN hd hp
  have hqBounds := gmReducedRatioPairs_ratio_bounds hN hd hq
  have hpLog : Real.log (p.1 : ℝ) - Real.log (p.2 : ℝ) =
      Real.log ((p.1 : ℝ) / p.2) := by
    rw [Real.log_div (by positivity) (by positivity)]
  have hqLog : Real.log (q.1 : ℝ) - Real.log (q.2 : ℝ) =
      Real.log ((q.1 : ℝ) / q.2) := by
    rw [Real.log_div (by positivity) (by positivity)]
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hne hlogNe
  have hratio := gmReducedRatioPairs_ratio_separated hN hd hp hq hpq
  have hlog := half_abs_sub_le_abs_log_sub
    (div_pos (by exact_mod_cast hp₁) (by exact_mod_cast hp₂))
    (div_pos (by exact_mod_cast hq₁) (by exact_mod_cast hq₂))
    hpBounds.2.le hqBounds.2.le
  rw [hpLog]
  have hyEq : y = Real.log ((q.1 : ℝ) / q.2) := hlogNe.symm.trans hqLog
  rw [hyEq]
  have hscaleEq : (d : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2) =
      ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2)) / 2 := by ring
  rw [hscaleEq]
  exact (div_le_div_of_nonneg_right hratio (by norm_num)).trans hlog

/-- Finite Fubini plus the floor-bin packing bound.  This is the exact
bounded-overlap statement needed to sum the local reproducing intervals in
Lemma 11.8. -/
theorem sum_setIntegral_Icc_le_packing_mul_setIntegral
    (S : Finset ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hSep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|)
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y)
    (A B r : ℝ) (_hAB : A ≤ B) (hr : 0 ≤ r)
    (hBounds : ∀ x ∈ S, A ≤ x ∧ x ≤ B) :
    (∑ x ∈ S, ∫ y in Set.Icc (x - r) (x + r), f y) ≤
      (2 * (r / δ) + 3) *
        ∫ y in Set.Icc (A - r) (B + r), f y := by
  let G : Set ℝ := Set.Icc (A - r) (B + r)
  let I : ℝ → Set ℝ := fun x => Set.Icc (x - r) (x + r)
  let K : ℝ := 2 * (r / δ) + 3
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hsub (x : ℝ) (hx : x ∈ S) : I x ⊆ G := by
    intro y hy
    rw [Set.mem_Icc] at hy ⊢
    have hxB := hBounds x hx
    constructor <;> linarith
  have hIntIndicator (x : ℝ) : Integrable ((I x).indicator f) := by
    apply IntegrableOn.integrable_indicator
    · exact hf.continuousOn.integrableOn_Icc
    · exact measurableSet_Icc
  have hrewrite (x : ℝ) (hx : x ∈ S) :
      (∫ y in I x, f y) = ∫ y in G, (I x).indicator f y := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc,
      ← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ I x
    · have hyG := hsub x hx hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hyG,
        Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      by_cases hyG : y ∈ G
      · rw [Set.indicator_of_mem hyG, Set.indicator_of_notMem hy]
      · rw [Set.indicator_of_notMem hyG]
  have hsumInt :
      (∑ x ∈ S, ∫ y in G, (I x).indicator f y) =
        ∫ y in G, ∑ x ∈ S, (I x).indicator f y := by
    rw [MeasureTheory.integral_finsetSum]
    intro x hx
    exact (hIntIndicator x).integrableOn
  have hPoint (y : ℝ) :
      (∑ x ∈ S, (I x).indicator f y) ≤ K * f y := by
    have hsumEq : (∑ x ∈ S, (I x).indicator f y) =
        ((S.filter fun x => |x - y| ≤ r).card : ℝ) * f y := by
      calc
        (∑ x ∈ S, (I x).indicator f y) =
            ∑ x ∈ S, if |x - y| ≤ r then f y else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          have hmem : y ∈ I x ↔ |x - y| ≤ r := by
            dsimp only [I]
            rw [Set.mem_Icc, abs_le]
            constructor
            · intro h
              constructor <;> linarith
            · intro h
              constructor <;> linarith
          simp [Set.indicator, hmem]
        _ = ∑ _x ∈ S.filter (fun x => |x - y| ≤ r), f y := by
          rw [Finset.sum_filter]
        _ = ((S.filter fun x => |x - y| ≤ r).card : ℝ) * f y := by simp
    rw [hsumEq]
    have hcard := cast_card_filter_abs_sub_le_ratio
      S hδ hSep y r hr
    exact mul_le_mul_of_nonneg_right (by simpa only [K] using hcard) (hf0 y)
  calc
    (∑ x ∈ S, ∫ y in Set.Icc (x - r) (x + r), f y) =
        ∑ x ∈ S, ∫ y in G, (I x).indicator f y := by
      apply Finset.sum_congr rfl
      intro x hx
      simpa only [I] using hrewrite x hx
    _ = ∫ y in G, ∑ x ∈ S, (I x).indicator f y := hsumInt
    _ ≤ ∫ y in G, K * f y := by
      apply setIntegral_mono
      · exact MeasureTheory.integrable_finsetSum S fun x hx =>
          (hIntIndicator x).integrableOn
      · exact (hf.const_mul K).continuousOn.integrableOn_Icc
      · exact hPoint
    _ = K * ∫ y in G, f y := by rw [integral_const_mul]
    _ = _ := rfl

noncomputable def gmReducedRatioMoment
    (p N d : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ nm ∈ gmReducedRatioPairs N d,
    ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ p

theorem norm_gmR_reducedRatio_eq_phase
    {N d : ℕ} {p : ℕ × ℕ} (hp : p ∈ gmReducedRatioPairs N d)
    (W : Finset ℝ) :
    ‖gmR W ((p.1 : ℝ) / p.2)‖ =
      ‖gmRPhase W (Real.log (p.1 : ℝ) - Real.log (p.2 : ℝ))‖ := by
  have hp₁ := gmReducedRatioPairs_fst_pos hp
  have hp₂ := gmReducedRatioPairs_snd_pos hp
  have hratio : (0 : ℝ) < (p.1 : ℝ) / p.2 := by positivity
  rw [gmR_eq_gmRPhase_log hratio.ne', abs_of_pos hratio,
    Real.log_div (by positivity) (by positivity)]

theorem gmReducedRatioMoment_eq_logSum
    (k N d : ℕ) (W : Finset ℝ) :
    gmReducedRatioMoment k N d W =
      ∑ x ∈ gmReducedLogRatios N d, ‖gmRPhase W x‖ ^ k := by
  unfold gmReducedRatioMoment gmReducedLogRatios
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [norm_gmR_reducedRatio_eq_phase hp]
  · exact gmReducedLogRatios_image_injective

theorem gmReducedThirdMoment_le_sqrt
    (N d : ℕ) (W : Finset ℝ) :
    gmReducedRatioMoment 3 N d W ≤
      Real.sqrt (gmReducedRatioMoment 2 N d W) *
        Real.sqrt (gmReducedRatioMoment 4 N d W) := by
  unfold gmReducedRatioMoment
  have h := Real.sum_mul_le_sqrt_mul_sqrt
    (gmReducedRatioPairs N d)
    (fun nm => ‖gmR W ((nm.1 : ℝ) / nm.2)‖)
    (fun nm => ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ 2)
  convert h using 1
  · apply Finset.sum_congr rfl
    intro nm hnm
    ring
  · congr 2
    apply Finset.sum_congr rfl
    intro nm hnm
    ring

theorem gmReducedLogRatios_bounds
    {N d : ℕ} (hN : 0 < N) (hd : 0 < d) {x : ℝ}
    (hx : x ∈ gmReducedLogRatios N d) :
    Real.log (1 / 2 : ℝ) ≤ x ∧ x ≤ Real.log 2 := by
  rw [gmReducedLogRatios, Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have hp₁ := gmReducedRatioPairs_fst_pos hp
  have hp₂ := gmReducedRatioPairs_snd_pos hp
  have hb := gmReducedRatioPairs_ratio_bounds hN hd hp
  have hratioPos : (0 : ℝ) < (p.1 : ℝ) / p.2 := by positivity
  have hlog : Real.log (p.1 : ℝ) - Real.log (p.2 : ℝ) =
      Real.log ((p.1 : ℝ) / p.2) := by
    rw [Real.log_div (by positivity) (by positivity)]
  rw [hlog]
  have hhalfPos : (0 : ℝ) < 1 / 2 := by norm_num
  have htwoPos : (0 : ℝ) < 2 := by norm_num
  constructor
  · exact Real.strictMonoOn_log.monotoneOn hhalfPos hratioPos hb.1.le
  · exact Real.strictMonoOn_log.monotoneOn hratioPos htwoPos hb.2.le

/-- The exact pre-asymptotic second-moment estimate in the small-gcd
argument.  Its two summands are respectively the packed local integral and
the complete Schwartz tail from Lemma 11.7. -/
theorem gmReducedRatioMoment_two_le_local_raw
    {ε T H : ℝ} {N d q : ℕ} {W : Finset ℝ}
    (hε : 0 < ε) (hT : 1 ≤ T) (hSep : IsSeparated 1 W)
    (hBase : InBaseInterval T W) (hN : 0 < N) (hd : 0 < d)
    (hH : 1 ≤ H) (hq : 2 ≤ q) :
    gmReducedRatioMoment 2 N d W ≤
      gmAffineLocalBumpFourierSup * (T / (2 * Real.pi)) *
          (2 * ((2 * Real.pi * H / T) /
            ((d : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2))) + 3) *
          ((|((Real.log 2 + 2 * Real.pi * H / T) -
              (Real.log (1 / 2 : ℝ) - 2 * Real.pi * H / T))| +
            4 * (1 + ε⁻¹) * 2 ^ ε * T ^ ε) * (W.card : ℝ)) +
        ((gmReducedRatioPairs N d).card : ℝ) * (W.card : ℝ) ^ 2 *
          gmAffineLocalBumpFourierTailConstant q hq *
            H ^ (1 - (q : ℝ)) := by
  let S := gmReducedLogRatios N d
  let δ : ℝ := (d : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2)
  let r : ℝ := 2 * Real.pi * H / T
  let A : ℝ := Real.log (1 / 2 : ℝ)
  let B : ℝ := Real.log 2
  let C₀ : ℝ := gmAffineLocalBumpFourierSup * (T / (2 * Real.pi))
  let tail : ℝ := (W.card : ℝ) ^ 2 *
    gmAffineLocalBumpFourierTailConstant q hq * H ^ (1 - (q : ℝ))
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) (by norm_num)
  have hSepLog : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hxy
    exact gmReducedLogRatios_separated hN hd hx hy hxy
  have hBounds : ∀ x ∈ S, A ≤ x ∧ x ≤ B := by
    intro x hx
    exact gmReducedLogRatios_bounds hN hd hx
  let f : ℝ → ℝ := fun y => ‖gmRPhase W y‖ ^ 2
  have hf : Continuous f := continuous_norm_gmRPhase_pow W 2
  have hf0 : ∀ y, 0 ≤ f y := fun _ => sq_nonneg _
  have hpack :
      (∑ x ∈ S, ∫ y in Set.Icc (x - r) (x + r), f y) ≤
        (2 * (r / δ) + 3) *
          ∫ y in Set.Icc (A - r) (B + r), f y :=
    sum_setIntegral_Icc_le_packing_mul_setIntegral
      S hδ hSepLog f hf hf0 A B r hAB hr hBounds
  have habWide : A - r ≤ B + r := by linarith
  have hglobal :
      (∫ y in Set.Icc (A - r) (B + r), f y) ≤
        (|(B + r) - (A - r)| +
          4 * (1 + ε⁻¹) * 2 ^ ε * T ^ ε) * (W.card : ℝ) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le habWide]
    exact intervalIntegral_norm_gmRPhase_sq_le_epsilon
      hε hT hSep hBase (A - r) (B + r) habWide
  have hlocal :
      ∀ x ∈ S, f x ≤ C₀ * (∫ y in Set.Icc (x - r) (x + r), f y) + tail := by
    intro x hx
    simpa only [f, C₀, tail, r] using
      norm_gmRPhase_sq_le_localIntegral_add_tail
        hTpos hBase x H hH q hq
  have hC₀0 : 0 ≤ C₀ := by
    dsimp only [C₀]
    exact mul_nonneg gmAffineLocalBumpFourierSup_pos.le (div_nonneg hTpos.le (by positivity))
  have hK0 : 0 ≤ 2 * (r / δ) + 3 := by positivity
  rw [gmReducedRatioMoment_eq_logSum]
  change (∑ x ∈ S, f x) ≤ _
  calc
    (∑ x ∈ S, f x) ≤
        ∑ x ∈ S, (C₀ * (∫ y in Set.Icc (x - r) (x + r), f y) + tail) := by
      gcongr with x hx
      exact hlocal x hx
    _ = C₀ * (∑ x ∈ S, ∫ y in Set.Icc (x - r) (x + r), f y) +
          (S.card : ℝ) * tail := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul]
    _ ≤ C₀ * ((2 * (r / δ) + 3) *
          ∫ y in Set.Icc (A - r) (B + r), f y) +
          (S.card : ℝ) * tail := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpack hC₀0) (le_refl _)
    _ ≤ C₀ * ((2 * (r / δ) + 3) *
          ((|(B + r) - (A - r)| +
            4 * (1 + ε⁻¹) * 2 ^ ε * T ^ ε) * (W.card : ℝ))) +
          (S.card : ℝ) * tail := by
      have hscaled := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hglobal hK0) hC₀0
      linarith
    _ = _ := by
      rw [card_gmReducedLogRatios]
      dsimp only [C₀, tail, S, δ, r, A, B]
      ring

/-- The exact fourth-moment companion to
`gmReducedRatioMoment_two_le_local_raw`. -/
theorem gmReducedRatioMoment_four_le_local_raw
    {ε T H : ℝ} {N d q : ℕ} {W : Finset ℝ}
    (hε : 0 < ε) (hT : 1 ≤ T) (hBase : InBaseInterval T W)
    (hN : 0 < N) (hd : 0 < d) (hH : 1 ≤ H) (hq : 2 ≤ q) :
    gmReducedRatioMoment 4 N d W ≤
      gmAffineLocalBumpFourierSup * (2 * T / (2 * Real.pi)) *
          (2 * ((2 * Real.pi * H / (2 * T)) /
            ((d : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2))) + 3) *
          ((4 * |((Real.log 2 + 2 * Real.pi * H / (2 * T)) -
              (Real.log (1 / 2 : ℝ) - 2 * Real.pi * H / (2 * T)))| +
            8 * (1 + ε⁻¹) * 3 ^ ε) * T ^ ε *
              (ApproxAddEnergy 1 W : ℝ)) +
        ((gmReducedRatioPairs N d).card : ℝ) * (W.card : ℝ) ^ 4 *
          gmAffineLocalBumpFourierTailConstant q hq *
            H ^ (1 - (q : ℝ)) := by
  let S := gmReducedLogRatios N d
  let δ : ℝ := (d : ℝ) ^ 2 / (8 * (N : ℝ) ^ 2)
  let r : ℝ := 2 * Real.pi * H / (2 * T)
  let A : ℝ := Real.log (1 / 2 : ℝ)
  let B : ℝ := Real.log 2
  let C₀ : ℝ := gmAffineLocalBumpFourierSup * (2 * T / (2 * Real.pi))
  let tail : ℝ := (W.card : ℝ) ^ 4 *
    gmAffineLocalBumpFourierTailConstant q hq * H ^ (1 - (q : ℝ))
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) (by norm_num) (by norm_num)
  have hSepLog : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hxy
    exact gmReducedLogRatios_separated hN hd hx hy hxy
  have hBounds : ∀ x ∈ S, A ≤ x ∧ x ≤ B := by
    intro x hx
    exact gmReducedLogRatios_bounds hN hd hx
  let f : ℝ → ℝ := fun y => ‖gmRPhase W y‖ ^ 4
  have hf : Continuous f := continuous_norm_gmRPhase_pow W 4
  have hf0 : ∀ y, 0 ≤ f y := fun _ => by positivity
  have hpack :
      (∑ x ∈ S, ∫ y in Set.Icc (x - r) (x + r), f y) ≤
        (2 * (r / δ) + 3) *
          ∫ y in Set.Icc (A - r) (B + r), f y :=
    sum_setIntegral_Icc_le_packing_mul_setIntegral
      S hδ hSepLog f hf hf0 A B r hAB hr hBounds
  have habWide : A - r ≤ B + r := by linarith
  have hglobal :
      (∫ y in Set.Icc (A - r) (B + r), f y) ≤
        (4 * |(B + r) - (A - r)| +
          8 * (1 + ε⁻¹) * 3 ^ ε) * T ^ ε *
            (ApproxAddEnergy 1 W : ℝ) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le habWide]
    exact intervalIntegral_norm_gmRPhase_fourth_le_energy_epsilon
      hε hT hBase (A - r) (B + r) habWide
  have hlocal :
      ∀ x ∈ S, f x ≤ C₀ * (∫ y in Set.Icc (x - r) (x + r), f y) + tail := by
    intro x hx
    simpa only [f, C₀, tail, r] using
      norm_gmRPhase_fourth_le_localIntegral_add_tail
        hTpos hBase x H hH q hq
  have hC₀0 : 0 ≤ C₀ := by
    dsimp only [C₀]
    exact mul_nonneg gmAffineLocalBumpFourierSup_pos.le (div_nonneg (by positivity) (by positivity))
  have hK0 : 0 ≤ 2 * (r / δ) + 3 := by positivity
  rw [gmReducedRatioMoment_eq_logSum]
  change (∑ x ∈ S, f x) ≤ _
  calc
    (∑ x ∈ S, f x) ≤
        ∑ x ∈ S, (C₀ * (∫ y in Set.Icc (x - r) (x + r), f y) + tail) := by
      gcongr with x hx
      exact hlocal x hx
    _ = C₀ * (∑ x ∈ S, ∫ y in Set.Icc (x - r) (x + r), f y) +
          (S.card : ℝ) * tail := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul]
    _ ≤ C₀ * ((2 * (r / δ) + 3) *
          ∫ y in Set.Icc (A - r) (B + r), f y) +
          (S.card : ℝ) * tail := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpack hC₀0) (le_refl _)
    _ ≤ C₀ * ((2 * (r / δ) + 3) *
          ((4 * |(B + r) - (A - r)| +
            8 * (1 + ε⁻¹) * 3 ^ ε) * T ^ ε *
              (ApproxAddEnergy 1 W : ℝ))) +
          (S.card : ℝ) * tail := by
      have hscaled := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hglobal hK0) hC₀0
      linarith
    _ = _ := by
      rw [card_gmReducedLogRatios]
      dsimp only [C₀, tail, S, δ, r, A, B]
      ring

/-! ### Exact gcd decomposition of the source ratio moment -/

def gmGcdSlice (N d : ℕ) : Finset (ℕ × ℕ) :=
  (dyadicInterval N ×ˢ dyadicInterval N).filter fun p =>
    Nat.gcd p.1 p.2 = d

noncomputable def gmGcdSliceMoment
    (k N d : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ nm ∈ gmGcdSlice N d,
    ‖gmR W ((nm.1 : ℝ) / nm.2)‖ ^ k

theorem gmGcdSlice_fst_pos
    {N d : ℕ} {p : ℕ × ℕ} (hp : p ∈ gmGcdSlice N d) : 0 < p.1 := by
  have hp' := (Finset.mem_filter.mp hp).1
  rw [Finset.mem_product] at hp'
  exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hp'.1).1

theorem gmGcdSlice_snd_pos
    {N d : ℕ} {p : ℕ × ℕ} (hp : p ∈ gmGcdSlice N d) : 0 < p.2 := by
  have hp' := (Finset.mem_filter.mp hp).1
  rw [Finset.mem_product] at hp'
  exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hp'.2).1

theorem gmGcdSlice_index_pos
    {N d : ℕ} {p : ℕ × ℕ} (hp : p ∈ gmGcdSlice N d) : 0 < d := by
  rw [← (Finset.mem_filter.mp hp).2]
  exact Nat.gcd_pos_of_pos_left p.2 (gmGcdSlice_fst_pos hp)

theorem gmGcdSlice_to_reduced_mem
    {N d : ℕ} {p : ℕ × ℕ} (hp : p ∈ gmGcdSlice N d) :
    (p.1 / d, p.2 / d) ∈ gmReducedRatioPairs N d := by
  have hpProd := (Finset.mem_filter.mp hp).1
  have hpGcd := (Finset.mem_filter.mp hp).2
  have hpI := Finset.mem_product.mp hpProd
  have hp₁I := Finset.mem_Ioc.mp hpI.1
  have hp₂I := Finset.mem_Ioc.mp hpI.2
  have hp₁ := gmGcdSlice_fst_pos hp
  have hp₂ := gmGcdSlice_snd_pos hp
  have hd := gmGcdSlice_index_pos hp
  have hdDvd₁ : d ∣ p.1 := by rw [← hpGcd]; exact Nat.gcd_dvd_left _ _
  have hdDvd₂ : d ∣ p.2 := by rw [← hpGcd]; exact Nat.gcd_dvd_right _ _
  have hmul₁ : d * (p.1 / d) = p.1 := Nat.mul_div_cancel' hdDvd₁
  have hmul₂ : d * (p.2 / d) = p.2 := Nat.mul_div_cancel' hdDvd₂
  rw [gmReducedRatioPairs, Finset.mem_filter, Finset.mem_product]
  constructor
  · constructor <;> rw [Finset.mem_Icc]
    · constructor
      · apply Nat.one_le_iff_ne_zero.mpr
        intro hz
        change p.1 / d = 0 at hz
        rw [hz, mul_zero] at hmul₁
        omega
      · exact (Nat.div_le_self p.1 d).trans hp₁I.2
    · constructor
      · apply Nat.one_le_iff_ne_zero.mpr
        intro hz
        change p.2 / d = 0 at hz
        rw [hz, mul_zero] at hmul₂
        omega
      · exact (Nat.div_le_self p.2 d).trans hp₂I.2
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hmul₁] using hp₁I.1
    · simpa only [hmul₁] using hp₁I.2
    · simpa only [hmul₂] using hp₂I.1
    · simpa only [hmul₂] using hp₂I.2
    · rw [Nat.Coprime, ← hpGcd]
      exact Nat.gcd_div_gcd_div_gcd_of_pos_left hp₁

theorem gmReducedRatioPairs_to_gcdSlice_mem
    {N d : ℕ} {p : ℕ × ℕ} (hp : p ∈ gmReducedRatioPairs N d) :
    (d * p.1, d * p.2) ∈ gmGcdSlice N d := by
  have hpCond := (Finset.mem_filter.mp hp).2
  have hpCop := gmReducedRatioPairs_coprime hp
  rw [gmGcdSlice, Finset.mem_filter, Finset.mem_product]
  constructor
  · constructor <;> rw [dyadicInterval, Finset.mem_Ioc]
    · exact ⟨hpCond.1, hpCond.2.1⟩
    · exact ⟨hpCond.2.2.1, hpCond.2.2.2.1⟩
  · rw [Nat.gcd_mul_left, hpCop]
    simp

/-- The `gcd = d` source slice is exactly the reduced-rational slice;
there is no floor replacement of `N/d` in this identity. -/
theorem gmGcdSliceMoment_eq_reduced
    (k N d : ℕ) (W : Finset ℝ) :
    gmGcdSliceMoment k N d W = gmReducedRatioMoment k N d W := by
  classical
  unfold gmGcdSliceMoment gmReducedRatioMoment
  refine Finset.sum_bij
    (fun p _ => (p.1 / d, p.2 / d)) ?_ ?_ ?_ ?_
  · intro p hp
    exact gmGcdSlice_to_reduced_mem hp
  · intro p hp q hq heq
    have hd := gmGcdSlice_index_pos hp
    have hpGcd := (Finset.mem_filter.mp hp).2
    have hqGcd := (Finset.mem_filter.mp hq).2
    have hdDvdP₁ : d ∣ p.1 := by rw [← hpGcd]; exact Nat.gcd_dvd_left _ _
    have hdDvdP₂ : d ∣ p.2 := by rw [← hpGcd]; exact Nat.gcd_dvd_right _ _
    have hdDvdQ₁ : d ∣ q.1 := by rw [← hqGcd]; exact Nat.gcd_dvd_left _ _
    have hdDvdQ₂ : d ∣ q.2 := by rw [← hqGcd]; exact Nat.gcd_dvd_right _ _
    apply Prod.ext
    · have := congrArg (fun z : ℕ × ℕ => d * z.1) heq
      simpa [Nat.mul_div_cancel' hdDvdP₁, Nat.mul_div_cancel' hdDvdQ₁] using this
    · have := congrArg (fun z : ℕ × ℕ => d * z.2) heq
      simpa [Nat.mul_div_cancel' hdDvdP₂, Nat.mul_div_cancel' hdDvdQ₂] using this
  · intro p hp
    refine ⟨(d * p.1, d * p.2), gmReducedRatioPairs_to_gcdSlice_mem hp, ?_⟩
    have hd : 0 < d := by
      have hpCond := (Finset.mem_filter.mp hp).2
      exact Nat.pos_of_mul_pos_right
        (lt_of_le_of_lt (Nat.zero_le N) hpCond.1)
    simp [Nat.mul_div_cancel_left _ hd]
  · intro p hp
    have hpGcd := (Finset.mem_filter.mp hp).2
    have hdDvd₁ : d ∣ p.1 := by rw [← hpGcd]; exact Nat.gcd_dvd_left _ _
    have hdDvd₂ : d ∣ p.2 := by rw [← hpGcd]; exact Nat.gcd_dvd_right _ _
    have hp₂ := gmGcdSlice_snd_pos hp
    have hcast₁ : ((p.1 / d : ℕ) : ℝ) = (p.1 : ℝ) / d := by
      have hdPos := gmGcdSlice_index_pos hp
      rw [Nat.cast_div hdDvd₁]
      exact_mod_cast hdPos.ne'
    have hcast₂ : ((p.2 / d : ℕ) : ℝ) = (p.2 : ℝ) / d := by
      have hdPos := gmGcdSlice_index_pos hp
      rw [Nat.cast_div hdDvd₂]
      exact_mod_cast hdPos.ne'
    congr 2
    rw [hcast₁, hcast₂]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (gmGcdSlice_index_pos hp).ne'
    have hp₂R : (p.2 : ℝ) ≠ 0 := by exact_mod_cast hp₂.ne'
    field_simp

/-- Exact finite partition of the source double ratio moment by its gcd.
The upper index `2*N` is derived from the dyadic support. -/
theorem gmDiscreteRatioMoment_eq_sum_gcdSlices
    (k N : ℕ) (W : Finset ℝ) :
    gmDiscreteRatioMoment k N W =
      ∑ d ∈ Finset.Icc 1 (2 * N), gmGcdSliceMoment k N d W := by
  classical
  unfold gmDiscreteRatioMoment gmGcdSliceMoment gmGcdSlice
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hpI := Finset.mem_product.mp hp
  have hp₁ := Finset.mem_Ioc.mp hpI.1
  have hp₂ := Finset.mem_Ioc.mp hpI.2
  have hgPos : 0 < Nat.gcd p.1 p.2 :=
    Nat.gcd_pos_of_pos_left p.2 (Nat.zero_lt_of_lt hp₁.1)
  have hgLe : Nat.gcd p.1 p.2 ≤ 2 * N :=
    (Nat.gcd_le_left p.2 (Nat.zero_lt_of_lt hp₁.1)).trans hp₁.2
  have hgMem : Nat.gcd p.1 p.2 ∈ Finset.Icc 1 (2 * N) :=
    Finset.mem_Icc.mpr ⟨hgPos, hgLe⟩
  rw [Finset.sum_eq_single (Nat.gcd p.1 p.2)]
  · simp
  · intro d hd hdne
    have hne : Nat.gcd p.1 p.2 ≠ d := Ne.symm hdne
    simp [hne]
  · intro hnot
    exact (hnot hgMem).elim

theorem gmDiscreteRatioMoment_eq_sum_reduced
    (k N : ℕ) (W : Finset ℝ) :
    gmDiscreteRatioMoment k N W =
      ∑ d ∈ Finset.Icc 1 (2 * N), gmReducedRatioMoment k N d W := by
  rw [gmDiscreteRatioMoment_eq_sum_gcdSlices]
  apply Finset.sum_congr rfl
  intro d hd
  exact gmGcdSliceMoment_eq_reduced k N d W

/-! ### Elementary summation used in the small-gcd range -/

theorem sum_range_one_div_succ_sq_le (D : ℕ) :
    (∑ n ∈ Finset.range D, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) ≤
      2 - 2 / ((D + 1 : ℕ) : ℝ) := by
  induction D with
  | zero => norm_num
  | succ D ih =>
      have hD : (0 : ℝ) < ((D + 1 : ℕ) : ℝ) := by positivity
      have hDs : (0 : ℝ) < ((D + 2 : ℕ) : ℝ) := by positivity
      have hterm :
          (1 : ℝ) / ((D + 1 : ℕ) : ℝ) ^ 2 ≤
            2 / ((D + 1 : ℕ) : ℝ) - 2 / ((D + 2 : ℕ) : ℝ) := by
        have hDone : (1 : ℝ) ≤ (D + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le D)
        have hDsEq : ((D + 2 : ℕ) : ℝ) = ((D + 1 : ℕ) : ℝ) + 1 := by
          push_cast
          ring
        rw [hDsEq]
        field_simp [hD.ne']
        nlinarith
      rw [Finset.sum_range_succ]
      calc
        (∑ n ∈ Finset.range D, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) +
              1 / ((D + 1 : ℕ) : ℝ) ^ 2 ≤
            (2 - 2 / ((D + 1 : ℕ) : ℝ)) +
              1 / ((D + 1 : ℕ) : ℝ) ^ 2 := by gcongr
        _ ≤ (2 - 2 / ((D + 1 : ℕ) : ℝ)) +
              (2 / ((D + 1 : ℕ) : ℝ) - 2 / ((D + 2 : ℕ) : ℝ)) := by
          gcongr
        _ = 2 - 2 / (((D + 1) + 1 : ℕ) : ℝ) := by
          push_cast
          ring

theorem sum_Icc_one_div_sq_le_two (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 2 := by
  have hsub : Finset.Icc 1 D ⊆ Finset.range (D + 1) := by
    intro d hd
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hd).2)
  have hle :
      (∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ) ^ 2) ≤
        ∑ d ∈ Finset.range (D + 1), if d = 0 then 0 else (1 : ℝ) / (d : ℝ) ^ 2 := by
    calc
      (∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ) ^ 2) =
          ∑ d ∈ Finset.Icc 1 D,
            if d = 0 then 0 else (1 : ℝ) / (d : ℝ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdPos : 0 < d := (Finset.mem_Icc.mp hd).1
        simp [hdPos.ne']
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro d hdRange hdNot
        positivity
  have hshift :
      (∑ d ∈ Finset.range (D + 1), if d = 0 then 0 else (1 : ℝ) / (d : ℝ) ^ 2) =
        ∑ n ∈ Finset.range D, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp
  rw [hshift] at hle
  exact hle.trans ((sum_range_one_div_succ_sq_le D).trans (by
    have : (0 : ℝ) ≤ 2 / ((D + 1 : ℕ) : ℝ) := by positivity
    linarith))

theorem card_gmReducedRatioPairs_le_four_mul_sq (N d : ℕ) :
    (gmReducedRatioPairs N d).card ≤ 4 * N ^ 2 := by
  unfold gmReducedRatioPairs
  calc
    (((Finset.Icc 1 (2 * N)) ×ˢ (Finset.Icc 1 (2 * N))).filter fun p =>
        N < d * p.1 ∧ d * p.1 ≤ 2 * N ∧
          N < d * p.2 ∧ d * p.2 ≤ 2 * N ∧ Nat.Coprime p.1 p.2).card ≤
        ((Finset.Icc 1 (2 * N)) ×ˢ (Finset.Icc 1 (2 * N))).card :=
      Finset.card_filter_le _ _
    _ = (Finset.Icc 1 (2 * N)).card ^ 2 := by
      simp only [Finset.card_product]
      ring
    _ ≤ (2 * N) ^ 2 := by
      gcongr
      rw [Nat.card_Icc]
      omega
    _ = 4 * N ^ 2 := by ring

theorem cast_card_gmReducedRatioPairs_le_four_mul_sq (N d : ℕ) :
    ((gmReducedRatioPairs N d).card : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
  exact_mod_cast card_gmReducedRatioPairs_le_four_mul_sq N d

theorem gmSecondLocalPackingPrefactor_le
    {T H N d : ℝ} (hT : 1 ≤ T) (hH : 0 ≤ H)
    (hN : 0 ≤ N) (hd : 0 < d) :
    gmAffineLocalBumpFourierSup * (T / (2 * Real.pi)) *
        (2 * ((2 * Real.pi * H / T) / (d ^ 2 / (8 * N ^ 2))) + 3) ≤
      19 * gmAffineLocalBumpFourierSup * (T + H * N ^ 2 / d ^ 2) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hpi : 0 < Real.pi := Real.pi_pos
  have hSup : 0 ≤ gmAffineLocalBumpFourierSup :=
    gmAffineLocalBumpFourierSup_pos.le
  by_cases hNz : N = 0
  · subst N
    norm_num
    have hpiHalf : (1 : ℝ) / (2 * Real.pi) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      nlinarith [Real.pi_gt_three]
    calc
      gmAffineLocalBumpFourierSup * (T / (2 * Real.pi)) * 3 =
          gmAffineLocalBumpFourierSup * (T / (2 * Real.pi) * 3) := by ring
      _ ≤ gmAffineLocalBumpFourierSup * (19 * T) := by
        apply mul_le_mul_of_nonneg_left _ hSup
        calc
          T / (2 * Real.pi) * 3 ≤ T * 3 := by
            calc
              T / (2 * Real.pi) * 3 = (T * 3) * (1 / (2 * Real.pi)) := by ring
              _ ≤ (T * 3) * 1 :=
                mul_le_mul_of_nonneg_left hpiHalf (by positivity)
              _ = T * 3 := by ring
          _ ≤ 19 * T := by nlinarith
      _ = 19 * gmAffineLocalBumpFourierSup * T := by ring
  · have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hNz)
    have heq :
        gmAffineLocalBumpFourierSup * (T / (2 * Real.pi)) *
            (2 * ((2 * Real.pi * H / T) / (d ^ 2 / (8 * N ^ 2))) + 3) =
          gmAffineLocalBumpFourierSup *
            (16 * H * N ^ 2 / d ^ 2 + 3 * T / (2 * Real.pi)) := by
      field_simp
      ring
    rw [heq]
    have hpiHalf : (1 : ℝ) / (2 * Real.pi) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      nlinarith [Real.pi_gt_three]
    have hcore0 : 0 ≤ H * N ^ 2 / d ^ 2 := by positivity
    have hfirst : 16 * H * N ^ 2 / d ^ 2 ≤
        19 * (H * N ^ 2 / d ^ 2) := by
      calc
        16 * H * N ^ 2 / d ^ 2 = 16 * (H * N ^ 2 / d ^ 2) := by ring
        _ ≤ 19 * (H * N ^ 2 / d ^ 2) := by gcongr; norm_num
    have hsecond : 3 * T / (2 * Real.pi) ≤ 19 * T := by
      calc
        3 * T / (2 * Real.pi) = 3 * T * (1 / (2 * Real.pi)) := by ring
        _ ≤ 3 * T * 1 := by gcongr
        _ ≤ 19 * T := by nlinarith
    calc
      gmAffineLocalBumpFourierSup *
          (16 * H * N ^ 2 / d ^ 2 + 3 * T / (2 * Real.pi)) ≤
        gmAffineLocalBumpFourierSup *
          (19 * (H * N ^ 2 / d ^ 2) + 19 * T) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hSup
      _ = 19 * gmAffineLocalBumpFourierSup *
          (T + H * N ^ 2 / d ^ 2) := by ring

theorem gmFourthLocalPackingPrefactor_le
    {T H N d : ℝ} (hT : 1 ≤ T) (hH : 0 ≤ H)
    (hN : 0 ≤ N) (hd : 0 < d) :
    gmAffineLocalBumpFourierSup * (2 * T / (2 * Real.pi)) *
        (2 * ((2 * Real.pi * H / (2 * T)) /
          (d ^ 2 / (8 * N ^ 2))) + 3) ≤
      19 * gmAffineLocalBumpFourierSup * (T + H * N ^ 2 / d ^ 2) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hpi : 0 < Real.pi := Real.pi_pos
  have hSup : 0 ≤ gmAffineLocalBumpFourierSup :=
    gmAffineLocalBumpFourierSup_pos.le
  by_cases hNz : N = 0
  · subst N
    norm_num
    have hpiInv : (1 : ℝ) / Real.pi ≤ 1 := by
      apply (div_le_one Real.pi_pos).2
      nlinarith [Real.pi_gt_three]
    calc
      gmAffineLocalBumpFourierSup * (2 * T / (2 * Real.pi)) * 3 =
          gmAffineLocalBumpFourierSup * (2 * T / (2 * Real.pi) * 3) := by ring
      _ ≤ gmAffineLocalBumpFourierSup * (19 * T) := by
        apply mul_le_mul_of_nonneg_left _ hSup
        calc
          2 * T / (2 * Real.pi) * 3 ≤ 2 * T / 2 * 3 := by
            gcongr
            nlinarith [Real.pi_gt_three]
          _ ≤ 19 * T := by nlinarith
      _ = 19 * gmAffineLocalBumpFourierSup * T := by ring
  · have hNpos : 0 < N := lt_of_le_of_ne hN (Ne.symm hNz)
    have heq :
        gmAffineLocalBumpFourierSup * (2 * T / (2 * Real.pi)) *
            (2 * ((2 * Real.pi * H / (2 * T)) /
              (d ^ 2 / (8 * N ^ 2))) + 3) =
          gmAffineLocalBumpFourierSup *
            (16 * H * N ^ 2 / d ^ 2 + 3 * T / Real.pi) := by
      field_simp
      ring
    rw [heq]
    have hpiInv : (1 : ℝ) / Real.pi ≤ 1 := by
      apply (div_le_one Real.pi_pos).2
      nlinarith [Real.pi_gt_three]
    have hcore0 : 0 ≤ H * N ^ 2 / d ^ 2 := by positivity
    have hfirst : 16 * H * N ^ 2 / d ^ 2 ≤
        19 * (H * N ^ 2 / d ^ 2) := by
      calc
        16 * H * N ^ 2 / d ^ 2 = 16 * (H * N ^ 2 / d ^ 2) := by ring
        _ ≤ 19 * (H * N ^ 2 / d ^ 2) := by gcongr; norm_num
    have hsecond : 3 * T / Real.pi ≤ 19 * T := by
      calc
        3 * T / Real.pi = 3 * T * (1 / Real.pi) := by ring
        _ ≤ 3 * T * 1 := by gcongr
        _ ≤ 19 * T := by nlinarith
    calc
      gmAffineLocalBumpFourierSup *
          (16 * H * N ^ 2 / d ^ 2 + 3 * T / Real.pi) ≤
        gmAffineLocalBumpFourierSup *
          (19 * (H * N ^ 2 / d ^ 2) + 19 * T) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hSup
      _ = 19 * gmAffineLocalBumpFourierSup *
          (T + H * N ^ 2 / d ^ 2) := by ring

noncomputable def gmSmallGcdL2Constant (μ : ℝ) : ℝ :=
  19 * gmAffineLocalBumpFourierSup *
    (|Real.log 2 - Real.log (1 / 2 : ℝ)| + 4 * Real.pi +
      4 * (1 + μ⁻¹) * 2 ^ μ)

noncomputable def gmSmallGcdL4Constant (μ : ℝ) : ℝ :=
  19 * gmAffineLocalBumpFourierSup *
    (4 * (|Real.log 2 - Real.log (1 / 2 : ℝ)| + 4 * Real.pi) +
      8 * (1 + μ⁻¹) * 3 ^ μ)

theorem gmSmallGcdL2Constant_pos {μ : ℝ} (hμ : 0 < μ) :
    0 < gmSmallGcdL2Constant μ := by
  unfold gmSmallGcdL2Constant
  have hSup := gmAffineLocalBumpFourierSup_pos
  positivity

theorem gmSmallGcdL4Constant_pos {μ : ℝ} (hμ : 0 < μ) :
    0 < gmSmallGcdL4Constant μ := by
  unfold gmSmallGcdL4Constant
  have hSup := gmAffineLocalBumpFourierSup_pos
  positivity

theorem gmReducedRatioMoment_two_le_main_add_tail
    {μ T H : ℝ} {N d q : ℕ} {W : Finset ℝ}
    (hμ : 0 < μ) (hT : 1 ≤ T) (hSep : IsSeparated 1 W)
    (hBase : InBaseInterval T W) (hN : 0 < N) (hd : 0 < d)
    (hHOne : 1 ≤ H) (hHT : H ≤ T) (hq : 2 ≤ q) :
    gmReducedRatioMoment 2 N d W ≤
      gmSmallGcdL2Constant μ * T ^ μ *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) * (W.card : ℝ) +
        4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 *
          gmAffineLocalBumpFourierTailConstant q hq *
            H ^ (1 - (q : ℝ)) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hH0 : 0 ≤ H := zero_le_one.trans hHOne
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrLe : 2 * Real.pi * H / T ≤ 2 * Real.pi := by
    rw [div_le_iff₀ hTpos]
    nlinarith [Real.pi_pos]
  have hlen :
      |((Real.log 2 + 2 * Real.pi * H / T) -
          (Real.log (1 / 2 : ℝ) - 2 * Real.pi * H / T))| ≤
        |Real.log 2 - Real.log (1 / 2 : ℝ)| + 4 * Real.pi := by
    calc
      |((Real.log 2 + 2 * Real.pi * H / T) -
          (Real.log (1 / 2 : ℝ) - 2 * Real.pi * H / T))| =
          |(Real.log 2 - Real.log (1 / 2 : ℝ)) +
            2 * (2 * Real.pi * H / T)| := by ring_nf
      _ ≤ |Real.log 2 - Real.log (1 / 2 : ℝ)| +
          |2 * (2 * Real.pi * H / T)| := abs_add_le _ _
      _ = |Real.log 2 - Real.log (1 / 2 : ℝ)| +
          2 * (2 * Real.pi * H / T) := by
        rw [abs_of_nonneg (mul_nonneg (by norm_num)
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hH0)
            hTpos.le))]
      _ ≤ |Real.log 2 - Real.log (1 / 2 : ℝ)| + 4 * Real.pi := by
        nlinarith
  have hTpow : 1 ≤ T ^ μ := Real.one_le_rpow hT hμ.le
  let L : ℝ := |Real.log 2 - Real.log (1 / 2 : ℝ)| + 4 * Real.pi
  let A : ℝ := 4 * (1 + μ⁻¹) * 2 ^ μ
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hglobal :
      (|((Real.log 2 + 2 * Real.pi * H / T) -
          (Real.log (1 / 2 : ℝ) - 2 * Real.pi * H / T))| +
        4 * (1 + μ⁻¹) * 2 ^ μ * T ^ μ) * (W.card : ℝ) ≤
        (L + A) * T ^ μ * (W.card : ℝ) := by
    have hinside :
        |((Real.log 2 + 2 * Real.pi * H / T) -
            (Real.log (1 / 2 : ℝ) - 2 * Real.pi * H / T))| +
          4 * (1 + μ⁻¹) * 2 ^ μ * T ^ μ ≤
            (L + A) * T ^ μ := by
      dsimp only [L, A]
      nlinarith [mul_nonneg hL0 (sub_nonneg.mpr hTpow)]
    gcongr
  have hpref := gmSecondLocalPackingPrefactor_le
    hT hH0 hN0 hdR
  have hraw := gmReducedRatioMoment_two_le_local_raw
    hμ hT hSep hBase hN hd hHOne hq
  have hpair := cast_card_gmReducedRatioPairs_le_four_mul_sq N d
  calc
    gmReducedRatioMoment 2 N d W ≤ _ := hraw
    _ ≤ (19 * gmAffineLocalBumpFourierSup *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2)) *
          ((L + A) * T ^ μ * (W.card : ℝ)) +
        (4 * (N : ℝ) ^ 2) * (W.card : ℝ) ^ 2 *
          gmAffineLocalBumpFourierTailConstant q hq *
            H ^ (1 - (q : ℝ)) := by
      have hPref0 : 0 ≤ 19 * gmAffineLocalBumpFourierSup *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) := by
        exact mul_nonneg (mul_nonneg (by norm_num) gmAffineLocalBumpFourierSup_pos.le)
          (add_nonneg hTpos.le (by positivity))
      have hTail0 := gmAffineLocalBumpFourierTailConstant_pos q hq
      gcongr
    _ = _ := by
      dsimp only [gmSmallGcdL2Constant, L, A]
      ring

theorem gmReducedRatioMoment_four_le_main_add_tail
    {μ T H : ℝ} {N d q : ℕ} {W : Finset ℝ}
    (hμ : 0 < μ) (hT : 1 ≤ T) (hBase : InBaseInterval T W)
    (hN : 0 < N) (hd : 0 < d) (hHOne : 1 ≤ H) (hHT : H ≤ T)
    (hq : 2 ≤ q) :
    gmReducedRatioMoment 4 N d W ≤
      gmSmallGcdL4Constant μ * T ^ μ *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
            (ApproxAddEnergy 1 W : ℝ) +
        4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 4 *
          gmAffineLocalBumpFourierTailConstant q hq *
            H ^ (1 - (q : ℝ)) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hH0 : 0 ≤ H := zero_le_one.trans hHOne
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrLe : 2 * Real.pi * H / (2 * T) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * T)]
    nlinarith [Real.pi_pos]
  have hlen :
      |((Real.log 2 + 2 * Real.pi * H / (2 * T)) -
          (Real.log (1 / 2 : ℝ) - 2 * Real.pi * H / (2 * T)))| ≤
        |Real.log 2 - Real.log (1 / 2 : ℝ)| + 4 * Real.pi := by
    calc
      |((Real.log 2 + 2 * Real.pi * H / (2 * T)) -
          (Real.log (1 / 2 : ℝ) - 2 * Real.pi * H / (2 * T)))| =
          |(Real.log 2 - Real.log (1 / 2 : ℝ)) +
            2 * (2 * Real.pi * H / (2 * T))| := by ring_nf
      _ ≤ |Real.log 2 - Real.log (1 / 2 : ℝ)| +
          |2 * (2 * Real.pi * H / (2 * T))| := abs_add_le _ _
      _ = |Real.log 2 - Real.log (1 / 2 : ℝ)| +
          2 * (2 * Real.pi * H / (2 * T)) := by
        rw [abs_of_nonneg (mul_nonneg (by norm_num)
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hH0)
            (by positivity)))]
      _ ≤ |Real.log 2 - Real.log (1 / 2 : ℝ)| + 4 * Real.pi := by
        nlinarith [Real.pi_pos]
  have hTpow : 1 ≤ T ^ μ := Real.one_le_rpow hT hμ.le
  let L : ℝ := |Real.log 2 - Real.log (1 / 2 : ℝ)| + 4 * Real.pi
  let A : ℝ := 8 * (1 + μ⁻¹) * 3 ^ μ
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hglobal :
      (4 * |((Real.log 2 + 2 * Real.pi * H / (2 * T)) -
          (Real.log (1 / 2 : ℝ) - 2 * Real.pi * H / (2 * T)))| +
        8 * (1 + μ⁻¹) * 3 ^ μ) * T ^ μ *
          (ApproxAddEnergy 1 W : ℝ) ≤
        (4 * L + A) * T ^ μ * (ApproxAddEnergy 1 W : ℝ) := by
    have hinside :
        4 * |((Real.log 2 + 2 * Real.pi * H / (2 * T)) -
            (Real.log (1 / 2 : ℝ) - 2 * Real.pi * H / (2 * T)))| +
          8 * (1 + μ⁻¹) * 3 ^ μ ≤ 4 * L + A := by
      dsimp only [L, A]
      nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hinside (Real.rpow_nonneg hTpos.le μ))
      (by positivity)
  have hpref := gmFourthLocalPackingPrefactor_le
    hT hH0 hN0 hdR
  have hraw := gmReducedRatioMoment_four_le_local_raw
    hμ hT hBase hN hd hHOne hq
  have hpair := cast_card_gmReducedRatioPairs_le_four_mul_sq N d
  calc
    gmReducedRatioMoment 4 N d W ≤ _ := hraw
    _ ≤ (19 * gmAffineLocalBumpFourierSup *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2)) *
          ((4 * L + A) * T ^ μ * (ApproxAddEnergy 1 W : ℝ)) +
        (4 * (N : ℝ) ^ 2) * (W.card : ℝ) ^ 4 *
          gmAffineLocalBumpFourierTailConstant q hq *
            H ^ (1 - (q : ℝ)) := by
      have hPref0 : 0 ≤ 19 * gmAffineLocalBumpFourierSup *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) := by
        exact mul_nonneg (mul_nonneg (by norm_num) gmAffineLocalBumpFourierSup_pos.le)
          (add_nonneg hTpos.le (by positivity))
      have hTail0 := gmAffineLocalBumpFourierTailConstant_pos q hq
      gcongr
    _ = _ := by
      dsimp only [gmSmallGcdL4Constant, L, A]
      ring

noncomputable def gmSmallGcdTailConstant (μ : ℝ) : ℝ :=
  gmAffineLocalBumpFourierTailConstant
    (gmReflectionDecayOrder 8 μ) (gmReflectionDecayOrder_two_le 8 μ)

noncomputable def gmSmallGcdL2SliceConstant (μ : ℝ) : ℝ :=
  gmSmallGcdL2Constant μ + 16 * gmSmallGcdTailConstant μ

noncomputable def gmSmallGcdL4SliceConstant (μ : ℝ) : ℝ :=
  gmSmallGcdL4Constant μ + 64 * gmSmallGcdTailConstant μ

theorem gmSmallGcdL2SliceConstant_pos {μ : ℝ} (hμ : 0 < μ) :
    0 < gmSmallGcdL2SliceConstant μ := by
  unfold gmSmallGcdL2SliceConstant gmSmallGcdTailConstant
  have hmain := gmSmallGcdL2Constant_pos hμ
  have htail := gmAffineLocalBumpFourierTailConstant_pos
    (gmReflectionDecayOrder 8 μ) (gmReflectionDecayOrder_two_le 8 μ)
  positivity

theorem gmSmallGcdL4SliceConstant_pos {μ : ℝ} (hμ : 0 < μ) :
    0 < gmSmallGcdL4SliceConstant μ := by
  unfold gmSmallGcdL4SliceConstant gmSmallGcdTailConstant
  have hmain := gmSmallGcdL4Constant_pos hμ
  have htail := gmAffineLocalBumpFourierTailConstant_pos
    (gmReflectionDecayOrder 8 μ) (gmReflectionDecayOrder_two_le 8 μ)
  positivity

theorem gmReducedRatioMoment_two_le_epsilon
    {μ T : ℝ} {N d : ℕ} {W : Finset ℝ}
    (hμ : 0 < μ) (hT : 1 ≤ T) (hSep : IsSeparated 1 W)
    (hBase : InBaseInterval T W) (hN : 0 < N) (hNT : (N : ℝ) ≤ T)
    (hd : 0 < d) :
    gmReducedRatioMoment 2 N d W ≤
      gmSmallGcdL2SliceConstant μ * T ^ μ *
        (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
          (W.card : ℝ) := by
  let H := gmReflectionHeight T μ
  let q := gmReflectionDecayOrder 8 μ
  let Ctail := gmSmallGcdTailConstant μ
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hHOne : 1 ≤ H := by
    dsimp only [H, gmReflectionHeight]
    exact Real.one_le_rpow hT (gmReflectionEta_pos hμ).le
  have hHT : H ≤ T := by
    dsimp only [H, gmReflectionHeight]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT gmReflectionEta_le_one
  have hq : 2 ≤ q := gmReflectionDecayOrder_two_le 8 μ
  have hCtail : 0 < Ctail := by
    dsimp only [Ctail, gmSmallGcdTailConstant, q]
    exact gmAffineLocalBumpFourierTailConstant_pos _ _
  have hmain := gmReducedRatioMoment_two_le_main_add_tail
    hμ hT hSep hBase hN hd hHOne hHT hq
  by_cases hWzero : W.card = 0
  · have hWempty : W = ∅ := Finset.card_eq_zero.mp hWzero
    subst W
    simp [gmReducedRatioMoment, gmR]
  have hWposNat : 0 < W.card := Nat.pos_of_ne_zero hWzero
  have hWone : (1 : ℝ) ≤ W.card := by exact_mod_cast hWposNat
  have hCard := gmSeparated_card_le_two_height hT hSep hBase
  have hTailBase :
      Ctail * H ^ (1 - (q : ℝ)) ≤ Ctail / T ^ (8 : ℝ) := by
    have h := gmLemma11ThreeFourierError_le
      (A := (8 : ℝ)) (ε := μ) (C := Ctail) (T := T) (M := 1)
      (by norm_num) hμ hCtail.le hT (by simpa using hT)
    simpa only [Nat.cast_one, one_mul, H, q] using h
  have hNsq : (N : ℝ) ^ 2 ≤ T ^ 2 :=
    pow_le_pow_left₀ (by positivity) hNT 2
  have hWsq : (W.card : ℝ) ^ 2 ≤ (2 * T) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hCard 2
  have hpower : T ^ (4 : ℕ) * (Ctail / T ^ (8 : ℝ)) ≤ Ctail := by
    have hpow : T ^ (4 : ℕ) ≤ T ^ (8 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
    calc
      T ^ (4 : ℕ) * (Ctail / T ^ (8 : ℝ)) ≤
          T ^ (8 : ℝ) * (Ctail / T ^ (8 : ℝ)) := by gcongr
      _ = Ctail := by field_simp
  have htail :
      4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 * Ctail *
          H ^ (1 - (q : ℝ)) ≤
        16 * Ctail * T ^ μ *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) * (W.card : ℝ) := by
    have hcore : 1 ≤ T ^ μ *
        (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) * (W.card : ℝ) := by
      have hTpow : 1 ≤ T ^ μ := Real.one_le_rpow hT hμ.le
      have hterm0 : 0 ≤ H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2 := by positivity
      have hsum : 1 ≤ T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2 := by linarith
      nlinarith [mul_le_mul hTpow hsum (by norm_num : (0 : ℝ) ≤ 1)
        (Real.rpow_nonneg hTpos.le μ)]
    have hpoly : 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 ≤
        16 * T ^ (4 : ℕ) := by
      calc
        4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 ≤
            4 * T ^ 2 * (2 * T) ^ 2 := by gcongr
        _ = 16 * T ^ (4 : ℕ) := by ring
    have hTailNonneg : 0 ≤ Ctail * H ^ (1 - (q : ℝ)) := by positivity
    calc
      4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 * Ctail *
          H ^ (1 - (q : ℝ)) =
        (4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2) *
          (Ctail * H ^ (1 - (q : ℝ))) := by ring
      _ ≤ 16 * T ^ (4 : ℕ) * (Ctail * H ^ (1 - (q : ℝ))) :=
        mul_le_mul_of_nonneg_right hpoly hTailNonneg
      _ ≤ 16 * T ^ (4 : ℕ) * (Ctail / T ^ (8 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hTailBase (by positivity)
      _ = 16 * (T ^ (4 : ℕ) * (Ctail / T ^ (8 : ℝ))) := by ring
      _ ≤ 16 * Ctail := mul_le_mul_of_nonneg_left hpower (by norm_num)
      _ ≤ 16 * Ctail * T ^ μ *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) * (W.card : ℝ) := by
        have := mul_le_mul_of_nonneg_left hcore (by positivity : 0 ≤ 16 * Ctail)
        nlinarith
  calc
    gmReducedRatioMoment 2 N d W ≤ _ := hmain
    _ ≤ gmSmallGcdL2Constant μ * T ^ μ *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) * (W.card : ℝ) +
        16 * Ctail * T ^ μ *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) * (W.card : ℝ) := by
      have htail' :
          4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 2 *
              gmAffineLocalBumpFourierTailConstant q hq * H ^ (1 - (q : ℝ)) ≤
            16 * Ctail * T ^ μ *
              (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) * (W.card : ℝ) := by
        simpa only [Ctail] using htail
      linarith
    _ = _ := by
      dsimp only [gmSmallGcdL2SliceConstant, Ctail, H]
      ring

theorem gmReducedRatioMoment_four_le_epsilon
    {μ T : ℝ} {N d : ℕ} {W : Finset ℝ}
    (hμ : 0 < μ) (hT : 1 ≤ T) (hSep : IsSeparated 1 W)
    (hBase : InBaseInterval T W) (hN : 0 < N) (hNT : (N : ℝ) ≤ T)
    (hd : 0 < d) :
    gmReducedRatioMoment 4 N d W ≤
      gmSmallGcdL4SliceConstant μ * T ^ μ *
        (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
          (ApproxAddEnergy 1 W : ℝ) := by
  let H := gmReflectionHeight T μ
  let q := gmReflectionDecayOrder 8 μ
  let Ctail := gmSmallGcdTailConstant μ
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hHOne : 1 ≤ H := by
    dsimp only [H, gmReflectionHeight]
    exact Real.one_le_rpow hT (gmReflectionEta_pos hμ).le
  have hHT : H ≤ T := by
    dsimp only [H, gmReflectionHeight]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT gmReflectionEta_le_one
  have hq : 2 ≤ q := gmReflectionDecayOrder_two_le 8 μ
  have hCtail : 0 < Ctail := by
    dsimp only [Ctail, gmSmallGcdTailConstant, q]
    exact gmAffineLocalBumpFourierTailConstant_pos _ _
  have hmain := gmReducedRatioMoment_four_le_main_add_tail
    hμ hT hBase hN hd hHOne hHT hq
  by_cases hWzero : W.card = 0
  · have hWempty : W = ∅ := Finset.card_eq_zero.mp hWzero
    subst W
    simp [gmReducedRatioMoment, gmR]
  have hWposNat : 0 < W.card := Nat.pos_of_ne_zero hWzero
  have hCard := gmSeparated_card_le_two_height hT hSep hBase
  have hTailBase :
      Ctail * H ^ (1 - (q : ℝ)) ≤ Ctail / T ^ (8 : ℝ) := by
    have h := gmLemma11ThreeFourierError_le
      (A := (8 : ℝ)) (ε := μ) (C := Ctail) (T := T) (M := 1)
      (by norm_num) hμ hCtail.le hT (by simpa using hT)
    simpa only [Nat.cast_one, one_mul, H, q] using h
  have hNsq : (N : ℝ) ^ 2 ≤ T ^ 2 :=
    pow_le_pow_left₀ (by positivity) hNT 2
  have hWfour : (W.card : ℝ) ^ 4 ≤ (2 * T) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hCard 4
  have hpower : T ^ (6 : ℕ) * (Ctail / T ^ (8 : ℝ)) ≤ Ctail := by
    have hpow : T ^ (6 : ℕ) ≤ T ^ (8 : ℝ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
    calc
      T ^ (6 : ℕ) * (Ctail / T ^ (8 : ℝ)) ≤
          T ^ (8 : ℝ) * (Ctail / T ^ (8 : ℝ)) := by gcongr
      _ = Ctail := by field_simp
  have henergyOne : (1 : ℝ) ≤ ApproxAddEnergy 1 W := by
    have hdiag := card_sq_le_approxAddEnergy (by norm_num : (0 : ℝ) ≤ 1) W
    have honeNat : 1 ≤ W.card ^ 2 := Nat.one_le_pow 2 W.card hWposNat
    have honeR : (1 : ℝ) ≤ (W.card ^ 2 : ℕ) := by exact_mod_cast honeNat
    have hdiagR : ((W.card ^ 2 : ℕ) : ℝ) ≤ ApproxAddEnergy 1 W := by
      exact_mod_cast hdiag
    exact honeR.trans hdiagR
  have htail :
      4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 4 * Ctail *
          H ^ (1 - (q : ℝ)) ≤
        64 * Ctail * T ^ μ *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
            (ApproxAddEnergy 1 W : ℝ) := by
    have hTpow : 1 ≤ T ^ μ := Real.one_le_rpow hT hμ.le
    have hterm0 : 0 ≤ H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2 := by positivity
    have hsum : 1 ≤ T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2 := by linarith
    have hcore : 1 ≤ T ^ μ *
        (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
          (ApproxAddEnergy 1 W : ℝ) := by
      have hmul := mul_le_mul hTpow hsum (by norm_num : (0 : ℝ) ≤ 1)
        (Real.rpow_nonneg hTpos.le μ)
      nlinarith
    have hpoly : 4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 4 ≤
        64 * T ^ (6 : ℕ) := by
      calc
        4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 4 ≤
            4 * T ^ 2 * (2 * T) ^ 4 := by gcongr
        _ = 64 * T ^ (6 : ℕ) := by ring
    have hTailNonneg : 0 ≤ Ctail * H ^ (1 - (q : ℝ)) := by positivity
    calc
      4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 4 * Ctail *
          H ^ (1 - (q : ℝ)) =
        (4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 4) *
          (Ctail * H ^ (1 - (q : ℝ))) := by ring
      _ ≤ 64 * T ^ (6 : ℕ) * (Ctail * H ^ (1 - (q : ℝ))) :=
        mul_le_mul_of_nonneg_right hpoly hTailNonneg
      _ ≤ 64 * T ^ (6 : ℕ) * (Ctail / T ^ (8 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hTailBase (by positivity)
      _ = 64 * (T ^ (6 : ℕ) * (Ctail / T ^ (8 : ℝ))) := by ring
      _ ≤ 64 * Ctail := mul_le_mul_of_nonneg_left hpower (by norm_num)
      _ ≤ 64 * Ctail * T ^ μ *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
            (ApproxAddEnergy 1 W : ℝ) := by
        have := mul_le_mul_of_nonneg_left hcore (by positivity : 0 ≤ 64 * Ctail)
        nlinarith
  calc
    gmReducedRatioMoment 4 N d W ≤ _ := hmain
    _ ≤ gmSmallGcdL4Constant μ * T ^ μ *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
            (ApproxAddEnergy 1 W : ℝ) +
        64 * Ctail * T ^ μ *
          (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
            (ApproxAddEnergy 1 W : ℝ) := by
      have htail' :
          4 * (N : ℝ) ^ 2 * (W.card : ℝ) ^ 4 *
              gmAffineLocalBumpFourierTailConstant q hq * H ^ (1 - (q : ℝ)) ≤
            64 * Ctail * T ^ μ *
              (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
                (ApproxAddEnergy 1 W : ℝ) := by
        simpa only [Ctail] using htail
      linarith
    _ = _ := by
      dsimp only [gmSmallGcdL4SliceConstant, Ctail, H]
      ring

noncomputable def gmSmallGcdL3SliceConstant (μ : ℝ) : ℝ :=
  Real.sqrt (gmSmallGcdL2SliceConstant μ) *
    Real.sqrt (gmSmallGcdL4SliceConstant μ)

theorem gmSmallGcdL3SliceConstant_pos {μ : ℝ} (hμ : 0 < μ) :
    0 < gmSmallGcdL3SliceConstant μ := by
  unfold gmSmallGcdL3SliceConstant
  exact mul_pos (Real.sqrt_pos.2 (gmSmallGcdL2SliceConstant_pos hμ))
    (Real.sqrt_pos.2 (gmSmallGcdL4SliceConstant_pos hμ))

theorem gmReducedRatioMoment_three_le_epsilon
    {μ T : ℝ} {N d : ℕ} {W : Finset ℝ}
    (hμ : 0 < μ) (hT : 1 ≤ T) (hSep : IsSeparated 1 W)
    (hBase : InBaseInterval T W) (hN : 0 < N) (hNT : (N : ℝ) ≤ T)
    (hd : 0 < d) :
    gmReducedRatioMoment 3 N d W ≤
      gmSmallGcdL3SliceConstant μ * T ^ μ *
        (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
          Real.sqrt (W.card : ℝ) *
            Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
  let P : ℝ := T ^ μ *
    (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2)
  let C₂ := gmSmallGcdL2SliceConstant μ
  let C₄ := gmSmallGcdL4SliceConstant μ
  have hP : 0 ≤ P := by
    dsimp only [P]
    have hterm0 : 0 ≤
        gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
      exact div_nonneg (mul_nonneg
        (Real.rpow_nonneg (zero_lt_one.trans_le hT).le _) (sq_nonneg _))
        (sq_nonneg _)
    exact mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans_le hT).le μ)
      (add_nonneg (zero_lt_one.trans_le hT).le hterm0)
  have hC₂ : 0 ≤ C₂ := (gmSmallGcdL2SliceConstant_pos hμ).le
  have hC₄ : 0 ≤ C₄ := (gmSmallGcdL4SliceConstant_pos hμ).le
  have htwo := gmReducedRatioMoment_two_le_epsilon
    hμ hT hSep hBase hN hNT hd
  have hfour := gmReducedRatioMoment_four_le_epsilon
    hμ hT hSep hBase hN hNT hd
  have hthird := gmReducedThirdMoment_le_sqrt N d W
  have htwoSqrt : Real.sqrt (gmReducedRatioMoment 2 N d W) ≤
      Real.sqrt (C₂ * P * (W.card : ℝ)) := by
    apply Real.sqrt_le_sqrt
    simpa only [C₂, P, mul_assoc] using htwo
  have hfourSqrt : Real.sqrt (gmReducedRatioMoment 4 N d W) ≤
      Real.sqrt (C₄ * P * (ApproxAddEnergy 1 W : ℝ)) := by
    apply Real.sqrt_le_sqrt
    simpa only [C₄, P, mul_assoc] using hfour
  calc
    gmReducedRatioMoment 3 N d W ≤
        Real.sqrt (gmReducedRatioMoment 2 N d W) *
          Real.sqrt (gmReducedRatioMoment 4 N d W) := hthird
    _ ≤ Real.sqrt (C₂ * P * (W.card : ℝ)) *
          Real.sqrt (C₄ * P * (ApproxAddEnergy 1 W : ℝ)) := by
      exact mul_le_mul htwoSqrt hfourSqrt (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    _ = gmSmallGcdL3SliceConstant μ * T ^ μ *
        (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
          Real.sqrt (W.card : ℝ) *
            Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
      rw [Real.sqrt_mul (mul_nonneg hC₂ hP), Real.sqrt_mul hC₂,
        Real.sqrt_mul (mul_nonneg hC₄ hP), Real.sqrt_mul hC₄]
      have hPsqrt : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP
      have hPsqrt' :
          Real.sqrt (T ^ μ *
              (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2)) *
              Real.sqrt (T ^ μ *
                (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2)) =
            T ^ μ *
              (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) := by
        simpa only [P] using hPsqrt
      calc
        _ = (Real.sqrt (gmSmallGcdL2SliceConstant μ) *
              Real.sqrt (gmSmallGcdL4SliceConstant μ)) *
              (Real.sqrt (T ^ μ *
                  (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2)) *
                Real.sqrt (T ^ μ *
                  (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2))) *
                Real.sqrt (W.card : ℝ) *
                  Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by ring
        _ = _ := by
          rw [hPsqrt']
          simp only [gmSmallGcdL3SliceConstant]
          ring

/-! ### Guth--Maynard Lemma 11.8: the summed small-gcd range -/

/-- The part of the cubic ratio moment whose exact gcd is at most `D`. -/
noncomputable def gmSmallGcdThirdMoment
    (N D : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, gmGcdSliceMoment 3 N d W

theorem gmSmallGcdThirdMoment_eq_reduced
    (N D : ℕ) (W : Finset ℝ) :
    gmSmallGcdThirdMoment N D W =
      ∑ d ∈ Finset.Icc 1 D, gmReducedRatioMoment 3 N d W := by
  unfold gmSmallGcdThirdMoment
  apply Finset.sum_congr rfl
  intro d hd
  exact gmGcdSliceMoment_eq_reduced 3 N d W

theorem sum_smallGcd_local_scales_le
    {T H : ℝ} {N D : ℕ} (hT : 0 ≤ T) (hH : 0 ≤ H) :
    (∑ d ∈ Finset.Icc 1 D,
        (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2)) ≤
      (D : ℝ) * T + 2 * H * (N : ℝ) ^ 2 := by
  have hrecip := sum_Icc_one_div_sq_le_two D
  calc
    (∑ d ∈ Finset.Icc 1 D,
        (T + H * (N : ℝ) ^ 2 / (d : ℝ) ^ 2)) =
        ((Finset.Icc 1 D).card : ℝ) * T +
          H * (N : ℝ) ^ 2 *
            (∑ d ∈ Finset.Icc 1 D, (1 : ℝ) / (d : ℝ) ^ 2) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply congrArg₂ (· + ·) rfl
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (D : ℝ) * T + H * (N : ℝ) ^ 2 * 2 := by
      have hcard : ((Finset.Icc 1 D).card : ℝ) ≤ D := by
        simp only [Nat.card_Icc]
        norm_cast
      gcongr
    _ = (D : ℝ) * T + 2 * H * (N : ℝ) ^ 2 := by ring

noncomputable def gmSmallGcdSumConstant (μ : ℝ) : ℝ :=
  gmSmallGcdL3SliceConstant μ

theorem gmSmallGcdSumConstant_pos {μ : ℝ} (hμ : 0 < μ) :
    0 < gmSmallGcdSumConstant μ :=
  gmSmallGcdL3SliceConstant_pos hμ

/-- Lemma 11.8 before the harmless `T^ε` absorption.  The exact source
factor `D*T + H*N^2` remains visible here. -/
theorem gmSmallGcdThirdMoment_le_raw
    {μ T : ℝ} {N D : ℕ} {W : Finset ℝ}
    (hμ : 0 < μ) (hT : 1 ≤ T) (hSep : IsSeparated 1 W)
    (hBase : InBaseInterval T W) (hN : 0 < N) (hNT : (N : ℝ) ≤ T) :
    gmSmallGcdThirdMoment N D W ≤
      gmSmallGcdSumConstant μ * T ^ μ *
        ((D : ℝ) * T +
          2 * gmReflectionHeight T μ * (N : ℝ) ^ 2) *
            Real.sqrt (W.card : ℝ) *
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
  rw [gmSmallGcdThirdMoment_eq_reduced]
  have hSlice : ∀ d ∈ Finset.Icc 1 D,
      gmReducedRatioMoment 3 N d W ≤
        gmSmallGcdSumConstant μ * T ^ μ *
          (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
            Real.sqrt (W.card : ℝ) *
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
    intro d hd
    exact gmReducedRatioMoment_three_le_epsilon hμ hT hSep hBase hN hNT
      (Finset.mem_Icc.mp hd).1
  calc
    (∑ d ∈ Finset.Icc 1 D, gmReducedRatioMoment 3 N d W) ≤
        ∑ d ∈ Finset.Icc 1 D,
          gmSmallGcdSumConstant μ * T ^ μ *
            (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2) *
              Real.sqrt (W.card : ℝ) *
                Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
      exact Finset.sum_le_sum fun d hd => hSlice d hd
    _ = gmSmallGcdSumConstant μ * T ^ μ *
          (∑ d ∈ Finset.Icc 1 D,
            (T + gmReflectionHeight T μ * (N : ℝ) ^ 2 / (d : ℝ) ^ 2)) *
              Real.sqrt (W.card : ℝ) *
                Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ gmSmallGcdSumConstant μ * T ^ μ *
          ((D : ℝ) * T +
            2 * gmReflectionHeight T μ * (N : ℝ) ^ 2) *
              Real.sqrt (W.card : ℝ) *
                Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
      have hsum := sum_smallGcd_local_scales_le
        (H := gmReflectionHeight T μ) (N := N) (D := D)
        (zero_le_one.trans hT)
        (Real.rpow_nonneg (zero_le_one.trans hT) (gmReflectionEta μ))
      have hpref : 0 ≤ gmSmallGcdSumConstant μ * T ^ μ :=
        mul_nonneg (gmSmallGcdSumConstant_pos hμ).le
          (Real.rpow_nonneg (zero_le_one.trans hT) μ)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsum hpref) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)

/-- Guth--Maynard Lemma 11.8 in the epsilon-uniform form used by
Proposition 11.1. -/
theorem gmSmallGcdThirdMoment_native
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ {N D : ℕ} {T : ℝ} (W : Finset ℝ),
        0 < N → T₀ ≤ T → (N : ℝ) ≤ T →
        IsSeparated 1 W → InBaseInterval T W →
        gmSmallGcdThirdMoment N D W ≤
          C * T ^ ε * ((D : ℝ) * T + (N : ℝ) ^ 2) *
            Real.sqrt (W.card : ℝ) *
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
  let μ : ℝ := ε / 4
  let C : ℝ := 2 * gmSmallGcdSumConstant μ
  refine ⟨C, 1, ?_, by norm_num, ?_⟩
  · dsimp only [C]
    exact mul_pos (by norm_num) (gmSmallGcdSumConstant_pos (by dsimp only [μ]; positivity))
  intro N D T W hN hT hNT hSep hBase
  have hTOne : 1 ≤ T := hT
  have hTPos : 0 < T := zero_lt_one.trans_le hTOne
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have hraw := gmSmallGcdThirdMoment_le_raw (D := D)
    hμ hTOne hSep hBase hN hNT
  have hEta : gmReflectionEta μ ≤ μ := (gmReflectionEta_lt_eps hμ).le
  have hHeight : gmReflectionHeight T μ ≤ T ^ μ := by
    unfold gmReflectionHeight
    exact Real.rpow_le_rpow_of_exponent_le hTOne hEta
  have hScale :
      (D : ℝ) * T + 2 * gmReflectionHeight T μ * (N : ℝ) ^ 2 ≤
        2 * T ^ μ * ((D : ℝ) * T + (N : ℝ) ^ 2) := by
    have hDT : 0 ≤ (D : ℝ) * T := by positivity
    have hN2 : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
    have hPowOne : 1 ≤ T ^ μ := Real.one_le_rpow hTOne hμ.le
    calc
      (D : ℝ) * T + 2 * gmReflectionHeight T μ * (N : ℝ) ^ 2 ≤
          (D : ℝ) * T + 2 * T ^ μ * (N : ℝ) ^ 2 := by gcongr
      _ ≤ 2 * T ^ μ * ((D : ℝ) * T + (N : ℝ) ^ 2) := by nlinarith
  have hBudget : 2 * μ ≤ ε := by dsimp only [μ]; linarith
  have hPowBudget : T ^ (2 * μ) ≤ T ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hTOne hBudget
  calc
    gmSmallGcdThirdMoment N D W ≤
        gmSmallGcdSumConstant μ * T ^ μ *
          ((D : ℝ) * T + 2 * gmReflectionHeight T μ * (N : ℝ) ^ 2) *
            Real.sqrt (W.card : ℝ) *
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) := hraw
    _ ≤ gmSmallGcdSumConstant μ * T ^ μ *
          (2 * T ^ μ * ((D : ℝ) * T + (N : ℝ) ^ 2)) *
            Real.sqrt (W.card : ℝ) *
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
      have hpref : 0 ≤ gmSmallGcdSumConstant μ * T ^ μ :=
        mul_nonneg (gmSmallGcdSumConstant_pos hμ).le
          (Real.rpow_nonneg hTPos.le μ)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hScale hpref) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    _ = C * T ^ (2 * μ) * ((D : ℝ) * T + (N : ℝ) ^ 2) *
          Real.sqrt (W.card : ℝ) *
            Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
      dsimp only [C]
      rw [show 2 * μ = μ + μ by ring, Real.rpow_add hTPos]
      ring
    _ ≤ C * T ^ ε * ((D : ℝ) * T + (N : ℝ) ^ 2) *
          Real.sqrt (W.card : ℝ) *
            Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
      have hC0 : 0 ≤ C := by
        dsimp only [C]
        exact mul_nonneg (by norm_num) (gmSmallGcdSumConstant_pos hμ).le
      have hShape0 : 0 ≤ ((D : ℝ) * T + (N : ℝ) ^ 2) := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hPowBudget hC0) hShape0)
          (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)

end RiemannZeta.GuthMaynard
