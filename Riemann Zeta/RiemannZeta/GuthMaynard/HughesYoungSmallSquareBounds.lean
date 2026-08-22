import RiemannZeta.GuthMaynard.HughesYoungInfiniteTransfer

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Uniform bounds for the finite Hughes--Young small-contour square

This module assembles the moving-Gamma estimate with the uniform Gaussian
ordinate majorant.  It supplies the quantitative bounds needed to pass from
finite Mellin height to the literal whole small-contour integral.
-/

/-- The literal small-contour weight is uniformly dominated by a Gaussian.
The factors `log T` and `exp (4 C)` are the exact specializations of
`c⁻¹` and `T^(4 C c)` at `c = 1 / log T`. -/
theorem exists_norm_hughesYoungRightContourWeight_small_le_gaussian :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {T t u : ℝ},
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) →
      ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ ≤
        Real.log T * Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_height_power
  obtain ⟨K, hK, hgaussian⟩ :=
    exists_hughesYoungIntegratedOrdinateFactor_le_gaussian hC
  refine ⟨C, K, hC, hK, ?_⟩
  intro T t u hT ht
  obtain ⟨hc, hc1, hcinv⟩ := hughesYoungSmallContour_spec hT
  have hT1 : 1 ≤ T := (Real.one_le_exp (by norm_num)).trans hT
  have hraw := hweight T t u (hughesYoungSmallContour T) hT1 ht hc hc1
  have hord :
      Real.exp
          (100 * hughesYoungSmallContour T ^ 2 - 84 * u ^ 2 +
            4 * C * hughesYoungSmallContour T *
              Real.log (6 * (|u| + 1))) *
          (25 + 8 * u ^ 2) ^ 8 ≤
        hughesYoungIntegratedOrdinateFactor C (hughesYoungSmallContour T) u := by
    unfold hughesYoungIntegratedOrdinateFactor
    gcongr
    norm_num
  calc
    ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ ≤
        (hughesYoungSmallContour T)⁻¹ *
          T ^ (4 * C * hughesYoungSmallContour T) *
          (Real.exp
            (100 * hughesYoungSmallContour T ^ 2 - 84 * u ^ 2 +
              4 * C * hughesYoungSmallContour T *
                Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8) := hraw
    _ ≤ (hughesYoungSmallContour T)⁻¹ *
          T ^ (4 * C * hughesYoungSmallContour T) *
          hughesYoungIntegratedOrdinateFactor C
            (hughesYoungSmallContour T) u := by
      gcongr
    _ ≤ Real.log T * Real.exp (4 * C) *
          (K * Real.exp (-80 * u ^ 2)) := by
      rw [hcinv, rpow_smallContour_four_mul_eq C hT]
      have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
      exact mul_le_mul_of_nonneg_left (hgaussian hc hc1 u)
        (mul_nonneg hlog (Real.exp_pos _).le)
    _ = Real.log T * Real.exp (4 * C) * K *
          Real.exp (-80 * u ^ 2) := by ring

/-- Uniform finite-interval mass of the literal small-contour weight. -/
theorem exists_uniform_intervalIntegral_norm_hughesYoungRightContourWeight_small_le :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {T t H : ℝ},
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) → 0 ≤ H →
      (∫ u in -H..H,
        ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖) ≤
        Real.log T * Real.exp (4 * C) * K *
          Real.sqrt (Real.pi / 80) := by
  obtain ⟨C, K, hC, hK, hpoint⟩ :=
    exists_norm_hughesYoungRightContourWeight_small_le_gaussian
  refine ⟨C, K, hC, hK, ?_⟩
  intro T t H hT ht hH
  have horder : -H ≤ H := by linarith
  have hpairInt := integrable_hughesYoungRightPairTerm_small
    hT ht (m := 1) (n := 1) (by norm_num) (by norm_num)
  have hweightWhole : Integrable (fun u : ℝ =>
      hughesYoungRightContourWeight t (hughesYoungSmallContour T) u) := by
    simpa [hughesYoungRightPairTerm, divisorDirichletTerm] using hpairInt
  have hweightInt : IntervalIntegrable
      (fun u : ℝ => ‖hughesYoungRightContourWeight t
        (hughesYoungSmallContour T) u‖) volume (-H) H :=
    hweightWhole.norm.intervalIntegrable
  have hgauss : Integrable (fun u : ℝ =>
      Real.log T * Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2)) := by
    simpa only [mul_assoc] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 80)).const_mul
        (Real.log T * Real.exp (4 * C) * K)
  calc
    (∫ u in -H..H,
        ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖) ≤
        ∫ u in -H..H,
          Real.log T * Real.exp (4 * C) * K *
            Real.exp (-80 * u ^ 2) := by
      apply intervalIntegral.integral_mono_on horder hweightInt
        hgauss.intervalIntegrable
      intro u _hu
      exact hpoint hT ht
    _ ≤ ∫ u : ℝ,
          Real.log T * Real.exp (4 * C) * K *
            Real.exp (-80 * u ^ 2) := by
      rw [intervalIntegral.integral_of_le horder]
      apply setIntegral_le_integral hgauss
      filter_upwards with u
      have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hK.le)
        (Real.exp_pos _).le
    _ = Real.log T * Real.exp (4 * C) * K *
          Real.sqrt (Real.pi / 80) := by
      rw [integral_const_mul, integral_gaussian]

/-- A divisor Dirichlet term on a nonnegative real line is bounded by its
positive integer index. -/
theorem norm_divisorDirichletTerm_afe_nonneg_le_nat
    {t c : ℝ} {n : ℕ} (hn : 0 < n) (hc : 0 ≤ c) :
    ‖divisorDirichletTerm (afeCriticalPoint t + (c : ℂ)) n‖ ≤ (n : ℝ) := by
  rw [divisorDirichletTerm, LSeries.norm_term_eq, if_neg hn.ne']
  have hcard : (n.divisors.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self n
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 1 ≤ (n : ℝ) ^ (afeCriticalPoint t + (c : ℂ)).re := by
    apply Real.one_le_rpow hnOne
    have hre : (afeCriticalPoint t + (c : ℂ)).re = 1 / 2 + c := by
      simp [afeCriticalPoint]
    rw [hre]
    linarith
  have hcoeff : ‖(n.divisors.card : ℂ)‖ = (n.divisors.card : ℝ) := by simp
  rw [hcoeff]
  exact (div_le_self (by positivity) hden).trans hcard

/-- The finite square on the small contour has the crude but uniform `M⁴`
majorant used in the Hughes--Young transfer. -/
theorem norm_hughesYoungIntegratedSmallPairSquare_le
    {T t H : ℝ} {M : ℕ} (hM : 0 < M) (hH : 0 ≤ H)
    (hc : 0 < hughesYoungSmallContour T) :
    ‖hughesYoungIntegratedSmallPairSquare T t H M‖ ≤
      (M : ℝ) ^ 4 *
        (∫ u in -H..H,
          ‖hughesYoungRightContourWeight t
            (hughesYoungSmallContour T) u‖) := by
  classical
  let S : Finset (ℕ × ℕ) := Finset.Icc (1, 1) (M, M)
  let W : ℝ := ∫ u in -H..H,
    ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖
  have horder : -H ≤ H := by linarith
  have hW : 0 ≤ W := by
    unfold W
    exact intervalIntegral.integral_nonneg horder fun _ _ => norm_nonneg _
  have hterm : ∀ p ∈ S,
      ‖∫ u in -H..H,
          hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ ≤
        (M : ℝ) ^ 2 * W := by
    intro p hp
    have hpI := Finset.mem_Icc.mp hp
    have hpLower := Prod.le_def.mp hpI.1
    have hpUpper := Prod.le_def.mp hpI.2
    have hp1 : 0 < p.1 := Nat.zero_lt_one.trans_le hpLower.1
    have hp2 : 0 < p.2 := Nat.zero_lt_one.trans_le hpLower.2
    have hd1 := norm_divisorDirichletTerm_afe_nonneg_le_nat
      (t := t) hp1 hc.le
    have hd2 := norm_divisorDirichletTerm_afe_nonneg_le_nat
      (t := -t) hp2 hc.le
    have hp1M : (p.1 : ℝ) ≤ M := by exact_mod_cast hpUpper.1
    have hp2M : (p.2 : ℝ) ≤ M := by exact_mod_cast hpUpper.2
    calc
      ‖∫ u in -H..H,
          hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ ≤
          ∫ u in -H..H,
            ‖hughesYoungRightPairTerm t
              (hughesYoungSmallContour T) u p‖ :=
        intervalIntegral.norm_integral_le_integral_norm horder
      _ = ∫ u in -H..H,
            (‖divisorDirichletTerm
                (afeCriticalPoint t +
                  (hughesYoungSmallContour T : ℂ)) p.1‖ *
              ‖divisorDirichletTerm
                (afeCriticalPoint (-t) +
                  (hughesYoungSmallContour T : ℂ)) p.2‖) *
              ‖hughesYoungRightContourWeight t
                (hughesYoungSmallContour T) u‖ := by
        apply intervalIntegral.integral_congr
        intro u _hu
        simp only [hughesYoungRightPairTerm]
        rw [norm_mul, norm_mul,
          norm_divisorDirichletTerm_afe_vertical,
          norm_divisorDirichletTerm_afe_vertical]
        ring
      _ = (‖divisorDirichletTerm
                (afeCriticalPoint t +
                  (hughesYoungSmallContour T : ℂ)) p.1‖ *
              ‖divisorDirichletTerm
                (afeCriticalPoint (-t) +
                  (hughesYoungSmallContour T : ℂ)) p.2‖) * W := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ((M : ℝ) * M) * W := by
        gcongr
        · exact hd1.trans hp1M
        · exact hd2.trans hp2M
      _ = (M : ℝ) ^ 2 * W := by ring
  unfold hughesYoungIntegratedSmallPairSquare
  change ‖∑ p ∈ S, ∫ u in -H..H,
      hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ ≤ _
  calc
    _ ≤ ∑ p ∈ S, ‖∫ u in -H..H,
        hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ S, (M : ℝ) ^ 2 * W := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ = (S.card : ℝ) * ((M : ℝ) ^ 2 * W) := by simp
    _ ≤ (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 * W) := by
      gcongr
      change (S.card : ℝ) ≤ (M : ℝ) ^ 2
      have hScard : S.card = M ^ 2 := by
        simp [S, Finset.card_Icc_prod, pow_two]
      rw [hScard, Nat.cast_pow]
    _ = (M : ℝ) ^ 4 * W := by ring

/-- Removing `[-H,H]` from the `exp (-80 u²)` Gaussian costs
`exp (-40 H²)` and leaves an exactly integrable `exp (-40 u²)` factor. -/
theorem integral_compl_Ioc_exp_neg_eighty_sq_le
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ u in (Set.Ioc (-H) H)ᶜ, Real.exp (-80 * u ^ 2)) ≤
      Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40) := by
  let g : ℝ → ℝ := fun u =>
    Real.exp (-40 * H ^ 2) * Real.exp (-40 * u ^ 2)
  have hsource : Integrable (fun u : ℝ => Real.exp (-80 * u ^ 2)) := by
    simpa only [neg_mul] using
      integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 80)
  have hg : Integrable g := by
    simpa only [g] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 40)).const_mul
        (Real.exp (-40 * H ^ 2))
  have hpoint : ∀ u ∈ (Set.Ioc (-H) H)ᶜ,
      Real.exp (-80 * u ^ 2) ≤ g u := by
    intro u hu
    have hHu : H ≤ |u| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or] at hu
      rcases hu with hu | hu
      · have hut : u ≤ -H := le_of_not_gt hu
        rw [abs_of_nonpos (hut.trans (neg_nonpos.mpr hH))]
        linarith
      · have hut : H < u := lt_of_not_ge hu
        rw [abs_of_nonneg (hH.trans hut.le)]
        exact hut.le
    have hsq : H ^ 2 ≤ u ^ 2 := by
      rw [← sq_abs u]
      nlinarith [sq_nonneg (|u| - H)]
    unfold g
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    (∫ u in (Set.Ioc (-H) H)ᶜ, Real.exp (-80 * u ^ 2)) ≤
        ∫ u in (Set.Ioc (-H) H)ᶜ, g u :=
      MeasureTheory.setIntegral_mono_on hsource.integrableOn hg.integrableOn
        measurableSet_Ioc.compl hpoint
    _ ≤ ∫ u : ℝ, g u := by
      apply MeasureTheory.setIntegral_le_integral hg
      filter_upwards with u
      unfold g
      positivity
    _ = Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40) := by
      unfold g
      rw [integral_const_mul, integral_gaussian]

/-- Norm control for deleting a symmetric interval from an integrable
complex-valued function. -/
theorem norm_integral_sub_intervalIntegral_le_compl_integral_norm
    {f : ℝ → ℂ} (hf : Integrable f) {H : ℝ} (hH : 0 ≤ H) :
    ‖(∫ u : ℝ, f u) - ∫ u in -H..H, f u‖ ≤
      ∫ u in (Set.Ioc (-H) H)ᶜ, ‖f u‖ := by
  rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H),
    ← MeasureTheory.setIntegral_compl measurableSet_Ioc hf]
  exact MeasureTheory.norm_integral_le_integral_norm _

/-- Quantitative tail for one positive pair in a finite square. -/
theorem norm_hughesYoungWholePairTerm_sub_interval_le
    {C D : ℝ} {T t H : ℝ} {M : ℕ} {p : ℕ × ℕ}
    (hD : 0 < D)
    (hweight : ∀ {T t u : ℝ},
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) →
      ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ ≤
        Real.log T * Real.exp (4 * C) * D * Real.exp (-80 * u ^ 2))
    (hT : Real.exp 1 ≤ T) (ht : t ∈ Set.Icc (T / 4) (4 * T))
    (hH : 0 ≤ H) (hM : 0 < M) (hp1 : 0 < p.1) (hp2 : 0 < p.2)
    (hp1M : p.1 ≤ M) (hp2M : p.2 ≤ M) :
    ‖(∫ u : ℝ,
        hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p) -
      ∫ u in -H..H,
        hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ ≤
      (Real.log T * Real.exp (4 * C) * D * (M : ℝ) ^ 2) *
        (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hA : 0 ≤ Real.log T * Real.exp (4 * C) * D := by
    exact mul_nonneg
      (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hD.le
  have hd1 := norm_divisorDirichletTerm_afe_nonneg_le_nat
    (t := t) hp1 (hughesYoungSmallContour_spec hT).1.le
  have hd2 := norm_divisorDirichletTerm_afe_nonneg_le_nat
    (t := -t) hp2 (hughesYoungSmallContour_spec hT).1.le
  have hp1MR : (p.1 : ℝ) ≤ M := by exact_mod_cast hp1M
  have hp2MR : (p.2 : ℝ) ≤ M := by exact_mod_cast hp2M
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hpairInt := integrable_hughesYoungRightPairTerm_small hT ht hp1 hp2
  calc
    ‖(∫ u : ℝ,
        hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p) -
      ∫ u in -H..H,
        hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ ≤
        ∫ u in (Set.Ioc (-H) H)ᶜ,
          ‖hughesYoungRightPairTerm t
            (hughesYoungSmallContour T) u p‖ :=
      norm_integral_sub_intervalIntegral_le_compl_integral_norm hpairInt hH
    _ ≤ ∫ u in (Set.Ioc (-H) H)ᶜ,
          ((M : ℝ) ^ 2 *
            (Real.log T * Real.exp (4 * C) * D)) *
              Real.exp (-80 * u ^ 2) := by
      apply MeasureTheory.setIntegral_mono_on hpairInt.norm.integrableOn
      · exact ((integrable_exp_neg_mul_sq
            (by norm_num : (0 : ℝ) < 80)).const_mul
              ((M : ℝ) ^ 2 *
                (Real.log T * Real.exp (4 * C) * D))).integrableOn
      · exact measurableSet_Ioc.compl
      · intro u _hu
        unfold hughesYoungRightPairTerm
        rw [norm_mul, norm_mul,
          norm_divisorDirichletTerm_afe_vertical,
          norm_divisorDirichletTerm_afe_vertical]
        calc
          ‖hughesYoungRightContourWeight t
                (hughesYoungSmallContour T) u‖ *
              ‖divisorDirichletTerm
                (afeCriticalPoint t +
                  (hughesYoungSmallContour T : ℂ)) p.1‖ *
              ‖divisorDirichletTerm
                (afeCriticalPoint (-t) +
                  (hughesYoungSmallContour T : ℂ)) p.2‖ ≤
            ((Real.log T * Real.exp (4 * C) * D) *
                Real.exp (-80 * u ^ 2)) * M * M := by
              gcongr
              · exact hweight hT ht
              · exact hd1.trans hp1MR
              · exact hd2.trans hp2MR
          _ = ((M : ℝ) ^ 2 *
                (Real.log T * Real.exp (4 * C) * D)) *
              Real.exp (-80 * u ^ 2) := by ring
    _ = ((M : ℝ) ^ 2 *
          (Real.log T * Real.exp (4 * C) * D)) *
        (∫ u in (Set.Ioc (-H) H)ᶜ,
          Real.exp (-80 * u ^ 2)) := by
      rw [integral_const_mul]
    _ ≤ ((M : ℝ) ^ 2 *
          (Real.log T * Real.exp (4 * C) * D)) *
        (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
      exact mul_le_mul_of_nonneg_left
        (integral_compl_Ioc_exp_neg_eighty_sq_le hH)
        (mul_nonneg (pow_nonneg hMR.le 2) hA)
    _ = (Real.log T * Real.exp (4 * C) * D * (M : ℝ) ^ 2) *
        (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by ring

/-- Uniform quantitative removal of the finite ordinate cutoff from the
literal finite small-contour square. -/
theorem exists_norm_hughesYoungWholeSmallPairSquare_sub_integrated_le :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {T t H : ℝ} {M : ℕ},
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) →
      0 ≤ H → 0 < M →
      ‖hughesYoungWholeSmallPairSquare T t M -
          hughesYoungIntegratedSmallPairSquare T t H M‖ ≤
        Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
          (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
  obtain ⟨C, K, hC, hK, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_small_le_gaussian
  refine ⟨C, K, hC, hK, ?_⟩
  intro T t H M hT ht hH hM
  classical
  let S : Finset (ℕ × ℕ) := Finset.Icc (1, 1) (M, M)
  let A : ℝ := Real.log T * Real.exp (4 * C) * K
  let G : ℝ := Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hA : 0 ≤ A := by
    unfold A
    exact mul_nonneg
      (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hK.le
  have hG : 0 ≤ G := by unfold G; positivity
  have hterm : ∀ p ∈ S,
      ‖(∫ u : ℝ,
          hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p) -
        ∫ u in -H..H,
          hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ ≤
        (M : ℝ) ^ 2 * (A * G) := by
    intro p hp
    have hpI := Finset.mem_Icc.mp hp
    have hpLower := Prod.le_def.mp hpI.1
    have hpUpper := Prod.le_def.mp hpI.2
    have hp1 : 0 < p.1 := Nat.zero_lt_one.trans_le hpLower.1
    have hp2 : 0 < p.2 := Nat.zero_lt_one.trans_le hpLower.2
    have hd1 := norm_divisorDirichletTerm_afe_nonneg_le_nat
      (t := t) hp1 (hughesYoungSmallContour_spec hT).1.le
    have hd2 := norm_divisorDirichletTerm_afe_nonneg_le_nat
      (t := -t) hp2 (hughesYoungSmallContour_spec hT).1.le
    have hp1M : (p.1 : ℝ) ≤ M := by exact_mod_cast hpUpper.1
    have hp2M : (p.2 : ℝ) ≤ M := by exact_mod_cast hpUpper.2
    have hpairInt := integrable_hughesYoungRightPairTerm_small hT ht hp1 hp2
    have htail := norm_integral_sub_intervalIntegral_le_compl_integral_norm
      hpairInt hH
    calc
      ‖(∫ u : ℝ,
          hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p) -
        ∫ u in -H..H,
          hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ ≤
          ∫ u in (Set.Ioc (-H) H)ᶜ,
            ‖hughesYoungRightPairTerm t
              (hughesYoungSmallContour T) u p‖ := htail
      _ ≤ ∫ u in (Set.Ioc (-H) H)ᶜ,
            ((M : ℝ) ^ 2 * A) * Real.exp (-80 * u ^ 2) := by
        apply MeasureTheory.setIntegral_mono_on hpairInt.norm.integrableOn
        · exact ((integrable_exp_neg_mul_sq
              (by norm_num : (0 : ℝ) < 80)).const_mul
                ((M : ℝ) ^ 2 * A)).integrableOn
        · exact measurableSet_Ioc.compl
        · intro u _hu
          unfold hughesYoungRightPairTerm
          rw [norm_mul, norm_mul,
            norm_divisorDirichletTerm_afe_vertical,
            norm_divisorDirichletTerm_afe_vertical]
          calc
            ‖hughesYoungRightContourWeight t
                  (hughesYoungSmallContour T) u‖ *
                ‖divisorDirichletTerm
                  (afeCriticalPoint t +
                    (hughesYoungSmallContour T : ℂ)) p.1‖ *
                ‖divisorDirichletTerm
                  (afeCriticalPoint (-t) +
                    (hughesYoungSmallContour T : ℂ)) p.2‖ ≤
              (A * Real.exp (-80 * u ^ 2)) * M * M := by
                gcongr
                · exact hweight hT ht
                · exact hd1.trans hp1M
                · exact hd2.trans hp2M
            _ = ((M : ℝ) ^ 2 * A) * Real.exp (-80 * u ^ 2) := by ring
      _ = ((M : ℝ) ^ 2 * A) *
            (∫ u in (Set.Ioc (-H) H)ᶜ,
              Real.exp (-80 * u ^ 2)) := by
        rw [integral_const_mul]
      _ ≤ ((M : ℝ) ^ 2 * A) * G := by
        exact mul_le_mul_of_nonneg_left
          (integral_compl_Ioc_exp_neg_eighty_sq_le hH)
          (mul_nonneg (sq_nonneg _) hA)
      _ = (M : ℝ) ^ 2 * (A * G) := by ring
  unfold hughesYoungWholeSmallPairSquare hughesYoungWholeSmallPairSet
    hughesYoungIntegratedSmallPairSquare
  change ‖(∑ p ∈ S, ∫ u : ℝ,
      hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p) -
      ∑ p ∈ S, ∫ u in -H..H,
        hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ S,
        ‖(∫ u : ℝ,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p) -
          ∫ u in -H..H,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ S, (M : ℝ) ^ 2 * (A * G) := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ = (S.card : ℝ) * ((M : ℝ) ^ 2 * (A * G)) := by simp
    _ = (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 * (A * G)) := by
      have hScard : S.card = M ^ 2 := by
        simp [S, Finset.card_Icc_prod, pow_two]
      rw [hScard, Nat.cast_pow]
    _ = Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
          (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
      unfold A G
      ring

/-- The opening-line complementary square retains the same uniform bound
after the finite ordinate cutoff tends to the whole real line. -/
theorem exists_norm_hughesYoungWholeHighPairSquareTail_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T t : ℝ} {M : ℕ},
      1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) → 0 < M →
      ‖hughesYoungWholeHighPairSquareTail q t M‖ ≤
        (256 * Real.exp (400 * (q : ℝ) ^ 2) *
          ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
          (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
          hughesYoungReferenceDivisorPairMass η) * L := by
  obtain ⟨L, hL, hfinite⟩ :=
    exists_norm_hughesYoungIntegratedHighPairSquareTail_le
      q hq η hη0 hη
  refine ⟨L, hL, ?_⟩
  intro T t M hT ht hM
  let B : ℝ :=
    (256 * Real.exp (400 * (q : ℝ) ^ 2) *
      ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
      (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
      hughesYoungReferenceDivisorPairMass η) * L
  have hlim :=
    (tendsto_hughesYoungIntegratedHighPairSquareTail
      hq η hη0 hη hT ht hM).norm
  have hevent : ∀ᶠ H : ℝ in atTop,
      ‖hughesYoungIntegratedHighPairSquareTail q t H M‖ ≤ B := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    simpa only [B] using hfinite hT ht hM hH
  exact isClosed_Iic.mem_of_tendsto hlim hevent

end RiemannZeta.GuthMaynard
