import RiemannZeta.GuthMaynard.HughesYoungFiniteSquareBridge

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative removal of the small-contour ordinate tails
-/

theorem norm_divisorDirichletTerm_small_le_nat
    {t c u : ℝ} (hc : 0 < c) {n : ℕ} (hn : 0 < n) :
    ‖divisorDirichletTerm
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) n‖ ≤ n := by
  rw [norm_divisorDirichletTerm_afe_vertical_eq t c u hn]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (-(1 / 2 + c : ℝ)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hnR (by linarith)
  have hcard : (n.divisors.card : ℝ) ≤ n := by
    exact_mod_cast Nat.card_divisors_le_self n
  calc
    (n.divisors.card : ℝ) * (n : ℝ) ^ (-(1 / 2 + c : ℝ)) ≤
        (n.divisors.card : ℝ) * 1 := by gcongr
    _ ≤ n := by simpa using hcard

theorem norm_hughesYoungRightPairTerm_small_le
    {t c u : ℝ} (hc : 0 < c) {M : ℕ} {p : ℕ × ℕ}
    (hp₁ : 0 < p.1) (hp₂ : 0 < p.2)
    (hp₁M : p.1 ≤ M) (hp₂M : p.2 ≤ M) :
    ‖hughesYoungRightPairTerm t c u p‖ ≤
      ‖hughesYoungRightContourWeight t c u‖ * (M : ℝ) ^ 2 := by
  rw [hughesYoungRightPairTerm, norm_mul, norm_mul]
  have h₁ := norm_divisorDirichletTerm_small_le_nat (t := t) (u := u) hc hp₁
  have h₂ := norm_divisorDirichletTerm_small_le_nat (t := -t) (u := u) hc hp₂
  have hp₁MR : (p.1 : ℝ) ≤ M := by exact_mod_cast hp₁M
  have hp₂MR : (p.2 : ℝ) ≤ M := by exact_mod_cast hp₂M
  calc
    ‖hughesYoungRightContourWeight t c u‖ *
          ‖divisorDirichletTerm
            (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)) p.1‖ *
          ‖divisorDirichletTerm
            (afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I)) p.2‖ ≤
        ‖hughesYoungRightContourWeight t c u‖ * (p.1 : ℝ) * p.2 := by
      gcongr
    _ ≤ ‖hughesYoungRightContourWeight t c u‖ * (M : ℝ) * M := by
      gcongr
    _ = ‖hughesYoungRightContourWeight t c u‖ * (M : ℝ) ^ 2 := by ring

/-- On the source contour `1 / log T`, the complete Hughes--Young kernel is
uniformly dominated by one logarithm times a fixed Gaussian. -/
theorem exists_norm_hughesYoungRightContourWeight_small_le_gaussian :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {T t : ℝ},
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) → ∀ u : ℝ,
      ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ ≤
        Real.log T * Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2) := by
  obtain ⟨C, hC, hraw⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_height_power
  obtain ⟨K, hK, hgauss⟩ :=
    exists_hughesYoungIntegratedOrdinateFactor_le_gaussian hC
  refine ⟨C, K, hC, hK, ?_⟩
  intro T t hT ht u
  obtain ⟨hc, hc1, hcinv⟩ := hughesYoungSmallContour_spec hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hsource := hraw T t u (hughesYoungSmallContour T) hT1 ht hc hc1
  rw [hcinv, rpow_smallContour_four_mul_eq C hT] at hsource
  have hfactor :
      Real.exp
          (100 * hughesYoungSmallContour T ^ 2 - 84 * u ^ 2 +
            4 * C * hughesYoungSmallContour T * Real.log (6 * (|u| + 1))) *
          (25 + 8 * u ^ 2) ^ 4 ≤
        hughesYoungIntegratedOrdinateFactor C (hughesYoungSmallContour T) u := by
    unfold hughesYoungIntegratedOrdinateFactor
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])) (by positivity)
  have hfront : 0 ≤ Real.log T * Real.exp (4 * C) :=
    mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le
  calc
    ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ ≤
        Real.log T * Real.exp (4 * C) *
          (Real.exp
            (100 * hughesYoungSmallContour T ^ 2 - 84 * u ^ 2 +
              4 * C * hughesYoungSmallContour T * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 4) := hsource
    _ ≤ Real.log T * Real.exp (4 * C) *
          hughesYoungIntegratedOrdinateFactor C (hughesYoungSmallContour T) u := by
      exact mul_le_mul_of_nonneg_left hfactor hfront
    _ ≤ Real.log T * Real.exp (4 * C) *
          (K * Real.exp (-80 * u ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (hgauss hc hc1 u) hfront
    _ = Real.log T * Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2) := by ring

theorem integrable_hughesYoungRightPairTerm_small
    {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T)) {M : ℕ} (hM : 0 < M)
    {p : ℕ × ℕ} (hp₁ : 0 < p.1) (hp₂ : 0 < p.2)
    (hp₁M : p.1 ≤ M) (hp₂M : p.2 ≤ M) :
    Integrable (fun u : ℝ =>
      hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p) := by
  obtain ⟨C, K, hC, hK, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_small_le_gaussian
  let A : ℝ := Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 2
  have hg : Integrable (fun u : ℝ => A * Real.exp (-80 * u ^ 2)) := by
    apply Integrable.const_mul
    simpa only [neg_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 80))
  apply hg.mono'
  · exact ((continuous_uncurry_hughesYoungRightPairTerm_height_ordinate
        (p := p) (hughesYoungSmallContour_spec hT).1 hp₁ hp₂).comp
      ((continuous_const : Continuous (fun _u : ℝ => t)).prodMk
        continuous_id)).aestronglyMeasurable
  · filter_upwards with u
    calc
      ‖hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ ≤
          ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ *
            (M : ℝ) ^ 2 :=
        norm_hughesYoungRightPairTerm_small_le
          (hughesYoungSmallContour_spec hT).1 hp₁ hp₂ hp₁M hp₂M
      _ ≤ (Real.log T * Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2)) *
            (M : ℝ) ^ 2 := by
        gcongr
        exact hweight hT ht u
      _ = A * Real.exp (-80 * u ^ 2) := by
        unfold A
        ring

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
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hgauss : Integrable (fun u : ℝ =>
      Real.log T * Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2)) := by
    apply Integrable.const_mul
    simpa only [neg_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 80))
  have hcont : Continuous (fun u : ℝ =>
      ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖) :=
    ((continuous_uncurry_hughesYoungRightContourWeight
      (hughesYoungSmallContour_spec hT).1).comp
      ((continuous_const : Continuous (fun _u : ℝ => t)).prodMk
        continuous_id)).norm
  calc
    (∫ u in -H..H,
        ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖) ≤
      ∫ u in -H..H,
        Real.log T * Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact hcont.intervalIntegrable (a := -H) (b := H) (μ := volume)
      · exact hgauss.intervalIntegrable
      · intro u _hu
        exact hpoint hT ht u
    _ ≤ ∫ u : ℝ,
        Real.log T * Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2) := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_le_integral hgauss
        (Eventually.of_forall fun u =>
          mul_nonneg
            (mul_nonneg
              (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hK.le)
            (Real.exp_pos _).le)
    _ = Real.log T * Real.exp (4 * C) * K *
        Real.sqrt (Real.pi / 80) := by
      rw [integral_const_mul, integral_gaussian]

theorem norm_hughesYoungIntegratedSmallPairSquare_le
    {T t H : ℝ} {M : ℕ} (hM : 0 < M)
    (hH : 0 ≤ H)
    (hc : 0 < hughesYoungSmallContour T) :
    ‖hughesYoungIntegratedSmallPairSquare T t H M‖ ≤
      (M : ℝ) ^ 4 *
        (∫ u in -H..H,
          ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖) := by
  classical
  unfold hughesYoungIntegratedSmallPairSquare
  rw [Finset.Icc_prod_def, Finset.sum_product]
  calc
    ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        ∫ u in -H..H,
          hughesYoungRightPairTerm t (hughesYoungSmallContour T) u (m, n)‖ ≤
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        ‖∫ u in -H..H,
          hughesYoungRightPairTerm t (hughesYoungSmallContour T) u (m, n)‖ :=
      (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun _m _hm => norm_sum_le _ _)
    _ ≤ ∑ _m ∈ Finset.Icc 1 M, ∑ _n ∈ Finset.Icc 1 M,
        (M : ℝ) ^ 2 *
          (∫ u in -H..H,
            ‖hughesYoungRightContourWeight t
              (hughesYoungSmallContour T) u‖) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      have hm' := Finset.mem_Icc.mp hm
      have hn' := Finset.mem_Icc.mp hn
      calc
        ‖∫ u in -H..H,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u (m, n)‖ ≤
          ∫ u in -H..H,
            ‖hughesYoungRightPairTerm t
              (hughesYoungSmallContour T) u (m, n)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith)
        _ ≤ ∫ u in -H..H,
            ‖hughesYoungRightContourWeight t
              (hughesYoungSmallContour T) u‖ * (M : ℝ) ^ 2 := by
          apply intervalIntegral.integral_mono_on (by linarith)
          · simpa only [Function.comp_apply, Function.uncurry, id_eq] using
              (((continuous_uncurry_hughesYoungRightPairTerm_height_ordinate
                    (p := (m, n)) hc
                    (Nat.zero_lt_one.trans_le hm'.1)
                    (Nat.zero_lt_one.trans_le hn'.1)).comp
                  ((continuous_const : Continuous (fun _u : ℝ => t)).prodMk
                    continuous_id)).norm.intervalIntegrable
                (a := -H) (b := H) (μ := volume))
          · simpa only [Function.comp_apply, Function.uncurry, id_eq] using
              ((((continuous_uncurry_hughesYoungRightContourWeight hc).comp
                    ((continuous_const : Continuous (fun _u : ℝ => t)).prodMk
                      continuous_id)).norm.mul
                  (continuous_const : Continuous (fun _u : ℝ => (M : ℝ) ^ 2))).intervalIntegrable
                (a := -H) (b := H) (μ := volume))
          · intro u _hu
            exact norm_hughesYoungRightPairTerm_small_le hc
              (Nat.zero_lt_one.trans_le hm'.1)
              (Nat.zero_lt_one.trans_le hn'.1) hm'.2 hn'.2
        _ = (M : ℝ) ^ 2 *
            (∫ u in -H..H,
              ‖hughesYoungRightContourWeight t
                (hughesYoungSmallContour T) u‖) := by
          rw [intervalIntegral.integral_mul_const]
          ring
    _ = (M : ℝ) ^ 4 *
        (∫ u in -H..H,
          ‖hughesYoungRightContourWeight t
            (hughesYoungSmallContour T) u‖) := by
      have hcard : (Finset.Icc 1 M).card = M := by
        rw [Nat.card_Icc]
        omega
      simp [hcard]
      ring

noncomputable def hughesYoungWholeSmallPairSquare
    (T t : ℝ) (M : ℕ) : ℂ :=
  ∑ p ∈ Finset.Icc (1, 1) (M, M),
    ∫ u : ℝ, hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p

theorem tendsto_hughesYoungIntegratedSmallPairSquare_to_whole
    {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {M : ℕ} (hM : 0 < M) :
    Tendsto (fun H : ℝ => hughesYoungIntegratedSmallPairSquare T t H M)
      atTop (nhds (hughesYoungWholeSmallPairSquare T t M)) := by
  classical
  unfold hughesYoungIntegratedSmallPairSquare hughesYoungWholeSmallPairSquare
  apply tendsto_finsetSum
  intro p hp
  have hp' := Finset.mem_Icc.mp hp
  have hp₁ : 0 < p.1 :=
    Nat.zero_lt_one.trans_le (Prod.le_def.mp hp'.1).1
  have hp₂ : 0 < p.2 :=
    Nat.zero_lt_one.trans_le (Prod.le_def.mp hp'.1).2
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungRightPairTerm_small hT ht hM hp₁ hp₂
      (Prod.le_def.mp hp'.2).1 (Prod.le_def.mp hp'.2).2)
    tendsto_neg_atTop_atBot tendsto_id

/-- Exact infinite-contour identity obtained by uniqueness of the limit of
the finite square.  This is the source-faithful bridge from the shifted
small line back to the actual zeta-square product. -/
theorem hughesYoungWholeSmallPairSquare_eq_zetaSquare_sub_highTail
    {q : ℕ} (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {M : ℕ} (hM : 0 < M) :
    hughesYoungWholeSmallPairSquare T t M =
      (Real.pi : ℂ) *
          (riemannZeta (afeCriticalPoint t) ^ 2 *
            riemannZeta (afeCriticalPoint (-t)) ^ 2) -
        hughesYoungWholeHighPairSquareTail q t M := by
  exact tendsto_nhds_unique
    (tendsto_hughesYoungIntegratedSmallPairSquare_to_whole hT ht hM)
    (tendsto_hughesYoungIntegratedSmallPairSquare
      hq η hη0 hη hT ht hM)

theorem exp_neg_eighty_sq_le_gaussian_tail
    {H u : ℝ} (hH : 0 ≤ H) (hu : u ∈ (Set.Ioc (-H) H)ᶜ) :
    Real.exp (-80 * u ^ 2) ≤
      Real.exp (-40 * H ^ 2) * Real.exp (-40 * u ^ 2) := by
  have hu' : u ≤ -H ∨ H < u := by
    simpa only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] using hu
  have hsq : H ^ 2 ≤ u ^ 2 := by
    rcases hu' with huLeft | huRight
    · nlinarith [sq_nonneg (u + H)]
    · nlinarith [sq_nonneg (u - H)]
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith)

theorem integral_gaussian_tail_compl_Ioc_le
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ u in (Set.Ioc (-H) H)ᶜ, Real.exp (-80 * u ^ 2)) ≤
      Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40) := by
  let g : ℝ → ℝ := fun u =>
    Real.exp (-40 * H ^ 2) * Real.exp (-40 * u ^ 2)
  have h80 : Integrable (fun u : ℝ => Real.exp (-80 * u ^ 2)) := by
    simpa only [neg_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 80))
  have h40 : Integrable (fun u : ℝ => Real.exp (-40 * u ^ 2)) := by
    simpa only [neg_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 40))
  have hg : Integrable g := h40.const_mul _
  calc
    (∫ u in (Set.Ioc (-H) H)ᶜ, Real.exp (-80 * u ^ 2)) ≤
        ∫ u in (Set.Ioc (-H) H)ᶜ, g u := by
      apply setIntegral_mono_on h80.integrableOn hg.integrableOn
        measurableSet_Ioc.compl
      intro u hu
      exact exp_neg_eighty_sq_le_gaussian_tail hH hu
    _ ≤ ∫ u : ℝ, g u := by
      exact setIntegral_le_integral hg
        (Eventually.of_forall fun u => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40) := by
      unfold g
      rw [integral_const_mul, integral_gaussian]

theorem norm_hughesYoungWholePairTerm_sub_interval_le
    {C K T t H : ℝ} {M : ℕ} {p : ℕ × ℕ}
    (hK : 0 < K)
    (hweight : ∀ {T t : ℝ}, Real.exp 1 ≤ T →
      t ∈ Set.Icc (T / 4) (4 * T) → ∀ u : ℝ,
      ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ ≤
        Real.log T * Real.exp (4 * C) * K * Real.exp (-80 * u ^ 2))
    (hT : Real.exp 1 ≤ T) (ht : t ∈ Set.Icc (T / 4) (4 * T))
    (hH : 0 ≤ H) (hM : 0 < M)
    (hp₁ : 0 < p.1) (hp₂ : 0 < p.2)
    (hp₁M : p.1 ≤ M) (hp₂M : p.2 ≤ M) :
    ‖(∫ u : ℝ,
        hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p) -
      ∫ u in -H..H,
        hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ ≤
      (Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 2) *
        (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
  let f : ℝ → ℂ := fun u =>
    hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p
  let A : ℝ := Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 2
  let g : ℝ → ℝ := fun u => A * Real.exp (-80 * u ^ 2)
  have hf : Integrable f :=
    integrable_hughesYoungRightPairTerm_small hT ht hM hp₁ hp₂ hp₁M hp₂M
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hA : 0 ≤ A := by
    unfold A
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hK.le)
      (sq_nonneg (M : ℝ))
  have hg : Integrable g := by
    apply Integrable.const_mul
    simpa only [neg_mul] using
      (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 80))
  have hrepr :
      (∫ u : ℝ, f u) - ∫ u in -H..H, f u =
        ∫ u in (Set.Ioc (-H) H)ᶜ, f u := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact (setIntegral_compl measurableSet_Ioc hf).symm
  rw [hrepr]
  calc
    ‖∫ u in (Set.Ioc (-H) H)ᶜ, f u‖ ≤
        ∫ u in (Set.Ioc (-H) H)ᶜ, g u := by
      apply norm_integral_le_of_norm_le hg.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc.compl] with u hu
      calc
        ‖f u‖ ≤
            ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖ *
              (M : ℝ) ^ 2 := by
          exact norm_hughesYoungRightPairTerm_small_le
            (hughesYoungSmallContour_spec hT).1 hp₁ hp₂ hp₁M hp₂M
        _ ≤ (Real.log T * Real.exp (4 * C) * K *
              Real.exp (-80 * u ^ 2)) * (M : ℝ) ^ 2 := by
          gcongr
          exact hweight hT ht u
        _ = g u := by
          unfold g A
          ring
    _ = A * (∫ u in (Set.Ioc (-H) H)ᶜ, Real.exp (-80 * u ^ 2)) := by
      unfold g
      rw [integral_const_mul]
    _ ≤ A * (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
      exact mul_le_mul_of_nonneg_left (integral_gaussian_tail_compl_Ioc_le hH) hA
    _ = (Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 2) *
        (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
      rfl

/-- Quantitative removal of the finite small-contour ordinate cutoff for the
entire `M × M` arithmetic square. -/
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
  unfold hughesYoungWholeSmallPairSquare
    hughesYoungIntegratedSmallPairSquare
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p ∈ Finset.Icc (1, 1) (M, M),
        ((∫ u : ℝ,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p) -
          ∫ u in -H..H,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p)‖ ≤
      ∑ p ∈ Finset.Icc (1, 1) (M, M),
        ‖(∫ u : ℝ,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p) -
          ∫ u in -H..H,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u p‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.Icc (1, 1) (M, M),
        (Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 2) *
          (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_Icc.mp hp
      exact norm_hughesYoungWholePairTerm_sub_interval_le hK hweight
        hT ht hH hM
        (Nat.zero_lt_one.trans_le (Prod.le_def.mp hp'.1).1)
        (Nat.zero_lt_one.trans_le (Prod.le_def.mp hp'.1).2)
        (Prod.le_def.mp hp'.2).1 (Prod.le_def.mp hp'.2).2
    _ = Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
        (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
      have hcard : (Finset.Icc (1, 1) (M, M)).card = M ^ 2 := by
        simp [Finset.Icc_prod_def, Nat.card_Icc, pow_two]
      simp [hcard]
      ring

/-- The opening-line square tail satisfies the same uniform estimate after
the finite ordinate cutoff is removed. -/
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
    exists_norm_hughesYoungIntegratedHighPairSquareTail_le q hq η hη0 hη
  refine ⟨L, hL, ?_⟩
  intro T t M hT ht hM
  let B : ℝ :=
    (256 * Real.exp (400 * (q : ℝ) ^ 2) *
      ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
      (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
      hughesYoungReferenceDivisorPairMass η) * L
  have hlim := (tendsto_hughesYoungIntegratedHighPairSquareTail
    hq η hη0 hη hT ht hM).norm
  have hevent : ∀ᶠ H : ℝ in atTop,
      ‖hughesYoungIntegratedHighPairSquareTail q t H M‖ ≤ B := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    exact hfinite hT ht hM hH
  have hclosed : IsClosed (Set.Iic B) := isClosed_Iic
  have hmem : ‖hughesYoungWholeHighPairSquareTail q t M‖ ∈ Set.Iic B :=
    hclosed.mem_of_tendsto hlim hevent
  simpa only [B] using hmem

end RiemannZeta.GuthMaynard
