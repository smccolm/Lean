import RiemannZeta.GuthMaynard.HughesYoungSmallContourTail
import RiemannZeta.GuthMaynard.HughesYoungMoment
import RiemannZeta.GuthMaynard.HughesYoungFiniteSquareBridge
import RiemannZeta.GuthMaynard.HughesYoungSmallSquareBounds

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Transfer from the finite shifted square to the smooth twisted moment
-/

noncomputable def hughesYoungWholeFiniteSmallTwistedSquare
    (T t : ℝ) (M : ℕ) : ℂ :=
  (1 / (Real.pi : ℂ)) *
    shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
    shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2 *
    hughesYoungWholeSmallPairSquare T t M

noncomputable def hughesYoungWholeHighTwistedTail
    (q : ℕ) (T t : ℝ) (M : ℕ) : ℂ :=
  (1 / (Real.pi : ℂ)) *
    shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
    shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2 *
    hughesYoungWholeHighPairSquareTail q t M

theorem norm_hughesYoungWholeHighTwistedTail_le
    {q : ℕ} {T t B : ℝ} {M : ℕ}
    (hpair : ‖hughesYoungWholeHighPairSquareTail q t M‖ ≤ B) :
    ‖hughesYoungWholeHighTwistedTail q T t M‖ ≤
      (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) * B := by
  have hplus :
      ‖shortMobiusPolynomial T (afeCriticalPoint t)‖ ≤
        (detectorCutoff T : ℝ) := by
    simpa [afeCriticalPoint] using
      norm_shortMobiusPolynomial_criticalLine_le T t
  have hminus :
      ‖shortMobiusPolynomial T (afeCriticalPoint (-t))‖ ≤
        (detectorCutoff T : ℝ) := by
    simpa [afeCriticalPoint] using
      norm_shortMobiusPolynomial_criticalLine_le T (-t)
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold hughesYoungWholeHighTwistedTail
  simp only [norm_mul, norm_pow]
  have hscalar : ‖(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos hpi]
  rw [hscalar]
  calc
    (1 / Real.pi) *
          ‖shortMobiusPolynomial T (afeCriticalPoint t)‖ ^ 2 *
          ‖shortMobiusPolynomial T (afeCriticalPoint (-t))‖ ^ 2 *
          ‖hughesYoungWholeHighPairSquareTail q t M‖ ≤
        (1 / Real.pi) * (detectorCutoff T : ℝ) ^ 2 *
          (detectorCutoff T : ℝ) ^ 2 * B := by
      gcongr
    _ = (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) * B := by ring

theorem hughesYoungWholeFiniteSmallTwistedSquare_eq_integrand_sub_tail
    {q : ℕ} (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T))
    {M : ℕ} (hM : 0 < M) :
    hughesYoungWholeFiniteSmallTwistedSquare T t M =
      (twistedZetaMomentIntegrand T t : ℂ) -
        hughesYoungWholeHighTwistedTail q T t M := by
  unfold hughesYoungWholeFiniteSmallTwistedSquare
    hughesYoungWholeHighTwistedTail
  rw [hughesYoungWholeSmallPairSquare_eq_zetaSquare_sub_highTail
    hq η hη0 hη hT ht hM]
  rw [ofReal_twistedZetaMomentIntegrand_eq_conjugate_product]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]

theorem norm_hughesYoungWholeFiniteSmallTwistedSquare_sub_finite_le
    {C K T t H : ℝ} {M : ℕ}
    (hsmall :
      ‖hughesYoungWholeSmallPairSquare T t M -
          hughesYoungIntegratedSmallPairSquare T t H M‖ ≤
        Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
          (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) :
    ‖hughesYoungWholeFiniteSmallTwistedSquare T t M -
        hughesYoungFiniteSmallTwistedSquare T t H M‖ ≤
      (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) *
        (Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
          (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hplus :
      ‖shortMobiusPolynomial T (afeCriticalPoint t)‖ ≤
        (detectorCutoff T : ℝ) := by
    simpa [afeCriticalPoint] using
      norm_shortMobiusPolynomial_criticalLine_le T t
  have hminus :
      ‖shortMobiusPolynomial T (afeCriticalPoint (-t))‖ ≤
        (detectorCutoff T : ℝ) := by
    simpa [afeCriticalPoint] using
      norm_shortMobiusPolynomial_criticalLine_le T (-t)
  unfold hughesYoungWholeFiniteSmallTwistedSquare
    hughesYoungFiniteSmallTwistedSquare
  rw [show
    (1 / (Real.pi : ℂ)) *
          shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
          shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2 *
          hughesYoungWholeSmallPairSquare T t M -
        shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
          shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2 *
          ((1 / (Real.pi : ℂ)) *
            hughesYoungIntegratedSmallPairSquare T t H M) =
      (1 / (Real.pi : ℂ)) *
          shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
          shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2 *
          (hughesYoungWholeSmallPairSquare T t M -
            hughesYoungIntegratedSmallPairSquare T t H M) by ring]
  simp only [norm_mul, norm_pow]
  have hscalar :
      ‖(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos hpi]
  rw [hscalar]
  calc
    (1 / Real.pi) *
          ‖shortMobiusPolynomial T (afeCriticalPoint t)‖ ^ 2 *
          ‖shortMobiusPolynomial T (afeCriticalPoint (-t))‖ ^ 2 *
          ‖hughesYoungWholeSmallPairSquare T t M -
            hughesYoungIntegratedSmallPairSquare T t H M‖ ≤
        (1 / Real.pi) * (detectorCutoff T : ℝ) ^ 2 *
          (detectorCutoff T : ℝ) ^ 2 *
          (Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
            (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) := by
      gcongr
    _ = (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) *
        (Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
          (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) := by ring

theorem norm_hughesYoungFiniteSmallTwistedSquare_le_of_intervalWeight
    {T t H B : ℝ} {M : ℕ} (hM : 0 < M)
    (hH : 0 ≤ H) (hT : Real.exp 1 ≤ T)
    (hweight :
      (∫ u in -H..H,
        ‖hughesYoungRightContourWeight t (hughesYoungSmallContour T) u‖) ≤ B) :
    ‖hughesYoungFiniteSmallTwistedSquare T t H M‖ ≤
      (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) * (M : ℝ) ^ 4 * B := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hplus :
      ‖shortMobiusPolynomial T (afeCriticalPoint t)‖ ≤
        (detectorCutoff T : ℝ) := by
    simpa [afeCriticalPoint] using
      norm_shortMobiusPolynomial_criticalLine_le T t
  have hminus :
      ‖shortMobiusPolynomial T (afeCriticalPoint (-t))‖ ≤
        (detectorCutoff T : ℝ) := by
    simpa [afeCriticalPoint] using
      norm_shortMobiusPolynomial_criticalLine_le T (-t)
  have hsquare := norm_hughesYoungIntegratedSmallPairSquare_le (t := t) hM hH
    (hughesYoungSmallContour_spec hT).1
  have hsquareB :
      ‖hughesYoungIntegratedSmallPairSquare T t H M‖ ≤
        (M : ℝ) ^ 4 * B :=
    hsquare.trans (mul_le_mul_of_nonneg_left hweight (by positivity))
  unfold hughesYoungFiniteSmallTwistedSquare
  simp only [norm_mul, norm_pow]
  have hscalar : ‖(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos hpi]
  rw [hscalar]
  calc
    ‖shortMobiusPolynomial T (afeCriticalPoint t)‖ ^ 2 *
          ‖shortMobiusPolynomial T (afeCriticalPoint (-t))‖ ^ 2 *
          (1 / Real.pi *
            ‖hughesYoungIntegratedSmallPairSquare T t H M‖) ≤
        (detectorCutoff T : ℝ) ^ 2 *
          (detectorCutoff T : ℝ) ^ 2 *
          (1 / Real.pi * ((M : ℝ) ^ 4 * B)) := by
      gcongr
    _ = (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) *
          (M : ℝ) ^ 4 * B := by ring

theorem exists_uniform_norm_hughesYoungFiniteSmallTwistedSquare_le :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {T t H : ℝ} {M : ℕ},
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) →
      0 ≤ H → 0 < M →
      ‖hughesYoungFiniteSmallTwistedSquare T t H M‖ ≤
        (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) * (M : ℝ) ^ 4 *
          (Real.log T * Real.exp (4 * C) * K *
            Real.sqrt (Real.pi / 80)) := by
  obtain ⟨C, K, hC, hK, hweight⟩ :=
    exists_uniform_intervalIntegral_norm_hughesYoungRightContourWeight_small_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro T t H M hT ht hH hM
  exact norm_hughesYoungFiniteSmallTwistedSquare_le_of_intervalWeight
    hM hH hT (hweight hT ht hH)

theorem integrable_weight_mul_hughesYoungFiniteSmallTwistedSquare
    {T : ℝ} (hT : Real.exp 1 ≤ T) (H : ℝ) (M : ℕ) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungFiniteSmallTwistedSquare T t H M) := by
  classical
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hc : 0 < hughesYoungSmallContour T :=
    (hughesYoungSmallContour_spec hT).1
  let K : Finset ℕ := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let S : Finset ℕ := Finset.Icc 1 M
  have hterm : ∀ h ∈ K, ∀ k ∈ K, ∀ m ∈ S, ∀ n ∈ S,
      Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteArithmeticTerm T t (hughesYoungSmallContour T) H
          h k (m, n)) := by
    intro h hh k hk m hm n hn
    exact integrable_weight_mul_hughesYoungFiniteArithmeticTerm
      hT0 hc H
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hm).1)
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1)
  have hsum : Integrable (fun t : ℝ =>
      ∑ h ∈ K, ∑ k ∈ K, ∑ m ∈ S, ∑ n ∈ S,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteArithmeticTerm T t
            (hughesYoungSmallContour T) H h k (m, n)) := by
    apply integrable_finsetSum
    intro h hh
    apply integrable_finsetSum
    intro k hk
    apply integrable_finsetSum
    intro m hm
    apply integrable_finsetSum
    intro n hn
    exact hterm h hh k hk m hm n hn
  apply hsum.congr
  filter_upwards with t
  rw [hughesYoungFiniteSmallTwistedSquare_eq_four_index_sum]
  simp_rw [Finset.mul_sum]
  rfl

theorem tendsto_weight_mul_hughesYoungFiniteSmallTwistedSquare
    {T t : ℝ} (hT : Real.exp 1 ≤ T) (M : ℕ) :
    Tendsto (fun n : ℕ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFiniteSmallTwistedSquare T t (n : ℝ) M)
      atTop (𝓝 ((hughesYoungHeightWeight T t : ℂ) *
        hughesYoungWholeFiniteSmallTwistedSquare T t M)) := by
  by_cases hw : hughesYoungHeightWeight T t = 0
  · simp [hw]
  · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
      hughesYoungHeightWeight_support
        ((Real.exp_pos 1).trans_le hT) hw
    have hlim := tendsto_hughesYoungIntegratedSmallPairSquare_to_whole
      hT ht M
    have hmul := hlim.const_mul
      ((hughesYoungHeightWeight T t : ℂ) *
        ((1 / (Real.pi : ℂ)) *
          shortMobiusPolynomial T (afeCriticalPoint t) ^ 2 *
          shortMobiusPolynomial T (afeCriticalPoint (-t)) ^ 2))
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa only [Function.comp_apply,
      hughesYoungFiniteSmallTwistedSquare,
      hughesYoungWholeFiniteSmallTwistedSquare, mul_assoc, mul_left_comm,
      mul_comm] using hmul.comp hnat

/-- Dominated convergence through the physical height integral.  This is the
exact bridge from the finite arithmetic rectangles to the whole shifted
Hughes--Young square; it uses the concrete compactly supported height weight. -/
theorem tendsto_integral_hughesYoungFiniteSmallTwistedSquare
    {T : ℝ} (hT : Real.exp 1 ≤ T) {M : ℕ} (hM : 0 < M) :
    Tendsto (fun n : ℕ => ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteSmallTwistedSquare T t (n : ℝ) M)
      atTop (𝓝 (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungWholeFiniteSmallTwistedSquare T t M)) := by
  obtain ⟨C, K, hC, hK, hbound⟩ :=
    exists_uniform_norm_hughesYoungFiniteSmallTwistedSquare_le
  let A : ℝ := (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) * (M : ℝ) ^ 4 *
    (Real.log T * Real.exp (4 * C) * K * Real.sqrt (Real.pi / 80))
  let B : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
  have hA : 0 ≤ A := by
    unfold A
    have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
          (by positivity : 0 ≤ 1 / Real.pi))
        (pow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hK.le)
        (Real.sqrt_nonneg _))
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  apply tendsto_integral_of_dominated_convergence B
  · intro n
    exact (integrable_weight_mul_hughesYoungFiniteSmallTwistedSquare
      hT (n : ℝ) M).aestronglyMeasurable
  · exact hBint
  · intro n
    filter_upwards with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · rw [hw]
      simp only [ofReal_zero, zero_mul, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hA) t
    · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
        hughesYoungHeightWeight_support
          ((Real.exp_pos 1).trans_le hT) hw
      have hsquare := hbound hT ht (Nat.cast_nonneg n) hM
      have hw0 := hughesYoungHeightWeight_nonneg T t
      have hw1 := hughesYoungHeightWeight_le_one T t
      change ‖(hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteSmallTwistedSquare T t (n : ℝ) M‖ ≤ B t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hw0]
      change hughesYoungHeightWeight T t *
          ‖hughesYoungFiniteSmallTwistedSquare T t (n : ℝ) M‖ ≤
        Set.indicator (Set.Icc (T / 4) (4 * T)) (fun _ => A) t
      rw [Set.indicator_of_mem ht]
      calc
        hughesYoungHeightWeight T t *
            ‖hughesYoungFiniteSmallTwistedSquare T t (n : ℝ) M‖ ≤
          1 * ‖hughesYoungFiniteSmallTwistedSquare T t (n : ℝ) M‖ := by
            gcongr
        _ ≤ A := by simpa only [one_mul, A] using hsquare
  · filter_upwards with t
    exact tendsto_weight_mul_hughesYoungFiniteSmallTwistedSquare hT M

theorem integrable_weight_mul_hughesYoungWholeFiniteSmallTwistedSquare
    {T : ℝ} (hT : Real.exp 1 ≤ T) {M : ℕ} (hM : 0 < M) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungWholeFiniteSmallTwistedSquare T t M) := by
  obtain ⟨C, K, hC, hK, hbound⟩ :=
    exists_uniform_norm_hughesYoungFiniteSmallTwistedSquare_le
  let A : ℝ := (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) * (M : ℝ) ^ 4 *
    (Real.log T * Real.exp (4 * C) * K * Real.sqrt (Real.pi / 80))
  let B : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hA : 0 ≤ A := by
    unfold A
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
          (by positivity : 0 ≤ 1 / Real.pi))
        (pow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hK.le)
        (Real.sqrt_nonneg _))
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungWholeFiniteSmallTwistedSquare T t M) := by
    apply aestronglyMeasurable_of_tendsto_ae
      (atTop : Filter ℕ)
      (f := fun n : ℕ => fun t : ℝ =>
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteSmallTwistedSquare T t (n : ℝ) M)
      (fun n => (integrable_weight_mul_hughesYoungFiniteSmallTwistedSquare
        hT (n : ℝ) M).aestronglyMeasurable)
    filter_upwards with t
    exact tendsto_weight_mul_hughesYoungFiniteSmallTwistedSquare hT M
  apply hBint.mono' hmeas
  filter_upwards with t
  by_cases hw : hughesYoungHeightWeight T t = 0
  · rw [hw]
    simp only [ofReal_zero, zero_mul, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hA) t
  · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
      hughesYoungHeightWeight_support hT0 hw
    have hlim :=
      (tendsto_weight_mul_hughesYoungFiniteSmallTwistedSquare
        (t := t) hT M).norm
    have hevent : ∀ᶠ n : ℕ in atTop,
        ‖(hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteSmallTwistedSquare T t (n : ℝ) M‖ ≤ A := by
      filter_upwards with n
      have hsquare := hbound hT ht (Nat.cast_nonneg n) hM
      have hw0 := hughesYoungHeightWeight_nonneg T t
      have hw1 := hughesYoungHeightWeight_le_one T t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      calc
        hughesYoungHeightWeight T t *
            ‖hughesYoungFiniteSmallTwistedSquare T t (n : ℝ) M‖ ≤
          1 * ‖hughesYoungFiniteSmallTwistedSquare T t (n : ℝ) M‖ := by
            gcongr
        _ ≤ A := by simpa only [one_mul, A] using hsquare
    have hclosed : IsClosed (Set.Iic A) := isClosed_Iic
    have hwhole :
        ‖(hughesYoungHeightWeight T t : ℂ) *
          hughesYoungWholeFiniteSmallTwistedSquare T t M‖ ≤ A :=
      hclosed.mem_of_tendsto hlim hevent
    change _ ≤ Set.indicator (Set.Icc (T / 4) (4 * T)) (fun _ => A) t
    rw [Set.indicator_of_mem ht]
    exact hwhole

/-- Quantitative finite-height comparison on the physical height support.
The factor `15T/4` is the exact length of `[T/4,4T]`. -/
theorem exists_norm_integral_hughesYoungWholeFiniteSmallTwistedSquare_sub_finite_le :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ {T H : ℝ} {M : ℕ},
      Real.exp 1 ≤ T → 0 ≤ H → 0 < M →
      ‖(∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungWholeFiniteSmallTwistedSquare T t M) -
        ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFiniteSmallTwistedSquare T t H M‖ ≤
        (15 * T / 4) * (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) *
          (Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
            (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) := by
  obtain ⟨C, K, hC, hK, hsmall⟩ :=
    exists_norm_hughesYoungWholeSmallPairSquare_sub_integrated_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro T H M hT hH hM
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hwhole :=
    integrable_weight_mul_hughesYoungWholeFiniteSmallTwistedSquare hT hM
  have hfinite :=
    integrable_weight_mul_hughesYoungFiniteSmallTwistedSquare hT H M
  let A : ℝ := (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) *
    (Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
      (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)))
  let B : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
  have hA : 0 ≤ A := by
    unfold A
    have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
    have hfront :
        0 ≤ (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) := by
      exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (by positivity)
    have hinner :
        0 ≤ Real.log T * Real.exp (4 * C) * K * (M : ℝ) ^ 4 *
          (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg hlog (Real.exp_pos _).le) hK.le)
          (pow_nonneg (Nat.cast_nonneg _) _))
        (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
    exact mul_nonneg hfront hinner
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  rw [← integral_sub hwhole hfinite]
  apply (norm_integral_le_of_norm_le hBint ?_).trans_eq
  · rw [show (∫ t : ℝ, B t) = ∫ _t in Set.Icc (T / 4) (4 * T), A by
        exact MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ 4 * T - T / 4)]
    unfold A
    ring
  · filter_upwards with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · rw [hw]
      simp only [ofReal_zero, zero_mul, zero_sub, norm_neg, norm_zero]
      simpa only [B] using Set.indicator_nonneg (fun _ _ => hA) t
    · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
        hughesYoungHeightWeight_support hT0 hw
      have hpoint := norm_hughesYoungWholeFiniteSmallTwistedSquare_sub_finite_le
        (hsmall hT ht hH hM)
      have hw0 := hughesYoungHeightWeight_nonneg T t
      have hw1 := hughesYoungHeightWeight_le_one T t
      rw [show
        (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungWholeFiniteSmallTwistedSquare T t M -
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungFiniteSmallTwistedSquare T t H M =
          (hughesYoungHeightWeight T t : ℂ) *
            (hughesYoungWholeFiniteSmallTwistedSquare T t M -
              hughesYoungFiniteSmallTwistedSquare T t H M) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      change _ ≤ Set.indicator (Set.Icc (T / 4) (4 * T)) (fun _ => A) t
      rw [Set.indicator_of_mem ht]
      calc
        hughesYoungHeightWeight T t *
            ‖hughesYoungWholeFiniteSmallTwistedSquare T t M -
              hughesYoungFiniteSmallTwistedSquare T t H M‖ ≤
          1 * ‖hughesYoungWholeFiniteSmallTwistedSquare T t M -
              hughesYoungFiniteSmallTwistedSquare T t H M‖ := by
            gcongr
        _ ≤ A := by simpa only [one_mul, A] using hpoint

theorem integrable_weight_mul_hughesYoungWholeHighTwistedTail
    {q : ℕ} (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T : ℝ} (hT : Real.exp 1 ≤ T) {M : ℕ} (hM : 0 < M) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungWholeHighTwistedTail q T t M) := by
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hactual : Integrable (fun t : ℝ =>
      ((hughesYoungHeightWeight T t * twistedZetaMomentIntegrand T t : ℝ) : ℂ)) :=
    (integrable_hughesYoungSmoothedMoment_integrand hT0).ofReal
  have hwhole :=
    integrable_weight_mul_hughesYoungWholeFiniteSmallTwistedSquare hT hM
  have hdiff := hactual.sub hwhole
  apply hdiff.congr
  filter_upwards with t
  by_cases hw : hughesYoungHeightWeight T t = 0
  · simp [hw]
  · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
      hughesYoungHeightWeight_support hT0 hw
    change
      ((hughesYoungHeightWeight T t * twistedZetaMomentIntegrand T t : ℝ) : ℂ) -
          (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungWholeFiniteSmallTwistedSquare T t M =
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungWholeHighTwistedTail q T t M
    rw [hughesYoungWholeFiniteSmallTwistedSquare_eq_integrand_sub_tail
      hq η hη0 hη hT ht hM]
    push_cast
    ring

/-- The opening-line remainder remains uniformly negligible after inserting
the actual detector and the physical height cutoff.  This is the quantitative
tail estimate needed to return from the Hughes--Young shifted square to the
project's smoothed fourth moment. -/
theorem exists_norm_integral_weight_mul_hughesYoungWholeHighTwistedTail_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T : ℝ} {M : ℕ},
      Real.exp 1 ≤ T → 0 < M →
      ‖∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungWholeHighTwistedTail q T t M‖ ≤
        (15 * T / 4) * (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) *
          ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
            ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
            (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
            hughesYoungReferenceDivisorPairMass η) * L) := by
  obtain ⟨L, hL, hpair⟩ :=
    exists_norm_hughesYoungWholeHighPairSquareTail_le q hq η hη0 hη
  refine ⟨L, hL, ?_⟩
  intro T M hT hM
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  let D : ℝ :=
    (256 * Real.exp (400 * (q : ℝ) ^ 2) *
      ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
      (M : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
      hughesYoungReferenceDivisorPairMass η) * L
  let A : ℝ := (detectorCutoff T : ℝ) ^ 4 * (1 / Real.pi) * D
  let B : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
  have hD : 0 ≤ D := by
    have hmass : 0 ≤ hughesYoungReferenceDivisorPairMass η :=
      hughesYoungReferenceDivisorPairMass_nonneg η
    unfold D
    positivity
  have hA : 0 ≤ A := by
    unfold A
    positivity
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  apply (norm_integral_le_of_norm_le hBint ?_).trans_eq
  · rw [show (∫ t : ℝ, B t) = ∫ _t in Set.Icc (T / 4) (4 * T), A by
        exact MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ 4 * T - T / 4)]
    unfold A D
    ring
  · filter_upwards with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · rw [hw]
      simp only [ofReal_zero, zero_mul, norm_zero]
      simpa only [B] using Set.indicator_nonneg (fun _ _ => hA) t
    · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
        hughesYoungHeightWeight_support hT0 hw
      have htail := norm_hughesYoungWholeHighTwistedTail_le
        (T := T) (t := t) (M := M) (hpair hT1 ht hM)
      have hw0 := hughesYoungHeightWeight_nonneg T t
      have hw1 := hughesYoungHeightWeight_le_one T t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      change _ ≤ Set.indicator (Set.Icc (T / 4) (4 * T)) (fun _ => A) t
      rw [Set.indicator_of_mem ht]
      calc
        hughesYoungHeightWeight T t *
            ‖hughesYoungWholeHighTwistedTail q T t M‖ ≤
          1 * ‖hughesYoungWholeHighTwistedTail q T t M‖ := by
            gcongr
        _ ≤ A := by simpa only [one_mul, A, D] using htail

/-- The whole shifted square is exactly the actual smoothed twisted moment
minus the opening-line tail.  This is the Hughes--Young contour transfer at
the level of the concrete project moment. -/
theorem integral_hughesYoungWholeFiniteSmallTwistedSquare_eq_smoothed_sub_highTail
    {q : ℕ} (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T : ℝ} (hT : Real.exp 1 ≤ T) {M : ℕ} (hM : 0 < M) :
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungWholeFiniteSmallTwistedSquare T t M) =
      (hughesYoungSmoothedMoment T : ℂ) -
        ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungWholeHighTwistedTail q T t M := by
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hactualR := integrable_hughesYoungSmoothedMoment_integrand hT0
  have hactual : Integrable (fun t : ℝ =>
      ((hughesYoungHeightWeight T t * twistedZetaMomentIntegrand T t : ℝ) : ℂ)) :=
    hactualR.ofReal
  have hhigh := integrable_weight_mul_hughesYoungWholeHighTwistedTail
    hq η hη0 hη hT hM
  calc
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungWholeFiniteSmallTwistedSquare T t M) =
      ∫ t : ℝ,
        ((hughesYoungHeightWeight T t * twistedZetaMomentIntegrand T t : ℝ) : ℂ) -
          (hughesYoungHeightWeight T t : ℂ) *
            hughesYoungWholeHighTwistedTail q T t M := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases hw : hughesYoungHeightWeight T t = 0
      · simp [hw]
      · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
          hughesYoungHeightWeight_support hT0 hw
        rw [hughesYoungWholeFiniteSmallTwistedSquare_eq_integrand_sub_tail
          hq η hη0 hη hT ht hM]
        push_cast
        ring
    _ = (∫ t : ℝ,
          ((hughesYoungHeightWeight T t * twistedZetaMomentIntegrand T t : ℝ) : ℂ)) -
        ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungWholeHighTwistedTail q T t M :=
      integral_sub hactual hhigh
    _ = (hughesYoungSmoothedMoment T : ℂ) -
        ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungWholeHighTwistedTail q T t M := by
      rw [_root_.integral_complex_ofReal]
      rfl

end RiemannZeta.GuthMaynard
