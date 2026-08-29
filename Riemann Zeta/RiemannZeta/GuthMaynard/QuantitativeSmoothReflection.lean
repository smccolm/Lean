import RiemannZeta.GuthMaynard.LargeValuesCubic
import RiemannZeta.GuthMaynard.TypeIIFourthMomentReduction

open Complex Finset Filter MeasureTheory Real Set
open ComplexConjugate
open scoped BigOperators Interval

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative complete-frequency smooth reflection

This file completes Guth--Maynard Lemma 6.2 for the exact trace Fourier
coefficient and connects it to the complete scaled tail used by `gmCubicS2`.
-/

/-- The complete unscaled nonzero integer-frequency series in Lemma 6.2. -/
noncomputable def gmTraceNonzeroFourierSum
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) : ℂ :=
  ∑' m : ℤ, if m = 0 then 0 else
    gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))

/-- The omitted unscaled frequencies outside the symmetric window. -/
noncomputable def gmTraceFourierFarTail
    (cutoff : GMSmoothCutoff) (N M : ℕ) (t : ℝ) : ℂ :=
  ∑' m : ℤ, if M < m.natAbs then
    gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ)) else 0

theorem gmTraceFourier_summable (cutoff : GMSmoothCutoff)
    (N : ℕ) (hN : 0 < N) (t : ℝ) :
    Summable (fun m : ℤ =>
      gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))) := by
  have hScaled := gmScaledTraceFourier_summable cutoff t (N : ℝ)
    (by exact_mod_cast hN)
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  exact (summable_mul_left_iff hNC).mp (by simpa using hScaled)

/-- Exact sign decomposition of the finite nonzero integer window. -/
theorem gmTraceFourierCentral_eq_signed
    (cutoff : GMSmoothCutoff) (N M : ℕ) (t : ℝ) :
    (∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        if z = 0 then 0 else
          gmTraceFourier cutoff t ((N : ℝ) * (z : ℝ))) =
      ∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m))) := by
  induction M with
  | zero => simp
  | succ M ih =>
      let f : ℤ → ℂ := fun z =>
        if z = 0 then 0 else
          gmTraceFourier cutoff t ((N : ℝ) * (z : ℝ))
      have hInt : Finset.Icc (-(M.succ : ℤ)) (M.succ : ℤ) =
          insert (-(M.succ : ℤ))
            (insert (M.succ : ℤ) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_insert, Int.natCast_succ]
        omega
      have hNat : Finset.Icc 1 M.succ =
          insert M.succ (Finset.Icc 1 M) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      change (∑ z ∈ Finset.Icc (-(M.succ : ℤ)) (M.succ : ℤ), f z) = _
      rw [hInt, hNat]
      have hNegNotInner : -(M.succ : ℤ) ∉
          insert (M.succ : ℤ) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hPosNot : (M.succ : ℤ) ∉
          Finset.Icc (-(M : ℤ)) (M : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      have hNatNot : M.succ ∉ Finset.Icc 1 M := by
        simp only [Finset.mem_Icc]
        omega
      rw [Finset.sum_insert hNegNotInner, Finset.sum_insert hPosNot,
        Finset.sum_insert hNatNot]
      change f (-(M.succ : ℤ)) +
          (f (M.succ : ℤ) +
            ∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f z) = _
      rw [show (∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f z) =
          ∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff t ((N : ℝ) * m) +
              gmTraceFourier cutoff t (-((N : ℝ) * m))) by
        simpa only [f] using ih]
      dsimp only [f]
      have hneg : -(M.succ : ℤ) ≠ 0 := by omega
      have hpos : (M.succ : ℤ) ≠ 0 := by omega
      rw [if_neg hneg, if_neg hpos]
      push_cast
      ring_nf

/-- Exact decomposition of the complete nonzero integer series into the
retained signed window and its absolutely summable complement. -/
theorem gmTraceNonzeroFourierSum_eq_signed_add_far
    (cutoff : GMSmoothCutoff) (N M : ℕ) (hN : 0 < N) (t : ℝ) :
    gmTraceNonzeroFourierSum cutoff N t =
      (∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m)))) +
        gmTraceFourierFarTail cutoff N M t := by
  let f : ℤ → ℂ := fun m =>
    gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))
  have hf : Summable f := by
    simpa only [f] using gmTraceFourier_summable cutoff N hN t
  have hcentral : Summable (fun m : ℤ =>
      if m.natAbs ≤ M then (if m = 0 then 0 else f m) else 0) := by
    have hi := hf.indicator {m : ℤ | m.natAbs ≤ M ∧ m ≠ 0}
    convert hi using 1
    funext m
    by_cases hm : m.natAbs ≤ M <;> by_cases hm0 : m = 0 <;>
      simp [hm, hm0]
  have hfar : Summable (fun m : ℤ =>
      if M < m.natAbs then f m else 0) := by
    have hi := hf.indicator {m : ℤ | M < m.natAbs}
    convert hi using 1
    funext m
    by_cases hm : M < m.natAbs <;> simp [hm]
  have hsplit : gmTraceNonzeroFourierSum cutoff N t =
      (∑' m : ℤ,
        if m.natAbs ≤ M then (if m = 0 then 0 else f m) else 0) +
      ∑' m : ℤ, if M < m.natAbs then f m else 0 := by
    unfold gmTraceNonzeroFourierSum
    change (∑' m : ℤ, if m = 0 then 0 else f m) = _
    rw [← hcentral.tsum_add hfar]
    congr 1
    funext m
    by_cases hm : m.natAbs ≤ M
    · simp [hm, Nat.not_lt_of_ge hm]
    · have hm' : M < m.natAbs := Nat.lt_of_not_ge hm
      have hm0 : m ≠ 0 := by
        intro hzero
        subst m
        simp at hm'
      simp [hm, hm', hm0]
  rw [hsplit]
  congr 1
  · rw [tsum_eq_sum (s := Finset.Icc (-(M : ℤ)) (M : ℤ))]
    · calc
        (∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            if z.natAbs ≤ M then (if z = 0 then 0 else f z) else 0) =
            ∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
              if z = 0 then 0 else f z := by
                apply Finset.sum_congr rfl
                intro z hz
                rw [if_pos]
                have hzData := Finset.mem_Icc.mp hz
                omega
        _ = _ := by
          simpa only [f] using gmTraceFourierCentral_eq_signed cutoff N M t
    · intro z hz
      rw [if_neg]
      intro hzAbs
      have hzOut : z < -(M : ℤ) ∨ (M : ℤ) < z := by
        simpa only [Finset.mem_Icc, not_and_or, not_le] using hz
      omega

/-- Arbitrary-order summation of the omitted integer frequencies.  The
summable `|m|^-2` factor is retained before taking the `tsum`. -/
theorem gmTraceFourierFarTail_bound_order
    (cutoff : GMSmoothCutoff) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ), 0 < N → 0 < M → ∀ t : ℝ,
      ‖gmTraceFourierFarTail cutoff N M t‖ ≤
        K * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) * (M : ℝ) ^ n) := by
  obtain ⟨C₀, hC₀, hDecay⟩ := gmTraceFourier_uniform_decay cutoff (n + 2)
  let C : ℝ := C₀ + 1
  have hC : 0 < C := by dsimp only [C]; linarith
  have hPSeries : Summable (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) := by
    have hNorm : (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) =
        fun m : ℤ => |1 / (m : ℝ) ^ 2| := by
      funext m
      simp only [norm_div, norm_one, norm_pow, Complex.norm_intCast,
        abs_div, abs_one, pow_abs]
    rw [hNorm, summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (by norm_num)
  let B : ℝ := ∑' m : ℤ, ‖1 / (m : ℂ) ^ 2‖
  have hB : 0 ≤ B := tsum_nonneg fun m => norm_nonneg _
  refine ⟨C * B + 1, by positivity, ?_⟩
  intro N M hN hM t
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  let scale : ℝ := C * (1 + |t|) ^ (n + 2) /
    ((N : ℝ) ^ (n + 2) * (M : ℝ) ^ n)
  have hPointwise : ∀ m : ℤ, M < m.natAbs →
      ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
        scale * ‖1 / (m : ℂ) ^ 2‖ := by
    intro m hm
    have hmNatPos : 0 < m.natAbs := hM.trans hm
    have hmNe : m ≠ 0 := Int.natAbs_ne_zero.mp hmNatPos.ne'
    have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hmNe
    have hmAbsPos : 0 < |(m : ℝ)| := abs_pos.mpr hmReal
    have hmAbs : (M : ℝ) ≤ |(m : ℝ)| := by
      have hcast : (M : ℝ) ≤ (m.natAbs : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hm)
      simpa using hcast
    have hFreqAbs : |(N : ℝ) * (m : ℝ)| =
        (N : ℝ) * |(m : ℝ)| := by
      rw [abs_mul, abs_of_pos hNr]
    have hFreqPos : 0 < |(N : ℝ) * (m : ℝ)| := by
      rw [hFreqAbs]
      positivity
    have hFourier :
        ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
          C₀ * (1 + |t|) ^ (n + 2) /
            |(N : ℝ) * (m : ℝ)| ^ (n + 2) := by
      rw [le_div_iff₀ (pow_pos hFreqPos (n + 2))]
      simpa [mul_comm] using hDecay t ((N : ℝ) * (m : ℝ))
    have hpow : (M : ℝ) ^ n * |(m : ℝ)| ^ 2 ≤
        |(m : ℝ)| ^ (n + 2) := by
      calc
        (M : ℝ) ^ n * |(m : ℝ)| ^ 2 ≤
            |(m : ℝ)| ^ n * |(m : ℝ)| ^ 2 := by gcongr
        _ = |(m : ℝ)| ^ (n + 2) := by rw [pow_add]
    rw [norm_div, norm_one, norm_pow, Complex.norm_intCast]
    calc
      ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
          C₀ * (1 + |t|) ^ (n + 2) /
            |(N : ℝ) * (m : ℝ)| ^ (n + 2) := hFourier
      _ ≤ C * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) * |(m : ℝ)| ^ (n + 2)) := by
        rw [hFreqAbs, mul_pow]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith)
            (by positivity)) (by positivity)
      _ ≤ C * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) *
            ((M : ℝ) ^ n * |(m : ℝ)| ^ 2)) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = scale * (1 / |(m : ℝ)| ^ 2) := by
        dsimp only [scale]
        field_simp [hNr.ne', hMr.ne', hmAbsPos.ne']
  have hComparison : ∀ m : ℤ,
      ‖if M < m.natAbs then
          gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ)) else 0‖ ≤
        scale * ‖1 / (m : ℂ) ^ 2‖ := by
    intro m
    by_cases hm : M < m.natAbs
    · simpa only [if_pos hm] using hPointwise m hm
    · have hscale : 0 ≤ scale := by dsimp only [scale]; positivity
      rw [if_neg hm, norm_zero]
      exact mul_nonneg hscale (norm_nonneg _)
  have hScaled : Summable (fun m : ℤ => scale * ‖1 / (m : ℂ) ^ 2‖) :=
    hPSeries.mul_left scale
  have hBound := tsum_of_norm_bounded hScaled.hasSum hComparison
  rw [tsum_mul_left] at hBound
  change ‖gmTraceFourierFarTail cutoff N M t‖ ≤ scale * B at hBound
  have hDen : 0 < (N : ℝ) ^ (n + 2) * (M : ℝ) ^ n := by positivity
  calc
    ‖gmTraceFourierFarTail cutoff N M t‖ ≤ scale * B := hBound
    _ ≤ (C * B + 1) * (1 + |t|) ^ (n + 2) /
          ((N : ℝ) ^ (n + 2) * (M : ℝ) ^ n) := by
      dsimp only [scale]
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hDen).2
      have hpowNonneg : 0 ≤ (1 + |t|) ^ (n + 2) := by positivity
      nlinarith

/-! ## The cancellation-preserving Mellin core and tail -/

theorem continuous_gmReflectionDirichletPoly
    (t : ℝ) (M : ℕ) : Continuous (gmReflectionDirichletPoly t M) := by
  unfold gmReflectionDirichletPoly
  apply continuous_finsetSum
  intro m hm
  apply Continuous.const_cpow
  · fun_prop
  · left
    exact_mod_cast (show m ≠ 0 by
      exact (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1).ne')

theorem intervalIntegrable_norm_gmReflectionDirichletPoly
    (t : ℝ) (M : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ =>
      ‖gmReflectionDirichletPoly t M u‖) volume a b := by
  exact (continuous_gmReflectionDirichletPoly t M).norm.intervalIntegrable a b

theorem integral_norm_gmReflectionDirichletPoly_comp_neg
    (t : ℝ) (M : ℕ) (H : ℝ) :
    (∫ u in -H..H, ‖gmReflectionDirichletPoly t M (-u)‖) =
      ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
  simpa using (intervalIntegral.integral_comp_neg
    (f := fun u : ℝ => ‖gmReflectionDirichletPoly t M u‖)
    (a := -H) (b := H))

/-- The positive-frequency core of Lemma 6.2, with the coefficient-one
polynomial retained inside the integral. -/
theorem gmPositiveMellinCore_bound (cutoff : GMSmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ {t T₀ H : ℝ} {N M : ℕ},
      4 ≤ T₀ → T₀ ≤ t → 0 < H → H ≤ T₀ / 2 →
      0 < N → 0 < M →
      ∫ r : ℝ in Set.Icc (-H) H,
          (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
            ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
              ‖gmPositiveDualDirichletPoly t N M r‖ ≤
        C / Real.sqrt T₀ *
          ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
  obtain ⟨C₀, hC₀, hMellin⟩ := gmCutoffMellin_polynomial_decay cutoff 0
  let C : ℝ := 20 * (C₀ + 1) / (2 * Real.pi)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t T₀ H N M hT₀ ht hH hHT hN hM
  have hT₀Pos : 0 < T₀ := by linarith
  have hA : (0 : ℝ) < N := by exact_mod_cast hN
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hSqrtPos : 0 < Real.sqrt T₀ := Real.sqrt_pos.2 hT₀Pos
  have hHalfPos : 0 < Real.sqrt (T₀ / 2) := Real.sqrt_pos.2 (by positivity)
  have hSqrtCompare : Real.sqrt T₀ / 2 ≤ Real.sqrt (T₀ / 2) := by
    have hsq0 := Real.sq_sqrt hT₀Pos.le
    have hsq1 := Real.sq_sqrt (show 0 ≤ T₀ / 2 by positivity)
    nlinarith [Real.sqrt_nonneg T₀, Real.sqrt_nonneg (T₀ / 2)]
  have hStationary : 10 / Real.sqrt (T₀ / 2) ≤
      20 / Real.sqrt T₀ := by
    rw [div_le_div_iff₀ hHalfPos hSqrtPos]
    nlinarith
  have hDom : IntegrableOn (fun r : ℝ =>
      C / Real.sqrt T₀ * ‖gmReflectionDirichletPoly t M (-r)‖)
      (Set.Icc (-H) H) := by
    have hPoly := ((continuous_gmReflectionDirichletPoly t M).comp
      continuous_neg).norm
    exact (hPoly.continuousOn.integrableOn_compact isCompact_Icc).const_mul _
  have hTarget : IntegrableOn (fun r : ℝ =>
      (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
          ‖gmPositiveDualDirichletPoly t N M r‖) (Set.Icc (-H) H) :=
    (integrable_norm_gmPositiveDualAggregate cutoff t (M := M) hN).integrableOn
  calc
    ∫ r : ℝ in Set.Icc (-H) H,
        (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
          ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
            ‖gmPositiveDualDirichletPoly t N M r‖ ≤
      ∫ r : ℝ in Set.Icc (-H) H,
        C / Real.sqrt T₀ * ‖gmReflectionDirichletPoly t M (-r)‖ := by
      apply integral_mono_ae hTarget hDom
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hrAbs : |r| ≤ H := (abs_le).2 ⟨hr.1, hr.2⟩
      have hrCore : |r| ≤ T₀ / 2 := hrAbs.trans hHT
      have hMellinAt : ‖gmCutoffMellin cutoff r‖ ≤ C₀ := by
        simpa using hMellin r
      have hReflect := norm_gmReflectionIntegral_pos_core_le
        hT₀ ht hrCore hA hAB
      rw [norm_gmPositiveDualDirichletPoly_eq t r hN]
      dsimp only [C]
      have hPolyNonneg : 0 ≤ ‖gmReflectionDirichletPoly t M (-r)‖ :=
        norm_nonneg _
      have hPi : 0 < 2 * Real.pi := by positivity
      calc
        (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
                ‖gmReflectionDirichletPoly t M (-r)‖ ≤
            (1 / (2 * Real.pi)) * C₀ *
              (10 / Real.sqrt (T₀ / 2)) *
                ‖gmReflectionDirichletPoly t M (-r)‖ := by gcongr
        _ ≤ (20 * (C₀ + 1) / (2 * Real.pi)) /
              Real.sqrt T₀ *
                ‖gmReflectionDirichletPoly t M (-r)‖ := by
          have hCcmp : C₀ ≤ C₀ + 1 := by linarith
          calc
            _ ≤ (1 / (2 * Real.pi)) * (C₀ + 1) *
                (20 / Real.sqrt T₀) *
                  ‖gmReflectionDirichletPoly t M (-r)‖ := by gcongr
            _ = _ := by ring
    _ = C / Real.sqrt T₀ *
        ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
      have hset : (∫ r : ℝ in Set.Icc (-H) H,
          ‖gmReflectionDirichletPoly t M (-r)‖) =
          ∫ r in -H..H, ‖gmReflectionDirichletPoly t M (-r)‖ := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
      rw [MeasureTheory.integral_const_mul]
      rw [hset, integral_norm_gmReflectionDirichletPoly_comp_neg]

/-- Uniform Mellin-tail estimate.  The polynomial is bounded by `M` only
on this omitted range; no mode-cardinality loss enters the core. -/
theorem gmPositiveMellinTail_bound_order
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t H : ℝ) (N M : ℕ),
      1 ≤ H → 0 < N → 0 < M →
      ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
          (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
            ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
              ‖gmPositiveDualDirichletPoly t N M r‖ ≤
        K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) := by
  obtain ⟨C₀, hC₀, hDecay⟩ := gmCutoffMellin_polynomial_decay cutoff q
  let K : ℝ := max 1 (C₀ / Real.pi * (2 / ((q : ℝ) - 1)))
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro t H N M hH hN hM
  have hHPos : 0 < H := zero_lt_one.trans_le hH
  have hA : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hAB : (N : ℝ) ≤ 2 * N * M := by nlinarith
  have hqReal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have ha : -(q : ℝ) < -1 := by linarith
  have hDom : IntegrableOn (fun r : ℝ =>
      (C₀ / Real.pi * (M : ℝ) ^ 2) * |r| ^ (-(q : ℝ)))
      (Set.Icc (-H) H)ᶜ :=
    (integrableOn_abs_rpow_compl_Icc ha hHPos).const_mul _
  have hTarget : IntegrableOn (fun r : ℝ =>
      (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
          ‖gmPositiveDualDirichletPoly t N M r‖) (Set.Icc (-H) H)ᶜ :=
    (integrable_norm_gmPositiveDualAggregate cutoff t (M := M) hN).integrableOn
  have hPoint : ∀ r ∈ (Set.Icc (-H) H)ᶜ,
      (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
          ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
            ‖gmPositiveDualDirichletPoly t N M r‖ ≤
        (C₀ / Real.pi * (M : ℝ) ^ 2) * |r| ^ (-(q : ℝ)) := by
    intro r hr
    have hrAbs : H < |r| := by
      by_contra hnot
      exact hr ((abs_le).mp (le_of_not_gt hnot))
    have hrPos : 0 < |r| := hHPos.trans hrAbs
    have hMellin : ‖gmCutoffMellin cutoff r‖ ≤
        C₀ / |r| ^ q := by
      rw [le_div_iff₀ (pow_pos hrPos q)]
      simpa [mul_comm] using hDecay r
    have hReflect := norm_gmReflectionIntegral_le_log
      (tau := t - r) hA hAB
    have hRatio : (2 * (N : ℝ) * M) / N = 2 * (M : ℝ) := by
      field_simp [hA.ne']
    rw [hRatio] at hReflect
    have hLog : Real.log (2 * (M : ℝ)) ≤ 2 * (M : ℝ) :=
      Real.log_le_self (by positivity)
    have hPoly := norm_gmPositiveDualDirichletPoly_le t (M := M) hN r
    have hRpow : 1 / |r| ^ q = |r| ^ (-(q : ℝ)) := by
      rw [Real.rpow_neg hrPos.le]
      simp
    have hMellin' : ‖gmCutoffMellin cutoff r‖ ≤
        C₀ * |r| ^ (-(q : ℝ)) := by
      calc
        ‖gmCutoffMellin cutoff r‖ ≤ C₀ / |r| ^ q := hMellin
        _ = C₀ * (1 / |r| ^ q) := by ring
        _ = C₀ * |r| ^ (-(q : ℝ)) := by rw [hRpow]
    calc
      (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
            ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
              ‖gmPositiveDualDirichletPoly t N M r‖ ≤
          (1 / (2 * Real.pi)) *
            (C₀ * |r| ^ (-(q : ℝ))) * (2 * (M : ℝ)) * M := by
        gcongr
        exact hReflect.trans hLog
      _ = (C₀ / Real.pi * (M : ℝ) ^ 2) *
          |r| ^ (-(q : ℝ)) := by ring
  calc
    ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
        (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
          ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
            ‖gmPositiveDualDirichletPoly t N M r‖ ≤
      ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
        (C₀ / Real.pi * (M : ℝ) ^ 2) *
          |r| ^ (-(q : ℝ)) := by
      apply integral_mono_ae hTarget hDom
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with r hr
      exact hPoint r hr
    _ = (C₀ / Real.pi * (M : ℝ) ^ 2) *
        (-2 * H ^ (1 - (q : ℝ)) / (1 - (q : ℝ))) := by
      rw [integral_const_mul, integral_abs_rpow_compl_Icc ha hHPos]
      ring_nf
    _ ≤ K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) := by
      have hpow : 0 ≤ H ^ (1 - (q : ℝ)) := Real.rpow_nonneg hHPos.le _
      have hcoef : C₀ / Real.pi * (2 / ((q : ℝ) - 1)) ≤ K :=
        le_max_right _ _
      have hden : 1 - (q : ℝ) ≠ 0 := by linarith
      have hden' : (q : ℝ) - 1 ≠ 0 := by linarith
      have heq :
          (C₀ / Real.pi * (M : ℝ) ^ 2) *
              (-2 * H ^ (1 - (q : ℝ)) / (1 - (q : ℝ))) =
            (C₀ / Real.pi * (2 / ((q : ℝ) - 1))) *
              (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) := by
        field_simp [hden, hden']
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (sq_nonneg (M : ℝ))) hpow

/-- The negative-frequency core, expressed with the same coefficient-one
polynomial as the positive half. -/
theorem gmNegativeMellinCore_bound (cutoff : GMSmoothCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ {t T₀ H : ℝ} {N M : ℕ},
      4 ≤ T₀ → T₀ ≤ t → 0 < H → H ≤ T₀ / 2 →
      0 < N → 0 < M →
      ∫ r : ℝ in Set.Icc (-H) H,
          (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
            ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
              ‖gmPositiveDualDirichletPoly (-t) N M r‖ ≤
        C / Real.sqrt T₀ *
          ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
  obtain ⟨C₀, hC₀, hMellin⟩ := gmCutoffMellin_polynomial_decay cutoff 0
  let C : ℝ := 20 * (C₀ + 1) / (2 * Real.pi)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t T₀ H N M hT₀ ht hH hHT hN hM
  have hT₀Pos : 0 < T₀ := by linarith
  have hA : (0 : ℝ) < N := by exact_mod_cast hN
  have hAB : (N : ℝ) ≤ 2 * N * M := by
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hSqrtPos : 0 < Real.sqrt T₀ := Real.sqrt_pos.2 hT₀Pos
  have hHalfPos : 0 < Real.sqrt (T₀ / 2) := Real.sqrt_pos.2 (by positivity)
  have hSqrtCompare : Real.sqrt T₀ / 2 ≤ Real.sqrt (T₀ / 2) := by
    have hsq0 := Real.sq_sqrt hT₀Pos.le
    have hsq1 := Real.sq_sqrt (show 0 ≤ T₀ / 2 by positivity)
    nlinarith [Real.sqrt_nonneg T₀, Real.sqrt_nonneg (T₀ / 2)]
  have hStationary : 10 / Real.sqrt (T₀ / 2) ≤
      20 / Real.sqrt T₀ := by
    rw [div_le_div_iff₀ hHalfPos hSqrtPos]
    nlinarith
  have hDom : IntegrableOn (fun r : ℝ =>
      C / Real.sqrt T₀ * ‖gmReflectionDirichletPoly t M r‖)
      (Set.Icc (-H) H) := by
    have hPoly := (continuous_gmReflectionDirichletPoly t M).norm
    exact (hPoly.continuousOn.integrableOn_compact isCompact_Icc).const_mul _
  have hTarget : IntegrableOn (fun r : ℝ =>
      (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
        ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
          ‖gmPositiveDualDirichletPoly (-t) N M r‖) (Set.Icc (-H) H) :=
    (integrable_norm_gmPositiveDualAggregate cutoff (-t) (M := M) hN).integrableOn
  calc
    ∫ r : ℝ in Set.Icc (-H) H,
        (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
          ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
            ‖gmPositiveDualDirichletPoly (-t) N M r‖ ≤
      ∫ r : ℝ in Set.Icc (-H) H,
        C / Real.sqrt T₀ * ‖gmReflectionDirichletPoly t M r‖ := by
      apply integral_mono_ae hTarget hDom
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      have hrAbs : |r| ≤ H := (abs_le).2 ⟨hr.1, hr.2⟩
      have hrCore : |r| ≤ T₀ / 2 := hrAbs.trans hHT
      have hMellinAt : ‖gmCutoffMellin cutoff r‖ ≤ C₀ := by
        simpa using hMellin r
      have hReflect := norm_gmReflectionIntegral_neg_core_le
        hT₀ ht hrCore hA hAB
      rw [norm_gmPositiveDualDirichletPoly_eq (-t) r hN,
        norm_gmReflectionDirichletPoly_neg_time]
      simp only [neg_neg]
      dsimp only [C]
      calc
        (1 / (2 * Real.pi)) * ‖gmCutoffMellin cutoff r‖ *
              ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
                ‖gmReflectionDirichletPoly t M r‖ ≤
            (1 / (2 * Real.pi)) * C₀ *
              (10 / Real.sqrt (T₀ / 2)) *
                ‖gmReflectionDirichletPoly t M r‖ := by gcongr
        _ ≤ (20 * (C₀ + 1) / (2 * Real.pi)) /
              Real.sqrt T₀ * ‖gmReflectionDirichletPoly t M r‖ := by
          calc
            _ ≤ (1 / (2 * Real.pi)) * (C₀ + 1) *
                (20 / Real.sqrt T₀) *
                  ‖gmReflectionDirichletPoly t M r‖ := by
                    gcongr
                    linarith
            _ = _ := by ring
    _ = C / Real.sqrt T₀ *
        ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
      have hset : (∫ r : ℝ in Set.Icc (-H) H,
          ‖gmReflectionDirichletPoly t M r‖) =
          ∫ r in -H..H, ‖gmReflectionDirichletPoly t M r‖ := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
      rw [MeasureTheory.integral_const_mul, hset]

/-- Finite retained signed window with both Mellin tails removed at an
arbitrary order. -/
theorem gmRetainedSignedReflection_bound_order
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ {t T₀ H : ℝ} {N M : ℕ},
        4 ≤ T₀ → T₀ ≤ t → 1 ≤ H → H ≤ T₀ / 2 →
        0 < N → 0 < M →
        ‖∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff t ((N : ℝ) * m) +
              gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
          C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
            K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) := by
  obtain ⟨C₁, hC₁, hPos⟩ := gmPositiveMellinCore_bound cutoff
  obtain ⟨C₂, hC₂, hNeg⟩ := gmNegativeMellinCore_bound cutoff
  obtain ⟨K₀, hK₀, hTail⟩ := gmPositiveMellinTail_bound_order cutoff q hq
  refine ⟨C₁ + C₂, 2 * K₀, by positivity, by positivity, ?_⟩
  intro t T₀ H N M hT₀ ht hH hHT hN hM
  let fpos : ℝ → ℝ := fun r =>
    (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
      ‖gmReflectionIntegral (t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly t N M r‖
  let fneg : ℝ → ℝ := fun r =>
    (1 / (2 * Real.pi) : ℝ) * ‖gmCutoffMellin cutoff r‖ *
      ‖gmReflectionIntegral (-t - r) N (2 * N * M)‖ *
        ‖gmPositiveDualDirichletPoly (-t) N M r‖
  have hPosInt : Integrable fpos := by
    simpa only [fpos] using
      integrable_norm_gmPositiveDualAggregate cutoff t (M := M) hN
  have hNegInt : Integrable fneg := by
    simpa only [fneg] using
      integrable_norm_gmPositiveDualAggregate cutoff (-t) (M := M) hN
  have hSourceNonneg : 0 ≤
      ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
    exact intervalIntegral.integral_nonneg (by linarith) fun u _ => norm_nonneg _
  have hCorePos := hPos hT₀ ht (zero_lt_one.trans_le hH) hHT hN hM
  have hCoreNeg := hNeg hT₀ ht (zero_lt_one.trans_le hH) hHT hN hM
  have hTailPos := hTail t H N M hH hN hM
  have hTailNeg := hTail (-t) H N M hH hN hM
  calc
    ‖∑ m ∈ Finset.Icc 1 M,
        (gmTraceFourier cutoff t ((N : ℝ) * m) +
          gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ ≤
        (∫ r : ℝ, fpos r) + ∫ r : ℝ, fneg r := by
      simpa only [fpos, fneg] using
        norm_gmTraceFourier_signed_sum_le_dualPoly cutoff t hN
    _ = ((∫ r : ℝ in Set.Icc (-H) H, fpos r) +
          ∫ r : ℝ in (Set.Icc (-H) H)ᶜ, fpos r) +
        ((∫ r : ℝ in Set.Icc (-H) H, fneg r) +
          ∫ r : ℝ in (Set.Icc (-H) H)ᶜ, fneg r) := by
      rw [integral_add_compl measurableSet_Icc hPosInt,
        integral_add_compl measurableSet_Icc hNegInt]
    _ ≤ (C₁ + C₂) / Real.sqrt T₀ *
          (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
        (2 * K₀) * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) := by
      have hPieces := add_le_add
        (add_le_add hCorePos hTailPos) (add_le_add hCoreNeg hTailNeg)
      simpa only [fpos, fneg] using hPieces.trans_eq (by ring)

/-! ## Ordinate symmetry -/

/-- The complete nonzero-frequency series at the opposite ordinate is its
complex conjugate.  The proof reindexes the entire integer `tsum`; no finite
window or cardinality estimate is involved. -/
theorem gmTraceNonzeroFourierSum_neg_eq_conj
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    gmTraceNonzeroFourierSum cutoff N (-t) =
      star (gmTraceNonzeroFourierSum cutoff N t) := by
  unfold gmTraceNonzeroFourierSum
  rw [← (Equiv.neg ℤ).tsum_eq]
  change _ = conj (∑' m : ℤ,
    if m = 0 then 0 else gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ)))
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · subst m
    simp
  · have hneg : -m ≠ 0 := neg_ne_zero.mpr hm
    change (if -m = 0 then 0 else
        gmTraceFourier cutoff (-t) ((N : ℝ) * ((-m : ℤ) : ℝ))) =
      star (if m = 0 then 0 else
        gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ)))
    rw [if_neg hneg, if_neg hm]
    have hfreq : (N : ℝ) * ((-m : ℤ) : ℝ) =
        -((N : ℝ) * (m : ℝ)) := by push_cast; ring
    rw [hfreq, gmTraceFourier_neg_eq_conj]
    simp

theorem norm_gmTraceNonzeroFourierSum_neg
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    ‖gmTraceNonzeroFourierSum cutoff N (-t)‖ =
      ‖gmTraceNonzeroFourierSum cutoff N t‖ := by
  rw [gmTraceNonzeroFourierSum_neg_eq_conj]
  exact norm_star _

theorem integral_norm_gmReflectionDirichletPoly_neg_time
    (t H : ℝ) (M : ℕ) :
    (∫ u in -H..H, ‖gmReflectionDirichletPoly (-t) M u‖) =
      ∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖ := by
  simp_rw [norm_gmReflectionDirichletPoly_neg_time]
  exact integral_norm_gmReflectionDirichletPoly_comp_neg t M H

/-! ## Complete-frequency core-plus-tail theorem -/

/-- The complete nonzero integer series, before choosing the source scales.
This is the analytic heart of Lemma 6.2: the first error is the Mellin tail
and the second is the absolutely summed omitted-frequency tail. -/
theorem gmCompleteSmoothReflection_bound_order
    (cutoff : GMSmoothCutoff) (q : ℕ) (hq : 2 ≤ q) :
    ∃ C K L : ℝ, 0 < C ∧ 0 < K ∧ 0 < L ∧
      ∀ {t T₀ H : ℝ} {N M : ℕ},
        4 ≤ T₀ → T₀ ≤ |t| → 1 ≤ H → H ≤ T₀ / 2 →
        0 < N → 0 < M →
        ‖gmTraceNonzeroFourierSum cutoff N t‖ ≤
          C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
            K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
            L * (1 + |t|) ^ (q + 2) /
              ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) := by
  obtain ⟨C, K, hC, hK, hRetained⟩ :=
    gmRetainedSignedReflection_bound_order cutoff q hq
  obtain ⟨L, hL, hFar⟩ := gmTraceFourierFarTail_bound_order cutoff q
  refine ⟨C, K, L, hC, hK, hL, ?_⟩
  intro t T₀ H N M hT₀ ht hH hHT hN hM
  have hAbsNonneg : 0 ≤ |t| := abs_nonneg t
  have hFarAt := hFar N M hN hM t
  by_cases htnonneg : 0 ≤ t
  · have hRet := hRetained (t := t) hT₀
      (by simpa only [abs_of_nonneg htnonneg] using ht) hH hHT hN hM
    rw [gmTraceNonzeroFourierSum_eq_signed_add_far cutoff N M hN t]
    calc
      ‖(∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff t ((N : ℝ) * m) +
              gmTraceFourier cutoff t (-((N : ℝ) * m)))) +
          gmTraceFourierFarTail cutoff N M t‖ ≤
          ‖∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff t ((N : ℝ) * m) +
              gmTraceFourier cutoff t (-((N : ℝ) * m)))‖ +
            ‖gmTraceFourierFarTail cutoff N M t‖ := norm_add_le _ _
      _ ≤ (C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
            K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ))) +
          L * (1 + |t|) ^ (q + 2) /
            ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) :=
        add_le_add hRet hFarAt
      _ = _ := by ring
  · have htneg : t < 0 := lt_of_not_ge htnonneg
    let s : ℝ := -t
    have hs : s = |t| := by dsimp only [s]; rw [abs_of_neg htneg]
    have hsNonneg : 0 ≤ s := by rw [hs]; exact hAbsNonneg
    have hRet := hRetained (t := s) hT₀ (by simpa only [hs] using ht)
      hH hHT hN hM
    have hFarNeg := hFar N M hN hM s
    have hNorm : ‖gmTraceNonzeroFourierSum cutoff N t‖ =
        ‖gmTraceNonzeroFourierSum cutoff N s‖ := by
      have htEq : t = -s := by dsimp only [s]; ring
      rw [htEq, norm_gmTraceNonzeroFourierSum_neg]
    rw [hNorm, gmTraceNonzeroFourierSum_eq_signed_add_far cutoff N M hN s]
    calc
      ‖(∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff s ((N : ℝ) * m) +
              gmTraceFourier cutoff s (-((N : ℝ) * m)))) +
          gmTraceFourierFarTail cutoff N M s‖ ≤
          ‖∑ m ∈ Finset.Icc 1 M,
            (gmTraceFourier cutoff s ((N : ℝ) * m) +
              gmTraceFourier cutoff s (-((N : ℝ) * m)))‖ +
            ‖gmTraceFourierFarTail cutoff N M s‖ := norm_add_le _ _
      _ ≤ (C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly s M u‖) +
            K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ))) +
          L * (1 + |s|) ^ (q + 2) /
            ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) :=
        add_le_add hRet hFarNeg
      _ = C / Real.sqrt T₀ *
              (∫ u in -H..H, ‖gmReflectionDirichletPoly t M u‖) +
            K * (M : ℝ) ^ 2 * H ^ (1 - (q : ℝ)) +
          L * (1 + |t|) ^ (q + 2) /
            ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) := by
        have hst : s = -t := rfl
        rw [hst, integral_norm_gmReflectionDirichletPoly_neg_time]
        simp only [abs_neg]

/-! ## Source scale selection -/

/-- The epsilon reserve used for both the Mellin and frequency tails.  Capping
it at `1/16` keeps the smoothing window below the physical height even when
the caller supplies a large epsilon. -/
noncomputable def gmReflectionEta (ε : ℝ) : ℝ :=
  min (ε / 16) (1 / 16)

/-- The `gmReflectionHeight` definition used by the source-facing construction in `QuantitativeSmoothReflection`. -/
noncomputable def gmReflectionHeight (T ε : ℝ) : ℝ :=
  T ^ gmReflectionEta ε

/-- The `gmReflectionLength` definition used by the source-facing construction in `QuantitativeSmoothReflection`. -/
noncomputable def gmReflectionLength (T ε : ℝ) (N : ℕ) (t : ℝ) : ℕ :=
  Nat.ceil (((1 + |t|) * gmReflectionHeight T ε) / (N : ℝ))

theorem gmReflectionEta_pos {ε : ℝ} (hε : 0 < ε) :
    0 < gmReflectionEta ε := by
  unfold gmReflectionEta
  exact lt_min (by positivity) (by norm_num)

theorem gmReflectionEta_le_one {ε : ℝ} :
    gmReflectionEta ε ≤ 1 := by
  unfold gmReflectionEta
  exact (min_le_right _ _).trans (by norm_num)

theorem gmReflectionEta_lt_eps {ε : ℝ} (hε : 0 < ε) :
    gmReflectionEta ε < ε := by
  have hle : gmReflectionEta ε ≤ ε / 16 := by
    unfold gmReflectionEta
    exact min_le_left _ _
  nlinarith

theorem gmReflectionLength_pos {T ε t : ℝ} {N : ℕ}
    (hT : 0 < T) (hN : 0 < N) :
    0 < gmReflectionLength T ε N t := by
  apply Nat.ceil_pos.mpr
  exact div_pos (mul_pos (by positivity)
    (Real.rpow_pos_of_pos hT (gmReflectionEta ε))) (by exact_mod_cast hN)

theorem gmReflectionLength_lower {T ε t : ℝ} {N : ℕ}
    (hN : 0 < N) :
    (1 + |t|) * gmReflectionHeight T ε ≤
      (N : ℝ) * gmReflectionLength T ε N t := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hRatio : ((1 + |t|) * gmReflectionHeight T ε) / (N : ℝ) ≤
      (gmReflectionLength T ε N t : ℝ) := by
    exact Nat.le_ceil _
  rw [div_le_iff₀ hNr] at hRatio
  exact hRatio.trans_eq (mul_comm _ _)

theorem gmReflectionLength_upper {T ε t : ℝ} {N : ℕ}
    (hT : 1 ≤ T) (hN : 0 < N) (ht : |t| ≤ T) :
    (gmReflectionLength T ε N t : ℝ) ≤ 3 * T ^ 2 := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hH : gmReflectionHeight T ε ≤ T := by
    unfold gmReflectionHeight
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT (gmReflectionEta_le_one (ε := ε))
  have hHNonneg : 0 ≤ gmReflectionHeight T ε := by
    exact Real.rpow_nonneg hTpos.le _
  have hRatioNonneg : 0 ≤
      ((1 + |t|) * gmReflectionHeight T ε) / (N : ℝ) := by
    positivity
  have hCeil := Nat.ceil_lt_add_one hRatioNonneg
  have hRatio : ((1 + |t|) * gmReflectionHeight T ε) / (N : ℝ) ≤
      2 * T ^ 2 := by
    calc
      ((1 + |t|) * gmReflectionHeight T ε) / (N : ℝ) ≤
          (1 + |t|) * gmReflectionHeight T ε := by
        exact div_le_self (mul_nonneg (by positivity) hHNonneg) hNr
      _ ≤ (1 + T) * T := by gcongr
      _ ≤ 2 * T ^ 2 := by nlinarith [sq_nonneg (T - 1)]
  dsimp only [gmReflectionLength] at hCeil ⊢
  linarith [show (1 : ℝ) ≤ T ^ 2 by nlinarith]

/-- The `gmReflectionDecayOrder` definition used by the source-facing construction in `QuantitativeSmoothReflection`. -/
noncomputable def gmReflectionDecayOrder (A ε : ℝ) : ℕ :=
  Nat.ceil ((A + 6) / gmReflectionEta ε) + 2

theorem gmReflectionDecayOrder_two_le (A ε : ℝ) :
    2 ≤ gmReflectionDecayOrder A ε := by
  unfold gmReflectionDecayOrder
  omega

theorem gmReflectionDecayOrder_budget {A ε : ℝ}
    (hA : 0 < A) (hε : 0 < ε) :
    A + 5 ≤ gmReflectionEta ε *
      ((gmReflectionDecayOrder A ε : ℝ) - 1) := by
  have hη := gmReflectionEta_pos hε
  have hRatioNonneg : 0 ≤ (A + 6) / gmReflectionEta ε := by positivity
  have hceil : (A + 6) / gmReflectionEta ε ≤
      (Nat.ceil ((A + 6) / gmReflectionEta ε) : ℝ) := Nat.le_ceil _
  have hscaled : A + 6 ≤ gmReflectionEta ε *
      (Nat.ceil ((A + 6) / gmReflectionEta ε) : ℝ) := by
    rw [div_le_iff₀ hη] at hceil
    simpa only [mul_comm] using hceil
  unfold gmReflectionDecayOrder
  push_cast
  nlinarith

/-- Eventually the source window is nontrivial, lies in the stationary core,
and the requested error denominator is at least one. -/
theorem exists_gmReflectionScaleThreshold {ε : ℝ} (hε : 0 < ε) :
    ∃ T_min : ℝ, 1 ≤ T_min ∧ ∀ {T T₀ : ℝ}, T_min ≤ T →
      T ^ ε ≤ T₀ →
      4 ≤ T₀ ∧ 1 ≤ gmReflectionHeight T ε ∧
        gmReflectionHeight T ε ≤ T₀ / 2 := by
  let η := gmReflectionEta ε
  have hη : 0 < η := gmReflectionEta_pos hε
  have hgap : 0 < ε - η := sub_pos.mpr (gmReflectionEta_lt_eps hε)
  have hEpsTop := tendsto_rpow_atTop hε
  have hEtaTop := tendsto_rpow_atTop hη
  have hGapTop := tendsto_rpow_atTop hgap
  have hEpsEventually : ∀ᶠ T : ℝ in atTop, 4 ≤ T ^ ε :=
    hEpsTop.eventually (eventually_ge_atTop 4)
  have hEtaEventually : ∀ᶠ T : ℝ in atTop, 1 ≤ T ^ η :=
    hEtaTop.eventually (eventually_ge_atTop 1)
  have hGapEventually : ∀ᶠ T : ℝ in atTop, 2 ≤ T ^ (ε - η) :=
    hGapTop.eventually (eventually_ge_atTop 2)
  have hAll : ∀ᶠ T : ℝ in atTop,
      1 ≤ T ∧ 4 ≤ T ^ ε ∧ 1 ≤ T ^ η ∧ 2 ≤ T ^ (ε - η) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hEpsEventually,
      hEtaEventually, hGapEventually] with T hT hTE hTH hTG
    exact ⟨hT, hTE, hTH, hTG⟩
  rw [eventually_atTop] at hAll
  obtain ⟨T_min, hT_min⟩ := hAll
  refine ⟨max 1 T_min, le_max_left _ _, ?_⟩
  intro T T₀ hT hT₀
  have hData := hT_min T ((le_max_right _ _).trans hT)
  have hTpos : 0 < T := zero_lt_one.trans_le hData.1
  have hFactor : 2 * T ^ η ≤ T ^ ε := by
    calc
      2 * T ^ η ≤ T ^ (ε - η) * T ^ η :=
        mul_le_mul_of_nonneg_right hData.2.2.2
          (Real.rpow_nonneg hTpos.le _)
      _ = T ^ ε := by
        rw [← Real.rpow_add hTpos]
        congr 1
        ring
  refine ⟨hData.2.1.trans hT₀, ?_, ?_⟩
  · simpa only [gmReflectionHeight, η] using hData.2.2.1
  · dsimp only [gmReflectionHeight]
    have : 2 * T ^ gmReflectionEta ε ≤ T₀ := by
      exact hFactor.trans hT₀
    linarith

theorem gmReflectionMellinError_le
    {A ε K T t : ℝ} {N : ℕ}
    (hA : 0 < A) (hε : 0 < ε) (hK : 0 ≤ K)
    (hT : 1 ≤ T) (hN : 0 < N) (ht : |t| ≤ T) :
    K * (gmReflectionLength T ε N t : ℝ) ^ 2 *
        gmReflectionHeight T ε ^
          (1 - (gmReflectionDecayOrder A ε : ℝ)) ≤
      9 * K / T ^ A := by
  let η := gmReflectionEta ε
  let q := gmReflectionDecayOrder A ε
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hM := gmReflectionLength_upper (ε := ε) hT hN ht
  have hMsq : (gmReflectionLength T ε N t : ℝ) ^ 2 ≤
      9 * T ^ 4 := by
    have hMnonneg : 0 ≤ (gmReflectionLength T ε N t : ℝ) := by positivity
    nlinarith [sq_nonneg ((gmReflectionLength T ε N t : ℝ) - 3 * T ^ 2)]
  have hBudget := gmReflectionDecayOrder_budget hA hε
  have hExponent : 4 + η * (1 - (q : ℝ)) ≤ -A := by
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
    K * (gmReflectionLength T ε N t : ℝ) ^ 2 *
          gmReflectionHeight T ε ^ (1 - (q : ℝ)) ≤
        K * (9 * T ^ 4) *
          gmReflectionHeight T ε ^ (1 - (q : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hMsq hK)
        hHeightNonneg
    _ = 9 * K * T ^ (4 + η * (1 - (q : ℝ))) := by
      rw [hHeight]
      calc
        K * (9 * T ^ 4) * T ^ (η * (1 - (q : ℝ))) =
            9 * K * (T ^ 4 * T ^ (η * (1 - (q : ℝ)))) := by ring
        _ = 9 * K * T ^ (4 + η * (1 - (q : ℝ))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hTpos]
          norm_num
    _ ≤ 9 * K * T ^ (-A) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT hExponent)
        (mul_nonneg (by norm_num) hK)
    _ = 9 * K / T ^ A := by
      rw [Real.rpow_neg hTpos.le]
      ring

theorem gmReflectionFrequencyError_le
    {A ε L T t : ℝ} {N : ℕ}
    (hA : 0 < A) (hε : 0 < ε) (hL : 0 ≤ L)
    (hT : 1 ≤ T) (hN : 0 < N) (ht : |t| ≤ T) :
    L * (1 + |t|) ^ (gmReflectionDecayOrder A ε + 2) /
        ((N : ℝ) ^ (gmReflectionDecayOrder A ε + 2) *
          (gmReflectionLength T ε N t : ℝ) ^
            gmReflectionDecayOrder A ε) ≤
      4 * L / T ^ A := by
  let η := gmReflectionEta ε
  let q := gmReflectionDecayOrder A ε
  let H := gmReflectionHeight T ε
  let M := gmReflectionLength T ε N t
  let a := 1 + |t|
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hMposNat : 0 < M := gmReflectionLength_pos hTpos hN
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hMposNat
  have hHpos : 0 < H := by
    dsimp only [H, gmReflectionHeight]
    exact Real.rpow_pos_of_pos hTpos _
  have haPos : 0 < a := by dsimp only [a]; positivity
  have hNM : a * H ≤ (N : ℝ) * M := by
    simpa only [a, H, M] using
      gmReflectionLength_lower (T := T) (ε := ε) (t := t) hN
  have hNpow : (N : ℝ) ^ q ≤ (N : ℝ) ^ (q + 2) := by
    exact pow_le_pow_right₀ hNr (Nat.le_add_right q 2)
  have hDenLower : (a * H) ^ q ≤
      (N : ℝ) ^ (q + 2) * (M : ℝ) ^ q := by
    calc
      (a * H) ^ q ≤ ((N : ℝ) * M) ^ q := by gcongr
      _ = (N : ℝ) ^ q * (M : ℝ) ^ q := by rw [mul_pow]
      _ ≤ (N : ℝ) ^ (q + 2) * (M : ℝ) ^ q := by gcongr
  have hDenPos : 0 < (a * H) ^ q := pow_pos (mul_pos haPos hHpos) q
  have hRaw :
      L * a ^ (q + 2) /
          ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) ≤
        L * a ^ 2 / H ^ q := by
    calc
      L * a ^ (q + 2) /
            ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) ≤
          L * a ^ (q + 2) / (a * H) ^ q := by
        exact div_le_div_of_nonneg_left (mul_nonneg hL (by positivity))
          hDenPos hDenLower
      _ = L * a ^ 2 / H ^ q := by
        rw [pow_add, mul_pow]
        field_simp [haPos.ne', hHpos.ne']
  have haBound : a ≤ 2 * T := by
    dsimp only [a]
    nlinarith
  have haSq : a ^ 2 ≤ 4 * T ^ 2 := by
    nlinarith [sq_nonneg (a - 2 * T), sq_nonneg a]
  have hBudget := gmReflectionDecayOrder_budget hA hε
  have hExponent : 2 - η * (q : ℝ) ≤ -A := by
    dsimp only [η, q]
    have hη := gmReflectionEta_pos hε
    nlinarith
  have hHeightPow : H ^ q = T ^ (η * (q : ℝ)) := by
    dsimp only [H, gmReflectionHeight, η]
    rw [← Real.rpow_natCast, Real.rpow_mul hTpos.le]
  calc
    L * (1 + |t|) ^ (gmReflectionDecayOrder A ε + 2) /
          ((N : ℝ) ^ (gmReflectionDecayOrder A ε + 2) *
            (gmReflectionLength T ε N t : ℝ) ^
              gmReflectionDecayOrder A ε) =
        L * a ^ (q + 2) /
          ((N : ℝ) ^ (q + 2) * (M : ℝ) ^ q) := rfl
    _ ≤ L * a ^ 2 / H ^ q := hRaw
    _ ≤ L * (4 * T ^ 2) / H ^ q := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left haSq hL) (by positivity)
    _ = 4 * L * T ^ (2 - η * (q : ℝ)) := by
      rw [hHeightPow, Real.rpow_sub hTpos]
      rw [← Real.rpow_natCast]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hTpos (η * (q : ℝ)))]
      ring_nf
    _ ≤ 4 * L * T ^ (-A) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT hExponent)
        (mul_nonneg (by norm_num) hL)
    _ = 4 * L / T ^ A := by
      rw [Real.rpow_neg hTpos.le]
      ring

/-! ## Public Guth--Maynard Lemma 6.2 theorem -/

/-- Source-strength quantitative smooth reflection.  The complete nonzero
integer-frequency series is bounded by one coefficient-one Dirichlet
polynomial on the explicit smoothing window, with an arbitrary requested
power saving. -/
def GMQuantitativeSmoothReflection (cutoff : GMSmoothCutoff) : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∃ C T_min : ℝ, 0 < C ∧ 1 ≤ T_min ∧
      ∀ {T T₀ t : ℝ} {N : ℕ},
        T_min ≤ T → 0 < N → (N : ℝ) ≤ T →
        T ^ ε ≤ T₀ → T₀ ≤ |t| → |t| ≤ 2 * T₀ → |t| ≤ T →
        ‖gmTraceNonzeroFourierSum cutoff N t‖ ≤
          C / Real.sqrt T₀ *
            (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
              ‖gmReflectionDirichletPoly t
                (gmReflectionLength T ε N t) u‖) +
          C / T ^ A

theorem gmQuantitativeSmoothReflection_native
    (cutoff : GMSmoothCutoff) :
    GMQuantitativeSmoothReflection cutoff := by
  intro A ε hA hε
  let q := gmReflectionDecayOrder A ε
  have hq : 2 ≤ q := gmReflectionDecayOrder_two_le A ε
  obtain ⟨C₀, K, L, hC₀, hK, hL, hComplete⟩ :=
    gmCompleteSmoothReflection_bound_order cutoff q hq
  obtain ⟨T_min, hT_min, hScale⟩ := exists_gmReflectionScaleThreshold hε
  let C : ℝ := max C₀ (9 * K + 4 * L)
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨C, T_min, hC, hT_min, ?_⟩
  intro T T₀ t N hT hN _hNT hT₀ htLower _htDouble htUpper
  have hTOne : 1 ≤ T := hT_min.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hTOne
  have hScaleData := hScale hT hT₀
  have hMPos : 0 < gmReflectionLength T ε N t :=
    gmReflectionLength_pos hTpos hN
  have hRaw := hComplete hScaleData.1 htLower hScaleData.2.1
    hScaleData.2.2 hN hMPos
  have hMellin := gmReflectionMellinError_le hA hε hK.le
    hTOne hN htUpper
  have hFrequency := gmReflectionFrequencyError_le hA hε hL.le
    hTOne hN htUpper
  have hSourceNonneg : 0 ≤
      ∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
        ‖gmReflectionDirichletPoly t
          (gmReflectionLength T ε N t) u‖ := by
    have hHeightNonneg : 0 ≤ gmReflectionHeight T ε := by
      exact Real.rpow_nonneg hTpos.le _
    exact intervalIntegral.integral_nonneg
      (by linarith : -(gmReflectionHeight T ε) ≤ gmReflectionHeight T ε)
      fun u _ => norm_nonneg _
  have hT₀Pos : 0 < T₀ := by linarith [hScaleData.1]
  have hCore : C₀ / Real.sqrt T₀ *
        (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
          ‖gmReflectionDirichletPoly t
            (gmReflectionLength T ε N t) u‖) ≤
      C / Real.sqrt T₀ *
        (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
          ‖gmReflectionDirichletPoly t
            (gmReflectionLength T ε N t) u‖) := by
    gcongr
    exact le_max_left _ _
  have hErr :
      K * (gmReflectionLength T ε N t : ℝ) ^ 2 *
          gmReflectionHeight T ε ^ (1 - (q : ℝ)) +
        L * (1 + |t|) ^ (q + 2) /
          ((N : ℝ) ^ (q + 2) *
            (gmReflectionLength T ε N t : ℝ) ^ q) ≤
        (9 * K + 4 * L) / T ^ A := by
    dsimp only [q] at hMellin hFrequency ⊢
    calc
      _ ≤ 9 * K / T ^ A + 4 * L / T ^ A :=
        add_le_add hMellin hFrequency
      _ = (9 * K + 4 * L) / T ^ A := by ring
  have hErrC : (9 * K + 4 * L) / T ^ A ≤ C / T ^ A := by
    exact div_le_div_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg hTpos.le A)
  exact hRaw.trans <| by
    calc
      C₀ / Real.sqrt T₀ *
            (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
              ‖gmReflectionDirichletPoly t
                (gmReflectionLength T ε N t) u‖) +
          K * (gmReflectionLength T ε N t : ℝ) ^ 2 *
            gmReflectionHeight T ε ^ (1 - (q : ℝ)) +
          L * (1 + |t|) ^ (q + 2) /
            ((N : ℝ) ^ (q + 2) *
              (gmReflectionLength T ε N t : ℝ) ^ q) ≤
        C / Real.sqrt T₀ *
            (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
              ‖gmReflectionDirichletPoly t
                (gmReflectionLength T ε N t) u‖) +
          (9 * K + 4 * L) / T ^ A := by
        calc
          _ = C₀ / Real.sqrt T₀ *
                (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
                  ‖gmReflectionDirichletPoly t
                    (gmReflectionLength T ε N t) u‖) +
              (K * (gmReflectionLength T ε N t : ℝ) ^ 2 *
                gmReflectionHeight T ε ^ (1 - (q : ℝ)) +
              L * (1 + |t|) ^ (q + 2) /
                ((N : ℝ) ^ (q + 2) *
                  (gmReflectionLength T ε N t : ℝ) ^ q)) := by ring
          _ ≤ _ := add_le_add hCore hErr
      _ ≤ C / Real.sqrt T₀ *
            (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
              ‖gmReflectionDirichletPoly t
                (gmReflectionLength T ε N t) u‖) +
          C / T ^ A := add_le_add le_rfl hErrC

/-- The source's fixed `T^-100` version of the complete-frequency theorem. -/
theorem gmQuantitativeSmoothReflection_hundred
    (cutoff : GMSmoothCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∃ C T_min : ℝ, 0 < C ∧ 1 ≤ T_min ∧
      ∀ {T T₀ t : ℝ} {N : ℕ},
        T_min ≤ T → 0 < N → (N : ℝ) ≤ T →
        T ^ ε ≤ T₀ → T₀ ≤ |t| → |t| ≤ 2 * T₀ → |t| ≤ T →
        ‖gmTraceNonzeroFourierSum cutoff N t‖ ≤
          C / Real.sqrt T₀ *
            (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
              ‖gmReflectionDirichletPoly t
                (gmReflectionLength T ε N t) u‖) +
          C / T ^ (100 : ℝ) := by
  exact gmQuantitativeSmoothReflection_native cutoff 100 ε (by norm_num) hε

/-- The scaled cubic-trace tail is exactly `N` times the unscaled complete
nonzero-frequency series. -/
theorem gmTraceNonzeroTailAt_eq_scale_mul
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    gmTraceNonzeroTailAt cutoff N t =
      (N : ℂ) * gmTraceNonzeroFourierSum cutoff N t := by
  unfold gmTraceNonzeroTailAt gmTraceNonzeroFourierSum gmScaledTraceMode
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  by_cases hm : m = 0 <;> simp [hm]

theorem norm_gmTraceNonzeroTailAt_eq
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    ‖gmTraceNonzeroTailAt cutoff N t‖ =
      (N : ℝ) * ‖gmTraceNonzeroFourierSum cutoff N t‖ := by
  rw [gmTraceNonzeroTailAt_eq_scale_mul, norm_mul, Complex.norm_natCast]

/-- Arbitrary-power quantitative reflection for the exact scaled tail used in
the cubic trace.  Invoking the unscaled theorem at `A + 1` absorbs its leading
factor `N ≤ T` without losing the requested final power. -/
def GMScaledQuantitativeSmoothReflection (cutoff : GMSmoothCutoff) : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∃ C T_min : ℝ, 0 < C ∧ 1 ≤ T_min ∧
      ∀ {T T₀ t : ℝ} {N : ℕ},
        T_min ≤ T → 0 < N → (N : ℝ) ≤ T →
        T ^ ε ≤ T₀ → T₀ ≤ |t| → |t| ≤ 2 * T₀ → |t| ≤ T →
        ‖gmTraceNonzeroTailAt cutoff N t‖ ≤
          (N : ℝ) * C / Real.sqrt T₀ *
            (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
              ‖gmReflectionDirichletPoly t
                (gmReflectionLength T ε N t) u‖) +
          C / T ^ A

theorem gmScaledQuantitativeSmoothReflection_native
    (cutoff : GMSmoothCutoff) :
    GMScaledQuantitativeSmoothReflection cutoff := by
  intro A ε hA hε
  obtain ⟨C, T_min, hC, hT_min, hBound⟩ :=
    gmQuantitativeSmoothReflection_native cutoff (A + 1) ε (by linarith) hε
  refine ⟨C, T_min, hC, hT_min, ?_⟩
  intro T T₀ t N hT hN hNT hT₀ htLower htDouble htUpper
  have hTOne : 1 ≤ T := hT_min.trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hTOne
  have hUnscaled := hBound hT hN hNT hT₀ htLower htDouble htUpper
  have hError : (N : ℝ) * (C / T ^ (A + 1)) ≤ C / T ^ A := by
    have hPowA : 0 < T ^ A := Real.rpow_pos_of_pos hTpos A
    have hPowAdd : T ^ (A + 1) = T ^ A * T := by
      rw [Real.rpow_add hTpos]
      norm_num
    rw [hPowAdd]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hNT' : (N : ℝ) / T ≤ 1 := (div_le_one hTpos).2 hNT
    have hCpow : 0 ≤ C * (T ^ A)⁻¹ := mul_nonneg hC.le (inv_nonneg.2 hPowA.le)
    calc
      (N : ℝ) * (C * (T ^ A * T)⁻¹) =
          ((N : ℝ) / T) * (C * (T ^ A)⁻¹) := by
        field_simp [hTpos.ne', hPowA.ne']
      _ ≤ 1 * (C * (T ^ A)⁻¹) :=
        mul_le_mul_of_nonneg_right hNT' hCpow
      _ = C * (T ^ A)⁻¹ := one_mul _
  rw [norm_gmTraceNonzeroTailAt_eq]
  calc
    (N : ℝ) * ‖gmTraceNonzeroFourierSum cutoff N t‖ ≤
        (N : ℝ) *
          (C / Real.sqrt T₀ *
            (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
              ‖gmReflectionDirichletPoly t
                (gmReflectionLength T ε N t) u‖) +
          C / T ^ (A + 1)) :=
      mul_le_mul_of_nonneg_left hUnscaled (by positivity)
    _ = (N : ℝ) * C / Real.sqrt T₀ *
            (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
              ‖gmReflectionDirichletPoly t
                (gmReflectionLength T ε N t) u‖) +
          (N : ℝ) * (C / T ^ (A + 1)) := by ring
    _ ≤ (N : ℝ) * C / Real.sqrt T₀ *
            (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
              ‖gmReflectionDirichletPoly t
                (gmReflectionLength T ε N t) u‖) +
          C / T ^ A := add_le_add le_rfl hError

/-- Direct Section 6 consumer for the first cyclic product in the exact
`gmCubicS2` summand.  The reflected factor is the literal
`gmTraceNonzeroTailAt` in `gmCubicS2FirstSummand`; the other two factors are
left intact for the separate Proposition 6.1 summation argument. -/
theorem gmCubicS2FirstSummand_reflection_native
    (cutoff : GMSmoothCutoff) :
    ∀ A ε : ℝ, 0 < A → 0 < ε →
      ∃ C T_min : ℝ, 0 < C ∧ 1 ≤ T_min ∧
        ∀ {T T₀ : ℝ} {N : ℕ} {W : Finset ℝ}
            (x y z : GMRow W),
          T_min ≤ T → 0 < N → (N : ℝ) ≤ T →
          T ^ ε ≤ T₀ →
          T₀ ≤ |(x : ℝ) - (y : ℝ)| →
          |(x : ℝ) - (y : ℝ)| ≤ 2 * T₀ →
          |(x : ℝ) - (y : ℝ)| ≤ T →
          ‖gmCubicS2FirstSummand cutoff N x y z‖ ≤
            ((N : ℝ) * C / Real.sqrt T₀ *
                (∫ u in -(gmReflectionHeight T ε)..(gmReflectionHeight T ε),
                  ‖gmReflectionDirichletPoly
                    ((x : ℝ) - (y : ℝ))
                    (gmReflectionLength T ε N
                      ((x : ℝ) - (y : ℝ))) u‖) +
              C / T ^ A) *
            ‖gmTraceNonzeroTailAt cutoff N ((y : ℝ) - (z : ℝ))‖ *
            ‖gmTraceZeroMode cutoff N ((z : ℝ) - (x : ℝ))‖ := by
  intro A ε hA hε
  obtain ⟨C, T_min, hC, hT_min, hTail⟩ :=
    gmScaledQuantitativeSmoothReflection_native cutoff A ε hA hε
  refine ⟨C, T_min, hC, hT_min, ?_⟩
  intro T T₀ N W x y z hT hN hNT hT₀ hLower hDouble hUpper
  have hReflected := hTail hT hN hNT hT₀ hLower hDouble hUpper
  unfold gmCubicS2FirstSummand
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hReflected (norm_nonneg _)) (norm_nonneg _)

end RiemannZeta.GuthMaynard
