import RiemannZeta.GuthMaynard.HughesYoungCentralBounds

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Uniform modulus bounds for the Hughes--Young central series

The contour shift is termwise.  This module supplies the missing uniform
summability in the DFI modulus, retaining the two logarithmic factors from
equation (27).
-/

/-- A reduced equation-(27) logarithmic constant grows at most linearly in
the logarithm of the original positive modulus. -/
theorem norm_dfiEquation27LogConstant_reduced_le
    (a q : ℕ) (hq : 0 < q) :
    ‖dfiEquation27LogConstant a (dfiReducedDenominator a q)‖ ≤
      |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ) := by
  have hred := abs_log_dfiReducedDenominator_le a q hq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
  unfold dfiEquation27LogConstant
  calc
    ‖-Complex.log (a : ℂ) + 2 * Real.eulerMascheroniConstant -
        2 * Complex.log (dfiReducedDenominator a q : ℂ)‖ ≤
      ‖Complex.log (a : ℂ)‖ +
        ‖2 * (Real.eulerMascheroniConstant : ℂ)‖ +
        ‖2 * Complex.log (dfiReducedDenominator a q : ℂ)‖ := by
          calc
            _ ≤ ‖-Complex.log (a : ℂ) +
                2 * (Real.eulerMascheroniConstant : ℂ)‖ +
                ‖2 * Complex.log (dfiReducedDenominator a q : ℂ)‖ :=
              norm_sub_le _ _
            _ ≤ (‖-Complex.log (a : ℂ)‖ +
                ‖2 * (Real.eulerMascheroniConstant : ℂ)‖) +
                ‖2 * Complex.log (dfiReducedDenominator a q : ℂ)‖ := by
              gcongr
              exact norm_add_le _ _
            _ = _ := by rw [norm_neg]
    _ = |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * |Real.log (dfiReducedDenominator a q : ℝ)| := by
      simp only [← Complex.natCast_log, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      norm_num
    _ ≤ |Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
        2 * Real.log (q : ℝ) := by gcongr

/-- The complete affine constants in equation (84) inherit the same
linear-logarithmic modulus bound. -/
theorem norm_log_add_dfiEquation27LogConstant_reduced_le
    (a r q : ℕ) (hq : 0 < q) :
    ‖(Real.log (r : ℝ) : ℂ) +
        dfiEquation27LogConstant a (dfiReducedDenominator a q)‖ ≤
      |Real.log (r : ℝ)| + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (q : ℝ) := by
  calc
    _ ≤ ‖(Real.log (r : ℝ) : ℂ)‖ +
        ‖dfiEquation27LogConstant a (dfiReducedDenominator a q)‖ :=
      norm_add_le _ _
    _ ≤ |Real.log (r : ℝ)| +
        (|Real.log (a : ℝ)| + 2 * |Real.eulerMascheroniConstant| +
          2 * Real.log (q : ℝ)) := by
      have hr : ‖(Real.log (r : ℝ) : ℂ)‖ = |Real.log (r : ℝ)| := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [hr]
      gcongr
      exact norm_dfiEquation27LogConstant_reduced_le a q hq
    _ = _ := by ring

/-- The inverse-square modulus profile remains summable after both DFI
logarithmic factors are absorbed into a quarter power. -/
theorem summable_natCast_inv_sq_mul_log_profile_sq (A : ℝ) (hA : 0 ≤ A) :
    Summable (fun q : ℕ =>
      ((q : ℝ) ^ 2)⁻¹ * (A + 2 * Real.log (q : ℝ)) ^ 2) := by
  have hmajor : Summable (fun q : ℕ =>
      (A + 8) ^ 2 *
        (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ))) :=
    summable_natCast_inv_sq_mul_rpow_half.mul_left ((A + 8) ^ 2)
  apply Summable.of_norm_bounded hmajor
  intro q
  rw [Real.norm_eq_abs]
  by_cases hq0 : q = 0
  · subst q
    simp
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
    have hqQuarter : (1 : ℝ) ≤ (q : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow hqOne (by norm_num)
    have hlog := Real.log_natCast_le_rpow_div q
      (by norm_num : (0 : ℝ) < 1 / 4)
    have hlinear : A + 2 * Real.log (q : ℝ) ≤
        (A + 8) * (q : ℝ) ^ (1 / 4 : ℝ) := by
      have hAq : A ≤ A * (q : ℝ) ^ (1 / 4 : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hqQuarter hA]
      have hlog' : 2 * Real.log (q : ℝ) ≤
          8 * (q : ℝ) ^ (1 / 4 : ℝ) := by
        norm_num at hlog ⊢
        linarith
      nlinarith
    have hhalf :
        (q : ℝ) ^ (1 / 4 : ℝ) * (q : ℝ) ^ (1 / 4 : ℝ) =
          (q : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < q)]
      norm_num
    have hpow : ((q : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
        (q : ℝ) ^ (1 / 2 : ℝ) := by
      rw [pow_two, hhalf]
    rw [abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _))]
    calc
      ((q : ℝ) ^ 2)⁻¹ * (A + 2 * Real.log (q : ℝ)) ^ 2 ≤
          ((q : ℝ) ^ 2)⁻¹ *
            (((A + 8) * (q : ℝ) ^ (1 / 4 : ℝ)) ^ 2) := by gcongr
      _ = (A + 8) ^ 2 *
          (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [mul_pow, hpow]
        ring

set_option maxHeartbeats 1000000 in
/-- At a fixed contour point the regularized beta kernel is uniformly
quadratic in its two affine logarithmic constants.  This makes the
dependence on the DFI modulus explicit instead of burying it in an
existential constant. -/
theorem exists_norm_hughesYoungEquation84RegularizedBetaKernel_le_mul_logProfile
    (t : ℝ) (w : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ CX COne : ℂ,
      ‖hughesYoungEquation84RegularizedBetaKernel t w CX COne‖ ≤
        C * (1 + ‖CX‖ + ‖COne‖) ^ 2 := by
  let z : ℂ := afeCriticalPoint t - w
  let p : ℂ := afeCriticalPoint t + w
  let G : ℂ := Complex.Gamma (2 * w) / Complex.Gamma p
  let D : ℝ := 1 + ‖G‖ + ‖hughesYoungRegularizedGammaDigamma z‖ +
    ‖hughesYoungRegularizedGamma z‖ + ‖Complex.digamma (2 * w)‖ +
    ‖Complex.digamma p‖ + ‖hughesYoungPolygammaSeries 1 (2 * w)‖
  let C : ℝ := D ^ 3 + D ^ 4 + D ^ 3
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [norm_nonneg G, norm_nonneg (hughesYoungRegularizedGammaDigamma z),
      norm_nonneg (hughesYoungRegularizedGamma z),
      norm_nonneg (Complex.digamma (2 * w)), norm_nonneg (Complex.digamma p),
      norm_nonneg (hughesYoungPolygammaSeries 1 (2 * w))]
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro CX COne
  let S : ℝ := 1 + ‖CX‖ + ‖COne‖
  let U : ℂ := -Complex.digamma (2 * w) + CX
  let V : ℂ := Complex.digamma p - Complex.digamma (2 * w) + COne
  have hS : 1 ≤ S := by
    dsimp [S]
    linarith [norm_nonneg CX, norm_nonneg COne]
  have hG : ‖G‖ ≤ D := by
    dsimp [D]
    linarith [norm_nonneg (hughesYoungRegularizedGammaDigamma z),
      norm_nonneg (hughesYoungRegularizedGamma z),
      norm_nonneg (Complex.digamma (2 * w)), norm_nonneg (Complex.digamma p),
      norm_nonneg (hughesYoungPolygammaSeries 1 (2 * w))]
  have hRD : ‖hughesYoungRegularizedGammaDigamma z‖ ≤ D := by
    dsimp [D]
    linarith [norm_nonneg G, norm_nonneg (hughesYoungRegularizedGamma z),
      norm_nonneg (Complex.digamma (2 * w)), norm_nonneg (Complex.digamma p),
      norm_nonneg (hughesYoungPolygammaSeries 1 (2 * w))]
  have hR : ‖hughesYoungRegularizedGamma z‖ ≤ D := by
    dsimp [D]
    linarith [norm_nonneg G, norm_nonneg (hughesYoungRegularizedGammaDigamma z),
      norm_nonneg (Complex.digamma (2 * w)), norm_nonneg (Complex.digamma p),
      norm_nonneg (hughesYoungPolygammaSeries 1 (2 * w))]
  have hP : ‖hughesYoungPolygammaSeries 1 (2 * w)‖ ≤ D := by
    dsimp [D]
    linarith [norm_nonneg G, norm_nonneg (hughesYoungRegularizedGammaDigamma z),
      norm_nonneg (hughesYoungRegularizedGamma z),
      norm_nonneg (Complex.digamma (2 * w)), norm_nonneg (Complex.digamma p)]
  have hU : ‖U‖ ≤ D * S := by
    calc
      ‖U‖ ≤ ‖Complex.digamma (2 * w)‖ + ‖CX‖ := by
        simpa only [U, norm_neg] using
          norm_add_le (-Complex.digamma (2 * w)) CX
      _ ≤ D * S := by
        dsimp [D, S]
        nlinarith [norm_nonneg G, norm_nonneg (hughesYoungRegularizedGammaDigamma z),
          norm_nonneg (hughesYoungRegularizedGamma z),
          norm_nonneg (Complex.digamma (2 * w)), norm_nonneg (Complex.digamma p),
          norm_nonneg (hughesYoungPolygammaSeries 1 (2 * w)),
          norm_nonneg CX, norm_nonneg COne]
  have hV : ‖V‖ ≤ D * S := by
    calc
      ‖V‖ ≤ ‖Complex.digamma p‖ + ‖Complex.digamma (2 * w)‖ +
          ‖COne‖ := by
        calc
          _ ≤ ‖Complex.digamma p - Complex.digamma (2 * w)‖ + ‖COne‖ :=
            norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_sub_le _ _
      _ ≤ D * S := by
        dsimp [D, S]
        nlinarith [norm_nonneg G, norm_nonneg (hughesYoungRegularizedGammaDigamma z),
          norm_nonneg (hughesYoungRegularizedGamma z),
          norm_nonneg (Complex.digamma (2 * w)), norm_nonneg (Complex.digamma p),
          norm_nonneg (hughesYoungPolygammaSeries 1 (2 * w)),
          norm_nonneg CX, norm_nonneg COne]
  change ‖G * (hughesYoungRegularizedGammaDigamma z * V +
      hughesYoungRegularizedGamma z *
        (U * V + hughesYoungPolygammaSeries 1 (2 * w)))‖ ≤ C * S ^ 2
  simp only [norm_mul]
  calc
    ‖G‖ * ‖hughesYoungRegularizedGammaDigamma z * V +
        hughesYoungRegularizedGamma z *
          (U * V + hughesYoungPolygammaSeries 1 (2 * w))‖ ≤
      ‖G‖ * (‖hughesYoungRegularizedGammaDigamma z‖ * ‖V‖ +
        ‖hughesYoungRegularizedGamma z‖ * (‖U‖ * ‖V‖ +
          ‖hughesYoungPolygammaSeries 1 (2 * w)‖)) := by
      gcongr
      calc
        _ ≤ ‖hughesYoungRegularizedGammaDigamma z * V‖ +
            ‖hughesYoungRegularizedGamma z *
              (U * V + hughesYoungPolygammaSeries 1 (2 * w))‖ := norm_add_le _ _
        _ ≤ _ := by
          simp only [norm_mul]
          gcongr
          calc
            ‖U * V + hughesYoungPolygammaSeries 1 (2 * w)‖ ≤
                ‖U * V‖ + ‖hughesYoungPolygammaSeries 1 (2 * w)‖ := norm_add_le _ _
            _ = _ := by rw [norm_mul]
    _ ≤ D * (D * (D * S) + D * ((D * S) * (D * S) + D)) := by
      gcongr
    _ ≤ C * S ^ 2 := by
      have hS2 : 1 ≤ S ^ 2 := by nlinarith [sq_nonneg S]
      have hDS : 0 ≤ D := zero_le_one.trans hD
      have hSS : 0 ≤ S := zero_le_one.trans hS
      dsimp [C]
      ring_nf
      nlinarith [mul_le_mul_of_nonneg_left hS hDS,
        mul_le_mul_of_nonneg_left hS2 (pow_nonneg hDS 3)]

/-- The complete pole-cancelled contour kernel has the same explicit
quadratic dependence on the two DFI logarithmic constants at each fixed
contour point. -/
theorem exists_norm_hughesYoungEquation84RegularizedContourKernel_le_mul_logProfile
    (t : ℝ) (w : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ CX COne : ℂ,
      ‖hughesYoungEquation84RegularizedContourKernel t w CX COne‖ ≤
        C * (1 + ‖CX‖ + ‖COne‖) ^ 2 := by
  obtain ⟨B, hB, hBeta⟩ :=
    exists_norm_hughesYoungEquation84RegularizedBetaKernel_le_mul_logProfile t w
  let p : ℂ := afeCriticalPoint t + w
  let q : ℂ := afeCriticalPoint (-t) + w
  let A : ℂ := Complex.exp (100 * w ^ 2) * (p * (1 - p)) ^ 2 * q ^ 2 *
    Complex.Gammaℝ p ^ 2 * Complex.Gammaℝ q ^ 2 /
    afePoleNormalization t / w / afeGammaNormalization t
  let C : ℝ := max 1 ‖A‖ * B
  have hmax : 0 < max 1 ‖A‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C, mul_pos hmax hB, ?_⟩
  intro CX COne
  have hA : ‖A‖ ≤ max 1 ‖A‖ := le_max_right _ _
  unfold hughesYoungEquation84RegularizedContourKernel
  dsimp only [A, p, q, C]
  rw [norm_mul]
  calc
    _ ≤ ‖A‖ * (B * (1 + ‖CX‖ + ‖COne‖) ^ 2) := by
      gcongr
      exact hBeta CX COne
    _ ≤ max 1 ‖A‖ *
        (B * (1 + ‖CX‖ + ‖COne‖) ^ 2) :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

/-- The inverse-square profile is still summable with the four logarithms
coming from the two affine constants in equation (84). -/
theorem summable_natCast_inv_sq_mul_four_log_profile_sq
    (A : ℝ) (hA : 0 ≤ A) :
    Summable (fun q : ℕ =>
      ((q : ℝ) ^ 2)⁻¹ * (A + 4 * Real.log (q : ℝ)) ^ 2) := by
  have hhalf : 0 ≤ A / 2 := by positivity
  have h := (summable_natCast_inv_sq_mul_log_profile_sq (A / 2) hhalf).mul_left 4
  simpa only [mul_assoc] using h.congr (fun q => by ring)

set_option maxHeartbeats 1000000 in
/-- Absolute convergence of the complete positive equation-(84) modulus
series at every fixed contour point.  The proof exposes the inverse-square
DFI coefficient and absorbs both logarithmic factors. -/
theorem summable_hughesYoungEquation84PositiveContourTerm
    (T t : ℝ) (h k a b r : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (w : ℂ) :
    Summable (fun q : ℕ =>
      hughesYoungEquation84PositiveContourTerm T t h k a b r q w) := by
  obtain ⟨C, hC, hKernel⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_le_mul_logProfile
      t w
  let A₀ : ℝ := 1 + 2 * |Real.log (r : ℝ)| + |Real.log (a : ℝ)| +
    |Real.log (b : ℝ)| + 4 * |Real.eulerMascheroniConstant|
  let K : ℝ := ‖((a : ℂ) * b)⁻¹‖ *
    ((a * b * r ^ 2 : ℕ) : ℝ) *
    ‖hughesYoungReducedMellinStaticComplex T t h k w *
      hughesYoungCentralShiftPower r w‖ * C
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    positivity
  have hmajor : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A₀ + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A₀ hA₀).mul_left K
  apply Summable.of_norm_bounded hmajor
  intro q
  by_cases hq₀ : q = 0
  · subst q
    simp [hughesYoungEquation84PositiveContourTerm,
      dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq₀
    letI : NeZero q := ⟨hq₀⟩
    let CX : ℂ := (Real.log r : ℂ) +
      dfiEquation27LogConstant b (dfiReducedDenominator b q)
    let COne : ℂ := (Real.log r : ℂ) +
      dfiEquation27LogConstant a (dfiReducedDenominator a q)
    have hCX : ‖CX‖ ≤ |Real.log (r : ℝ)| + |Real.log (b : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (q : ℝ) := by
      simpa only [CX] using
        norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
    have hCOne : ‖COne‖ ≤ |Real.log (r : ℝ)| + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (q : ℝ) := by
      simpa only [COne] using
        norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
    have hProfile : 1 + ‖CX‖ + ‖COne‖ ≤
        A₀ + 4 * Real.log (q : ℝ) := by
      dsimp [A₀]
      linarith
    have hProfile₀ : 0 ≤ A₀ + 4 * Real.log (q : ℝ) := by
      have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have := Real.log_nonneg hqOne
      positivity
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    have hKer := hKernel CX COne
    unfold hughesYoungEquation84PositiveContourTerm
    simp only [norm_mul]
    change ‖((a : ℂ) * b)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient a b r q‖ *
        (‖hughesYoungReducedMellinStaticComplex T t h k w‖ *
          ‖hughesYoungCentralShiftPower r w‖ *
          ‖hughesYoungEquation84RegularizedContourKernel t w CX COne‖) ≤
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A₀ + 4 * Real.log (q : ℝ)) ^ 2)
    calc
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((‖hughesYoungReducedMellinStaticComplex T t h k w‖ *
            ‖hughesYoungCentralShiftPower r w‖) *
            (C * (1 + ‖CX‖ + ‖COne‖) ^ 2)) := by
        gcongr
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          (((a * b * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((‖hughesYoungReducedMellinStaticComplex T t h k w‖ *
            ‖hughesYoungCentralShiftPower r w‖) *
            (C * (A₀ + 4 * Real.log (q : ℝ)) ^ 2)) := by
        gcongr
      _ = K * (((q : ℝ) ^ 2)⁻¹ *
          (A₀ + 4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp [K]
        rw [← norm_mul]
        ring

set_option maxHeartbeats 1000000 in
/-- Absolute convergence of the coordinate-swapped negative equation-(84)
modulus series at every fixed contour point. -/
theorem summable_hughesYoungEquation84NegativeContourTerm
    (T t : ℝ) (h k a b r : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (w : ℂ) :
    Summable (fun q : ℕ =>
      hughesYoungEquation84NegativeContourTerm T t h k a b r q w) := by
  obtain ⟨C, hC, hKernel⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_le_mul_logProfile
      (-t) w
  let A₀ : ℝ := 1 + 2 * |Real.log (r : ℝ)| + |Real.log (a : ℝ)| +
    |Real.log (b : ℝ)| + 4 * |Real.eulerMascheroniConstant|
  let K : ℝ := ‖((b : ℂ) * a)⁻¹‖ *
    ((b * a * r ^ 2 : ℕ) : ℝ) *
    ‖hughesYoungReducedMellinStaticComplex T t h k w *
      hughesYoungCentralShiftPower r w‖ * C
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀]
    positivity
  have hmajor : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A₀ + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A₀ hA₀).mul_left K
  apply Summable.of_norm_bounded hmajor
  intro q
  by_cases hq₀ : q = 0
  · subst q
    simp [hughesYoungEquation84NegativeContourTerm,
      dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq₀
    letI : NeZero q := ⟨hq₀⟩
    let CX : ℂ := (Real.log r : ℂ) +
      dfiEquation27LogConstant a (dfiReducedDenominator a q)
    let COne : ℂ := (Real.log r : ℂ) +
      dfiEquation27LogConstant b (dfiReducedDenominator b q)
    have hCX : ‖CX‖ ≤ |Real.log (r : ℝ)| + |Real.log (a : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (q : ℝ) := by
      simpa only [CX] using
        norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
    have hCOne : ‖COne‖ ≤ |Real.log (r : ℝ)| + |Real.log (b : ℝ)| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (q : ℝ) := by
      simpa only [COne] using
        norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
    have hProfile : 1 + ‖CX‖ + ‖COne‖ ≤
        A₀ + 4 * Real.log (q : ℝ) := by
      dsimp [A₀]
      linarith
    have hProfile₀ : 0 ≤ A₀ + 4 * Real.log (q : ℝ) := by
      have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have := Real.log_nonneg hqOne
      positivity
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq b a r q hb ha hr
    have hKer := hKernel CX COne
    unfold hughesYoungEquation84NegativeContourTerm
    simp only [norm_mul]
    change ‖((b : ℂ) * a)⁻¹‖ *
        ‖dfiEquation27ArithmeticCoefficient b a r q‖ *
        (‖hughesYoungReducedMellinStaticComplex T t h k w‖ *
          ‖hughesYoungCentralShiftPower r w‖ *
          ‖hughesYoungEquation84RegularizedContourKernel (-t) w CX COne‖) ≤
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A₀ + 4 * Real.log (q : ℝ)) ^ 2)
    calc
      _ ≤ ‖((b : ℂ) * a)⁻¹‖ *
          (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((‖hughesYoungReducedMellinStaticComplex T t h k w‖ *
            ‖hughesYoungCentralShiftPower r w‖) *
            (C * (1 + ‖CX‖ + ‖COne‖) ^ 2)) := by
        gcongr
      _ ≤ ‖((b : ℂ) * a)⁻¹‖ *
          (((b * a * r ^ 2 : ℕ) : ℝ) * ((q : ℝ) ^ 2)⁻¹) *
          ((‖hughesYoungReducedMellinStaticComplex T t h k w‖ *
            ‖hughesYoungCentralShiftPower r w‖) *
            (C * (A₀ + 4 * Real.log (q : ℝ)) ^ 2)) := by
        gcongr
      _ = K * (((q : ℝ) ^ 2)⁻¹ *
          (A₀ + 4 * Real.log (q : ℝ)) ^ 2) := by
        dsimp [K]
        rw [← norm_mul]
        ring

/-- A reusable arithmetic summability principle for the four coefficients
created when the bilinear regularized beta kernel is expanded. -/
theorem summable_dfiEquation27ArithmeticCoefficient_mul_two_logProfiles
    (a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (X Y : ℕ → ℂ) (A : ℝ) (hA : 1 ≤ A)
    (hX : ∀ q, 0 < q → ‖X q‖ ≤ A + 4 * Real.log (q : ℝ))
    (hY : ∀ q, 0 < q → ‖Y q‖ ≤ A + 4 * Real.log (q : ℝ)) :
    Summable (fun q : ℕ =>
      dfiEquation27ArithmeticCoefficient a b r q * X q * Y q) := by
  let K : ℝ := ((a * b * r ^ 2 : ℕ) : ℝ)
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  have hmajor : Summable (fun q : ℕ =>
      K * (((q : ℝ) ^ 2)⁻¹ *
        (A + 4 * Real.log (q : ℝ)) ^ 2)) :=
    (summable_natCast_inv_sq_mul_four_log_profile_sq A hA₀).mul_left K
  apply Summable.of_norm_bounded hmajor
  intro q
  by_cases hq₀ : q = 0
  · subst q
    simp [dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq₀
    letI : NeZero q := ⟨hq₀⟩
    have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
    have hP₀ : 0 ≤ A + 4 * Real.log (q : ℝ) := by positivity
    have hCoeff :=
      norm_dfiEquation27ArithmeticCoefficient_le_inv_sq a b r q ha hb hr
    simp only [norm_mul]
    calc
      ‖dfiEquation27ArithmeticCoefficient a b r q‖ * ‖X q‖ * ‖Y q‖ ≤
          (K * ((q : ℝ) ^ 2)⁻¹) *
            (A + 4 * Real.log (q : ℝ)) *
            (A + 4 * Real.log (q : ℝ)) := by
        gcongr
        · exact hX q hq
        · exact hY q hq
      _ = K * (((q : ℝ) ^ 2)⁻¹ *
          (A + 4 * Real.log (q : ℝ)) ^ 2) := by ring

end RiemannZeta.GuthMaynard
