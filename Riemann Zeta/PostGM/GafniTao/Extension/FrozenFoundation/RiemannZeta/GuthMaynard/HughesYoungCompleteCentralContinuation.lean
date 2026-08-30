import RiemannZeta.GuthMaynard.HughesYoungEquation96Continuation
import RiemannZeta.GuthMaynard.HughesYoungEquation84SourceLine

open Complex Filter MeasureTheory Set
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Complete Hughes--Young central continuation

This is the first object in the DFI consumer at which the positive shift and
modulus sums have already been combined.  Its four arithmetic coefficients
are the equation-(98) continuations of the two DFI logarithmic jets.  Thus
subsequent contour estimates preserve the cancellations that are destroyed
by taking norms of individual shifts.
-/

/-- Equation-(96)'s Mellin variable corresponding to the equation-(84)
contour variable. -/
noncomputable def hughesYoungEquation96ContourParameter (W : ℂ) : ℂ :=
  2 * (W - 1)

/-- Complete positive signed-central integrand after the `(q,r)` series has
been analytically combined by equation (98). -/
noncomputable def hughesYoungCompletePositiveCentralContinuation
    (T t : ℝ) (h k a b : ℕ) (W : ℂ) : ℂ :=
  (((a : ℂ) * b)⁻¹) *
    hughesYoungReducedMellinStaticComplex T t h k W *
      (hughesYoungEquation96ContinuationCoefficient a b
          (hughesYoungEquation96ContourParameter W) false false *
            hughesYoungEquation84Kernel00 t W +
        hughesYoungEquation96ContinuationCoefficient a b
          (hughesYoungEquation96ContourParameter W) true false *
            hughesYoungEquation84Kernel10 t W +
        hughesYoungEquation96ContinuationCoefficient a b
          (hughesYoungEquation96ContourParameter W) false true *
            hughesYoungEquation84Kernel01 t W +
        hughesYoungEquation96ContinuationCoefficient a b
          (hughesYoungEquation96ContourParameter W) true true *
            hughesYoungEquation84Kernel11 t W)

/-- Coordinate-swapped negative signed-central continuation. -/
noncomputable def hughesYoungCompleteNegativeCentralContinuation
    (T t : ℝ) (h k a b : ℕ) (W : ℂ) : ℂ :=
  (((b : ℂ) * a)⁻¹) *
    hughesYoungReducedMellinStaticComplex T t h k W *
      (hughesYoungEquation96ContinuationCoefficient b a
          (hughesYoungEquation96ContourParameter W) false false *
            hughesYoungEquation84Kernel00 (-t) W +
        hughesYoungEquation96ContinuationCoefficient b a
          (hughesYoungEquation96ContourParameter W) true false *
            hughesYoungEquation84Kernel10 (-t) W +
        hughesYoungEquation96ContinuationCoefficient b a
          (hughesYoungEquation96ContourParameter W) false true *
            hughesYoungEquation84Kernel01 (-t) W +
        hughesYoungEquation96ContinuationCoefficient b a
          (hughesYoungEquation96ContourParameter W) true true *
            hughesYoungEquation84Kernel11 (-t) W)

theorem hughesYoungReducedMellinStaticComplex_swap
    (T t : ℝ) (h k : ℕ) (W : ℂ) :
    hughesYoungReducedMellinStaticComplex T (-t) k h W =
      hughesYoungReducedMellinStaticComplex T t h k W := by
  unfold hughesYoungReducedMellinStaticComplex hughesYoungReducedLeft
    hughesYoungReducedRight hughesYoungCommonDivisor
  simp only [neg_neg, Nat.gcd_comm h k]
  ring

theorem hughesYoungCompleteNegativeCentralContinuation_eq_swap
    (T t : ℝ) (h k a b : ℕ) (W : ℂ) :
    hughesYoungCompleteNegativeCentralContinuation T t h k a b W =
      hughesYoungCompletePositiveCentralContinuation T (-t) k h b a W := by
  unfold hughesYoungCompleteNegativeCentralContinuation
    hughesYoungCompletePositiveCentralContinuation
  rw [hughesYoungReducedMellinStaticComplex_swap]

private theorem contourParameter_sourceLine (u : ℝ) :
    hughesYoungEquation96ContourParameter
        ((1 : ℂ) + (u : ℂ) * I) =
      (2 * u : ℂ) * I := by
  unfold hughesYoungEquation96ContourParameter
  ring

/-- Exact identification with the absolutely convergent complete positive
source series. -/
theorem hughesYoungEquation84CompletePositiveSourceLine_eq_continuation
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (u : ℝ)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    hughesYoungEquation84CompletePositiveSourceLine T t h k a b u =
      hughesYoungCompletePositiveCentralContinuation T t h k a b
        ((1 : ℂ) + (u : ℂ) * I) := by
  rw [hughesYoungEquation84CompletePositiveSourceLine_eq_fourMoments
    T t h k ha hb hab u hη hη4]
  rw [hughesYoungEquation84CompletePositiveMomentAt_eq_jetCoefficient
      false false u ha hb hab,
    hughesYoungEquation84CompletePositiveMomentAt_eq_jetCoefficient
      true false u ha hb hab,
    hughesYoungEquation84CompletePositiveMomentAt_eq_jetCoefficient
      false true u ha hb hab,
    hughesYoungEquation84CompletePositiveMomentAt_eq_jetCoefficient
      true true u ha hb hab]
  rw [hughesYoungEquation96JetCoefficient_eq_continuationCoefficient
      false false ha hb hab (by simp),
    hughesYoungEquation96JetCoefficient_eq_continuationCoefficient
      true false ha hb hab (by simp),
    hughesYoungEquation96JetCoefficient_eq_continuationCoefficient
      false true ha hb hab (by simp),
    hughesYoungEquation96JetCoefficient_eq_continuationCoefficient
      true true ha hb hab (by simp)]
  unfold hughesYoungCompletePositiveCentralContinuation
    hughesYoungEquation84CompletePositiveOuter
  rw [contourParameter_sourceLine]

/-- Exact identification with the complete negative source series. -/
theorem hughesYoungEquation84CompleteNegativeSourceLine_eq_continuation
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) (u : ℝ)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    hughesYoungEquation84CompleteNegativeSourceLine T t h k a b u =
      hughesYoungCompleteNegativeCentralContinuation T t h k a b
        ((1 : ℂ) + (u : ℂ) * I) := by
  rw [hughesYoungEquation84CompleteNegativeSourceLine_eq_fourMoments
    T t h k ha hb hab u hη hη4]
  rw [hughesYoungEquation84CompletePositiveMomentAt_eq_jetCoefficient
      false false u hb ha hab.symm,
    hughesYoungEquation84CompletePositiveMomentAt_eq_jetCoefficient
      true false u hb ha hab.symm,
    hughesYoungEquation84CompletePositiveMomentAt_eq_jetCoefficient
      false true u hb ha hab.symm,
    hughesYoungEquation84CompletePositiveMomentAt_eq_jetCoefficient
      true true u hb ha hab.symm]
  rw [hughesYoungEquation96JetCoefficient_eq_continuationCoefficient
      false false hb ha hab.symm (by simp),
    hughesYoungEquation96JetCoefficient_eq_continuationCoefficient
      true false hb ha hab.symm (by simp),
    hughesYoungEquation96JetCoefficient_eq_continuationCoefficient
      false true hb ha hab.symm (by simp),
    hughesYoungEquation96JetCoefficient_eq_continuationCoefficient
      true true hb ha hab.symm (by simp)]
  unfold hughesYoungCompleteNegativeCentralContinuation
    hughesYoungEquation84CompleteNegativeOuter
  rw [contourParameter_sourceLine]

private theorem contourParameter_re
    (W : ℂ) : (hughesYoungEquation96ContourParameter W).re =
      2 * (W.re - 1) := by
  unfold hughesYoungEquation96ContourParameter
  norm_num [Complex.mul_re]

/-- Holomorphy of the complete positive central continuation on the strip
strictly to the right of `Re W = 7/8`.  This is the combined-series
holomorphy required to move the contour without interchanging a merely
conditionally convergent modulus sum. -/
theorem differentiableAt_hughesYoungCompletePositiveCentralContinuation
    (T t : ℝ) (h k a b : ℕ) {W : ℂ}
    (hWlower : (7 / 8 : ℝ) < W.re) (hWupper : W.re < 3 / 2) :
    DifferentiableAt ℂ
      (hughesYoungCompletePositiveCentralContinuation T t h k a b) W := by
  have hq : -(1 / 4 : ℝ) <
      (hughesYoungEquation96ContourParameter W).re := by
    rw [contourParameter_re]
    linarith
  have hqDiff : DifferentiableAt ℂ hughesYoungEquation96ContourParameter W := by
    unfold hughesYoungEquation96ContourParameter
    fun_prop
  have hcoeff (i j : Bool) : DifferentiableAt ℂ
      (fun z => hughesYoungEquation96ContinuationCoefficient a b
        (hughesYoungEquation96ContourParameter z) i j) W :=
    (analyticAt_hughesYoungEquation96ContinuationCoefficient a b i j hq).differentiableAt.comp
      W hqDiff
  have hkernel00 := differentiableAt_hughesYoungEquation84Kernel00
    t (by linarith) hWupper
  have hkernel10 := differentiableAt_hughesYoungEquation84Kernel10
    t (by linarith) hWupper
  have hkernel01 := differentiableAt_hughesYoungEquation84Kernel01
    t (by linarith) hWupper
  have hkernel11 := differentiableAt_hughesYoungEquation84Kernel11
    t (by linarith) hWupper
  unfold hughesYoungCompletePositiveCentralContinuation
  simpa only [mul_assoc] using
    (differentiableAt_const (c := (((a : ℂ) * b)⁻¹)).mul
    ((differentiableAt_hughesYoungReducedMellinStaticComplex T t h k W).mul
      (((((hcoeff false false).mul hkernel00).add
        ((hcoeff true false).mul hkernel10)).add
        ((hcoeff false true).mul hkernel01)).add
        ((hcoeff true true).mul hkernel11))))

/-- Holomorphy of the coordinate-swapped negative continuation on the same
strip. -/
theorem differentiableAt_hughesYoungCompleteNegativeCentralContinuation
    (T t : ℝ) (h k a b : ℕ) {W : ℂ}
    (hWlower : (7 / 8 : ℝ) < W.re) (hWupper : W.re < 3 / 2) :
    DifferentiableAt ℂ
      (hughesYoungCompleteNegativeCentralContinuation T t h k a b) W := by
  have hq : -(1 / 4 : ℝ) <
      (hughesYoungEquation96ContourParameter W).re := by
    rw [contourParameter_re]
    linarith
  have hqDiff : DifferentiableAt ℂ hughesYoungEquation96ContourParameter W := by
    unfold hughesYoungEquation96ContourParameter
    fun_prop
  have hcoeff (i j : Bool) : DifferentiableAt ℂ
      (fun z => hughesYoungEquation96ContinuationCoefficient b a
        (hughesYoungEquation96ContourParameter z) i j) W :=
    (analyticAt_hughesYoungEquation96ContinuationCoefficient b a i j hq).differentiableAt.comp
      W hqDiff
  have hkernel00 := differentiableAt_hughesYoungEquation84Kernel00
    (-t) (by linarith) hWupper
  have hkernel10 := differentiableAt_hughesYoungEquation84Kernel10
    (-t) (by linarith) hWupper
  have hkernel01 := differentiableAt_hughesYoungEquation84Kernel01
    (-t) (by linarith) hWupper
  have hkernel11 := differentiableAt_hughesYoungEquation84Kernel11
    (-t) (by linarith) hWupper
  unfold hughesYoungCompleteNegativeCentralContinuation
  simpa only [mul_assoc] using
    (differentiableAt_const (c := (((b : ℂ) * a)⁻¹)).mul
    ((differentiableAt_hughesYoungReducedMellinStaticComplex T t h k W).mul
      (((((hcoeff false false).mul hkernel00).add
        ((hcoeff true false).mul hkernel10)).add
        ((hcoeff false true).mul hkernel01)).add
        ((hcoeff true true).mul hkernel11))))

set_option maxHeartbeats 2000000 in
/-- Uniform Gaussian horizontal control of the complete positive
continuation on the pole-free rectangle `15/16 ≤ Re W ≤ 1`.  The
The constant may depend on the fixed arithmetic data, while the height
dependence is explicit. -/
theorem exists_norm_hughesYoungCompletePositiveCentralContinuation_horizontal_le
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ), 1 ≤ |y| → |t| + 1 ≤ |y| →
      ∀ x ∈ Set.Icc (15 / 16 : ℝ) 1,
        ‖hughesYoungCompletePositiveCentralContinuation T t h k a b
            ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 - 60 * y ^ 2) *
            (2 + |t| + 1 + |y|) ^ 17 := by
  obtain ⟨K, hK, hOuter⟩ := exists_uniform_norm_hughesYoungCentralOuterFactor
    T t h k 1 (((a : ℂ) * b)⁻¹)
      (c₀ := (15 / 16 : ℝ)) (c₁ := (1 : ℝ))
  obtain ⟨B, hB, hKernels⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_horizontal_le
      t (by norm_num : (0 : ℝ) < 15 / 16)
        (by norm_num : (1 : ℝ) < 3 / 2) (by norm_num)
  obtain ⟨D, hD, hCoefficients⟩ :=
    exists_uniform_norm_hughesYoungEquation96ContinuationCoefficient_le
      (by norm_num : (0 : ℝ) < 1)
  let M : ℝ := D * (a : ℝ) * (b : ℝ)
  let C : ℝ := K * (4 * M) * B
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨C, mul_pos (mul_pos hK (mul_pos (by norm_num) hM)) hB, ?_⟩
  intro y hy hty x hx
  have hq : -(1 / 4 : ℝ) ≤
      (hughesYoungEquation96ContourParameter
        ((x : ℂ) + (y : ℂ) * I)).re := by
    rw [contourParameter_re]
    norm_num
    linarith [hx.1]
  have hc (i j : Bool) :
      ‖hughesYoungEquation96ContinuationCoefficient a b
          (hughesYoungEquation96ContourParameter
            ((x : ℂ) + (y : ℂ) * I)) i j‖ ≤ M := by
    have hraw := hCoefficients i j ha hb hq
    simpa only [Real.rpow_one, M, mul_assoc] using hraw
  have ho :
      ‖((a : ℂ) * b)⁻¹ *
          hughesYoungReducedMellinStaticComplex T t h k
            ((x : ℂ) + (y : ℂ) * I)‖ ≤ K := by
    have hraw := hOuter y x hx
    simpa [hughesYoungCentralShiftPower] using hraw
  rcases hKernels y hy hty x hx with ⟨hk₀₀, hk₁₀, hk₀₁, hk₁₁⟩
  let E : ℝ := Real.exp (100 - 60 * y ^ 2)
  let R : ℝ := (2 + |t| + 1 + |y|) ^ 17
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hk₀₀' : ‖hughesYoungEquation84Kernel00 t
      ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * E * R := by
    simpa only [E, R, one_pow, mul_one] using hk₀₀
  have hk₁₀' : ‖hughesYoungEquation84Kernel10 t
      ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * E * R := by
    simpa only [E, R, one_pow, mul_one] using hk₁₀
  have hk₀₁' : ‖hughesYoungEquation84Kernel01 t
      ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * E * R := by
    simpa only [E, R, one_pow, mul_one] using hk₀₁
  have hk₁₁' : ‖hughesYoungEquation84Kernel11 t
      ((x : ℂ) + (y : ℂ) * I)‖ ≤ B * E * R := by
    simpa only [E, R, one_pow, mul_one] using hk₁₁
  let q := hughesYoungEquation96ContourParameter
    ((x : ℂ) + (y : ℂ) * I)
  have hinside :
      ‖hughesYoungEquation96ContinuationCoefficient a b q false false *
              hughesYoungEquation84Kernel00 t ((x : ℂ) + (y : ℂ) * I) +
            hughesYoungEquation96ContinuationCoefficient a b q true false *
              hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I) +
          hughesYoungEquation96ContinuationCoefficient a b q false true *
              hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I) +
        hughesYoungEquation96ContinuationCoefficient a b q true true *
              hughesYoungEquation84Kernel11 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
        4 * M * (B * E * R) := by
    calc
      _ ≤ ‖hughesYoungEquation96ContinuationCoefficient a b q false false‖ *
              ‖hughesYoungEquation84Kernel00 t ((x : ℂ) + (y : ℂ) * I)‖ +
            ‖hughesYoungEquation96ContinuationCoefficient a b q true false‖ *
              ‖hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I)‖ +
          ‖hughesYoungEquation96ContinuationCoefficient a b q false true‖ *
              ‖hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I)‖ +
        ‖hughesYoungEquation96ContinuationCoefficient a b q true true‖ *
              ‖hughesYoungEquation84Kernel11 t ((x : ℂ) + (y : ℂ) * I)‖ := by
          calc
            _ ≤ ‖_ + _ + _‖ + ‖_‖ := norm_add_le _ _
            _ ≤ (‖_ + _‖ + ‖_‖) + ‖_‖ := by gcongr; exact norm_add_le _ _
            _ ≤ ((‖_‖ + ‖_‖) + ‖_‖) + ‖_‖ := by gcongr; exact norm_add_le _ _
            _ = _ := by simp only [norm_mul]
      _ ≤ M * (B * E * R) + M * (B * E * R) +
          M * (B * E * R) + M * (B * E * R) := by
        dsimp only [q]
        gcongr
        · exact hc false false
        · exact hc true false
        · exact hc false true
        · exact hc true true
      _ = 4 * M * (B * E * R) := by ring
  unfold hughesYoungCompletePositiveCentralContinuation
  rw [norm_mul]
  calc
    _ ≤ K * (4 * M * (B * E * R)) :=
      mul_le_mul ho hinside (norm_nonneg _) hK.le
    _ = C * Real.exp (100 - 60 * y ^ 2) *
        (2 + |t| + 1 + |y|) ^ 17 := by
      dsimp [C, E, R]
      ring

theorem exists_norm_hughesYoungCompleteNegativeCentralContinuation_horizontal_le
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ), 1 ≤ |y| → |t| + 1 ≤ |y| →
      ∀ x ∈ Set.Icc (15 / 16 : ℝ) 1,
        ‖hughesYoungCompleteNegativeCentralContinuation T t h k a b
            ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 - 60 * y ^ 2) *
            (2 + |t| + 1 + |y|) ^ 17 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_hughesYoungCompletePositiveCentralContinuation_horizontal_le
      T (-t) k h hb ha
  refine ⟨C, hC, ?_⟩
  intro y hy hty x hx
  rw [hughesYoungCompleteNegativeCentralContinuation_eq_swap]
  simpa only [abs_neg] using hbound y hy (by simpa only [abs_neg] using hty) x hx

private theorem completePositive_horizontal_bound_for_shift
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ),
      1 ≤ |y| → |t| + 1 ≤ |y| → ∀ x ∈ Set.Icc (15 / 16 : ℝ) 1,
        ‖hughesYoungCompletePositiveCentralContinuation T t h k a b
            ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 * (1 : ℝ) ^ 2 - 60 * y ^ 2) *
            (2 + |t| + 1 + |y|) ^ 17 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_hughesYoungCompletePositiveCentralContinuation_horizontal_le
      T t h k ha hb
  refine ⟨C, hC, ?_⟩
  intro y hy hty x hx
  have h := hbound y hy hty x hx
  simpa only [one_pow, mul_one] using h

private theorem completeNegative_horizontal_bound_for_shift
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ),
      1 ≤ |y| → |t| + 1 ≤ |y| → ∀ x ∈ Set.Icc (15 / 16 : ℝ) 1,
        ‖hughesYoungCompleteNegativeCentralContinuation T t h k a b
            ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 * (1 : ℝ) ^ 2 - 60 * y ^ 2) *
            (2 + |t| + 1 + |y|) ^ 17 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_hughesYoungCompleteNegativeCentralContinuation_horizontal_le
      T t h k ha hb
  refine ⟨C, hC, ?_⟩
  intro y hy hty x hx
  have h := hbound y hy hty x hx
  simpa only [one_pow, mul_one] using h

theorem hughesYoungCompletePositiveCentralContinuation_boundaryRect_zero
    (T t : ℝ) (h k a b : ℕ) (H : ℝ) :
    (∫ x : ℝ in (15 / 16)..1,
        hughesYoungCompletePositiveCentralContinuation T t h k a b
          ((x : ℂ) + (-H : ℂ) * I)) -
      (∫ x : ℝ in (15 / 16)..1,
        hughesYoungCompletePositiveCentralContinuation T t h k a b
          ((x : ℂ) + (H : ℂ) * I)) +
      I • (∫ y : ℝ in -H..H,
        hughesYoungCompletePositiveCentralContinuation T t h k a b
          ((1 : ℂ) + (y : ℂ) * I)) -
      I • (∫ y : ℝ in -H..H,
        hughesYoungCompletePositiveCentralContinuation T t h k a b
          ((15 / 16 : ℂ) + (y : ℂ) * I)) = 0 := by
  have hrect : DifferentiableOn ℂ
      (hughesYoungCompletePositiveCentralContinuation T t h k a b)
      ([[(15 / 16 : ℝ), 1]] ×ℂ [[-H, H]]) := by
    intro W hW
    rw [mem_reProdIm, uIcc_of_le (by norm_num)] at hW
    exact (differentiableAt_hughesYoungCompletePositiveCentralContinuation
      T t h k a b (by linarith [hW.1.1]) (by linarith [hW.1.2])).differentiableWithinAt
  have hzero := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (hughesYoungCompletePositiveCentralContinuation T t h k a b)
    ((15 / 16 : ℂ) - (H : ℂ) * I) ((1 : ℂ) + (H : ℂ) * I)
    (by simpa using hrect)
  simpa using hzero

theorem hughesYoungCompleteNegativeCentralContinuation_boundaryRect_zero
    (T t : ℝ) (h k a b : ℕ) (H : ℝ) :
    (∫ x : ℝ in (15 / 16)..1,
        hughesYoungCompleteNegativeCentralContinuation T t h k a b
          ((x : ℂ) + (-H : ℂ) * I)) -
      (∫ x : ℝ in (15 / 16)..1,
        hughesYoungCompleteNegativeCentralContinuation T t h k a b
          ((x : ℂ) + (H : ℂ) * I)) +
      I • (∫ y : ℝ in -H..H,
        hughesYoungCompleteNegativeCentralContinuation T t h k a b
          ((1 : ℂ) + (y : ℂ) * I)) -
      I • (∫ y : ℝ in -H..H,
        hughesYoungCompleteNegativeCentralContinuation T t h k a b
          ((15 / 16 : ℂ) + (y : ℂ) * I)) = 0 := by
  simpa only [hughesYoungCompleteNegativeCentralContinuation_eq_swap] using
    hughesYoungCompletePositiveCentralContinuation_boundaryRect_zero
      T (-t) k h b a H

set_option maxHeartbeats 2000000 in
theorem tendsto_hughesYoungCompletePositiveCentralContinuation_vertical_sub_zero
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun H : ℝ =>
      (∫ u in -H..H, hughesYoungCompletePositiveCentralContinuation
          T t h k a b ((1 : ℂ) + (u : ℂ) * I)) -
      (∫ u in -H..H, hughesYoungCompletePositiveCentralContinuation
          T t h k a b ((15 / 16 : ℂ) + (u : ℂ) * I)))
      atTop (nhds 0) := by
  let f := hughesYoungCompletePositiveCentralContinuation T t h k a b
  have htop : Tendsto (fun H : ℝ => HIntegral f (15 / 16) 1 H)
      atTop (nhds 0) :=
    tendsto_HIntegral_top_zero_of_central_horizontal_bound
      f t (15 / 16) 1 (by norm_num) (by norm_num)
        (completePositive_horizontal_bound_for_shift T t h k ha hb)
  have hbottom : Tendsto (fun H : ℝ => HIntegral f (15 / 16) 1 (-H))
      atTop (nhds 0) :=
    tendsto_HIntegral_bottom_zero_of_central_horizontal_bound
      f t (15 / 16) 1 (by norm_num) (by norm_num)
        (completePositive_horizontal_bound_for_shift T t h k ha hb)
  have hhorizontal : Tendsto (fun H : ℝ =>
      (-I) * (HIntegral f (15 / 16) 1 H -
        HIntegral f (15 / 16) 1 (-H))) atTop (nhds 0) := by
    simpa only [sub_zero, mul_zero] using (htop.sub hbottom).const_mul (-I)
  apply hhorizontal.congr'
  exact Eventually.of_forall fun H => by
    have hr := hughesYoungCompletePositiveCentralContinuation_boundaryRect_zero
      T t h k a b H
    unfold HIntegral f
    rw [smul_eq_mul, smul_eq_mul] at hr
    have hI :
        I * ((∫ u in -H..H,
            hughesYoungCompletePositiveCentralContinuation T t h k a b
              ((1 : ℂ) + (u : ℂ) * I)) -
          (∫ u in -H..H,
            hughesYoungCompletePositiveCentralContinuation T t h k a b
              ((15 / 16 : ℂ) + (u : ℂ) * I))) =
          (∫ x in (15 / 16)..1,
            hughesYoungCompletePositiveCentralContinuation T t h k a b
              ((x : ℂ) + (H : ℂ) * I)) -
          (∫ x in (15 / 16)..1,
            hughesYoungCompletePositiveCentralContinuation T t h k a b
              ((x : ℂ) + (-H : ℂ) * I)) := by
      linear_combination hr
    push_cast
    rw [← hI, ← mul_assoc]
    have hnegI : (-I : ℂ) * I = 1 := by
      rw [neg_mul, I_mul_I]
      simp
    rw [hnegI, one_mul]

theorem tendsto_hughesYoungCompleteNegativeCentralContinuation_vertical_sub_zero
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun H : ℝ =>
      (∫ u in -H..H, hughesYoungCompleteNegativeCentralContinuation
          T t h k a b ((1 : ℂ) + (u : ℂ) * I)) -
      (∫ u in -H..H, hughesYoungCompleteNegativeCentralContinuation
          T t h k a b ((15 / 16 : ℂ) + (u : ℂ) * I)))
      atTop (nhds 0) := by
  simpa only [hughesYoungCompleteNegativeCentralContinuation_eq_swap] using
    tendsto_hughesYoungCompletePositiveCentralContinuation_vertical_sub_zero
      T (-t) k h hb ha

theorem continuous_hughesYoungCompletePositiveCentralContinuation_vertical
    (T t : ℝ) (h k a b : ℕ) {c : ℝ}
    (hc : c ∈ Set.Icc (15 / 16 : ℝ) 1) :
    Continuous (fun u : ℝ =>
      hughesYoungCompletePositiveCentralContinuation T t h k a b
        ((c : ℂ) + (u : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have houter : ContinuousAt
      (hughesYoungCompletePositiveCentralContinuation T t h k a b)
      ((c : ℂ) + (u : ℂ) * I) :=
    (differentiableAt_hughesYoungCompletePositiveCentralContinuation
      T t h k a b (by simpa using (show (7 / 8 : ℝ) < c by linarith [hc.1]))
        (by simpa using (show c < (3 / 2 : ℝ) by linarith [hc.2]))).continuousAt
  have hinner : ContinuousAt (fun v : ℝ => (c : ℂ) + (v : ℂ) * I) u := by
    fun_prop
  simpa only [Function.comp_apply] using
    houter.comp (x := u) (f := fun v : ℝ => (c : ℂ) + (v : ℂ) * I) hinner

theorem integrable_hughesYoungCompletePositiveCentralContinuation_vertical
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {c : ℝ} (hc : c ∈ Set.Icc (15 / 16 : ℝ) 1) :
    Integrable (fun u : ℝ =>
      hughesYoungCompletePositiveCentralContinuation T t h k a b
        ((c : ℂ) + (u : ℂ) * I)) := by
  obtain ⟨C, _hC, hbound⟩ :=
    exists_norm_hughesYoungCompletePositiveCentralContinuation_horizontal_le
      T t h k ha hb
  let L : ℝ := max 1 (|t| + 1)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply integrable_of_continuous_of_norm_le_gaussian_tail
    (fun u : ℝ => hughesYoungCompletePositiveCentralContinuation T t h k a b
      ((c : ℂ) + (u : ℂ) * I))
    (continuous_hughesYoungCompletePositiveCentralContinuation_vertical
      T t h k a b hc)
    (C := C) (A := 100) (B := 60) (D := 2 + |t| + 1) (j := 17)
    hL (by norm_num : (0 : ℝ) < 60)
  intro u hu
  have hu1 : 1 ≤ |u| := (le_max_left 1 (|t| + 1)).trans hu
  have hut : |t| + 1 ≤ |u| := (le_max_right 1 (|t| + 1)).trans hu
  simpa only [add_assoc] using hbound u hu1 hut c hc

theorem integrable_hughesYoungCompleteNegativeCentralContinuation_vertical
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {c : ℝ} (hc : c ∈ Set.Icc (15 / 16 : ℝ) 1) :
    Integrable (fun u : ℝ =>
      hughesYoungCompleteNegativeCentralContinuation T t h k a b
        ((c : ℂ) + (u : ℂ) * I)) := by
  have h := integrable_hughesYoungCompletePositiveCentralContinuation_vertical
    T (-t) k h hb ha hc
  simpa only [hughesYoungCompleteNegativeCentralContinuation_eq_swap] using h

theorem integral_hughesYoungCompletePositiveCentralContinuation_vertical_eq :
    ∀ (T t : ℝ) (h k : ℕ) {a b : ℕ}, 0 < a → 0 < b →
    (∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation T t h k a b
        ((1 : ℂ) + (u : ℂ) * I)) =
      ∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation T t h k a b
        ((15 / 16 : ℂ) + (u : ℂ) * I) := by
  intro T t h k a b ha hb
  have htop := MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungCompletePositiveCentralContinuation_vertical
      T t h k ha hb (by constructor <;> norm_num :
        (1 : ℝ) ∈ Set.Icc (15 / 16 : ℝ) 1))
    tendsto_neg_atTop_atBot tendsto_id
  have hbottom := MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungCompletePositiveCentralContinuation_vertical
      T t h k ha hb (by constructor <;> norm_num :
        (15 / 16 : ℝ) ∈ Set.Icc (15 / 16 : ℝ) 1))
    tendsto_neg_atTop_atBot tendsto_id
  have hsub := htop.sub hbottom
  have hzero :=
    tendsto_hughesYoungCompletePositiveCentralContinuation_vertical_sub_zero
      T t h k ha hb
  have hsub' : Tendsto (fun H : ℝ =>
      (∫ u in -H..H, hughesYoungCompletePositiveCentralContinuation
          T t h k a b ((1 : ℂ) + (u : ℂ) * I)) -
      (∫ u in -H..H, hughesYoungCompletePositiveCentralContinuation
          T t h k a b ((15 / 16 : ℂ) + (u : ℂ) * I)))
      atTop (nhds ((∫ u : ℝ,
        hughesYoungCompletePositiveCentralContinuation T t h k a b
          ((1 : ℂ) + (u : ℂ) * I)) -
        (∫ u : ℝ,
        hughesYoungCompletePositiveCentralContinuation T t h k a b
          ((15 / 16 : ℂ) + (u : ℂ) * I)))) := by
    simpa using hsub
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub' hzero)

theorem integral_hughesYoungCompleteNegativeCentralContinuation_vertical_eq
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (∫ u : ℝ, hughesYoungCompleteNegativeCentralContinuation T t h k a b
        ((1 : ℂ) + (u : ℂ) * I)) =
      ∫ u : ℝ, hughesYoungCompleteNegativeCentralContinuation T t h k a b
        ((15 / 16 : ℂ) + (u : ℂ) * I) := by
  simpa only [hughesYoungCompleteNegativeCentralContinuation_eq_swap] using
    integral_hughesYoungCompletePositiveCentralContinuation_vertical_eq
      T (-t) k h hb ha

theorem integral_hughesYoungEquation84CompletePositiveSourceLine_eq_shiftedContinuation
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    (∫ u : ℝ, hughesYoungEquation84CompletePositiveSourceLine
        T t h k a b u) =
      ∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation T t h k a b
        ((15 / 16 : ℂ) + (u : ℂ) * I) := by
  calc
    _ = ∫ u : ℝ, hughesYoungCompletePositiveCentralContinuation T t h k a b
          ((1 : ℂ) + (u : ℂ) * I) := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact hughesYoungEquation84CompletePositiveSourceLine_eq_continuation
        T t h k ha hb hab u hη hη4
    _ = _ := integral_hughesYoungCompletePositiveCentralContinuation_vertical_eq
      T t h k ha hb

theorem integral_hughesYoungEquation84CompleteNegativeSourceLine_eq_shiftedContinuation
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    (∫ u : ℝ, hughesYoungEquation84CompleteNegativeSourceLine
        T t h k a b u) =
      ∫ u : ℝ, hughesYoungCompleteNegativeCentralContinuation T t h k a b
        ((15 / 16 : ℂ) + (u : ℂ) * I) := by
  calc
    _ = ∫ u : ℝ, hughesYoungCompleteNegativeCentralContinuation T t h k a b
          ((1 : ℂ) + (u : ℂ) * I) := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact hughesYoungEquation84CompleteNegativeSourceLine_eq_continuation
        T t h k ha hb hab u hη hη4
    _ = _ := integral_hughesYoungCompleteNegativeCentralContinuation_vertical_eq
      T t h k ha hb

end RiemannZeta.GuthMaynard
