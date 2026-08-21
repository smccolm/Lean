import RiemannZeta.GuthMaynard.HughesYoungCentralSeriesBounds
import RiemannZeta.GuthMaynard.HughesYoungCentralArithmeticBridge

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

set_option maxHeartbeats 4000000
set_option Elab.async false

namespace RiemannZeta.GuthMaynard

/-!
# Finite arithmetic expansion of the Hughes--Young central series

The regularized equation-(84) kernel is affine in each of its two DFI
logarithmic constants.  Expanding it into four fixed analytic coefficient
functions turns the infinite modulus sum into four absolutely convergent
arithmetic moments.  This is the source-faithful route to contour shifting
the complete series rather than shifting its terms without a uniform
summation argument.
-/

noncomputable def hughesYoungEquation84Kernel00 (t : ℝ) (w : ℂ) : ℂ :=
  hughesYoungEquation84RegularizedContourKernel t w 0 0

noncomputable def hughesYoungEquation84Kernel10 (t : ℝ) (w : ℂ) : ℂ :=
  hughesYoungEquation84RegularizedContourKernel t w 1 0 -
    hughesYoungEquation84Kernel00 t w

noncomputable def hughesYoungEquation84Kernel01 (t : ℝ) (w : ℂ) : ℂ :=
  hughesYoungEquation84RegularizedContourKernel t w 0 1 -
    hughesYoungEquation84Kernel00 t w

noncomputable def hughesYoungEquation84Kernel11 (t : ℝ) (w : ℂ) : ℂ :=
  hughesYoungEquation84RegularizedContourKernel t w 1 1 -
    hughesYoungEquation84Kernel10 t w -
    hughesYoungEquation84Kernel01 t w -
    hughesYoungEquation84Kernel00 t w

noncomputable def hughesYoungEquation84KernelCore00 (t : ℝ) (w : ℂ) : ℂ :=
  hughesYoungEquation84RegularizedContourKernelCore t w 0 0

noncomputable def hughesYoungEquation84KernelCore10 (t : ℝ) (w : ℂ) : ℂ :=
  hughesYoungEquation84RegularizedContourKernelCore t w 1 0 -
    hughesYoungEquation84KernelCore00 t w

noncomputable def hughesYoungEquation84KernelCore01 (t : ℝ) (w : ℂ) : ℂ :=
  hughesYoungEquation84RegularizedContourKernelCore t w 0 1 -
    hughesYoungEquation84KernelCore00 t w

noncomputable def hughesYoungEquation84KernelCore11 (t : ℝ) (w : ℂ) : ℂ :=
  hughesYoungEquation84RegularizedContourKernelCore t w 1 1 -
    hughesYoungEquation84KernelCore10 t w -
    hughesYoungEquation84KernelCore01 t w -
    hughesYoungEquation84KernelCore00 t w

theorem hughesYoungEquation84Kernel00_eq_auxiliary_mul_core
    (t : ℝ) (w : ℂ) :
    hughesYoungEquation84Kernel00 t w =
      hughesYoungAuxiliaryZero w * hughesYoungEquation84KernelCore00 t w := by
  rfl

theorem hughesYoungEquation84Kernel10_eq_auxiliary_mul_core
    (t : ℝ) (w : ℂ) :
    hughesYoungEquation84Kernel10 t w =
      hughesYoungAuxiliaryZero w * hughesYoungEquation84KernelCore10 t w := by
  unfold hughesYoungEquation84Kernel10 hughesYoungEquation84KernelCore10
    hughesYoungEquation84Kernel00 hughesYoungEquation84KernelCore00
    hughesYoungEquation84RegularizedContourKernel
  ring

theorem hughesYoungEquation84Kernel01_eq_auxiliary_mul_core
    (t : ℝ) (w : ℂ) :
    hughesYoungEquation84Kernel01 t w =
      hughesYoungAuxiliaryZero w * hughesYoungEquation84KernelCore01 t w := by
  unfold hughesYoungEquation84Kernel01 hughesYoungEquation84KernelCore01
    hughesYoungEquation84Kernel00 hughesYoungEquation84KernelCore00
    hughesYoungEquation84RegularizedContourKernel
  ring

theorem hughesYoungEquation84Kernel11_eq_auxiliary_mul_core
    (t : ℝ) (w : ℂ) :
    hughesYoungEquation84Kernel11 t w =
      hughesYoungAuxiliaryZero w * hughesYoungEquation84KernelCore11 t w := by
  rw [hughesYoungEquation84Kernel11, hughesYoungEquation84KernelCore11,
    hughesYoungEquation84Kernel10_eq_auxiliary_mul_core,
    hughesYoungEquation84Kernel01_eq_auxiliary_mul_core,
    hughesYoungEquation84Kernel00_eq_auxiliary_mul_core]
  unfold hughesYoungEquation84RegularizedContourKernel
  ring

private theorem hughesYoungEquation84RegularizedBetaKernel_eq_fourTerm
    (t : ℝ) (w CX COne : ℂ) :
    hughesYoungEquation84RegularizedBetaKernel t w CX COne =
      hughesYoungEquation84RegularizedBetaKernel t w 0 0 +
      CX * (hughesYoungEquation84RegularizedBetaKernel t w 1 0 -
        hughesYoungEquation84RegularizedBetaKernel t w 0 0) +
      COne * (hughesYoungEquation84RegularizedBetaKernel t w 0 1 -
        hughesYoungEquation84RegularizedBetaKernel t w 0 0) +
      (CX * COne) *
        (hughesYoungEquation84RegularizedBetaKernel t w 1 1 -
          (hughesYoungEquation84RegularizedBetaKernel t w 1 0 -
            hughesYoungEquation84RegularizedBetaKernel t w 0 0) -
          (hughesYoungEquation84RegularizedBetaKernel t w 0 1 -
            hughesYoungEquation84RegularizedBetaKernel t w 0 0) -
          hughesYoungEquation84RegularizedBetaKernel t w 0 0) := by
  unfold hughesYoungEquation84RegularizedBetaKernel
  dsimp only
  ring

private theorem mul_bilinear_fourTerm
    (O CX COne b b00 b10 b01 b11 : ℂ)
    (hb : b =
      b00 + CX * (b10 - b00) + COne * (b01 - b00) +
        (CX * COne) * (b11 - (b10 - b00) - (b01 - b00) - b00)) :
    O * b =
      O * b00 + CX * (O * (b10 - b00)) +
        COne * (O * (b01 - b00)) +
        (CX * COne) *
          (O * (b11 - (b10 - b00) - (b01 - b00) - b00)) := by
  rw [hb]
  ring

private theorem hughesYoungEquation84Kernel00_eq_prefactor_mul_beta
    (t : ℝ) (w : ℂ) :
    hughesYoungEquation84Kernel00 t w =
      hughesYoungEquation84RegularizedContourPrefactor t w *
        hughesYoungEquation84RegularizedBetaKernel t w 0 0 := by
  unfold hughesYoungEquation84Kernel00
  exact hughesYoungEquation84RegularizedContourKernel_eq_prefactor_mul_beta
    t w 0 0

private theorem hughesYoungEquation84Kernel10_eq_prefactor_mul_beta
    (t : ℝ) (w : ℂ) :
    hughesYoungEquation84Kernel10 t w =
      hughesYoungEquation84RegularizedContourPrefactor t w *
        (hughesYoungEquation84RegularizedBetaKernel t w 1 0 -
          hughesYoungEquation84RegularizedBetaKernel t w 0 0) := by
  unfold hughesYoungEquation84Kernel10
  rw [hughesYoungEquation84RegularizedContourKernel_eq_prefactor_mul_beta,
    hughesYoungEquation84Kernel00_eq_prefactor_mul_beta]
  ring

private theorem hughesYoungEquation84Kernel01_eq_prefactor_mul_beta
    (t : ℝ) (w : ℂ) :
    hughesYoungEquation84Kernel01 t w =
      hughesYoungEquation84RegularizedContourPrefactor t w *
        (hughesYoungEquation84RegularizedBetaKernel t w 0 1 -
          hughesYoungEquation84RegularizedBetaKernel t w 0 0) := by
  unfold hughesYoungEquation84Kernel01
  rw [hughesYoungEquation84RegularizedContourKernel_eq_prefactor_mul_beta,
    hughesYoungEquation84Kernel00_eq_prefactor_mul_beta]
  ring

private theorem hughesYoungEquation84Kernel11_eq_prefactor_mul_beta
    (t : ℝ) (w : ℂ) :
    hughesYoungEquation84Kernel11 t w =
      hughesYoungEquation84RegularizedContourPrefactor t w *
        (hughesYoungEquation84RegularizedBetaKernel t w 1 1 -
          (hughesYoungEquation84RegularizedBetaKernel t w 1 0 -
            hughesYoungEquation84RegularizedBetaKernel t w 0 0) -
          (hughesYoungEquation84RegularizedBetaKernel t w 0 1 -
            hughesYoungEquation84RegularizedBetaKernel t w 0 0) -
          hughesYoungEquation84RegularizedBetaKernel t w 0 0) := by
  unfold hughesYoungEquation84Kernel11
  rw [hughesYoungEquation84RegularizedContourKernel_eq_prefactor_mul_beta,
    hughesYoungEquation84Kernel10_eq_prefactor_mul_beta,
    hughesYoungEquation84Kernel01_eq_prefactor_mul_beta,
    hughesYoungEquation84Kernel00_eq_prefactor_mul_beta]
  ring

/-- Exact bilinear four-coefficient expansion of the pole-cancelled
equation-(84) kernel. -/
theorem hughesYoungEquation84RegularizedContourKernel_eq_fourTerm
    (t : ℝ) (w CX COne : ℂ) :
    hughesYoungEquation84RegularizedContourKernel t w CX COne =
      hughesYoungEquation84Kernel00 t w +
      CX * hughesYoungEquation84Kernel10 t w +
      COne * hughesYoungEquation84Kernel01 t w +
      (CX * COne) * hughesYoungEquation84Kernel11 t w := by
  rw [hughesYoungEquation84RegularizedContourKernel_eq_prefactor_mul_beta,
    hughesYoungEquation84Kernel00_eq_prefactor_mul_beta,
    hughesYoungEquation84Kernel10_eq_prefactor_mul_beta,
    hughesYoungEquation84Kernel01_eq_prefactor_mul_beta,
    hughesYoungEquation84Kernel11_eq_prefactor_mul_beta]
  apply mul_bilinear_fourTerm
  exact hughesYoungEquation84RegularizedBetaKernel_eq_fourTerm t w CX COne

/-- Common nonnegative logarithmic budget for the two reduced DFI
denominators in a fixed positive shift. -/
noncomputable def hughesYoungEquation84LogBudget (a b r : ℕ) : ℝ :=
  1 + 2 * |Real.log (r : ℝ)| + |Real.log (a : ℝ)| +
    |Real.log (b : ℝ)| + 4 * |Real.eulerMascheroniConstant|

theorem one_le_hughesYoungEquation84LogBudget (a b r : ℕ) :
    1 ≤ hughesYoungEquation84LogBudget a b r := by
  unfold hughesYoungEquation84LogBudget
  linarith [abs_nonneg (Real.log (r : ℝ)), abs_nonneg (Real.log (a : ℝ)),
    abs_nonneg (Real.log (b : ℝ)), abs_nonneg Real.eulerMascheroniConstant]

noncomputable def hughesYoungEquation84PositiveCX (b r q : ℕ) : ℂ :=
  (Real.log r : ℂ) +
    dfiEquation27LogConstant b (dfiReducedDenominator b q)

noncomputable def hughesYoungEquation84PositiveCOne (a r q : ℕ) : ℂ :=
  (Real.log r : ℂ) +
    dfiEquation27LogConstant a (dfiReducedDenominator a q)

theorem norm_hughesYoungEquation84PositiveCX_le_logBudget
    (a b r q : ℕ) (hq : 0 < q) :
    ‖hughesYoungEquation84PositiveCX b r q‖ ≤
      hughesYoungEquation84LogBudget a b r + 4 * Real.log (q : ℝ) := by
  have h := norm_log_add_dfiEquation27LogConstant_reduced_le b r q hq
  unfold hughesYoungEquation84PositiveCX hughesYoungEquation84LogBudget
  linarith [abs_nonneg (Real.log (r : ℝ)), abs_nonneg (Real.log (a : ℝ)),
    abs_nonneg (Real.log (b : ℝ)),
    abs_nonneg Real.eulerMascheroniConstant,
    Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)]

theorem norm_hughesYoungEquation84PositiveCOne_le_logBudget
    (a b r q : ℕ) (hq : 0 < q) :
    ‖hughesYoungEquation84PositiveCOne a r q‖ ≤
      hughesYoungEquation84LogBudget a b r + 4 * Real.log (q : ℝ) := by
  have h := norm_log_add_dfiEquation27LogConstant_reduced_le a r q hq
  unfold hughesYoungEquation84PositiveCOne hughesYoungEquation84LogBudget
  linarith [abs_nonneg (Real.log (r : ℝ)), abs_nonneg (Real.log (a : ℝ)),
    abs_nonneg (Real.log (b : ℝ)),
    abs_nonneg Real.eulerMascheroniConstant,
    Real.log_nonneg (show (1 : ℝ) ≤ q by exact_mod_cast hq)]

theorem one_le_hughesYoungEquation84LogBudget_add_four_log
    (a b r q : ℕ) (hq : 0 < q) :
    (1 : ℝ) ≤ hughesYoungEquation84LogBudget a b r +
      4 * Real.log (q : ℝ) := by
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog := Real.log_nonneg hqOne
  linarith [one_le_hughesYoungEquation84LogBudget a b r]

/-- The four arithmetic moments required by the exact bilinear expansion
are all absolutely summable. -/
theorem summable_hughesYoungEquation84PositiveArithmeticMoment
    (a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (i j : Bool) :
    Summable (fun q : ℕ =>
      dfiEquation27ArithmeticCoefficient a b r q *
        (if i then hughesYoungEquation84PositiveCX b r q else 1) *
        (if j then hughesYoungEquation84PositiveCOne a r q else 1)) := by
  apply summable_dfiEquation27ArithmeticCoefficient_mul_two_logProfiles
    a b r ha hb hr _ _ (hughesYoungEquation84LogBudget a b r)
    (one_le_hughesYoungEquation84LogBudget a b r)
  · intro q hq
    split
    · exact norm_hughesYoungEquation84PositiveCX_le_logBudget a b r q hq
    · simpa using one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq
  · intro q hq
    split
    · exact norm_hughesYoungEquation84PositiveCOne_le_logBudget a b r q hq
    · simpa using one_le_hughesYoungEquation84LogBudget_add_four_log a b r q hq

noncomputable def hughesYoungEquation84PositiveArithmeticMoment
    (a b r : ℕ) (i j : Bool) : ℂ :=
  ∑' q : ℕ,
    dfiEquation27ArithmeticCoefficient a b r q *
      (if i then hughesYoungEquation84PositiveCX b r q else 1) *
      (if j then hughesYoungEquation84PositiveCOne a r q else 1)

noncomputable def hughesYoungEquation84PositiveOuter
    (T t : ℝ) (h k a b r : ℕ) (w : ℂ) : ℂ :=
  ((a : ℂ) * b)⁻¹ *
    (hughesYoungReducedMellinStaticComplex T t h k w *
      hughesYoungCentralShiftPower r w)

set_option maxHeartbeats 2000000 in
/-- The complete positive modulus series is exactly a finite linear
combination of four analytic kernel coefficients and four absolutely
convergent arithmetic moments. -/
theorem hughesYoungEquation84PositiveContourSeries_eq_fourMoments
    (T t : ℝ) (h k a b r : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (w : ℂ) :
    hughesYoungEquation84PositiveContourSeries T t h k a b r w =
      hughesYoungEquation84PositiveOuter T t h k a b r w *
        (hughesYoungEquation84PositiveArithmeticMoment a b r false false *
            hughesYoungEquation84Kernel00 t w +
          hughesYoungEquation84PositiveArithmeticMoment a b r true false *
            hughesYoungEquation84Kernel10 t w +
          hughesYoungEquation84PositiveArithmeticMoment a b r false true *
            hughesYoungEquation84Kernel01 t w +
          hughesYoungEquation84PositiveArithmeticMoment a b r true true *
            hughesYoungEquation84Kernel11 t w) := by
  let f₀₀ : ℕ → ℂ := fun q =>
    dfiEquation27ArithmeticCoefficient a b r q
  let f₁₀ : ℕ → ℂ := fun q =>
    dfiEquation27ArithmeticCoefficient a b r q *
      hughesYoungEquation84PositiveCX b r q
  let f₀₁ : ℕ → ℂ := fun q =>
    dfiEquation27ArithmeticCoefficient a b r q *
      hughesYoungEquation84PositiveCOne a r q
  let f₁₁ : ℕ → ℂ := fun q =>
    dfiEquation27ArithmeticCoefficient a b r q *
      hughesYoungEquation84PositiveCX b r q *
      hughesYoungEquation84PositiveCOne a r q
  have hf₀₀ : Summable f₀₀ := by
    have hs := summable_hughesYoungEquation84PositiveArithmeticMoment
      a b r ha hb hr false false
    change Summable (fun q =>
      dfiEquation27ArithmeticCoefficient a b r q * (1 : ℂ) * 1) at hs
    simpa only [f₀₀, mul_one] using hs
  have hf₁₀ : Summable f₁₀ := by
    have hs := summable_hughesYoungEquation84PositiveArithmeticMoment
      a b r ha hb hr true false
    change Summable (fun q =>
      dfiEquation27ArithmeticCoefficient a b r q *
        hughesYoungEquation84PositiveCX b r q * 1) at hs
    simpa only [f₁₀, mul_one] using hs
  have hf₀₁ : Summable f₀₁ := by
    have hs := summable_hughesYoungEquation84PositiveArithmeticMoment
      a b r ha hb hr false true
    change Summable (fun q =>
      dfiEquation27ArithmeticCoefficient a b r q * (1 : ℂ) *
        hughesYoungEquation84PositiveCOne a r q) at hs
    simpa only [f₀₁, mul_one, one_mul] using hs
  have hf₁₁ : Summable f₁₁ := by
    have hs := summable_hughesYoungEquation84PositiveArithmeticMoment
      a b r ha hb hr true true
    change Summable (fun q =>
      dfiEquation27ArithmeticCoefficient a b r q *
        hughesYoungEquation84PositiveCX b r q *
        hughesYoungEquation84PositiveCOne a r q) at hs
    simpa only [f₁₁] using hs
  let P : ℂ := hughesYoungEquation84PositiveOuter T t h k a b r w
  let g₀₀ : ℕ → ℂ := fun q => P * (f₀₀ q * hughesYoungEquation84Kernel00 t w)
  let g₁₀ : ℕ → ℂ := fun q => P * (f₁₀ q * hughesYoungEquation84Kernel10 t w)
  let g₀₁ : ℕ → ℂ := fun q => P * (f₀₁ q * hughesYoungEquation84Kernel01 t w)
  let g₁₁ : ℕ → ℂ := fun q => P * (f₁₁ q * hughesYoungEquation84Kernel11 t w)
  have hg₀₀ : Summable g₀₀ := (hf₀₀.mul_right _).mul_left _
  have hg₁₀ : Summable g₁₀ := (hf₁₀.mul_right _).mul_left _
  have hg₀₁ : Summable g₀₁ := (hf₀₁.mul_right _).mul_left _
  have hg₁₁ : Summable g₁₁ := (hf₁₁.mul_right _).mul_left _
  have hseries : hughesYoungEquation84PositiveContourSeries T t h k a b r w =
      ∑' q : ℕ, (g₀₀ q + g₁₀ q + g₀₁ q + g₁₁ q) := by
    unfold hughesYoungEquation84PositiveContourSeries
    apply tsum_congr
    intro q
    unfold hughesYoungEquation84PositiveContourTerm
    rw [hughesYoungEquation84RegularizedContourKernel_eq_fourTerm]
    dsimp only [P, g₀₀, g₁₀, g₀₁, g₁₁, f₀₀, f₁₀, f₀₁, f₁₁,
      hughesYoungEquation84PositiveOuter, hughesYoungEquation84PositiveCX,
      hughesYoungEquation84PositiveCOne]
    ring
  rw [hseries]
  rw [((hg₀₀.add hg₁₀).add hg₀₁).tsum_add hg₁₁,
    (hg₀₀.add hg₁₀).tsum_add hg₀₁,
    hg₀₀.tsum_add hg₁₀]
  simp only [g₀₀, g₁₀, g₀₁, g₁₁, tsum_mul_left, tsum_mul_right]
  change P * ((∑' q, f₀₀ q) * hughesYoungEquation84Kernel00 t w) +
      P * ((∑' q, f₁₀ q) * hughesYoungEquation84Kernel10 t w) +
      P * ((∑' q, f₀₁ q) * hughesYoungEquation84Kernel01 t w) +
      P * ((∑' q, f₁₁ q) * hughesYoungEquation84Kernel11 t w) = _
  have hM₀₀ : hughesYoungEquation84PositiveArithmeticMoment a b r false false =
      ∑' q, f₀₀ q := by
    unfold hughesYoungEquation84PositiveArithmeticMoment
    apply tsum_congr
    intro q
    simp [f₀₀]
  have hM₁₀ : hughesYoungEquation84PositiveArithmeticMoment a b r true false =
      ∑' q, f₁₀ q := by
    unfold hughesYoungEquation84PositiveArithmeticMoment
    apply tsum_congr
    intro q
    simp [f₁₀]
  have hM₀₁ : hughesYoungEquation84PositiveArithmeticMoment a b r false true =
      ∑' q, f₀₁ q := by
    unfold hughesYoungEquation84PositiveArithmeticMoment
    apply tsum_congr
    intro q
    simp [f₀₁]
  have hM₁₁ : hughesYoungEquation84PositiveArithmeticMoment a b r true true =
      ∑' q, f₁₁ q := by
    unfold hughesYoungEquation84PositiveArithmeticMoment
    apply tsum_congr
    intro q
    simp [f₁₁]
  rw [hM₀₀, hM₁₀, hM₀₁, hM₁₁]
  dsimp only [P]
  ring

noncomputable def hughesYoungEquation84NegativeOuter
    (T t : ℝ) (h k a b r : ℕ) (w : ℂ) : ℂ :=
  ((b : ℂ) * a)⁻¹ *
    (hughesYoungReducedMellinStaticComplex T t h k w *
      hughesYoungCentralShiftPower r w)

set_option maxHeartbeats 2000000 in
/-- Coordinate-swapping the arithmetic variables gives the identical
four-moment expansion for the negative-shift branch. -/
theorem hughesYoungEquation84NegativeContourSeries_eq_fourMoments
    (T t : ℝ) (h k a b r : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (w : ℂ) :
    hughesYoungEquation84NegativeContourSeries T t h k a b r w =
      hughesYoungEquation84NegativeOuter T t h k a b r w *
        (hughesYoungEquation84PositiveArithmeticMoment b a r false false *
            hughesYoungEquation84Kernel00 (-t) w +
          hughesYoungEquation84PositiveArithmeticMoment b a r true false *
            hughesYoungEquation84Kernel10 (-t) w +
          hughesYoungEquation84PositiveArithmeticMoment b a r false true *
            hughesYoungEquation84Kernel01 (-t) w +
          hughesYoungEquation84PositiveArithmeticMoment b a r true true *
            hughesYoungEquation84Kernel11 (-t) w) := by
  let f₀₀ : ℕ → ℂ := fun q => dfiEquation27ArithmeticCoefficient b a r q
  let f₁₀ : ℕ → ℂ := fun q =>
    dfiEquation27ArithmeticCoefficient b a r q *
      hughesYoungEquation84PositiveCX a r q
  let f₀₁ : ℕ → ℂ := fun q =>
    dfiEquation27ArithmeticCoefficient b a r q *
      hughesYoungEquation84PositiveCOne b r q
  let f₁₁ : ℕ → ℂ := fun q =>
    dfiEquation27ArithmeticCoefficient b a r q *
      hughesYoungEquation84PositiveCX a r q *
      hughesYoungEquation84PositiveCOne b r q
  have hf₀₀ : Summable f₀₀ := by
    have hs := summable_hughesYoungEquation84PositiveArithmeticMoment
      b a r hb ha hr false false
    change Summable (fun q => dfiEquation27ArithmeticCoefficient b a r q * (1 : ℂ) * 1) at hs
    simpa only [f₀₀, mul_one] using hs
  have hf₁₀ : Summable f₁₀ := by
    have hs := summable_hughesYoungEquation84PositiveArithmeticMoment
      b a r hb ha hr true false
    change Summable (fun q => dfiEquation27ArithmeticCoefficient b a r q *
      hughesYoungEquation84PositiveCX a r q * 1) at hs
    simpa only [f₁₀, mul_one] using hs
  have hf₀₁ : Summable f₀₁ := by
    have hs := summable_hughesYoungEquation84PositiveArithmeticMoment
      b a r hb ha hr false true
    change Summable (fun q => dfiEquation27ArithmeticCoefficient b a r q * (1 : ℂ) *
      hughesYoungEquation84PositiveCOne b r q) at hs
    simpa only [f₀₁, mul_one, one_mul] using hs
  have hf₁₁ : Summable f₁₁ := by
    simpa only [f₁₁] using
      (summable_hughesYoungEquation84PositiveArithmeticMoment
        b a r hb ha hr true true)
  let P : ℂ := hughesYoungEquation84NegativeOuter T t h k a b r w
  let g₀₀ : ℕ → ℂ := fun q => P * (f₀₀ q * hughesYoungEquation84Kernel00 (-t) w)
  let g₁₀ : ℕ → ℂ := fun q => P * (f₁₀ q * hughesYoungEquation84Kernel10 (-t) w)
  let g₀₁ : ℕ → ℂ := fun q => P * (f₀₁ q * hughesYoungEquation84Kernel01 (-t) w)
  let g₁₁ : ℕ → ℂ := fun q => P * (f₁₁ q * hughesYoungEquation84Kernel11 (-t) w)
  have hg₀₀ : Summable g₀₀ := (hf₀₀.mul_right _).mul_left _
  have hg₁₀ : Summable g₁₀ := (hf₁₀.mul_right _).mul_left _
  have hg₀₁ : Summable g₀₁ := (hf₀₁.mul_right _).mul_left _
  have hg₁₁ : Summable g₁₁ := (hf₁₁.mul_right _).mul_left _
  have hseries : hughesYoungEquation84NegativeContourSeries T t h k a b r w =
      ∑' q : ℕ, (g₀₀ q + g₁₀ q + g₀₁ q + g₁₁ q) := by
    unfold hughesYoungEquation84NegativeContourSeries
    apply tsum_congr
    intro q
    unfold hughesYoungEquation84NegativeContourTerm
    rw [hughesYoungEquation84RegularizedContourKernel_eq_fourTerm]
    dsimp only [P, g₀₀, g₁₀, g₀₁, g₁₁, f₀₀, f₁₀, f₀₁, f₁₁,
      hughesYoungEquation84NegativeOuter, hughesYoungEquation84PositiveCX,
      hughesYoungEquation84PositiveCOne]
    ring
  rw [hseries,
    ((hg₀₀.add hg₁₀).add hg₀₁).tsum_add hg₁₁,
    (hg₀₀.add hg₁₀).tsum_add hg₀₁,
    hg₀₀.tsum_add hg₁₀]
  simp only [g₀₀, g₁₀, g₀₁, g₁₁, tsum_mul_left, tsum_mul_right]
  have hM₀₀ : hughesYoungEquation84PositiveArithmeticMoment b a r false false =
      ∑' q, f₀₀ q := by
    unfold hughesYoungEquation84PositiveArithmeticMoment
    apply tsum_congr
    intro q
    simp [f₀₀]
  have hM₁₀ : hughesYoungEquation84PositiveArithmeticMoment b a r true false =
      ∑' q, f₁₀ q := by
    unfold hughesYoungEquation84PositiveArithmeticMoment
    apply tsum_congr
    intro q
    simp [f₁₀]
  have hM₀₁ : hughesYoungEquation84PositiveArithmeticMoment b a r false true =
      ∑' q, f₀₁ q := by
    unfold hughesYoungEquation84PositiveArithmeticMoment
    apply tsum_congr
    intro q
    simp [f₀₁]
  have hM₁₁ : hughesYoungEquation84PositiveArithmeticMoment b a r true true =
      ∑' q, f₁₁ q := by
    unfold hughesYoungEquation84PositiveArithmeticMoment
    apply tsum_congr
    intro q
    simp [f₁₁]
  rw [hM₀₀, hM₁₀, hM₀₁, hM₁₁]
  dsimp only [P]
  ring

theorem differentiableAt_hughesYoungEquation84PositiveOuter
    (T t : ℝ) (h k a b r : ℕ) (w : ℂ) :
    DifferentiableAt ℂ
      (hughesYoungEquation84PositiveOuter T t h k a b r) w := by
  unfold hughesYoungEquation84PositiveOuter
  exact (differentiableAt_const (c := ((a : ℂ) * b)⁻¹)).mul
    (differentiableAt_hughesYoungReducedMellinStaticComplex T t h k w |>.mul
      (differentiableAt_hughesYoungCentralShiftPower r w))

theorem differentiableAt_hughesYoungEquation84NegativeOuter
    (T t : ℝ) (h k a b r : ℕ) (w : ℂ) :
    DifferentiableAt ℂ
      (hughesYoungEquation84NegativeOuter T t h k a b r) w := by
  unfold hughesYoungEquation84NegativeOuter
  exact (differentiableAt_const (c := ((b : ℂ) * a)⁻¹)).mul
    (differentiableAt_hughesYoungReducedMellinStaticComplex T t h k w |>.mul
      (differentiableAt_hughesYoungCentralShiftPower r w))

theorem differentiableAt_hughesYoungEquation84Kernel00
    (t : ℝ) {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 3 / 2) :
    DifferentiableAt ℂ (hughesYoungEquation84Kernel00 t) w := by
  unfold hughesYoungEquation84Kernel00
  exact differentiableAt_hughesYoungEquation84RegularizedContourKernel
    (t := t) (w := w) (CX := 0) (COne := 0) hw₀ hw₁

theorem differentiableAt_hughesYoungEquation84KernelCore00
    (t : ℝ) {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 3 / 2) :
    DifferentiableAt ℂ (hughesYoungEquation84KernelCore00 t) w := by
  unfold hughesYoungEquation84KernelCore00
  exact differentiableAt_hughesYoungEquation84RegularizedContourKernelCore
    (t := t) (w := w) (CX := 0) (COne := 0) hw₀ hw₁

theorem differentiableAt_hughesYoungEquation84KernelCore10
    (t : ℝ) {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 3 / 2) :
    DifferentiableAt ℂ (hughesYoungEquation84KernelCore10 t) w := by
  unfold hughesYoungEquation84KernelCore10
  exact (differentiableAt_hughesYoungEquation84RegularizedContourKernelCore
    (t := t) (w := w) (CX := 1) (COne := 0) hw₀ hw₁).sub
      (differentiableAt_hughesYoungEquation84KernelCore00 t hw₀ hw₁)

theorem differentiableAt_hughesYoungEquation84KernelCore01
    (t : ℝ) {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 3 / 2) :
    DifferentiableAt ℂ (hughesYoungEquation84KernelCore01 t) w := by
  unfold hughesYoungEquation84KernelCore01
  exact (differentiableAt_hughesYoungEquation84RegularizedContourKernelCore
    (t := t) (w := w) (CX := 0) (COne := 1) hw₀ hw₁).sub
      (differentiableAt_hughesYoungEquation84KernelCore00 t hw₀ hw₁)

theorem differentiableAt_hughesYoungEquation84KernelCore11
    (t : ℝ) {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 3 / 2) :
    DifferentiableAt ℂ (hughesYoungEquation84KernelCore11 t) w := by
  unfold hughesYoungEquation84KernelCore11
  exact (((differentiableAt_hughesYoungEquation84RegularizedContourKernelCore
    (t := t) (w := w) (CX := 1) (COne := 1) hw₀ hw₁).sub
      (differentiableAt_hughesYoungEquation84KernelCore10 t hw₀ hw₁)).sub
      (differentiableAt_hughesYoungEquation84KernelCore01 t hw₀ hw₁)).sub
      (differentiableAt_hughesYoungEquation84KernelCore00 t hw₀ hw₁)

theorem differentiableAt_hughesYoungEquation84Kernel10
    (t : ℝ) {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 3 / 2) :
    DifferentiableAt ℂ (hughesYoungEquation84Kernel10 t) w := by
  unfold hughesYoungEquation84Kernel10
  exact (differentiableAt_hughesYoungEquation84RegularizedContourKernel
    (t := t) (w := w) (CX := 1) (COne := 0) hw₀ hw₁).sub
      (differentiableAt_hughesYoungEquation84Kernel00 t hw₀ hw₁)

theorem differentiableAt_hughesYoungEquation84Kernel01
    (t : ℝ) {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 3 / 2) :
    DifferentiableAt ℂ (hughesYoungEquation84Kernel01 t) w := by
  unfold hughesYoungEquation84Kernel01
  exact (differentiableAt_hughesYoungEquation84RegularizedContourKernel
    (t := t) (w := w) (CX := 0) (COne := 1) hw₀ hw₁).sub
      (differentiableAt_hughesYoungEquation84Kernel00 t hw₀ hw₁)

theorem differentiableAt_hughesYoungEquation84Kernel11
    (t : ℝ) {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 3 / 2) :
    DifferentiableAt ℂ (hughesYoungEquation84Kernel11 t) w := by
  unfold hughesYoungEquation84Kernel11
  exact (((differentiableAt_hughesYoungEquation84RegularizedContourKernel
    (t := t) (w := w) (CX := 1) (COne := 1) hw₀ hw₁).sub
      (differentiableAt_hughesYoungEquation84Kernel10 t hw₀ hw₁)).sub
      (differentiableAt_hughesYoungEquation84Kernel01 t hw₀ hw₁)).sub
      (differentiableAt_hughesYoungEquation84Kernel00 t hw₀ hw₁)

theorem differentiableAt_hughesYoungEquation84PositiveContourSeries
    (T t : ℝ) (h k a b r : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 3 / 2) :
    DifferentiableAt ℂ
      (hughesYoungEquation84PositiveContourSeries T t h k a b r) w := by
  have heq : hughesYoungEquation84PositiveContourSeries T t h k a b r =
      fun z => hughesYoungEquation84PositiveOuter T t h k a b r z *
        (hughesYoungEquation84PositiveArithmeticMoment a b r false false *
            hughesYoungEquation84Kernel00 t z +
          hughesYoungEquation84PositiveArithmeticMoment a b r true false *
            hughesYoungEquation84Kernel10 t z +
          hughesYoungEquation84PositiveArithmeticMoment a b r false true *
            hughesYoungEquation84Kernel01 t z +
          hughesYoungEquation84PositiveArithmeticMoment a b r true true *
            hughesYoungEquation84Kernel11 t z) := by
    funext z
    exact hughesYoungEquation84PositiveContourSeries_eq_fourMoments
      T t h k a b r ha hb hr z
  rw [heq]
  have h₀₀ := (differentiableAt_const
      (c := hughesYoungEquation84PositiveArithmeticMoment a b r false false)).mul
    (differentiableAt_hughesYoungEquation84Kernel00 t hw₀ hw₁)
  have h₁₀ := (differentiableAt_const
      (c := hughesYoungEquation84PositiveArithmeticMoment a b r true false)).mul
    (differentiableAt_hughesYoungEquation84Kernel10 t hw₀ hw₁)
  have h₀₁ := (differentiableAt_const
      (c := hughesYoungEquation84PositiveArithmeticMoment a b r false true)).mul
    (differentiableAt_hughesYoungEquation84Kernel01 t hw₀ hw₁)
  have h₁₁ := (differentiableAt_const
      (c := hughesYoungEquation84PositiveArithmeticMoment a b r true true)).mul
    (differentiableAt_hughesYoungEquation84Kernel11 t hw₀ hw₁)
  exact (differentiableAt_hughesYoungEquation84PositiveOuter
    T t h k a b r w).mul (((h₀₀.add h₁₀).add h₀₁).add h₁₁)

theorem differentiableAt_hughesYoungEquation84NegativeContourSeries
    (T t : ℝ) (h k a b r : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 3 / 2) :
    DifferentiableAt ℂ
      (hughesYoungEquation84NegativeContourSeries T t h k a b r) w := by
  have heq : hughesYoungEquation84NegativeContourSeries T t h k a b r =
      fun z => hughesYoungEquation84NegativeOuter T t h k a b r z *
        (hughesYoungEquation84PositiveArithmeticMoment b a r false false *
            hughesYoungEquation84Kernel00 (-t) z +
          hughesYoungEquation84PositiveArithmeticMoment b a r true false *
            hughesYoungEquation84Kernel10 (-t) z +
          hughesYoungEquation84PositiveArithmeticMoment b a r false true *
            hughesYoungEquation84Kernel01 (-t) z +
          hughesYoungEquation84PositiveArithmeticMoment b a r true true *
            hughesYoungEquation84Kernel11 (-t) z) := by
    funext z
    exact hughesYoungEquation84NegativeContourSeries_eq_fourMoments
      T t h k a b r ha hb hr z
  rw [heq]
  have h₀₀ := (differentiableAt_const
      (c := hughesYoungEquation84PositiveArithmeticMoment b a r false false)).mul
    (differentiableAt_hughesYoungEquation84Kernel00 (-t) hw₀ hw₁)
  have h₁₀ := (differentiableAt_const
      (c := hughesYoungEquation84PositiveArithmeticMoment b a r true false)).mul
    (differentiableAt_hughesYoungEquation84Kernel10 (-t) hw₀ hw₁)
  have h₀₁ := (differentiableAt_const
      (c := hughesYoungEquation84PositiveArithmeticMoment b a r false true)).mul
    (differentiableAt_hughesYoungEquation84Kernel01 (-t) hw₀ hw₁)
  have h₁₁ := (differentiableAt_const
      (c := hughesYoungEquation84PositiveArithmeticMoment b a r true true)).mul
    (differentiableAt_hughesYoungEquation84Kernel11 (-t) hw₀ hw₁)
  exact (differentiableAt_hughesYoungEquation84NegativeOuter
    T t h k a b r w).mul (((h₀₀.add h₁₀).add h₀₁).add h₁₁)

/-- A holomorphic function on the open strip has zero integral around any
closed rectangle contained in that strip. -/
theorem boundaryRect_zero_of_differentiableOn_hughesYoungCentralStrip
    (f : ℂ → ℂ) {c₀ c₁ H : ℝ}
    (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ < 3 / 2)
    (hdiff : ∀ w : ℂ, 0 < w.re → w.re < 3 / 2 → DifferentiableAt ℂ f w) :
    (∫ x : ℝ in c₀..c₁, f ((x : ℂ) + (-H : ℂ) * I)) -
      (∫ x : ℝ in c₀..c₁, f ((x : ℂ) + (H : ℂ) * I)) +
      I • (∫ y : ℝ in -H..H, f ((c₁ : ℂ) + (y : ℂ) * I)) -
      I • (∫ y : ℝ in -H..H, f ((c₀ : ℂ) + (y : ℂ) * I)) = 0 := by
  have hrect : DifferentiableOn ℂ f ([[c₀, c₁]] ×ℂ [[-H, H]]) := by
    intro w hw
    rw [mem_reProdIm] at hw
    rw [uIcc_of_le hc] at hw
    exact (hdiff w (hc₀.trans_le hw.1.1) (hw.1.2.trans_lt hc₁)).differentiableWithinAt
  have hzero := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f ((c₀ : ℂ) - (H : ℂ) * I) ((c₁ : ℂ) + (H : ℂ) * I) (by
      simpa using hrect)
  simpa using hzero

theorem hughesYoungEquation84PositiveContourSeries_boundaryRect_zero
    (T t : ℝ) (h k a b r : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ H : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ < 3 / 2) :
    (∫ x : ℝ in c₀..c₁,
        hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((x : ℂ) + (-H : ℂ) * I)) -
      (∫ x : ℝ in c₀..c₁,
        hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((x : ℂ) + (H : ℂ) * I)) +
      I • (∫ y : ℝ in -H..H,
        hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((c₁ : ℂ) + (y : ℂ) * I)) -
      I • (∫ y : ℝ in -H..H,
        hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((c₀ : ℂ) + (y : ℂ) * I)) = 0 := by
  exact boundaryRect_zero_of_differentiableOn_hughesYoungCentralStrip _ hc₀ hc hc₁
    (fun w hw₀ hw₁ => differentiableAt_hughesYoungEquation84PositiveContourSeries
      T t h k a b r ha hb hr hw₀ hw₁)

theorem hughesYoungEquation84NegativeContourSeries_boundaryRect_zero
    (T t : ℝ) (h k a b r : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ H : ℝ} (hc₀ : 0 < c₀) (hc : c₀ ≤ c₁) (hc₁ : c₁ < 3 / 2) :
    (∫ x : ℝ in c₀..c₁,
        hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((x : ℂ) + (-H : ℂ) * I)) -
      (∫ x : ℝ in c₀..c₁,
        hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((x : ℂ) + (H : ℂ) * I)) +
      I • (∫ y : ℝ in -H..H,
        hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((c₁ : ℂ) + (y : ℂ) * I)) -
      I • (∫ y : ℝ in -H..H,
        hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((c₀ : ℂ) + (y : ℂ) * I)) = 0 := by
  exact boundaryRect_zero_of_differentiableOn_hughesYoungCentralStrip _ hc₀ hc hc₁
    (fun w hw₀ hw₁ => differentiableAt_hughesYoungEquation84NegativeContourSeries
      T t h k a b r ha hb hr hw₀ hw₁)

theorem fourFiniteDifference_norm_le
    (z₀₀ z₁₀ z₀₁ z₁₁ : ℂ)
    (B₀₀ B₁₀ B₀₁ B₁₁ E R : ℝ)
    (hB₀₀ : 0 < B₀₀) (hB₁₀ : 0 < B₁₀)
    (hB₀₁ : 0 < B₀₁) (hB₁₁ : 0 < B₁₁)
    (hE : 0 ≤ E) (hR : 0 ≤ R)
    (h₀₀ : ‖z₀₀‖ ≤ B₀₀ * E * R)
    (h₁₀ : ‖z₁₀‖ ≤ B₁₀ * E * R)
    (h₀₁ : ‖z₀₁‖ ≤ B₀₁ * E * R)
    (h₁₁ : ‖z₁₁‖ ≤ B₁₁ * E * R) :
    let B := B₁₁ + B₁₀ + B₀₁ + 3 * B₀₀
    ‖z₀₀‖ ≤ B * E * R ∧
      ‖z₁₀ - z₀₀‖ ≤ B * E * R ∧
      ‖z₀₁ - z₀₀‖ ≤ B * E * R ∧
      ‖z₁₁ - (z₁₀ - z₀₀) - (z₀₁ - z₀₀) - z₀₀‖ ≤
        B * E * R := by
  dsimp only
  have h₀₀' : ‖z₀₀‖ ≤
      (B₁₁ + B₁₀ + B₀₁ + 3 * B₀₀) * E * R := by
    calc
      _ ≤ B₀₀ * E * R := h₀₀
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hR
        apply mul_le_mul_of_nonneg_right _ hE
        linarith
  have h₁₀small : ‖z₁₀ - z₀₀‖ ≤ (B₁₀ + B₀₀) * E * R := by
    calc
      _ ≤ ‖z₁₀‖ + ‖z₀₀‖ := norm_sub_le _ _
      _ ≤ B₁₀ * E * R + B₀₀ * E * R := add_le_add h₁₀ h₀₀
      _ = _ := by ring
  have h₁₀' : ‖z₁₀ - z₀₀‖ ≤
      (B₁₁ + B₁₀ + B₀₁ + 3 * B₀₀) * E * R := by
    calc
      _ ≤ (B₁₀ + B₀₀) * E * R := h₁₀small
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hR
        apply mul_le_mul_of_nonneg_right _ hE
        linarith
  have h₀₁small : ‖z₀₁ - z₀₀‖ ≤ (B₀₁ + B₀₀) * E * R := by
    calc
      _ ≤ ‖z₀₁‖ + ‖z₀₀‖ := norm_sub_le _ _
      _ ≤ B₀₁ * E * R + B₀₀ * E * R := add_le_add h₀₁ h₀₀
      _ = _ := by ring
  have h₀₁' : ‖z₀₁ - z₀₀‖ ≤
      (B₁₁ + B₁₀ + B₀₁ + 3 * B₀₀) * E * R := by
    calc
      _ ≤ (B₀₁ + B₀₀) * E * R := h₀₁small
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hR
        apply mul_le_mul_of_nonneg_right _ hE
        linarith
  have h₁₁' :
      ‖z₁₁ - (z₁₀ - z₀₀) - (z₀₁ - z₀₀) - z₀₀‖ ≤
        (B₁₁ + B₁₀ + B₀₁ + 3 * B₀₀) * E * R := by
    calc
      _ ≤ ‖z₁₁‖ + ‖z₁₀ - z₀₀‖ +
          ‖z₀₁ - z₀₀‖ + ‖z₀₀‖ := by
        calc
          _ ≤ ‖z₁₁ - (z₁₀ - z₀₀) - (z₀₁ - z₀₀)‖ +
              ‖z₀₀‖ := norm_sub_le _ _
          _ ≤ (‖z₁₁ - (z₁₀ - z₀₀)‖ +
              ‖z₀₁ - z₀₀‖) + ‖z₀₀‖ := by
            gcongr
            exact norm_sub_le _ _
          _ ≤ ((‖z₁₁‖ + ‖z₁₀ - z₀₀‖) +
              ‖z₀₁ - z₀₀‖) + ‖z₀₀‖ := by
            gcongr
            exact norm_sub_le _ _
      _ ≤ B₁₁ * E * R + (B₁₀ + B₀₀) * E * R +
          (B₀₁ + B₀₀) * E * R + B₀₀ * E * R := by
        exact add_le_add (add_le_add (add_le_add h₁₁ h₁₀small)
          h₀₁small) h₀₀
      _ = _ := by ring
  exact ⟨h₀₀', h₁₀', h₀₁', h₁₁'⟩

set_option maxHeartbeats 2000000 in
/-- All four finite-difference kernel coefficients share one Gaussian
horizontal envelope on a fixed contour strip. -/
theorem exists_norm_hughesYoungEquation84KernelCoefficients_horizontal_le
    (t : ℝ) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    ∃ B : ℝ, 0 < B ∧ ∀ (y : ℝ), 1 ≤ |y| → |t| + 1 ≤ |y| →
      ∀ x ∈ Set.Icc c₀ c₁,
        ‖hughesYoungEquation84Kernel00 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
            B * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
              (2 + |t| + c₁ + |y|) ^ 17 ∧
        ‖hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
            B * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
              (2 + |t| + c₁ + |y|) ^ 17 ∧
        ‖hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
            B * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
              (2 + |t| + c₁ + |y|) ^ 17 ∧
        ‖hughesYoungEquation84Kernel11 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
            B * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
              (2 + |t| + c₁ + |y|) ^ 17 := by
  obtain ⟨B₀₀, hB₀₀, hb₀₀⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_horizontal_le
      t 0 0 hc₀ hc₁ hc
  obtain ⟨B₁₀, hB₁₀, hb₁₀⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_horizontal_le
      t 1 0 hc₀ hc₁ hc
  obtain ⟨B₀₁, hB₀₁, hb₀₁⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_horizontal_le
      t 0 1 hc₀ hc₁ hc
  obtain ⟨B₁₁, hB₁₁, hb₁₁⟩ :=
    exists_norm_hughesYoungEquation84RegularizedContourKernel_horizontal_le
      t 1 1 hc₀ hc₁ hc
  let B : ℝ := B₁₁ + B₁₀ + B₀₁ + 3 * B₀₀
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro y hy hty x hx
  have hc₁₀ : 0 ≤ c₁ := hc₀.le.trans hc
  have hs := fourFiniteDifference_norm_le
    (hughesYoungEquation84RegularizedContourKernel t
      ((x : ℂ) + (y : ℂ) * I) 0 0)
    (hughesYoungEquation84RegularizedContourKernel t
      ((x : ℂ) + (y : ℂ) * I) 1 0)
    (hughesYoungEquation84RegularizedContourKernel t
      ((x : ℂ) + (y : ℂ) * I) 0 1)
    (hughesYoungEquation84RegularizedContourKernel t
      ((x : ℂ) + (y : ℂ) * I) 1 1)
    B₀₀ B₁₀ B₀₁ B₁₁
    (Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2))
    ((2 + |t| + c₁ + |y|) ^ 17)
    hB₀₀ hB₁₀ hB₀₁ hB₁₁
    (by positivity) (pow_nonneg (by positivity) 17)
    (hb₀₀ y hy hty x hx) (hb₁₀ y hy hty x hx)
    (hb₀₁ y hy hty x hx) (hb₁₁ y hy hty x hx)
  simpa only [B, hughesYoungEquation84Kernel00,
    hughesYoungEquation84Kernel10, hughesYoungEquation84Kernel01,
    hughesYoungEquation84Kernel11] using hs
  /-
  set E : ℝ := Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) with hEdef
  set R : ℝ := (2 + |t| + c₁ + |y|) ^ 17 with hRdef
  have hE : 0 ≤ E := by rw [hEdef]; positivity
  have hc₁₀ : 0 ≤ c₁ := hc₀.le.trans hc
  have hR : 0 ≤ R := by rw [hRdef]; positivity
  have h₀₀ : ‖hughesYoungEquation84RegularizedContourKernel t
      ((x : ℂ) + (y : ℂ) * I) 0 0‖ ≤ B₀₀ * E * R := by
    simpa only [hEdef, hRdef] using hb₀₀ y hy hty x hx
  have h₁₀ : ‖hughesYoungEquation84RegularizedContourKernel t
      ((x : ℂ) + (y : ℂ) * I) 1 0‖ ≤ B₁₀ * E * R := by
    simpa only [hEdef, hRdef] using hb₁₀ y hy hty x hx
  have h₀₁ : ‖hughesYoungEquation84RegularizedContourKernel t
      ((x : ℂ) + (y : ℂ) * I) 0 1‖ ≤ B₀₁ * E * R := by
    simpa only [hEdef, hRdef] using hb₀₁ y hy hty x hx
  have h₁₁ : ‖hughesYoungEquation84RegularizedContourKernel t
      ((x : ℂ) + (y : ℂ) * I) 1 1‖ ≤ B₁₁ * E * R := by
    simpa only [hEdef, hRdef] using hb₁₁ y hy hty x hx
  have hk₀₀ : ‖hughesYoungEquation84Kernel00 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
      B * E * R := by
    unfold hughesYoungEquation84Kernel00
    calc
      _ ≤ B₀₀ * E * R := h₀₀
      _ ≤ B * E * R := by
        gcongr
        dsimp [B]
        linarith [hB₁₁, hB₁₀, hB₀₁, hB₀₀]
  have hk₁₀small : ‖hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
      (B₁₀ + B₀₀) * E * R := by
    unfold hughesYoungEquation84Kernel10 hughesYoungEquation84Kernel00
    calc
      _ ≤ ‖hughesYoungEquation84RegularizedContourKernel t
          ((x : ℂ) + (y : ℂ) * I) 1 0‖ +
        ‖hughesYoungEquation84RegularizedContourKernel t
          ((x : ℂ) + (y : ℂ) * I) 0 0‖ := norm_sub_le _ _
      _ ≤ (B₁₀ + B₀₀) * E * R := by
        calc
          _ ≤ B₁₀ * E * R + B₀₀ * E * R := add_le_add h₁₀ h₀₀
          _ = _ := by ring
  have hk₁₀ : ‖hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
      B * E * R := by
    calc
      _ ≤ (B₁₀ + B₀₀) * E * R := hk₁₀small
      _ ≤ B * E * R := by
        gcongr
        dsimp [B]
        linarith [hB₁₁, hB₁₀, hB₀₁, hB₀₀]
  have hk₀₁small : ‖hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
      (B₀₁ + B₀₀) * E * R := by
    unfold hughesYoungEquation84Kernel01 hughesYoungEquation84Kernel00
    calc
      _ ≤ ‖hughesYoungEquation84RegularizedContourKernel t
          ((x : ℂ) + (y : ℂ) * I) 0 1‖ +
        ‖hughesYoungEquation84RegularizedContourKernel t
          ((x : ℂ) + (y : ℂ) * I) 0 0‖ := norm_sub_le _ _
      _ ≤ (B₀₁ + B₀₀) * E * R := by
        calc
          _ ≤ B₀₁ * E * R + B₀₀ * E * R := add_le_add h₀₁ h₀₀
          _ = _ := by ring
  have hk₀₁ : ‖hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
      B * E * R := by
    calc
      _ ≤ (B₀₁ + B₀₀) * E * R := hk₀₁small
      _ ≤ B * E * R := by
        gcongr
        dsimp [B]
        linarith [hB₁₁, hB₁₀, hB₀₁, hB₀₀]
  have hk₁₁ : ‖hughesYoungEquation84Kernel11 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
      B * E * R := by
    unfold hughesYoungEquation84Kernel11
    calc
      _ ≤ ‖hughesYoungEquation84RegularizedContourKernel t
          ((x : ℂ) + (y : ℂ) * I) 1 1‖ +
        ‖hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I)‖ +
        ‖hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I)‖ +
        ‖hughesYoungEquation84Kernel00 t ((x : ℂ) + (y : ℂ) * I)‖ := by
          calc
            _ ≤ ‖hughesYoungEquation84RegularizedContourKernel t
                ((x : ℂ) + (y : ℂ) * I) 1 1 -
              hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I) -
              hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I)‖ +
              ‖hughesYoungEquation84Kernel00 t ((x : ℂ) + (y : ℂ) * I)‖ := norm_sub_le _ _
            _ ≤ _ := by
              have hsub := norm_sub_le
                (hughesYoungEquation84RegularizedContourKernel t
                  ((x : ℂ) + (y : ℂ) * I) 1 1 -
                  hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I))
                (hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I))
              have hfirst := norm_sub_le
                (hughesYoungEquation84RegularizedContourKernel t
                  ((x : ℂ) + (y : ℂ) * I) 1 1)
                (hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I))
              linarith
      _ ≤ B₁₁ * E * R +
          (B₁₀ + B₀₀) * E * R +
          (B₀₁ + B₀₀) * E * R + B₀₀ * E * R := by
        exact add_le_add (add_le_add (add_le_add h₁₁ hk₁₀small)
          hk₀₁small) h₀₀
      _ = B * E * R := by
        dsimp [B]
        ring
  exact ⟨by simpa only [hEdef, hRdef] using hk₀₀,
    by simpa only [hEdef, hRdef] using hk₁₀,
    by simpa only [hEdef, hRdef] using hk₀₁,
    by simpa only [hEdef, hRdef] using hk₁₁⟩
  -/

private theorem norm_mul_fourTerm_le
    (P a₀₀ a₁₀ a₀₁ a₁₁ z₀₀ z₁₀ z₀₁ z₁₁ : ℂ)
    (K B E R : ℝ) (hK : ‖P‖ ≤ K) (hK₀ : 0 ≤ K)
    (hz₀₀ : ‖z₀₀‖ ≤ B * E * R) (hz₁₀ : ‖z₁₀‖ ≤ B * E * R)
    (hz₀₁ : ‖z₀₁‖ ≤ B * E * R) (hz₁₁ : ‖z₁₁‖ ≤ B * E * R) :
    ‖P * (a₀₀ * z₀₀ + a₁₀ * z₁₀ + a₀₁ * z₀₁ + a₁₁ * z₁₁)‖ ≤
      (K * (1 + ‖a₀₀‖ + ‖a₁₀‖ + ‖a₀₁‖ + ‖a₁₁‖) * B) * E * R := by
  rw [norm_mul]
  have hinside :
      ‖a₀₀ * z₀₀ + a₁₀ * z₁₀ + a₀₁ * z₀₁ + a₁₁ * z₁₁‖ ≤
        (1 + ‖a₀₀‖ + ‖a₁₀‖ + ‖a₀₁‖ + ‖a₁₁‖) *
          (B * E * R) := by
    calc
      _ ≤ ‖a₀₀‖ * ‖z₀₀‖ + ‖a₁₀‖ * ‖z₁₀‖ +
          ‖a₀₁‖ * ‖z₀₁‖ + ‖a₁₁‖ * ‖z₁₁‖ := by
        calc
          _ ≤ ‖a₀₀ * z₀₀ + a₁₀ * z₁₀ + a₀₁ * z₀₁‖ +
              ‖a₁₁ * z₁₁‖ := norm_add_le _ _
          _ ≤ (‖a₀₀ * z₀₀ + a₁₀ * z₁₀‖ +
              ‖a₀₁ * z₀₁‖) + ‖a₁₁ * z₁₁‖ := by
            gcongr
            exact norm_add_le _ _
          _ ≤ ((‖a₀₀ * z₀₀‖ + ‖a₁₀ * z₁₀‖) +
              ‖a₀₁ * z₀₁‖) + ‖a₁₁ * z₁₁‖ := by
            gcongr
            exact norm_add_le _ _
          _ = _ := by simp only [norm_mul]
      _ ≤ ‖a₀₀‖ * (B * E * R) + ‖a₁₀‖ * (B * E * R) +
          ‖a₀₁‖ * (B * E * R) + ‖a₁₁‖ * (B * E * R) := by
        gcongr
      _ ≤ (1 + ‖a₀₀‖ + ‖a₁₀‖ + ‖a₀₁‖ + ‖a₁₁‖) *
          (B * E * R) := by
        have hBER : 0 ≤ B * E * R := le_trans (norm_nonneg _) hz₀₀
        nlinarith
  calc
    _ ≤ K * ((1 + ‖a₀₀‖ + ‖a₁₀‖ + ‖a₀₁‖ + ‖a₁₁‖) *
        (B * E * R)) := mul_le_mul hK hinside (norm_nonneg _) hK₀
    _ = _ := by ring

set_option maxHeartbeats 2000000 in
theorem exists_norm_hughesYoungEquation84PositiveContourSeries_horizontal_le
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ), 1 ≤ |y| → |t| + 1 ≤ |y| →
      ∀ x ∈ Set.Icc c₀ c₁,
        ‖hughesYoungEquation84PositiveContourSeries T t h k a b r
            ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
            (2 + |t| + c₁ + |y|) ^ 17 := by
  obtain ⟨K, hK, hOuter⟩ := exists_uniform_norm_hughesYoungCentralOuterFactor
    T t h k r (((a : ℂ) * b)⁻¹) (c₀ := c₀) (c₁ := c₁)
  obtain ⟨B, hB, hCoeff⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_horizontal_le
      t hc₀ hc₁ hc
  let m₀₀ := ‖hughesYoungEquation84PositiveArithmeticMoment a b r false false‖
  let m₁₀ := ‖hughesYoungEquation84PositiveArithmeticMoment a b r true false‖
  let m₀₁ := ‖hughesYoungEquation84PositiveArithmeticMoment a b r false true‖
  let m₁₁ := ‖hughesYoungEquation84PositiveArithmeticMoment a b r true true‖
  let M : ℝ := 1 + m₀₀ + m₁₀ + m₀₁ + m₁₁
  let C : ℝ := K * M * B
  have hM : 0 < M := by dsimp [M, m₀₀, m₁₀, m₀₁, m₁₁]; positivity
  refine ⟨C, mul_pos (mul_pos hK hM) hB, ?_⟩
  intro y hy hty x hx
  have ho : ‖hughesYoungEquation84PositiveOuter T t h k a b r
      ((x : ℂ) + (y : ℂ) * I)‖ ≤ K := by
    simpa only [hughesYoungEquation84PositiveOuter] using hOuter y x hx
  rcases hCoeff y hy hty x hx with ⟨hk₀₀, hk₁₀, hk₀₁, hk₁₁⟩
  rw [hughesYoungEquation84PositiveContourSeries_eq_fourMoments
    T t h k a b r ha hb hr]
  have hbound := norm_mul_fourTerm_le
    (hughesYoungEquation84PositiveOuter T t h k a b r
      ((x : ℂ) + (y : ℂ) * I))
    (hughesYoungEquation84PositiveArithmeticMoment a b r false false)
    (hughesYoungEquation84PositiveArithmeticMoment a b r true false)
    (hughesYoungEquation84PositiveArithmeticMoment a b r false true)
    (hughesYoungEquation84PositiveArithmeticMoment a b r true true)
    (hughesYoungEquation84Kernel00 t ((x : ℂ) + (y : ℂ) * I))
    (hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I))
    (hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I))
    (hughesYoungEquation84Kernel11 t ((x : ℂ) + (y : ℂ) * I))
    K B (Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2))
    ((2 + |t| + c₁ + |y|) ^ 17) ho hK.le
    hk₀₀ hk₁₀ hk₀₁ hk₁₁
  simpa only [C, M, m₀₀, m₁₀, m₀₁, m₁₁] using hbound
  /-
  have ho := hOuter y x hx
  have hk := hCoeff y hy hty x hx
  have heq := hughesYoungEquation84PositiveContourSeries_eq_fourMoments
    T t h k a b r ha hb hr ((x : ℂ) + (y : ℂ) * I)
  rw [heq, norm_mul]
  have ho' : ‖hughesYoungEquation84PositiveOuter T t h k a b r
      ((x : ℂ) + (y : ℂ) * I)‖ ≤ K := by
    simpa only [hughesYoungEquation84PositiveOuter] using ho
  set E : ℝ := Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) with hEdef
  set R : ℝ := (2 + |t| + c₁ + |y|) ^ 17 with hRdef
  have hE : 0 ≤ E := by rw [hEdef]; positivity
  have hc₁0 : 0 ≤ c₁ := hc₀.le.trans hc
  have hR : 0 ≤ R := by
    rw [hRdef]
    exact pow_nonneg (by positivity) 17
  have hinside :
      ‖hughesYoungEquation84PositiveArithmeticMoment a b r false false *
            hughesYoungEquation84Kernel00 t ((x : ℂ) + (y : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment a b r true false *
            hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment a b r false true *
            hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment a b r true true *
            hughesYoungEquation84Kernel11 t ((x : ℂ) + (y : ℂ) * I)‖ ≤
        M * (B * E * R) := by
    calc
      _ ≤ m₀₀ * ‖hughesYoungEquation84Kernel00 t ((x : ℂ) + (y : ℂ) * I)‖ +
          m₁₀ * ‖hughesYoungEquation84Kernel10 t ((x : ℂ) + (y : ℂ) * I)‖ +
          m₀₁ * ‖hughesYoungEquation84Kernel01 t ((x : ℂ) + (y : ℂ) * I)‖ +
          m₁₁ * ‖hughesYoungEquation84Kernel11 t ((x : ℂ) + (y : ℂ) * I)‖ := by
            dsimp [m₀₀, m₁₀, m₀₁, m₁₁]
            calc
              _ ≤ ‖_ + _ + _‖ + ‖_‖ := norm_add_le _ _
              _ ≤ (‖_ + _‖ + ‖_‖) + ‖_‖ := by gcongr; exact norm_add_le _ _
              _ ≤ ((‖_‖ + ‖_‖) + ‖_‖) + ‖_‖ := by gcongr; exact norm_add_le _ _
              _ = _ := by simp only [norm_mul]
      _ ≤ (m₀₀ + m₁₀ + m₀₁ + m₁₁) * (B * E * R) := by
        rcases hk with ⟨hk₀₀, hk₁₀, hk₀₁, hk₁₁⟩
        rw [← hEdef, ← hRdef] at hk₀₀ hk₁₀ hk₀₁ hk₁₁
        calc
          _ ≤ m₀₀ * (B * E * R) + m₁₀ * (B * E * R) +
              m₀₁ * (B * E * R) + m₁₁ * (B * E * R) := by gcongr
          _ = _ := by ring
      _ ≤ M * (B * E * R) := by
        gcongr
        dsimp [M]
        linarith
  calc
    _ ≤ K * (M * (B * E * R)) := mul_le_mul ho' hinside (norm_nonneg _) hK.le
    _ = C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
        (2 + |t| + c₁ + |y|) ^ 17 := by
      rw [← hEdef, ← hRdef]
      dsimp [C]
      ring
  -/

set_option maxHeartbeats 2000000 in
theorem exists_norm_hughesYoungEquation84NegativeContourSeries_horizontal_le
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : ℝ), 1 ≤ |y| → |t| + 1 ≤ |y| →
      ∀ x ∈ Set.Icc c₀ c₁,
        ‖hughesYoungEquation84NegativeContourSeries T t h k a b r
            ((x : ℂ) + (y : ℂ) * I)‖ ≤
          C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
            (2 + |t| + c₁ + |y|) ^ 17 := by
  obtain ⟨K, hK, hOuter⟩ := exists_uniform_norm_hughesYoungCentralOuterFactor
    T t h k r (((b : ℂ) * a)⁻¹) (c₀ := c₀) (c₁ := c₁)
  obtain ⟨B, hB, hCoeff⟩ :=
    exists_norm_hughesYoungEquation84KernelCoefficients_horizontal_le
      (-t) hc₀ hc₁ hc
  let m₀₀ := ‖hughesYoungEquation84PositiveArithmeticMoment b a r false false‖
  let m₁₀ := ‖hughesYoungEquation84PositiveArithmeticMoment b a r true false‖
  let m₀₁ := ‖hughesYoungEquation84PositiveArithmeticMoment b a r false true‖
  let m₁₁ := ‖hughesYoungEquation84PositiveArithmeticMoment b a r true true‖
  let M : ℝ := 1 + m₀₀ + m₁₀ + m₀₁ + m₁₁
  let C : ℝ := K * M * B
  have hM : 0 < M := by dsimp [M, m₀₀, m₁₀, m₀₁, m₁₁]; positivity
  refine ⟨C, mul_pos (mul_pos hK hM) hB, ?_⟩
  intro y hy hty x hx
  have ho : ‖hughesYoungEquation84NegativeOuter T t h k a b r
      ((x : ℂ) + (y : ℂ) * I)‖ ≤ K := by
    simpa only [hughesYoungEquation84NegativeOuter] using hOuter y x hx
  rcases hCoeff y hy (by simpa only [abs_neg] using hty) x hx with
    ⟨hk₀₀, hk₁₀, hk₀₁, hk₁₁⟩
  simp only [abs_neg] at hk₀₀ hk₁₀ hk₀₁ hk₁₁
  rw [hughesYoungEquation84NegativeContourSeries_eq_fourMoments
    T t h k a b r ha hb hr]
  have hbound := norm_mul_fourTerm_le
    (hughesYoungEquation84NegativeOuter T t h k a b r
      ((x : ℂ) + (y : ℂ) * I))
    (hughesYoungEquation84PositiveArithmeticMoment b a r false false)
    (hughesYoungEquation84PositiveArithmeticMoment b a r true false)
    (hughesYoungEquation84PositiveArithmeticMoment b a r false true)
    (hughesYoungEquation84PositiveArithmeticMoment b a r true true)
    (hughesYoungEquation84Kernel00 (-t) ((x : ℂ) + (y : ℂ) * I))
    (hughesYoungEquation84Kernel10 (-t) ((x : ℂ) + (y : ℂ) * I))
    (hughesYoungEquation84Kernel01 (-t) ((x : ℂ) + (y : ℂ) * I))
    (hughesYoungEquation84Kernel11 (-t) ((x : ℂ) + (y : ℂ) * I))
    K B (Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2))
    ((2 + |t| + c₁ + |y|) ^ 17) ho hK.le
    hk₀₀ hk₁₀ hk₀₁ hk₁₁
  simpa only [C, M, m₀₀, m₁₀, m₀₁, m₁₁] using hbound
  /-
  have ho := hOuter y x hx
  have hk := hCoeff y hy (by simpa only [abs_neg] using hty) x hx
  have heq := hughesYoungEquation84NegativeContourSeries_eq_fourMoments
    T t h k a b r ha hb hr ((x : ℂ) + (y : ℂ) * I)
  rw [heq, norm_mul]
  have ho' : ‖hughesYoungEquation84NegativeOuter T t h k a b r
      ((x : ℂ) + (y : ℂ) * I)‖ ≤ K := by
    simpa only [hughesYoungEquation84NegativeOuter] using ho
  set E : ℝ := Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) with hEdef
  set R : ℝ := (2 + |t| + c₁ + |y|) ^ 17 with hRdef
  have hE : 0 ≤ E := by rw [hEdef]; positivity
  have hc₁0 : 0 ≤ c₁ := hc₀.le.trans hc
  have hR : 0 ≤ R := by
    rw [hRdef]
    exact pow_nonneg (by positivity) 17
  have hinside :
      ‖hughesYoungEquation84PositiveArithmeticMoment b a r false false *
            hughesYoungEquation84Kernel00 (-t) ((x : ℂ) + (y : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment b a r true false *
            hughesYoungEquation84Kernel10 (-t) ((x : ℂ) + (y : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment b a r false true *
            hughesYoungEquation84Kernel01 (-t) ((x : ℂ) + (y : ℂ) * I) +
          hughesYoungEquation84PositiveArithmeticMoment b a r true true *
            hughesYoungEquation84Kernel11 (-t) ((x : ℂ) + (y : ℂ) * I)‖ ≤
        M * (B * E * R) := by
    calc
      _ ≤ m₀₀ * ‖hughesYoungEquation84Kernel00 (-t) ((x : ℂ) + (y : ℂ) * I)‖ +
          m₁₀ * ‖hughesYoungEquation84Kernel10 (-t) ((x : ℂ) + (y : ℂ) * I)‖ +
          m₀₁ * ‖hughesYoungEquation84Kernel01 (-t) ((x : ℂ) + (y : ℂ) * I)‖ +
          m₁₁ * ‖hughesYoungEquation84Kernel11 (-t) ((x : ℂ) + (y : ℂ) * I)‖ := by
            dsimp [m₀₀, m₁₀, m₀₁, m₁₁]
            calc
              _ ≤ ‖_ + _ + _‖ + ‖_‖ := norm_add_le _ _
              _ ≤ (‖_ + _‖ + ‖_‖) + ‖_‖ := by gcongr; exact norm_add_le _ _
              _ ≤ ((‖_‖ + ‖_‖) + ‖_‖) + ‖_‖ := by gcongr; exact norm_add_le _ _
              _ = _ := by simp only [norm_mul]
      _ ≤ (m₀₀ + m₁₀ + m₀₁ + m₁₁) * (B * E * R) := by
        rcases hk with ⟨hk₀₀, hk₁₀, hk₀₁, hk₁₁⟩
        simp only [abs_neg] at hk₀₀ hk₁₀ hk₀₁ hk₁₁
        rw [← hEdef, ← hRdef] at hk₀₀ hk₁₀ hk₀₁ hk₁₁
        calc
          _ ≤ m₀₀ * (B * E * R) + m₁₀ * (B * E * R) +
              m₀₁ * (B * E * R) + m₁₁ * (B * E * R) := by gcongr
          _ = _ := by ring
      _ ≤ M * (B * E * R) := by
        gcongr
        dsimp [M]
        linarith
  calc
    _ ≤ K * (M * (B * E * R)) := mul_le_mul ho' hinside (norm_nonneg _) hK.le
    _ = C * Real.exp (100 * c₁ ^ 2 - 60 * y ^ 2) *
        (2 + |t| + c₁ + |y|) ^ 17 := by
      rw [← hEdef, ← hRdef]
      dsimp [C]
      ring
  -/

theorem tendsto_hughesYoungEquation84PositiveContourSeries_top_zero
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ => HIntegral
      (hughesYoungEquation84PositiveContourSeries T t h k a b r) c₀ c₁ H)
      atTop (nhds 0) := by
  exact tendsto_HIntegral_top_zero_of_central_horizontal_bound
    _ t c₀ c₁ hc₀ hc
      (exists_norm_hughesYoungEquation84PositiveContourSeries_horizontal_le
        T t h k a b r ha hb hr hc₀ hc₁ hc)

theorem tendsto_hughesYoungEquation84PositiveContourSeries_bottom_zero
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ => HIntegral
      (hughesYoungEquation84PositiveContourSeries T t h k a b r) c₀ c₁ (-H))
      atTop (nhds 0) := by
  exact tendsto_HIntegral_bottom_zero_of_central_horizontal_bound
    _ t c₀ c₁ hc₀ hc
      (exists_norm_hughesYoungEquation84PositiveContourSeries_horizontal_le
        T t h k a b r ha hb hr hc₀ hc₁ hc)

theorem tendsto_hughesYoungEquation84NegativeContourSeries_top_zero
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ => HIntegral
      (hughesYoungEquation84NegativeContourSeries T t h k a b r) c₀ c₁ H)
      atTop (nhds 0) := by
  exact tendsto_HIntegral_top_zero_of_central_horizontal_bound
    _ t c₀ c₁ hc₀ hc
      (exists_norm_hughesYoungEquation84NegativeContourSeries_horizontal_le
        T t h k a b r ha hb hr hc₀ hc₁ hc)

theorem tendsto_hughesYoungEquation84NegativeContourSeries_bottom_zero
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ => HIntegral
      (hughesYoungEquation84NegativeContourSeries T t h k a b r) c₀ c₁ (-H))
      atTop (nhds 0) := by
  exact tendsto_HIntegral_bottom_zero_of_central_horizontal_bound
    _ t c₀ c₁ hc₀ hc
      (exists_norm_hughesYoungEquation84NegativeContourSeries_horizontal_le
        T t h k a b r ha hb hr hc₀ hc₁ hc)

/-- Hughes--Young's full positive-shift arithmetic series can be moved between
any two vertical lines in the regularized central strip.  This is a statement
about the complete absolutely convergent modulus series, not a fixed-modulus
surrogate. -/
theorem tendsto_hughesYoungEquation84PositiveContourSeries_vertical_sub_zero
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ =>
      (∫ u in -H..H, hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((c₁ : ℂ) + (u : ℂ) * I)) -
      (∫ u in -H..H, hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((c₀ : ℂ) + (u : ℂ) * I)))
      atTop (nhds 0) := by
  exact tendsto_vertical_sub_zero_of_boundaryRect _ c₀ c₁
    (fun H => hughesYoungEquation84PositiveContourSeries_boundaryRect_zero
      T t h k a b r ha hb hr hc₀ hc hc₁)
    (tendsto_hughesYoungEquation84PositiveContourSeries_top_zero
      T t h k a b r ha hb hr hc₀ hc₁ hc)
    (tendsto_hughesYoungEquation84PositiveContourSeries_bottom_zero
      T t h k a b r ha hb hr hc₀ hc₁ hc)

/-- The corresponding complete negative-shift arithmetic series has the same
regularized contour-shift identity. -/
theorem tendsto_hughesYoungEquation84NegativeContourSeries_vertical_sub_zero
    (T t : ℝ) (h k a b r : ℕ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₁ < 3 / 2) (hc : c₀ ≤ c₁) :
    Tendsto (fun H : ℝ =>
      (∫ u in -H..H, hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((c₁ : ℂ) + (u : ℂ) * I)) -
      (∫ u in -H..H, hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((c₀ : ℂ) + (u : ℂ) * I)))
      atTop (nhds 0) := by
  exact tendsto_vertical_sub_zero_of_boundaryRect _ c₀ c₁
    (fun H => hughesYoungEquation84NegativeContourSeries_boundaryRect_zero
      T t h k a b r ha hb hr hc₀ hc hc₁)
    (tendsto_hughesYoungEquation84NegativeContourSeries_top_zero
      T t h k a b r ha hb hr hc₀ hc₁ hc)
    (tendsto_hughesYoungEquation84NegativeContourSeries_bottom_zero
      T t h k a b r ha hb hr hc₀ hc₁ hc)

end RiemannZeta.GuthMaynard
