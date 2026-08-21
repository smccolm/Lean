import RiemannZeta.GuthMaynard.HughesYoungEquation96LogSummability
import RiemannZeta.GuthMaynard.HughesYoungCentralExpansion

open Complex
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The complete DFI central arithmetic series on the Hughes--Young source line

The contour in Hughes--Young equation (84) is moved to `Re w = 1` before
the shift and modulus sums are rearranged.  These lemmas identify the two
DFI logarithmic factors and the DFI arithmetic coefficient with the
corresponding equation-(96) summand.  In particular, the fixed twist terms
`-log h` and `-log k` are retained.
-/

private theorem complex_log_reduced_denominator
    {a q : ℕ} (hq : 0 < q) :
    Complex.log (q : ℂ) =
      Complex.log (Nat.gcd a q : ℂ) +
        Complex.log (dfiReducedDenominator a q : ℂ) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let R := dfiReducedModulus a q
  have hg : 0 < R.gcd := R.gcd_pos
  have hd : 0 < R.denominator := R.denominator_pos
  have hrec : R.gcd * R.denominator = q := R.denominator_reconstruct
  have hlogR : Real.log (q : ℝ) =
      Real.log (R.gcd : ℝ) + Real.log (R.denominator : ℝ) := by
    rw [show (q : ℝ) = (R.gcd : ℝ) * (R.denominator : ℝ) by
      exact_mod_cast hrec.symm]
    exact Real.log_mul (by exact_mod_cast hg.ne') (by exact_mod_cast hd.ne')
  simpa only [Complex.natCast_log, Complex.ofReal_add] using
    congrArg (fun x : ℝ => (x : ℂ)) hlogR

private theorem complex_log_reduced_denominator_eq_sub
    {a q : ℕ} (hq : 0 < q) :
    Complex.log (dfiReducedDenominator a q : ℂ) =
      Complex.log (q : ℂ) - Complex.log (Nat.gcd a q : ℂ) := by
  have hlog := complex_log_reduced_denominator (a := a) hq
  calc
    Complex.log (dfiReducedDenominator a q : ℂ) =
        (Complex.log (Nat.gcd a q : ℂ) +
          Complex.log (dfiReducedDenominator a q : ℂ)) -
            Complex.log (Nat.gcd a q : ℂ) := by ring
    _ = Complex.log (q : ℂ) - Complex.log (Nat.gcd a q : ℂ) :=
      congrArg (fun z : ℂ => z - Complex.log (Nat.gcd a q : ℂ)) hlog.symm

private theorem dfi_log_constant_eq_equation96_factor
    (a r : ℕ) {q : ℕ} (hq : 0 < q) :
    (Real.log r : ℂ) +
        dfiEquation27LogConstant a (dfiReducedDenominator a q) =
      (Real.log r : ℂ) + 2 * Real.eulerMascheroniConstant +
        2 * (Complex.log (Nat.gcd a q : ℂ) - Complex.log (q : ℂ)) -
          Complex.log (a : ℂ) := by
  have hden := complex_log_reduced_denominator_eq_sub (a := a) hq
  unfold dfiEquation27LogConstant
  rw [hden]
  ring

/-- The first DFI equation-(84) logarithm is the first corrected
equation-(96) differential eigenvalue. -/
theorem hughesYoungEquation84PositiveCOne_eq_dfiPositiveLogFactorLeft
    (h : ℕ) (y : ℕ+ × ℕ+) :
    hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) =
      hughesYoungDFIPositiveLogFactorLeft h y := by
  simpa only [hughesYoungEquation84PositiveCOne,
    hughesYoungDFIPositiveLogFactorLeft,
    hughesYoungEquation96PositiveLogR,
    hughesYoungEquation96PositiveLogA, Complex.natCast_log] using
      dfi_log_constant_eq_equation96_factor h (y.2 : ℕ) y.1.2

/-- The second DFI equation-(84) logarithm is the second corrected
equation-(96) differential eigenvalue. -/
theorem hughesYoungEquation84PositiveCX_eq_dfiPositiveLogFactorRight
    (k : ℕ) (y : ℕ+ × ℕ+) :
    hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) =
      hughesYoungDFIPositiveLogFactorRight k y := by
  simpa only [hughesYoungEquation84PositiveCX,
    hughesYoungDFIPositiveLogFactorRight,
    hughesYoungEquation96PositiveLogR,
    hughesYoungEquation96PositiveLogB, Complex.natCast_log] using
      dfi_log_constant_eq_equation96_factor k (y.2 : ℕ) y.1.2

/-- The DFI coefficient with its `r⁻²` source-line factor is exactly the
unshifted equation-(96) positive summand. -/
theorem dfiEquation27ArithmeticCoefficient_div_sq_eq_equation96PositiveTerm
    {h k : ℕ} (hhk : h.Coprime k)
    (y : ℕ+ × ℕ+) :
    dfiEquation27ArithmeticCoefficient h k (y.2 : ℕ) (y.1 : ℕ) /
        (((y.2 : ℕ) : ℂ) ^ 2) =
      hughesYoungEquation96PositiveTerm h k 1 1 2 y := by
  letI : NeZero (y.1 : ℕ) := ⟨y.1.2.ne'⟩
  rw [dfiEquation27ArithmeticCoefficient_eq_hughesYoung96 hhk]
  unfold hughesYoungEquation96PositiveTerm
  simp only [Complex.cpow_one]
  rw [show (1 : ℂ) + 1 = (2 : ℕ) by norm_num, Complex.cpow_natCast]
  rw [show ((2 : ℂ) : ℂ) = (2 : ℕ) by norm_num, Complex.cpow_natCast]
  have hq : (((y.1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast y.1.2.ne'
  have hr : (((y.2 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast y.2.2.ne'
  field_simp [hq, hr]

/-- Exact termwise form of the twice-logarithmic DFI central arithmetic
series on the absolutely convergent Hughes--Young source line. -/
theorem dfiEquation84PositiveArithmeticTerm_eq_equation96LogTerm
    {h k : ℕ} (hhk : h.Coprime k)
    (y : ℕ+ × ℕ+) :
    (dfiEquation27ArithmeticCoefficient h k (y.2 : ℕ) (y.1 : ℕ) /
        (((y.2 : ℕ) : ℂ) ^ 2)) *
        hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) *
        hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) =
      hughesYoungEquation96PositiveTerm h k 1 1 2 y *
        hughesYoungDFIPositiveLogFactorRight k y *
        hughesYoungDFIPositiveLogFactorLeft h y := by
  rw [dfiEquation27ArithmeticCoefficient_div_sq_eq_equation96PositiveTerm
    hhk y,
    hughesYoungEquation84PositiveCX_eq_dfiPositiveLogFactorRight k y,
    hughesYoungEquation84PositiveCOne_eq_dfiPositiveLogFactorLeft h y]

/-- The complete twice-logarithmic DFI arithmetic series is absolutely
summable on the source line `Re w = 1`. -/
theorem summable_dfiEquation84PositiveArithmeticTerm
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Summable (fun y : ℕ+ × ℕ+ =>
      (dfiEquation27ArithmeticCoefficient h k (y.2 : ℕ) (y.1 : ℕ) /
          (((y.2 : ℕ) : ℂ) ^ 2)) *
        hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) *
        hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ)) := by
  have hs := summable_hughesYoungEquation96PositiveTerm_mul_dfiLogFactors
    hh hk hη hη4
  apply hs.congr
  intro y
  rw [dfiEquation84PositiveArithmeticTerm_eq_equation96LogTerm hhk y]
  ring

/-- The complete positive-shift arithmetic factor appearing after the
equation-(84) contour has reached `Re w = 1`. -/
noncomputable def hughesYoungEquation84CompletePositiveArithmetic
    (h k : ℕ) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    (dfiEquation27ArithmeticCoefficient h k (y.2 : ℕ) (y.1 : ℕ) /
        (((y.2 : ℕ) : ℂ) ^ 2)) *
      hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) *
      hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ)

/-- Exact equation-(96) representation of the complete twice-logarithmic
DFI arithmetic factor. -/
theorem hughesYoungEquation84CompletePositiveArithmetic_eq_equation96
    {h k : ℕ} (hhk : h.Coprime k) :
    hughesYoungEquation84CompletePositiveArithmetic h k =
      ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1 2 y *
          hughesYoungDFIPositiveLogFactorLeft h y *
          hughesYoungDFIPositiveLogFactorRight k y := by
  unfold hughesYoungEquation84CompletePositiveArithmetic
  apply tsum_congr
  intro y
  rw [dfiEquation84PositiveArithmeticTerm_eq_equation96LogTerm hhk y]
  ring

/-- Source-strength twist-uniform bound for the complete DFI arithmetic
factor.  The exponent is `1/2 + 3η` on each twist, with `η` arbitrarily
small. -/
theorem norm_hughesYoungEquation84CompletePositiveArithmetic_le
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖hughesYoungEquation84CompletePositiveArithmetic h k‖ ≤
      (((h : ℝ) ^ (1 / 2 + 2 * η) * (k : ℝ) ^ (1 / 2 + 2 * η)) *
          (6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        ∑' y : ℕ+ × ℕ+,
          hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y := by
  rw [hughesYoungEquation84CompletePositiveArithmetic_eq_equation96 hhk]
  exact norm_tsum_hughesYoungEquation96PositiveTerm_mul_dfiLogFactors_le
    hh hk hη hη4

/-- The four complete arithmetic moments used by the bilinear expansion
of the regularized equation-(84) kernel.  The first Boolean selects `CX`
(the right twist) and the second selects `COne` (the left twist). -/
noncomputable def hughesYoungEquation84CompletePositiveMoment
    (h k : ℕ) (i j : Bool) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    (dfiEquation27ArithmeticCoefficient h k (y.2 : ℕ) (y.1 : ℕ) /
        (((y.2 : ℕ) : ℂ) ^ 2)) *
      (if i then hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) else 1) *
      (if j then hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) else 1)

theorem dfiEquation84PositiveMomentTerm_eq_equation96SelectorTerm
    (i j : Bool) {h k : ℕ} (hhk : h.Coprime k) (y : ℕ+ × ℕ+) :
    (dfiEquation27ArithmeticCoefficient h k (y.2 : ℕ) (y.1 : ℕ) /
        (((y.2 : ℕ) : ℂ) ^ 2)) *
      (if i then hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) else 1) *
      (if j then hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) else 1) =
    hughesYoungEquation96PositiveTerm h k 1 1 2 y *
      hughesYoungDFIPositiveLogSelectorLeft j h y *
      hughesYoungDFIPositiveLogSelectorRight i k y := by
  rw [dfiEquation27ArithmeticCoefficient_div_sq_eq_equation96PositiveTerm hhk y]
  have hCX :
      (if i then hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) else 1) =
        hughesYoungDFIPositiveLogSelectorRight i k y := by
    cases i
    · simp [hughesYoungDFIPositiveLogSelectorRight]
    · simp [hughesYoungDFIPositiveLogSelectorRight,
        hughesYoungEquation84PositiveCX_eq_dfiPositiveLogFactorRight k y]
  have hCOne :
      (if j then hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) else 1) =
        hughesYoungDFIPositiveLogSelectorLeft j h y := by
    cases j
    · simp [hughesYoungDFIPositiveLogSelectorLeft]
    · simp [hughesYoungDFIPositiveLogSelectorLeft,
        hughesYoungEquation84PositiveCOne_eq_dfiPositiveLogFactorLeft h y]
  rw [hCX, hCOne]
  ring

theorem hughesYoungEquation84CompletePositiveMoment_eq_equation96
    (i j : Bool) {h k : ℕ} (hhk : h.Coprime k) :
    hughesYoungEquation84CompletePositiveMoment h k i j =
      ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1 2 y *
          hughesYoungDFIPositiveLogSelectorLeft j h y *
          hughesYoungDFIPositiveLogSelectorRight i k y := by
  unfold hughesYoungEquation84CompletePositiveMoment
  apply tsum_congr
  exact dfiEquation84PositiveMomentTerm_eq_equation96SelectorTerm i j hhk

theorem summable_dfiEquation84PositiveMomentTerm
    (i j : Bool) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Summable (fun y : ℕ+ × ℕ+ =>
      (dfiEquation27ArithmeticCoefficient h k (y.2 : ℕ) (y.1 : ℕ) /
          (((y.2 : ℕ) : ℂ) ^ 2)) *
        (if i then hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) else 1) *
        (if j then hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) else 1)) := by
  have hs := summable_hughesYoungEquation96PositiveTerm_mul_logSelectors
    j i hh hk hη hη4
  exact hs.congr fun y =>
    (dfiEquation84PositiveMomentTerm_eq_equation96SelectorTerm i j hhk y).symm

theorem norm_hughesYoungEquation84CompletePositiveMoment_le
    (i j : Bool) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖hughesYoungEquation84CompletePositiveMoment h k i j‖ ≤
      (((h : ℝ) ^ (1 / 2 + 2 * η) * (k : ℝ) ^ (1 / 2 + 2 * η)) *
          (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        ∑' y : ℕ+ × ℕ+,
          hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y := by
  rw [hughesYoungEquation84CompletePositiveMoment_eq_equation96 i j hhk]
  exact norm_tsum_hughesYoungEquation96PositiveTerm_mul_logSelectors_le
    j i hh hk hη hη4

/-- Vertical-source-line version of the DFI coefficient bridge. -/
theorem dfiEquation27ArithmeticCoefficient_div_vertical_cpow_eq_equation96PositiveTerm
    (u : ℝ) {h k : ℕ} (hhk : h.Coprime k) (y : ℕ+ × ℕ+) :
    dfiEquation27ArithmeticCoefficient h k (y.2 : ℕ) (y.1 : ℕ) /
        (((y.2 : ℕ) : ℂ) ^ ((2 : ℂ) + (2 * u : ℂ) * I)) =
      hughesYoungEquation96PositiveTerm h k 1 1
        ((2 : ℂ) + (2 * u : ℂ) * I) y := by
  letI : NeZero (y.1 : ℕ) := ⟨y.1.2.ne'⟩
  rw [dfiEquation27ArithmeticCoefficient_eq_hughesYoung96 hhk]
  unfold hughesYoungEquation96PositiveTerm
  simp only [Complex.cpow_one]
  rw [show (1 : ℂ) + 1 = (2 : ℕ) by norm_num, Complex.cpow_natCast]
  have hq : (((y.1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast y.1.2.ne'
  have hrpow : (((y.2 : ℕ) : ℂ) ^
      ((2 : ℂ) + (2 * u : ℂ) * I)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast y.2.2.ne'))
  field_simp [hq, hrpow]

noncomputable def hughesYoungEquation84CompletePositiveMomentAt
    (h k : ℕ) (i j : Bool) (u : ℝ) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    (dfiEquation27ArithmeticCoefficient h k (y.2 : ℕ) (y.1 : ℕ) /
        (((y.2 : ℕ) : ℂ) ^ ((2 : ℂ) + (2 * u : ℂ) * I))) *
      (if i then hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) else 1) *
      (if j then hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) else 1)

theorem hughesYoungEquation84CompletePositiveMomentAt_eq_equation96
    (i j : Bool) (u : ℝ) {h k : ℕ} (hhk : h.Coprime k) :
    hughesYoungEquation84CompletePositiveMomentAt h k i j u =
      ∑' y : ℕ+ × ℕ+,
        hughesYoungEquation96PositiveTerm h k 1 1
            ((2 : ℂ) + (2 * u : ℂ) * I) y *
          hughesYoungDFIPositiveLogSelectorLeft j h y *
          hughesYoungDFIPositiveLogSelectorRight i k y := by
  unfold hughesYoungEquation84CompletePositiveMomentAt
  apply tsum_congr
  intro y
  rw [dfiEquation27ArithmeticCoefficient_div_vertical_cpow_eq_equation96PositiveTerm
    u hhk y]
  have hCX :
      (if i then hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) else 1) =
        hughesYoungDFIPositiveLogSelectorRight i k y := by
    cases i
    · simp [hughesYoungDFIPositiveLogSelectorRight]
    · simp [hughesYoungDFIPositiveLogSelectorRight,
        hughesYoungEquation84PositiveCX_eq_dfiPositiveLogFactorRight k y]
  have hCOne :
      (if j then hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) else 1) =
        hughesYoungDFIPositiveLogSelectorLeft j h y := by
    cases j
    · simp [hughesYoungDFIPositiveLogSelectorLeft]
    · simp [hughesYoungDFIPositiveLogSelectorLeft,
        hughesYoungEquation84PositiveCOne_eq_dfiPositiveLogFactorLeft h y]
  rw [hCX, hCOne]
  ring

/-- Termwise vertical-line version of the equation-(96) selector bridge. -/
theorem dfiEquation84PositiveMomentAtTerm_eq_equation96SelectorTerm
    (i j : Bool) (u : ℝ) {h k : ℕ} (hhk : h.Coprime k)
    (y : ℕ+ × ℕ+) :
    (dfiEquation27ArithmeticCoefficient h k (y.2 : ℕ) (y.1 : ℕ) /
        (((y.2 : ℕ) : ℂ) ^ ((2 : ℂ) + (2 * u : ℂ) * I))) *
      (if i then hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) else 1) *
      (if j then hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) else 1) =
      hughesYoungEquation96PositiveTerm h k 1 1
          ((2 : ℂ) + (2 * u : ℂ) * I) y *
        hughesYoungDFIPositiveLogSelectorLeft j h y *
        hughesYoungDFIPositiveLogSelectorRight i k y := by
  rw [dfiEquation27ArithmeticCoefficient_div_vertical_cpow_eq_equation96PositiveTerm
    u hhk y]
  have hCX :
      (if i then hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) else 1) =
        hughesYoungDFIPositiveLogSelectorRight i k y := by
    cases i
    · simp [hughesYoungDFIPositiveLogSelectorRight]
    · simp [hughesYoungDFIPositiveLogSelectorRight,
        hughesYoungEquation84PositiveCX_eq_dfiPositiveLogFactorRight k y]
  have hCOne :
      (if j then hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) else 1) =
        hughesYoungDFIPositiveLogSelectorLeft j h y := by
    cases j
    · simp [hughesYoungDFIPositiveLogSelectorLeft]
    · simp [hughesYoungDFIPositiveLogSelectorLeft,
        hughesYoungEquation84PositiveCOne_eq_dfiPositiveLogFactorLeft h y]
  rw [hCX, hCOne]
  ring

theorem summable_dfiEquation84PositiveMomentAtTerm
    (i j : Bool) (u : ℝ) {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Summable (fun y : ℕ+ × ℕ+ =>
      (dfiEquation27ArithmeticCoefficient h k (y.2 : ℕ) (y.1 : ℕ) /
          (((y.2 : ℕ) : ℂ) ^ ((2 : ℂ) + (2 * u : ℂ) * I))) *
        (if i then hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) else 1) *
        (if j then hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) else 1)) := by
  have hs := summable_hughesYoungEquation96VerticalTerm_mul_logSelectors
    j i u hh hk hη hη4
  apply hs.congr
  intro y
  rw [dfiEquation27ArithmeticCoefficient_div_vertical_cpow_eq_equation96PositiveTerm
    u hhk y]
  have hCX :
      (if i then hughesYoungEquation84PositiveCX k (y.2 : ℕ) (y.1 : ℕ) else 1) =
        hughesYoungDFIPositiveLogSelectorRight i k y := by
    cases i
    · simp [hughesYoungDFIPositiveLogSelectorRight]
    · simp [hughesYoungDFIPositiveLogSelectorRight,
        hughesYoungEquation84PositiveCX_eq_dfiPositiveLogFactorRight k y]
  have hCOne :
      (if j then hughesYoungEquation84PositiveCOne h (y.2 : ℕ) (y.1 : ℕ) else 1) =
        hughesYoungDFIPositiveLogSelectorLeft j h y := by
    cases j
    · simp [hughesYoungDFIPositiveLogSelectorLeft]
    · simp [hughesYoungDFIPositiveLogSelectorLeft,
        hughesYoungEquation84PositiveCOne_eq_dfiPositiveLogFactorLeft h y]
  rw [hCX, hCOne]
  ring

theorem norm_hughesYoungEquation84CompletePositiveMomentAt_le
    (i j : Bool) (u : ℝ) {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖hughesYoungEquation84CompletePositiveMomentAt h k i j u‖ ≤
      (((h : ℝ) ^ (1 / 2 + 2 * η) * (k : ℝ) ^ (1 / 2 + 2 * η)) *
          (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        ∑' y : ℕ+ × ℕ+,
          hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y := by
  rw [hughesYoungEquation84CompletePositiveMomentAt_eq_equation96 i j u hhk]
  exact norm_tsum_hughesYoungEquation96VerticalTerm_mul_logSelectors_le
    j i u hh hk hη hη4

end RiemannZeta.GuthMaynard
