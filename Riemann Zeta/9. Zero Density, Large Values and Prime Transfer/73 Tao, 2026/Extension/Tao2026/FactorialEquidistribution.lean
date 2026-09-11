import Tao2026.FactorialShortIntervals
import Tao2026.VeryBadEquidistribution
import Tao2026.FourierRadial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The equidistribution obstruction for short type-`F₃` intervals

This module begins the large-`P` branch of Tao's Lemma 4.2.  A point in the
final arc `{N/p} ≥ 1-H/p` supplies an element of `(N,N+H]` divisible by `p`.
For a type-`F₃` interval and `P = H log² N > √(2N)`, the arithmetic developed
in `FactorialShortIntervals` says that no prime in `(P,2P)` can divide the
interval product.  Hence every periodic weight supported on those divisor
points has an identically zero prime sum, ready for Theorem 2.5.
-/

open Filter Set MeasureTheory
open scoped ContDiff

namespace Tao2026

noncomputable section

/-- The same forbidden residue rectangle used in Lemma 3.1 is impossible
for a type-`F₃` interval as soon as the prime lies above both the interval
length and the factorial index. -/
theorem not_forbiddenResidues_of_factorialThree
    {N H a p : ℕ}
    (hcomponent : squarefreeComponent (consecutiveProduct N H) =
      squarefreeComponent a.factorial)
    (hp : p.Prime) (hHltp : H < p) (haLtp : a < p)
    (hpLe : p ≤ 2 * H) :
    ¬InVeryBadForbiddenResidueRegion N p := by
  intro hregion
  obtain ⟨h, hhPos, hhLe, hpDvd, hpSqNotDvd⟩ :=
    exists_nonsquare_intervalElement_of_forbiddenResidues hp hHltp hpLe hregion
  have hk : N + h ∈ consecutiveInterval N H := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    omega
  have hpNotDvdFactorial : ¬p ∣ a.factorial := by
    rw [hp.dvd_factorial, not_le]
    exact haLtp
  exact hpSqNotDvd
    (prime_sq_dvd_intervalElement_of_factorialThree
      hcomponent hk hp hHltp hpDvd hpNotDvdFactorial)

/-- If the quadratic fractional coordinate is below `9/10`, an interval
element of length at most `H` cannot be divisible by `p²` once `p²>10H`.
This is the local arithmetic obstruction needed in the low-`P` branch. -/
theorem not_prime_sq_dvd_add_of_quadraticFract_lt_nineTenths
    {N H h p : ℕ} (hp : 0 < p) (hh : 1 ≤ h) (hhH : h ≤ H)
    (hlarge : 10 * H < p ^ 2)
    (hfract : Int.fract ((N : ℝ) / ((p ^ 2 : ℕ) : ℝ)) < 9 / 10) :
    ¬p ^ 2 ∣ N + h := by
  intro hpSqDvd
  have hpSqPos : 0 < p ^ 2 := pow_pos hp 2
  have hpSqReal : (0 : ℝ) < (p ^ 2 : ℕ) := by exact_mod_cast hpSqPos
  rw [Int.fract_div_natCast_eq_div_natCast_mod,
    div_lt_iff₀ hpSqReal] at hfract
  have hresidue : 10 * (N % (p ^ 2)) < 9 * (p ^ 2) := by
    exact_mod_cast (show
      (10 : ℝ) * (N % (p ^ 2) : ℕ) < 9 * (p ^ 2 : ℕ) by nlinarith)
  have hsumLt : N % (p ^ 2) + h < p ^ 2 := by
    omega
  have hrewrite :
      N + h = (N % (p ^ 2) + h) + p ^ 2 * (N / p ^ 2) := by
    have hdecomp := Nat.mod_add_div N (p ^ 2)
    omega
  have hpSqDvdSmall : p ^ 2 ∣ N % (p ^ 2) + h := by
    rw [hrewrite] at hpSqDvd
    exact (Nat.dvd_add_iff_left
      (dvd_mul_right (p ^ 2) (N / p ^ 2))).mpr hpSqDvd
  have hsumPos : 0 < N % (p ^ 2) + h := by omega
  exact (not_lt_of_ge (Nat.le_of_dvd hsumPos hpSqDvdSmall)) hsumLt

/-- The final fractional arc which detects a multiple of `p` in `(N,N+H]`. -/
def InFactorialDivisorFractionalRegion (N H p : ℕ) : Prop :=
  1 - (H : ℝ) / (p : ℝ) ≤ Int.fract ((N : ℝ) / (p : ℝ))

/-- If `p>H` and `{N/p}` lies in the final arc of length `H/p`, then one of
`N+1, …, N+H` is divisible by `p`. -/
theorem exists_intervalElement_dvd_of_factorialDivisorFractionalRegion
    {N H p : ℕ} (hp : 0 < p) (hHltp : H < p)
    (hregion : InFactorialDivisorFractionalRegion N H p) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ p ∣ N + h := by
  let r := N % p
  let h := p - r
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have hrLt : r < p := Nat.mod_lt N hp
  have hHltpReal : (H : ℝ) < p := by exact_mod_cast hHltp
  have hregion' :
      1 - (H : ℝ) / (p : ℝ) ≤ (r : ℝ) / (p : ℝ) := by
    simpa only [InFactorialDivisorFractionalRegion, r,
      Int.fract_div_natCast_eq_div_natCast_mod] using hregion
  have hrPos : 0 < r := by
    have hlowerPos : 0 < 1 - (H : ℝ) / (p : ℝ) := by
      rw [sub_pos, div_lt_one hpReal]
      exact hHltpReal
    have hratioPos : 0 < (r : ℝ) / (p : ℝ) :=
      lt_of_lt_of_le hlowerPos hregion'
    by_contra hnot
    have hrZero : r = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hrZero] at hratioPos
  have hhPos : 1 ≤ h := by
    dsimp [h]
    omega
  have hdiffLeReal : (p : ℝ) - H ≤ r := by
    have hscaled := mul_le_mul_of_nonneg_right hregion' hpReal.le
    field_simp at hscaled
    nlinarith
  have hpLeReal : (p : ℝ) ≤ r + H := by linarith
  have hpLe : p ≤ r + H := by exact_mod_cast hpLeReal
  have hhLe : h ≤ H := by
    dsimp [h]
    omega
  have hpDvd : p ∣ N + h := by
    refine ⟨N / p + 1, ?_⟩
    rw [mul_add, mul_one]
    have hdecomp := Nat.mod_add_div N p
    dsimp [h, r]
    omega
  exact ⟨h, hhPos, hhLe, hpDvd⟩

/-- The shrinking final arc used in Tao's large-`P` cutoff.  The numerical
factor `10` leaves room between the cutoff support and the divisor arc. -/
def IsSupportedInFactorialFinalArc
    (N : ℕ) (W : ℝ × ℝ → ℂ) : Prop :=
  ∀ x y : ℝ, W (x, y) ≠ 0 →
    1 - 1 / (10 * (Real.log N) ^ 2) ≤ Int.fract x

/-- The two-coordinate support condition for the low-`P` branch: the first
coordinate detects a divisor in the original length-`H` interval, while the
second excludes divisibility by the square of that prime. -/
def IsSupportedInFactorialLowObstruction
    (N : ℕ) (W : ℝ × ℝ → ℂ) : Prop :=
  ∀ x y : ℝ, W (x, y) ≠ 0 →
    1 - 1 / (10 * (Real.log N) ^ 2) ≤ Int.fract x ∧
      Int.fract y < 9 / 10

/-- General left-end support property of the periodic smooth bump. -/
theorem fract_ge_left_of_smoothPeriodicIntervalBump_ne_zero
    {a x : ℝ} (haLtOne : a < 1)
    (hx : smoothPeriodicIntervalBump a 1 x ≠ 0) :
    a ≤ Int.fract x := by
  let f := Int.fract x
  have heq : smoothPeriodicIntervalBump a 1 x =
      smoothPeriodicIntervalBump a 1 f := by
    simpa only [f, Int.fract_add_floor] using
      smoothPeriodicIntervalBump_add_int a 1 f ⌊x⌋
  have hfne : smoothPeriodicIntervalBump a 1 f ≠ 0 := by
    rwa [heq] at hx
  have hproductPos :
      0 < Real.sin (Real.pi * (f - a)) *
        Real.sin (Real.pi * (1 - f)) := by
    apply lt_of_not_ge
    intro hnonpos
    exact hfne (expNegInvGlue.zero_of_nonpos hnonpos)
  have hfNonneg : 0 ≤ f := Int.fract_nonneg x
  have hfLtOne : f < 1 := Int.fract_lt_one x
  by_contra hnot
  have hfLt : f < a := lt_of_not_ge hnot
  have hfirstNonpos : Real.sin (Real.pi * (f - a)) ≤ 0 := by
    have hz : Real.pi * (a - f) ∈ Icc 0 Real.pi := by
      constructor
      · positivity
      · nlinarith [Real.pi_pos]
    have hsin := Real.sin_nonneg_of_mem_Icc hz
    rw [show Real.pi * (f - a) = -(Real.pi * (a - f)) by ring,
      Real.sin_neg]
    linarith
  have hsecondNonneg : 0 ≤ Real.sin (Real.pi * (1 - f)) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg
    hfirstNonpos hsecondNonneg)) hproductPos

/-- An explicit one-coordinate smooth cutoff supported on the high-`P` arc.
Its normalization and quantitative mass-to-`C³` ratio are deliberately not
asserted here. -/
def factorialFinalArcSmoothCutoff (N : ℕ) (z : ℝ × ℝ) : ℂ :=
  (smoothPeriodicIntervalBump
    (1 - 1 / (10 * (Real.log N) ^ 2)) 1 z.1 : ℝ)

theorem factorialFinalArcSmoothCutoff_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (factorialFinalArcSmoothCutoff N) := by
  rw [contDiff_infty]
  intro n
  have hn : (n : ℕ∞) < ∞ := WithTop.coe_lt_coe.mpr (ENat.coe_lt_top n)
  have hx : ContDiff ℝ n (fun z : ℝ × ℝ =>
      smoothPeriodicIntervalBump
        (1 - 1 / (10 * (Real.log N) ^ 2)) 1 z.1) :=
    ((smoothPeriodicIntervalBump_contDiff
      (1 - 1 / (10 * (Real.log N) ^ 2)) 1).of_le hn.le).comp
        contDiff_fst
  simpa only [factorialFinalArcSmoothCutoff, Function.comp_apply,
    Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp hx

theorem factorialFinalArcSmoothCutoff_isZ2Periodic (N : ℕ) :
    IsZ2Periodic (factorialFinalArcSmoothCutoff N) := by
  intro x y m n
  unfold factorialFinalArcSmoothCutoff
  rw [smoothPeriodicIntervalBump_add_int]

theorem factorialFinalArcSmoothCutoff_re_nonneg (N : ℕ) (z : ℝ × ℝ) :
    0 ≤ (factorialFinalArcSmoothCutoff N z).re := by
  simp only [factorialFinalArcSmoothCutoff, Complex.ofReal_re]
  exact expNegInvGlue.nonneg _

theorem factorialFinalArcSmoothCutoff_supported
    {N : ℕ} (hlog : 1 < Real.log (N : ℝ)) :
    IsSupportedInFactorialFinalArc N (factorialFinalArcSmoothCutoff N) := by
  intro x y hne
  have hlogSq : (1 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by nlinarith
  have hdenPos : (0 : ℝ) < 10 * (Real.log (N : ℝ)) ^ 2 := by positivity
  have hrecipPos : (0 : ℝ) < 1 / (10 * (Real.log (N : ℝ)) ^ 2) := by
    exact one_div_pos.mpr hdenPos
  apply fract_ge_left_of_smoothPeriodicIntervalBump_ne_zero (by linarith)
  simpa only [factorialFinalArcSmoothCutoff, Complex.ofReal_ne_zero] using hne

/-- Left endpoint of the plateau arc in Tao's high-`P` cutoff. -/
def factorialPlateauArcLeft (N : ℕ) : ℝ :=
  1 - 1 / (20 * (Real.log N) ^ 2)

/-- Right endpoint of the plateau arc in Tao's high-`P` cutoff. -/
def factorialPlateauArcRight (N : ℕ) : ℝ :=
  1 - 1 / (30 * (Real.log N) ^ 2)

/-- Exact quantitative specification of the one-dimensional cutoff used in
the high-`P` argument. -/
structure IsFactorialPlateauWeight (N : ℕ) (w : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ w
  periodic : Function.Periodic w 1
  nonneg : ∀ x : ℝ, 0 ≤ w x
  supported : ∀ x : ℝ, w x ≠ 0 →
    1 - 1 / (10 * (Real.log N) ^ 2) ≤ Int.fract x
  plateau : ∀ x : ℝ,
    factorialPlateauArcLeft N ≤ Int.fract x →
    Int.fract x ≤ factorialPlateauArcRight N → w x = 1

/-- Periodic sine-product profile, normalized so that it is at least one on
Tao's inner plateau arc. -/
def factorialPlateauProfile (N : ℕ) (x : ℝ) : ℝ :=
  150 * (Real.log N) ^ 4 *
    (Real.sin (Real.pi *
      (x - (1 - 1 / (10 * (Real.log N) ^ 2)))) *
      Real.sin (Real.pi * (1 - x)))

/-- Smooth normalized plateau weight for the high-`P` argument. -/
def factorialNormalizedPlateauWeight (N : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (factorialPlateauProfile N x)

/-- The left sine factor in the normalized plateau profile. -/
def factorialPlateauLeftSine (N : ℕ) (x : ℝ) : ℝ :=
  Real.sin (Real.pi *
    (x - (1 - 1 / (10 * (Real.log N) ^ 2))))

/-- The right sine factor in the normalized plateau profile. -/
def factorialPlateauRightSine (x : ℝ) : ℝ :=
  Real.sin (Real.pi * (1 - x))

theorem factorialPlateauProfile_eq_sineProduct (N : ℕ) :
    factorialPlateauProfile N = fun x =>
      150 * (Real.log N) ^ 4 *
        (factorialPlateauLeftSine N x * factorialPlateauRightSine x) := by
  rfl

theorem factorialPlateauLeftSine_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (factorialPlateauLeftSine N) := by
  unfold factorialPlateauLeftSine
  fun_prop

theorem factorialPlateauRightSine_contDiff :
    ContDiff ℝ ∞ factorialPlateauRightSine := by
  unfold factorialPlateauRightSine
  fun_prop

/-- Translation does not affect the derivative bounds for the left sine
factor; its `i`-th derivative has norm at most `π^i`. -/
theorem norm_iteratedFDeriv_factorialPlateauLeftSine_le
    (N i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ i (factorialPlateauLeftSine N) x‖ ≤ Real.pi ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  let a : ℝ := 1 - 1 / (10 * (Real.log N) ^ 2)
  let f : ℝ → ℝ := fun z => Real.sin (Real.pi * z)
  have hshift :
      iteratedDeriv i (factorialPlateauLeftSine N) x =
        iteratedDeriv i f (x - a) := by
    simpa only [factorialPlateauLeftSine, a, f] using
      congrFun (iteratedDeriv_comp_sub_const i f a) x
  have hscale :
      iteratedDeriv i f (x - a) =
        Real.pi ^ i * iteratedDeriv i Real.sin (Real.pi * (x - a)) := by
    simpa only [f, smul_eq_mul] using
      congrFun (iteratedDeriv_comp_const_mul
        (n := i) (Real.contDiff_sin.of_le le_rfl) Real.pi) (x - a)
  rw [hshift, hscale, norm_mul, Real.norm_of_nonneg (pow_nonneg Real.pi_pos.le i)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.abs_iteratedDeriv_sin_le_one i (Real.pi * (x - a)))
    (pow_nonneg Real.pi_pos.le i)

/-- The reflected right sine factor obeys the same derivative bound. -/
theorem norm_iteratedFDeriv_factorialPlateauRightSine_le
    (i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ i factorialPlateauRightSine x‖ ≤ Real.pi ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  let f : ℝ → ℝ := fun z => Real.sin (Real.pi * z)
  have hreflect :
      iteratedDeriv i factorialPlateauRightSine x =
        (-1 : ℝ) ^ i * iteratedDeriv i f (1 - x) := by
    simpa only [factorialPlateauRightSine, f, smul_eq_mul] using
      congrFun (iteratedDeriv_comp_const_sub i f 1) x
  have hscale :
      iteratedDeriv i f (1 - x) =
        Real.pi ^ i * iteratedDeriv i Real.sin (Real.pi * (1 - x)) := by
    simpa only [f, smul_eq_mul] using
      congrFun (iteratedDeriv_comp_const_mul
        (n := i) (Real.contDiff_sin.of_le le_rfl) Real.pi) (1 - x)
  rw [hreflect, hscale, norm_mul]
  simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [norm_mul, Real.norm_of_nonneg (pow_nonneg Real.pi_pos.le i)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (Real.abs_iteratedDeriv_sin_le_one i (Real.pi * (1 - x)))
    (pow_nonneg Real.pi_pos.le i)

theorem norm_iteratedFDeriv_factorialPlateauLeftSine_le_four_pow
    (N i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ i (factorialPlateauLeftSine N) x‖ ≤ (4 : ℝ) ^ i := by
  calc
    ‖iteratedFDeriv ℝ i (factorialPlateauLeftSine N) x‖ ≤ Real.pi ^ i :=
      norm_iteratedFDeriv_factorialPlateauLeftSine_le N i x
    _ ≤ (4 : ℝ) ^ i := by gcongr; exact Real.pi_le_four

theorem norm_iteratedFDeriv_factorialPlateauRightSine_le_four_pow
    (i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ i factorialPlateauRightSine x‖ ≤ (4 : ℝ) ^ i := by
  calc
    ‖iteratedFDeriv ℝ i factorialPlateauRightSine x‖ ≤ Real.pi ^ i :=
      norm_iteratedFDeriv_factorialPlateauRightSine_le i x
    _ ≤ (4 : ℝ) ^ i := by gcongr; exact Real.pi_le_four

/-- The product before normalization has the elementary uniform derivative
bound `8^i`, obtained from Leibniz and the binomial theorem. -/
theorem norm_iteratedFDeriv_factorialPlateauSineProduct_le
    (N i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ i (fun y =>
      factorialPlateauLeftSine N y * factorialPlateauRightSine y) x‖ ≤
        (8 : ℝ) ^ i := by
  calc
    ‖iteratedFDeriv ℝ i (fun y =>
        factorialPlateauLeftSine N y * factorialPlateauRightSine y) x‖ ≤
        ∑ k ∈ Finset.range (i + 1),
          (i.choose k : ℝ) *
            ‖iteratedFDeriv ℝ k (factorialPlateauLeftSine N) x‖ *
            ‖iteratedFDeriv ℝ (i - k) factorialPlateauRightSine x‖ := by
      exact norm_iteratedFDeriv_mul_le
        (factorialPlateauLeftSine_contDiff N)
        factorialPlateauRightSine_contDiff x (mod_cast le_top)
    _ ≤ ∑ k ∈ Finset.range (i + 1),
          (i.choose k : ℝ) * (4 : ℝ) ^ k * (4 : ℝ) ^ (i - k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hleft :=
        norm_iteratedFDeriv_factorialPlateauLeftSine_le_four_pow N k x
      have hright :=
        norm_iteratedFDeriv_factorialPlateauRightSine_le_four_pow (i - k) x
      gcongr
    _ = (8 : ℝ) ^ i := by
      simpa only [show (8 : ℝ) = 4 + 4 by norm_num,
        mul_comm, mul_left_comm, mul_assoc] using
        (add_pow (4 : ℝ) 4 i).symm

/-- Before composing with `smoothTransition`, every derivative of the
plateau profile is bounded by its height times `8^i`. -/
theorem norm_iteratedFDeriv_factorialPlateauProfile_le
    (N i : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ i (factorialPlateauProfile N) x‖ ≤
      150 * (Real.log N) ^ 4 * (8 : ℝ) ^ i := by
  let c : ℝ := 150 * (Real.log N) ^ 4
  let f : ℝ → ℝ := fun y =>
    factorialPlateauLeftSine N y * factorialPlateauRightSine y
  have hf : ContDiffAt ℝ i f x :=
    (((factorialPlateauLeftSine_contDiff N).mul
      factorialPlateauRightSine_contDiff).of_le (mod_cast le_top)).contDiffAt
  have heq : iteratedFDeriv ℝ i (factorialPlateauProfile N) x =
      c • iteratedFDeriv ℝ i f x := by
    rw [factorialPlateauProfile_eq_sineProduct]
    simpa only [c, f, smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply' (a := c) hf)
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  calc
    ‖iteratedFDeriv ℝ i (factorialPlateauProfile N) x‖ =
        c * ‖iteratedFDeriv ℝ i f x‖ := by
      rw [heq, norm_smul, Real.norm_of_nonneg hc]
    _ ≤ c * (8 : ℝ) ^ i := by
      apply mul_le_mul_of_nonneg_left _ hc
      exact norm_iteratedFDeriv_factorialPlateauSineProduct_le N i x
    _ = 150 * (Real.log N) ^ 4 * (8 : ℝ) ^ i := by rfl

/-- Every fixed derivative of the scalar transition function is globally
bounded.  Compactness handles `[0,1]`; off that interval the function is
locally constant. -/
theorem exists_smoothTransition_iteratedFDeriv_bound (i : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
      ‖iteratedFDeriv ℝ i Real.smoothTransition x‖ ≤ B := by
  have hcontinuous : Continuous fun x : ℝ =>
      ‖iteratedFDeriv ℝ i Real.smoothTransition x‖ :=
    (Real.smoothTransition.contDiff.continuous_iteratedFDeriv
      (mod_cast le_top)).norm
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcontinuous.continuousOn
  refine ⟨max 1 B, by positivity, fun x => ?_⟩
  by_cases hx0 : x < 0
  · have heq : Real.smoothTransition =ᶠ[nhds x] (0 : ℝ → ℝ) := by
      filter_upwards [Iio_mem_nhds hx0] with y hy
      simpa only [Pi.zero_apply] using
        Real.smoothTransition.zero_of_nonpos hy.le
    have hzero : iteratedFDeriv ℝ i Real.smoothTransition x = 0 := by
      rw [(heq.iteratedFDeriv ℝ i).self_of_nhds]
      simp
    rw [hzero, norm_zero]
    positivity
  · by_cases hx1 : x ≤ 1
    · exact (hB (mem_image_of_mem _ ⟨le_of_not_gt hx0, hx1⟩)).trans
        (le_max_right _ _)
    · have hx1' : 1 < x := lt_of_not_ge hx1
      have heq : Real.smoothTransition =ᶠ[nhds x] fun _ : ℝ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hx1'] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      rw [(heq.iteratedFDeriv ℝ i).self_of_nhds]
      apply le_trans (b := 1)
      · cases i with
        | zero => simp [norm_iteratedFDeriv_zero]
        | succ i => simp [iteratedFDeriv_const_of_ne]
      · exact le_max_left _ _

/-- One constant controls all four derivatives of `smoothTransition` used by
Tao's `C³` norm. -/
theorem exists_smoothTransition_C3_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i < 4, ∀ x : ℝ,
      ‖iteratedFDeriv ℝ i Real.smoothTransition x‖ ≤ B := by
  choose B hBnonneg hBbound using
    fun i : ℕ => exists_smoothTransition_iteratedFDeriv_bound i
  refine ⟨1 + ∑ i ∈ Finset.range 4, B i, ?_, ?_⟩
  · have hsum : 0 ≤ ∑ i ∈ Finset.range 4, B i := by
      exact Finset.sum_nonneg fun i _hi => hBnonneg i
    linarith
  · intro i hi x
    calc
      ‖iteratedFDeriv ℝ i Real.smoothTransition x‖ ≤ B i := hBbound i x
      _ ≤ ∑ j ∈ Finset.range 4, B j := by
        exact Finset.single_le_sum (fun j _hj => hBnonneg j)
          (Finset.mem_range.mpr hi)
      _ ≤ 1 + ∑ j ∈ Finset.range 4, B j := by linarith

/-- The profile derivatives of positive order through three fit the single
scale `1200 log⁴ N`, in the power form required by the quantitative chain
rule. -/
theorem norm_iteratedFDeriv_factorialPlateauProfile_le_scale_pow
    {N i : ℕ} (hlog : 1 ≤ Real.log (N : ℝ)) (hiPos : 1 ≤ i) (hi : i ≤ 3)
    (x : ℝ) :
    ‖iteratedFDeriv ℝ i (factorialPlateauProfile N) x‖ ≤
      (1200 * (Real.log N) ^ 4) ^ i := by
  have hprofile := norm_iteratedFDeriv_factorialPlateauProfile_le N i x
  have hlogPow : 1 ≤ (Real.log (N : ℝ)) ^ 4 :=
    one_le_pow₀ hlog
  have hselfPow : (Real.log (N : ℝ)) ^ 4 ≤
      ((Real.log (N : ℝ)) ^ 4) ^ i := by
    simpa only [pow_one] using pow_le_pow_right₀ hlogPow hiPos
  have hcoeff : 150 * (8 : ℝ) ^ i ≤ (1200 : ℝ) ^ i := by
    interval_cases i <;> norm_num
  calc
    ‖iteratedFDeriv ℝ i (factorialPlateauProfile N) x‖ ≤
        150 * (Real.log N) ^ 4 * (8 : ℝ) ^ i := hprofile
    _ = (150 * (8 : ℝ) ^ i) * (Real.log N) ^ 4 := by ring
    _ ≤ (1200 : ℝ) ^ i * ((Real.log N) ^ 4) ^ i := by
      gcongr
    _ = (1200 * (Real.log N) ^ 4) ^ i := by rw [mul_pow]

/-- Quantitative chain-rule bound for the normalized one-dimensional
plateau weight.  The deliberately coarse exponent `12` is uniform in `N`
and is enough for Theorem 2.5 with a larger logarithmic saving. -/
theorem norm_iteratedFDeriv_factorialNormalizedPlateauWeight_le
    {B : ℝ} (hB : 1 ≤ B)
    (htransition : ∀ i < 4, ∀ x : ℝ,
      ‖iteratedFDeriv ℝ i Real.smoothTransition x‖ ≤ B)
    {N i : ℕ} (hlog : 1 ≤ Real.log (N : ℝ)) (hi : i < 4) (x : ℝ) :
    ‖iteratedFDeriv ℝ i (factorialNormalizedPlateauWeight N) x‖ ≤
      6 * B * (1200 * (Real.log N) ^ 4) ^ 3 := by
  let D : ℝ := 1200 * (Real.log N) ^ 4
  have hD : 1 ≤ D := by
    dsimp only [D]
    have hpow : 1 ≤ (Real.log (N : ℝ)) ^ 4 :=
      one_le_pow₀ hlog
    nlinarith
  have hcomp :
      ‖iteratedFDeriv ℝ i
          (Real.smoothTransition ∘ factorialPlateauProfile N) x‖ ≤
        (Nat.factorial i : ℝ) * B * D ^ i := by
    exact norm_iteratedFDeriv_comp_le
      Real.smoothTransition.contDiff (by
        unfold factorialPlateauProfile
        fun_prop)
      (mod_cast le_top) x
      (fun j hj => htransition j (lt_of_le_of_lt hj hi)
        (factorialPlateauProfile N x))
      (fun j hjPos hj =>
        norm_iteratedFDeriv_factorialPlateauProfile_le_scale_pow
          hlog hjPos (le_trans hj (Nat.le_of_lt_succ hi)) x)
  have hfactorial : (Nat.factorial i : ℝ) ≤ 6 := by
    interval_cases i <;> norm_num
  have hpow : D ^ i ≤ D ^ 3 :=
    pow_le_pow_right₀ hD (Nat.le_of_lt_succ hi)
  unfold factorialNormalizedPlateauWeight
  change ‖iteratedFDeriv ℝ i
    (Real.smoothTransition ∘ factorialPlateauProfile N) x‖ ≤ _
  calc
    ‖iteratedFDeriv ℝ i
        (Real.smoothTransition ∘ factorialPlateauProfile N) x‖ ≤
        (Nat.factorial i : ℝ) * B * D ^ i := hcomp
    _ ≤ 6 * B * D ^ 3 := by gcongr
    _ = 6 * B * (1200 * (Real.log N) ^ 4) ^ 3 := by rfl

theorem factorialPlateauProfile_add_int
    (N : ℕ) (x : ℝ) (m : ℤ) :
    factorialPlateauProfile N (x + m) = factorialPlateauProfile N x := by
  unfold factorialPlateauProfile
  have hfirst :
      Real.pi * (x + (m : ℝ) -
        (1 - 1 / (10 * (Real.log N) ^ 2))) =
        Real.pi * (x - (1 - 1 / (10 * (Real.log N) ^ 2))) +
          (m : ℝ) * Real.pi := by ring
  have hsecond : Real.pi * (1 - (x + (m : ℝ))) =
      Real.pi * (1 - x) - (m : ℝ) * Real.pi := by ring
  rw [hfirst, Real.sin_add_int_mul_pi, hsecond, Real.sin_sub_int_mul_pi]
  have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    have habs : |(-1 : ℝ) ^ m| = 1 := abs_neg_one_zpow m
    have hsquare := sq_abs ((-1 : ℝ) ^ m)
    rw [habs] at hsquare
    nlinarith
  have hsign' : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [pow_two, hsign]
  ring_nf
  rw [hsign']
  ring

theorem factorialPlateauProfile_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (factorialPlateauProfile N) := by
  unfold factorialPlateauProfile
  fun_prop

theorem factorialNormalizedPlateauWeight_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (factorialNormalizedPlateauWeight N) := by
  exact Real.smoothTransition.contDiff.comp (factorialPlateauProfile_contDiff N)

theorem factorialNormalizedPlateauWeight_periodic (N : ℕ) :
    Function.Periodic (factorialNormalizedPlateauWeight N) 1 := by
  intro x
  unfold factorialNormalizedPlateauWeight
  congr 1
  simpa using factorialPlateauProfile_add_int N x 1

theorem factorialNormalizedPlateauWeight_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ factorialNormalizedPlateauWeight N x :=
  Real.smoothTransition.nonneg _

theorem factorialPlateauProfile_pos_of_normalized_ne_zero
    {N : ℕ} {x : ℝ} (hne : factorialNormalizedPlateauWeight N x ≠ 0) :
    0 < factorialPlateauProfile N x := by
  rw [factorialNormalizedPlateauWeight,
    ne_eq, Real.smoothTransition.zero_iff_nonpos, not_le] at hne
  exact hne

theorem factorialNormalizedPlateauWeight_supported
    {N : ℕ} (hlog : 1 < Real.log (N : ℝ)) {x : ℝ}
    (hne : factorialNormalizedPlateauWeight N x ≠ 0) :
    1 - 1 / (10 * (Real.log N) ^ 2) ≤ Int.fract x := by
  have hlogPos : 0 < Real.log (N : ℝ) := lt_trans (by norm_num) hlog
  have hscalePos : 0 < 150 * (Real.log (N : ℝ)) ^ 4 := by positivity
  have hprofile := factorialPlateauProfile_pos_of_normalized_ne_zero hne
  have hproductPos :
      0 < Real.sin (Real.pi *
        (x - (1 - 1 / (10 * (Real.log N) ^ 2)))) *
        Real.sin (Real.pi * (1 - x)) := by
    rw [factorialPlateauProfile] at hprofile
    exact pos_of_mul_pos_right hprofile hscalePos.le
  apply fract_ge_left_of_smoothPeriodicIntervalBump_ne_zero
  · have hrecipPos : 0 < 1 / (10 * (Real.log (N : ℝ)) ^ 2) := by positivity
    linarith
  · unfold smoothPeriodicIntervalBump
    exact ne_of_gt (expNegInvGlue.pos_of_pos hproductPos)

theorem factorialPlateauProfile_one_le_of_mem_inner
    {N : ℕ} (hlog : 1 < Real.log (N : ℝ)) {x : ℝ}
    (hleft : factorialPlateauArcLeft N ≤ x)
    (hright : x ≤ factorialPlateauArcRight N) :
    1 ≤ factorialPlateauProfile N x := by
  let q := (Real.log (N : ℝ)) ^ 2
  let a := 1 - 1 / (10 * q)
  have hq : 1 < q := by dsimp [q]; nlinarith
  have hqPos : 0 < q := lt_trans (by norm_num) hq
  have htenqPos : 0 < 10 * q := by positivity
  have htwentyqPos : 0 < 20 * q := by positivity
  have hthirtyqPos : 0 < 30 * q := by positivity
  have hdeltaLe : 1 / (10 * q) ≤ (1 / 10 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hxltOne : x < 1 := by
    have hright' : x ≤ 1 - 1 / (30 * q) := by
      simpa only [factorialPlateauArcRight, q] using hright
    have hrecipPos : 0 < 1 / (30 * q) := by positivity
    linarith
  have hd₁Nonneg : 0 ≤ x - a := by
    have hleft' : 1 - 1 / (20 * q) ≤ x := by
      simpa only [factorialPlateauArcLeft, q] using hleft
    dsimp [a]
    have hinv : 1 / (20 * q) ≤ 1 / (10 * q) := by
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    linarith
  have hd₁Le : x - a ≤ 1 / 10 := by
    dsimp [a]
    linarith
  have hd₂Nonneg : 0 ≤ 1 - x := by linarith
  have hd₂Le : 1 - x ≤ 1 / 10 := by
    have hleft' : 1 - 1 / (20 * q) ≤ x := by
      simpa only [factorialPlateauArcLeft, q] using hleft
    have hinv : 1 / (20 * q) ≤ (1 / 10 : ℝ) := by
      apply one_div_le_one_div_of_le (by norm_num)
      nlinarith
    linarith
  have hs₁raw := Real.mul_le_sin
    (mul_nonneg Real.pi_pos.le hd₁Nonneg)
    (by nlinarith [Real.pi_pos] : Real.pi * (x - a) ≤ Real.pi / 2)
  have hs₂raw := Real.mul_le_sin
    (mul_nonneg Real.pi_pos.le hd₂Nonneg)
    (by nlinarith [Real.pi_pos] : Real.pi * (1 - x) ≤ Real.pi / 2)
  have hs₁ : 2 * (x - a) ≤ Real.sin (Real.pi * (x - a)) := by
    convert hs₁raw using 1
    all_goals field_simp [Real.pi_ne_zero]
  have hs₂ : 2 * (1 - x) ≤ Real.sin (Real.pi * (1 - x)) := by
    convert hs₂raw using 1
    all_goals field_simp [Real.pi_ne_zero]
  have hd₁Lower : 1 / (20 * q) ≤ x - a := by
    have hleft' : 1 - 1 / (20 * q) ≤ x := by
      simpa only [factorialPlateauArcLeft, q] using hleft
    dsimp [a]
    have heq : 1 / (10 * q) - 1 / (20 * q) = 1 / (20 * q) := by
      field_simp
      ring
    linarith
  have hd₂Lower : 1 / (30 * q) ≤ 1 - x := by
    have hright' : x ≤ 1 - 1 / (30 * q) := by
      simpa only [factorialPlateauArcRight, q] using hright
    linarith
  have hs₁Lower : 1 / (10 * q) ≤ Real.sin (Real.pi * (x - a)) := by
    calc
      1 / (10 * q) = 2 * (1 / (20 * q)) := by field_simp; norm_num
      _ ≤ 2 * (x - a) := mul_le_mul_of_nonneg_left hd₁Lower (by norm_num)
      _ ≤ Real.sin (Real.pi * (x - a)) := hs₁
  have hs₂Lower : 1 / (15 * q) ≤ Real.sin (Real.pi * (1 - x)) := by
    calc
      1 / (15 * q) = 2 * (1 / (30 * q)) := by field_simp; norm_num
      _ ≤ 2 * (1 - x) := mul_le_mul_of_nonneg_left hd₂Lower (by norm_num)
      _ ≤ Real.sin (Real.pi * (1 - x)) := hs₂
  have hprod : 1 / (150 * q ^ 2) ≤
      Real.sin (Real.pi * (x - a)) * Real.sin (Real.pi * (1 - x)) := by
    have hmul := mul_le_mul hs₁Lower hs₂Lower (by positivity)
      (le_trans (by positivity) hs₁Lower)
    convert hmul using 1
    all_goals field_simp
    all_goals ring
  have hscaled := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 150 * q ^ 2 by positivity)
  calc
    1 = (150 * q ^ 2) * (1 / (150 * q ^ 2)) := by field_simp
    _ ≤ (150 * q ^ 2) *
        (Real.sin (Real.pi * (x - a)) * Real.sin (Real.pi * (1 - x))) :=
      hscaled
    _ = factorialPlateauProfile N x := by
      simp only [factorialPlateauProfile, a, q]
      ring

theorem factorialNormalizedPlateauWeight_eq_one_of_innerFractionalArc
    {N : ℕ} (hlog : 1 < Real.log (N : ℝ)) {x : ℝ}
    (hleft : factorialPlateauArcLeft N ≤ Int.fract x)
    (hright : Int.fract x ≤ factorialPlateauArcRight N) :
    factorialNormalizedPlateauWeight N x = 1 := by
  have hperiod := factorialPlateauProfile_add_int N (Int.fract x) ⌊x⌋
  have heq : factorialPlateauProfile N x =
      factorialPlateauProfile N (Int.fract x) := by
    simpa only [Int.fract_add_floor] using hperiod
  rw [factorialNormalizedPlateauWeight, heq]
  exact Real.smoothTransition.one_of_one_le
    (factorialPlateauProfile_one_le_of_mem_inner hlog hleft hright)

/-- The normalized smooth transition is an actual witness to Tao's complete
plateau-weight specification. -/
theorem factorialNormalizedPlateauWeight_spec
    {N : ℕ} (hlog : 1 < Real.log (N : ℝ)) :
    IsFactorialPlateauWeight N (factorialNormalizedPlateauWeight N) where
  contDiff := factorialNormalizedPlateauWeight_contDiff N
  periodic := factorialNormalizedPlateauWeight_periodic N
  nonneg := factorialNormalizedPlateauWeight_nonneg N
  supported := fun _x hne => factorialNormalizedPlateauWeight_supported hlog hne
  plateau := fun _x hleft hright =>
    factorialNormalizedPlateauWeight_eq_one_of_innerFractionalArc
      hlog hleft hright

theorem factorialPlateauArc_bounds
    {N : ℕ} (hlog : 1 < Real.log (N : ℝ)) :
    0 ≤ factorialPlateauArcLeft N ∧
      factorialPlateauArcLeft N ≤ factorialPlateauArcRight N ∧
      factorialPlateauArcRight N < 1 := by
  have hlogSq : (1 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by nlinarith
  have htwenty : (1 : ℝ) ≤ 20 * (Real.log (N : ℝ)) ^ 2 := by nlinarith
  have hthirtyPos : (0 : ℝ) < 30 * (Real.log (N : ℝ)) ^ 2 := by positivity
  have htwentyPos : (0 : ℝ) < 20 * (Real.log (N : ℝ)) ^ 2 := by positivity
  rw [factorialPlateauArcLeft, factorialPlateauArcRight]
  constructor
  · rw [sub_nonneg, div_le_one htwentyPos]
    exact htwenty
  constructor
  · have hden :
        20 * (Real.log (N : ℝ)) ^ 2 ≤
          30 * (Real.log (N : ℝ)) ^ 2 := by nlinarith
    have hinv :
        1 / (30 * (Real.log (N : ℝ)) ^ 2) ≤
          1 / (20 * (Real.log (N : ℝ)) ^ 2) := by
      exact one_div_le_one_div_of_le htwentyPos hden
    linarith
  · exact sub_lt_self 1 (by positivity)

theorem factorialPlateauArc_length
    {N : ℕ} (hlog : 1 < Real.log (N : ℝ)) :
    factorialPlateauArcRight N - factorialPlateauArcLeft N =
      1 / (60 * (Real.log N) ^ 2) := by
  have hlogNe : Real.log (N : ℝ) ≠ 0 := ne_of_gt (lt_trans (by norm_num) hlog)
  rw [factorialPlateauArcLeft, factorialPlateauArcRight]
  field_simp
  ring

/-- Every weight satisfying Tao's plateau specification has at least the
source mass `1/(60 log² N)` on one period. -/
theorem one_div_sixty_log_sq_le_intervalIntegral_factorialPlateauWeight
    {N : ℕ} {w : ℝ → ℝ} (hlog : 1 < Real.log (N : ℝ))
    (hw : IsFactorialPlateauWeight N w) :
    1 / (60 * (Real.log N) ^ 2) ≤ ∫ x in (0 : ℝ)..1, w x := by
  obtain ⟨hleftNonneg, hleftRight, hrightLtOne⟩ :=
    factorialPlateauArc_bounds hlog
  have hwInterval : IntervalIntegrable w volume (0 : ℝ) 1 :=
    hw.contDiff.continuous.intervalIntegrable 0 1
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] w :=
    Filter.Eventually.of_forall hw.nonneg
  have hmono := intervalIntegral.integral_mono_interval
    (f := w) (μ := volume)
    (a := factorialPlateauArcLeft N) (b := factorialPlateauArcRight N)
    (c := 0) (d := 1) hleftNonneg hleftRight hrightLtOne.le hnonneg hwInterval
  have hinner :
      (∫ x in factorialPlateauArcLeft N..factorialPlateauArcRight N, w x) =
        factorialPlateauArcRight N - factorialPlateauArcLeft N := by
    calc
      (∫ x in factorialPlateauArcLeft N..factorialPlateauArcRight N, w x) =
          ∫ _x in factorialPlateauArcLeft N..factorialPlateauArcRight N,
            (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (factorialPlateauArcLeft N)
            (factorialPlateauArcRight N) := by
          simpa [Set.uIcc_of_le hleftRight] using hx
        have hfract : Int.fract x = x := Int.fract_eq_self.2 ⟨
          le_trans hleftNonneg hx'.1, lt_of_le_of_lt hx'.2 hrightLtOne⟩
        rw [hw.plateau x (by simpa [hfract] using hx'.1)
          (by simpa [hfract] using hx'.2)]
      _ = factorialPlateauArcRight N - factorialPlateauArcLeft N := by simp
  rw [hinner, factorialPlateauArc_length hlog] at hmono
  exact hmono

/-- The same exact mass lower bound holds on every translated unit period. -/
theorem one_div_sixty_log_sq_le_intervalIntegral_factorialPlateauWeight_unit
    {N : ℕ} {w : ℝ → ℝ} (hlog : 1 < Real.log (N : ℝ))
    (hw : IsFactorialPlateauWeight N w) (a : ℝ) :
    1 / (60 * (Real.log N) ^ 2) ≤ ∫ x in a..a + 1, w x := by
  rw [hw.periodic.intervalIntegral_add_eq a 0, zero_add]
  exact one_div_sixty_log_sq_le_intervalIntegral_factorialPlateauWeight
    hlog hw

/-- A long interval retains at least half its length in complete unit cells,
and therefore the corresponding fraction of the plateau mass. -/
theorem intervalLength_div_one_twenty_log_sq_le_integral_factorialPlateauWeight
    {N : ℕ} {w : ℝ → ℝ} (hlog : 1 < Real.log (N : ℝ))
    (hw : IsFactorialPlateauWeight N w) {a b : ℝ}
    (hlength : 2 ≤ b - a) :
    (b - a) / (120 * (Real.log N) ^ 2) ≤ ∫ x in a..b, w x := by
  let n : ℤ := ⌊b - a⌋
  have hnle : (n : ℝ) ≤ b - a := by
    dsimp [n]
    exact Int.floor_le (b - a)
  have hnTwo : (2 : ℝ) ≤ n := by
    exact_mod_cast (Int.le_floor.mpr (by simpa using hlength) :
      (2 : ℤ) ≤ ⌊b - a⌋)
  have hnLower : (b - a) / 2 ≤ (n : ℝ) := by
    have hlt : b - a < (n : ℝ) + 1 := by
      simpa only [n, Int.cast_add, Int.cast_one] using
        (Int.lt_floor_add_one (b - a))
    linarith
  have hanb : a ≤ a + (n : ℝ) := by linarith
  have hanbLe : a + (n : ℝ) ≤ b := by linarith
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)] w :=
    Filter.Eventually.of_forall hw.nonneg
  have hmono := intervalIntegral.integral_mono_interval
    (f := w) (μ := volume) (a := a) (b := a + (n : ℝ))
    (c := a) (d := b) le_rfl hanb hanbLe hnonneg
    (hw.contDiff.continuous.intervalIntegrable a b)
  have hint : ∀ x y : ℝ, IntervalIntegrable w volume x y :=
    fun x y => hw.contDiff.continuous.intervalIntegrable x y
  have hperiod := hw.periodic.intervalIntegral_add_zsmul_eq n a hint
  have hperiodOne := hw.periodic.intervalIntegral_add_eq a 0
  simp only [zsmul_eq_mul, mul_one, hperiodOne, zero_add] at hperiod
  have hunit :=
    one_div_sixty_log_sq_le_intervalIntegral_factorialPlateauWeight hlog hw
  have hmassPos : 0 < 1 / (60 * (Real.log N) ^ 2) := by
    have hlogPos : 0 < Real.log (N : ℝ) := lt_trans (by norm_num) hlog
    positivity
  have hnMass :
      (n : ℝ) * (1 / (60 * (Real.log N) ^ 2)) ≤
        (n : ℝ) * ∫ x in (0 : ℝ)..1, w x :=
    mul_le_mul_of_nonneg_left hunit (by linarith)
  rw [hperiod] at hmono
  calc
    (b - a) / (120 * (Real.log N) ^ 2) =
        ((b - a) / 2) * (1 / (60 * (Real.log N) ^ 2)) := by ring
    _ ≤ (n : ℝ) * (1 / (60 * (Real.log N) ^ 2)) :=
      mul_le_mul_of_nonneg_right hnLower hmassPos.le
    _ ≤ (n : ℝ) * ∫ x in (0 : ℝ)..1, w x := hnMass
    _ ≤ ∫ x in a..b, w x := hmono

/-- Lift a real one-dimensional plateau weight to the two-dimensional complex
weight convention of Theorem 2.5. -/
def factorialPlateauWeightLift (w : ℝ → ℝ) (z : ℝ × ℝ) : ℂ :=
  (w z.1 : ℝ)

/-- Passing a scalar weight through the first projection and the isometric
real-to-complex embedding does not enlarge any iterated derivative. -/
theorem norm_iteratedFDeriv_factorialPlateauWeightLift_le
    {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) (i : ℕ) (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (factorialPlateauWeightLift w) z‖ ≤
      ‖iteratedFDeriv ℝ i w z.1‖ := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let f : (ℝ × ℝ) → ℝ := w ∘ L
  have hf : ContDiff ℝ ∞ f := hw.comp_continuousLinearMap
  have hlift : factorialPlateauWeightLift w = Complex.ofRealLI ∘ f := by
    rfl
  rw [hlift,
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf.contDiffAt
      (mod_cast le_top)]
  have heq := L.iteratedFDeriv_comp_right hw z (i := i) (mod_cast le_top)
  change ‖iteratedFDeriv ℝ i f z‖ ≤ _
  rw [show f = w ∘ L by rfl, heq]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ i w (L z)) (fun _ => L)).trans
  calc
    ‖iteratedFDeriv ℝ i w (L z)‖ * ∏ _j : Fin i, ‖L‖ ≤
        ‖iteratedFDeriv ℝ i w (L z)‖ * ∏ _j : Fin i, (1 : ℝ) := by
      gcongr with j
      exact ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
    _ = ‖iteratedFDeriv ℝ i w z.1‖ := by
      simp only [Finset.prod_const_one, mul_one, L]
      rfl

/-- The actual two-dimensional cutoff family has a uniform polynomial `C³`
bound.  The logarithmic exponent is `12`, reflecting the coarse quantitative
chain rule for the normalized transition. -/
theorem taoC3Norm_factorialNormalizedPlateauWeightLift_le
    {B : ℝ} (hB : 1 ≤ B)
    (htransition : ∀ i < 4, ∀ x : ℝ,
      ‖iteratedFDeriv ℝ i Real.smoothTransition x‖ ≤ B)
    {N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ)) :
    taoC3Norm
        (factorialPlateauWeightLift (factorialNormalizedPlateauWeight N)) ≤
      24 * B * (1200 * (Real.log N) ^ 4) ^ 3 := by
  have hpoint : ∀ i < 4, ∀ z : ℝ × ℝ,
      ‖iteratedFDeriv ℝ i
        (factorialPlateauWeightLift (factorialNormalizedPlateauWeight N)) z‖ ≤
        6 * B * (1200 * (Real.log N) ^ 4) ^ 3 := by
    intro i hi z
    exact (norm_iteratedFDeriv_factorialPlateauWeightLift_le
      (factorialNormalizedPlateauWeight_contDiff N) i z).trans
        (norm_iteratedFDeriv_factorialNormalizedPlateauWeight_le
          hB htransition hlog hi z.1)
  have hbound : 0 ≤ 6 * B * (1200 * (Real.log N) ^ 4) ^ 3 := by
    positivity
  calc
    taoC3Norm
        (factorialPlateauWeightLift (factorialNormalizedPlateauWeight N)) ≤
        4 * (6 * B * (1200 * (Real.log N) ^ 4) ^ 3) :=
      taoC3Norm_le_four_mul_of_iteratedFDeriv_le hbound hpoint
    _ = 24 * B * (1200 * (Real.log N) ^ 4) ^ 3 := by ring

theorem IsFactorialPlateauWeight.lift_contDiff
    {N : ℕ} {w : ℝ → ℝ} (hw : IsFactorialPlateauWeight N w) :
    ContDiff ℝ ∞ (factorialPlateauWeightLift w) := by
  have hreal : ContDiff ℝ ∞ (fun z : ℝ × ℝ => w z.1) :=
    hw.contDiff.comp contDiff_fst
  simpa only [factorialPlateauWeightLift, Function.comp_apply,
    Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp hreal

theorem IsFactorialPlateauWeight.lift_isZ2Periodic
    {N : ℕ} {w : ℝ → ℝ} (hw : IsFactorialPlateauWeight N w) :
    IsZ2Periodic (factorialPlateauWeightLift w) := by
  intro x y m n
  unfold factorialPlateauWeightLift
  change (w (x + (m : ℝ)) : ℂ) = (w x : ℂ)
  rw [show x + (m : ℝ) = x + (m : ℝ) * 1 by ring,
    hw.periodic.int_mul m]

theorem IsFactorialPlateauWeight.lift_supported
    {N : ℕ} {w : ℝ → ℝ} (hw : IsFactorialPlateauWeight N w) :
    IsSupportedInFactorialFinalArc N (factorialPlateauWeightLift w) := by
  intro x y hne
  apply hw.supported x
  simpa only [factorialPlateauWeightLift, Complex.ofReal_ne_zero] using hne

theorem IsFactorialPlateauWeight.lift_re_nonneg
    {N : ℕ} {w : ℝ → ℝ} (hw : IsFactorialPlateauWeight N w)
    (z : ℝ × ℝ) :
    0 ≤ (factorialPlateauWeightLift w z).re := by
  simpa only [factorialPlateauWeightLift, Complex.ofReal_re] using hw.nonneg z.1

/-- The fixed quadratic-coordinate factor in the low-`P` cutoff. -/
def factorialQuadraticBumpLift (z : ℝ × ℝ) : ℂ :=
  (smoothPeriodicIntervalBump 0 (9 / 10) z.2 : ℝ)

theorem factorialQuadraticBumpLift_contDiff :
    ContDiff ℝ ∞ factorialQuadraticBumpLift := by
  have hreal : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      smoothPeriodicIntervalBump 0 (9 / 10) z.2) :=
    (smoothPeriodicIntervalBump_contDiff 0 (9 / 10)).comp contDiff_snd
  simpa only [factorialQuadraticBumpLift, Function.comp_apply,
    Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp hreal

theorem factorialQuadraticBumpLift_isZ2Periodic :
    IsZ2Periodic factorialQuadraticBumpLift := by
  intro x y m n
  unfold factorialQuadraticBumpLift
  rw [smoothPeriodicIntervalBump_add_int]

/-- Tao's low-`P` cutoff: the normalized shrinking final-arc plateau in the
divisor coordinate, multiplied by the fixed quadratic-coordinate bump from
the proof of Lemma 3.1. -/
def factorialLowObstructionWeight (N : ℕ) (z : ℝ × ℝ) : ℂ :=
  ((factorialNormalizedPlateauWeight N z.1 *
    smoothPeriodicIntervalBump 0 (9 / 10) z.2 : ℝ) : ℂ)

theorem factorialLowObstructionWeight_eq_mul (N : ℕ) :
    factorialLowObstructionWeight N =
      fun z => factorialPlateauWeightLift
        (factorialNormalizedPlateauWeight N) z * factorialQuadraticBumpLift z := by
  funext z
  simp only [factorialLowObstructionWeight, factorialPlateauWeightLift,
    factorialQuadraticBumpLift, Complex.ofReal_mul]

theorem factorialLowObstructionWeight_contDiff (N : ℕ) :
    ContDiff ℝ ∞ (factorialLowObstructionWeight N) := by
  have hx : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      factorialNormalizedPlateauWeight N z.1) :=
    (factorialNormalizedPlateauWeight_contDiff N).comp contDiff_fst
  have hy : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
      smoothPeriodicIntervalBump 0 (9 / 10) z.2) :=
    (smoothPeriodicIntervalBump_contDiff 0 (9 / 10)).comp contDiff_snd
  have hreal := hx.mul hy
  simpa only [factorialLowObstructionWeight, Function.comp_apply,
    Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp hreal

theorem factorialLowObstructionWeight_isZ2Periodic (N : ℕ) :
    IsZ2Periodic (factorialLowObstructionWeight N) := by
  intro x y m n
  unfold factorialLowObstructionWeight
  rw [show x + (m : ℝ) = x + (m : ℝ) * 1 by ring,
    factorialNormalizedPlateauWeight_periodic N |>.int_mul m,
    smoothPeriodicIntervalBump_add_int]

theorem factorialLowObstructionWeight_re_nonneg (N : ℕ) (z : ℝ × ℝ) :
    0 ≤ (factorialLowObstructionWeight N z).re := by
  simp only [factorialLowObstructionWeight, Complex.ofReal_re]
  exact mul_nonneg (factorialNormalizedPlateauWeight_nonneg N z.1)
    (expNegInvGlue.nonneg _)

theorem factorialLowObstructionWeight_supported
    {N : ℕ} (hlog : 1 < Real.log (N : ℝ)) :
    IsSupportedInFactorialLowObstruction N
      (factorialLowObstructionWeight N) := by
  intro x y hne
  have hprod : factorialNormalizedPlateauWeight N x *
      smoothPeriodicIntervalBump 0 (9 / 10) y ≠ 0 := by
    simpa only [factorialLowObstructionWeight, Complex.ofReal_ne_zero] using hne
  exact ⟨
    (factorialNormalizedPlateauWeight_spec hlog).supported x
      (left_ne_zero_of_mul hprod),
    fract_lt_nineTenths_of_smoothPeriodicIntervalBump_ne_zero
      (right_ne_zero_of_mul hprod)⟩

/-- The low-`P` product cutoff has the same coarse `log^12 N` derivative
growth as its shrinking first-coordinate factor; the fixed second-coordinate
bump is absorbed into one absolute constant. -/
theorem norm_iteratedFDeriv_factorialLowObstructionWeight_le
    {B : ℝ} (hB : 1 ≤ B)
    (htransition : ∀ i < 4, ∀ x : ℝ,
      ‖iteratedFDeriv ℝ i Real.smoothTransition x‖ ≤ B)
    {N i : ℕ} (hlog : 1 ≤ Real.log (N : ℝ)) (hi : i < 4)
    (z : ℝ × ℝ) :
    ‖iteratedFDeriv ℝ i (factorialLowObstructionWeight N) z‖ ≤
      8 * (6 * B * (1200 * (Real.log N) ^ 4) ^ 3) *
        max 1 (taoC3Norm factorialQuadraticBumpLift) := by
  let X : ℝ × ℝ → ℂ :=
    factorialPlateauWeightLift (factorialNormalizedPlateauWeight N)
  let Y : ℝ × ℝ → ℂ := factorialQuadraticBumpLift
  let L : ℝ := 6 * B * (1200 * (Real.log N) ^ 4) ^ 3
  let D : ℝ := max 1 (taoC3Norm factorialQuadraticBumpLift)
  have hXdiff : ContDiff ℝ ∞ X := by
    have hreal : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
        factorialNormalizedPlateauWeight N z.1) :=
      (factorialNormalizedPlateauWeight_contDiff N).comp contDiff_fst
    dsimp only [X]
    simpa only [factorialPlateauWeightLift, Function.comp_apply,
      Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp hreal
  have hYdiff : ContDiff ℝ ∞ Y := by
    exact factorialQuadraticBumpLift_contDiff
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hXbound : ∀ j < 4, ‖iteratedFDeriv ℝ j X z‖ ≤ L := by
    intro j hj
    exact (norm_iteratedFDeriv_factorialPlateauWeightLift_le
      (factorialNormalizedPlateauWeight_contDiff N) j z).trans
        (norm_iteratedFDeriv_factorialNormalizedPlateauWeight_le
          hB htransition hlog hj z.1)
  have hYbdd : ∀ j ∈ Finset.range 4,
      BddAbove {r : ℝ | ∃ x : ℝ × ℝ,
        r = ‖iteratedFDeriv ℝ j Y x‖} := by
    intro j _hj
    exact bddAbove_iteratedFDeriv_norm_range Y hYdiff
      factorialQuadraticBumpLift_isZ2Periodic j
  have hYbound : ∀ j < 4, ‖iteratedFDeriv ℝ j Y z‖ ≤ D := by
    intro j hj
    exact (norm_iteratedFDeriv_le_taoC3Norm_of_bddAbove Y hYbdd
      (Finset.mem_range.mpr hj) z).trans (le_max_right _ _)
  rw [factorialLowObstructionWeight_eq_mul]
  have hproduct := norm_iteratedFDeriv_mul_le hXdiff hYdiff z
    (n := i) (mod_cast le_top)
  calc
    ‖iteratedFDeriv ℝ i (fun y => X y * Y y) z‖ ≤
        ∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j X z‖ *
            ‖iteratedFDeriv ℝ (i - j) Y z‖ := hproduct
    _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * L * D := by
      apply Finset.sum_le_sum
      intro j hj
      have hjle : j ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hj4 : j < 4 := lt_of_le_of_lt hjle hi
      have hij4 : i - j < 4 := lt_of_le_of_lt (Nat.sub_le i j) hi
      gcongr
      · exact hXbound j hj4
      · exact hYbound (i - j) hij4
    _ = (2 : ℝ) ^ i * L * D := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum,
        Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ 8 * L * D := by
      have hpow : (2 : ℝ) ^ i ≤ 8 := by
        interval_cases i <;> norm_num
      gcongr
    _ = 8 * (6 * B * (1200 * (Real.log N) ^ 4) ^ 3) *
        max 1 (taoC3Norm factorialQuadraticBumpLift) := by rfl

theorem taoC3Norm_factorialLowObstructionWeight_le
    {B : ℝ} (hB : 1 ≤ B)
    (htransition : ∀ i < 4, ∀ x : ℝ,
      ‖iteratedFDeriv ℝ i Real.smoothTransition x‖ ≤ B)
    {N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ)) :
    taoC3Norm (factorialLowObstructionWeight N) ≤
      32 * (6 * B * (1200 * (Real.log N) ^ 4) ^ 3) *
        max 1 (taoC3Norm factorialQuadraticBumpLift) := by
  calc
    taoC3Norm (factorialLowObstructionWeight N) ≤
        4 * (8 * (6 * B * (1200 * (Real.log N) ^ 4) ^ 3) *
          max 1 (taoC3Norm factorialQuadraticBumpLift)) :=
      taoC3Norm_le_four_mul_of_iteratedFDeriv_le (by positivity)
        (fun i hi z =>
          norm_iteratedFDeriv_factorialLowObstructionWeight_le
            hB htransition hlog hi z)
    _ = 32 * (6 * B * (1200 * (Real.log N) ^ 4) ^ 3) *
        max 1 (taoC3Norm factorialQuadraticBumpLift) := by ring

/-- Exact reciprocal substitution `u=N/t` for an arbitrary continuous real
weight. -/
theorem intervalIntegral_reciprocal_weighted_eq
    {N P : ℝ} (hN : 0 < N) (hP : 0 < P) {w : ℝ → ℝ} :
    (∫ u in N / (2 * P)..N / P, w u) =
      ∫ t in P..2 * P, (N / t ^ 2) * w (N / t) := by
  have htwoP : 0 < 2 * P := by positivity
  have hPtwoP : P ≤ 2 * P := by linarith
  have hfcont : ContinuousOn (fun t : ℝ => N / t) (uIcc P (2 * P)) := by
    rw [uIcc_of_le hPtwoP]
    intro t ht
    exact (continuousAt_const.div continuousAt_id
      (ne_of_gt (hP.trans_le ht.1))).continuousWithinAt
  have hfderiv : ∀ t ∈ Ioo (min P (2 * P)) (max P (2 * P)),
      HasDerivAt (fun s : ℝ => N / s) (-N / t ^ 2) t := by
    intro t ht
    rw [min_eq_left hPtwoP, max_eq_right hPtwoP] at ht
    exact hasDerivAt_real_const_div N (ne_of_gt (hP.trans ht.1))
  have hfnonpos : ∀ t ∈ Ioo (min P (2 * P)) (max P (2 * P)),
      (-N / t ^ 2 : ℝ) ≤ 0 := by
    intro t ht
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hN.le) (sq_nonneg t)
  have hsubst :
      (∫ t in P..2 * P, (-N / t ^ 2 : ℝ) * w (N / t)) =
        ∫ u in N / P..N / (2 * P), w u := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      (intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
        (g := w) hfcont hfderiv hfnonpos)
  have hleft :
      (∫ t in P..2 * P, (-N / t ^ 2 : ℝ) * w (N / t)) =
        -(∫ t in P..2 * P, (N / t ^ 2) * w (N / t)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hright :
      (∫ u in N / P..N / (2 * P), w u) =
        -(∫ u in N / (2 * P)..N / P, w u) := by
    rw [intervalIntegral.integral_symm]
  rw [hleft, hright] at hsubst
  exact neg_inj.mp hsubst.symm

/-- The plateau mass forces an unweighted prime-scale integral of order
`P/log² N` whenever the reciprocal interval has length at least two. -/
theorem factorialPlateauWeight_primeScaleIntegral_lower
    {N : ℕ} {P : ℝ} {w : ℝ → ℝ}
    (hN : 0 < N) (hP : 0 < P) (hlog : 1 < Real.log (N : ℝ))
    (hw : IsFactorialPlateauWeight N w)
    (hlength : 2 ≤ (N : ℝ) / (2 * P)) :
    P / (240 * (Real.log N) ^ 2) ≤
      ∫ t in P..2 * P, w ((N : ℝ) / t) := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have htwoP : 0 < 2 * P := by positivity
  have hab : (N : ℝ) / (2 * P) ≤ (N : ℝ) / P :=
    div_le_div_of_nonneg_left hNReal.le hP (by linarith)
  have hintervalLength :
      2 ≤ (N : ℝ) / P - (N : ℝ) / (2 * P) := by
    have heq : (N : ℝ) / P - (N : ℝ) / (2 * P) =
        (N : ℝ) / (2 * P) := by field_simp; ring
    rwa [heq]
  have hmass :=
    intervalLength_div_one_twenty_log_sq_le_integral_factorialPlateauWeight
      hlog hw hintervalLength
  have hmassEq :
      (∫ u in (N : ℝ) / (2 * P)..(N : ℝ) / P, w u) =
        ∫ t in P..2 * P,
          ((N : ℝ) / t ^ 2) * w ((N : ℝ) / t) :=
    intervalIntegral_reciprocal_weighted_eq hNReal hP
  rw [hmassEq] at hmass
  have hPtwoP : P ≤ 2 * P := by linarith
  have hcompCont : ContinuousOn (fun t : ℝ => w ((N : ℝ) / t))
      (uIcc P (2 * P)) := by
    rw [uIcc_of_le hPtwoP]
    apply hw.contDiff.continuous.comp_continuousOn
    intro t ht
    exact (continuousAt_const.div continuousAt_id
      (ne_of_gt (hP.trans_le ht.1))).continuousWithinAt
  have hweightedInt : IntervalIntegrable
      (fun t : ℝ => ((N : ℝ) / t ^ 2) * w ((N : ℝ) / t)) volume P (2 * P) := by
    have hjacCont : ContinuousOn (fun t : ℝ => (N : ℝ) / t ^ 2)
        (uIcc P (2 * P)) := by
      rw [uIcc_of_le hPtwoP]
      exact continuousOn_const.div (continuousOn_id.pow 2) (fun t ht =>
        pow_ne_zero 2 (ne_of_gt (hP.trans_le ht.1)))
    exact (hjacCont.mul hcompCont).intervalIntegrable
  have hunweightedInt : IntervalIntegrable
      (fun t : ℝ => ((N : ℝ) / P ^ 2) * w ((N : ℝ) / t)) volume P (2 * P) :=
    continuousOn_const.mul hcompCont |>.intervalIntegrable
  have hpoint : ∀ t ∈ Icc P (2 * P),
      ((N : ℝ) / t ^ 2) * w ((N : ℝ) / t) ≤
        ((N : ℝ) / P ^ 2) * w ((N : ℝ) / t) := by
    intro t ht
    have htPos : 0 < t := hP.trans_le ht.1
    have hsquares : P ^ 2 ≤ t ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self hP.le ht.1
    have hjac : (N : ℝ) / t ^ 2 ≤ (N : ℝ) / P ^ 2 :=
      div_le_div_of_nonneg_left hNReal.le (sq_pos_of_pos hP) hsquares
    exact mul_le_mul_of_nonneg_right hjac (hw.nonneg _)
  have hmono := intervalIntegral.integral_mono_on (by linarith : P ≤ 2 * P)
    hweightedInt hunweightedInt hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hlowerRewrite :
      ((N : ℝ) / P - (N : ℝ) / (2 * P)) /
          (120 * (Real.log N) ^ 2) =
        (N : ℝ) / (240 * P * (Real.log N) ^ 2) := by
    field_simp
    ring
  rw [hlowerRewrite] at hmass
  have hlogPos : 0 < Real.log (N : ℝ) := lt_trans (by norm_num) hlog
  have hIneq :
      (N : ℝ) / (240 * P * (Real.log N) ^ 2) ≤
        ((N : ℝ) / P ^ 2) *
          (∫ t in P..2 * P, w ((N : ℝ) / t)) :=
    hmass.trans hmono
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNReal
  have hPne : P ≠ 0 := ne_of_gt hP
  calc
    P / (240 * (Real.log N) ^ 2) =
        (P ^ 2 / (N : ℝ)) *
          ((N : ℝ) / (240 * P * (Real.log N) ^ 2)) := by
      field_simp
    _ ≤ (P ^ 2 / (N : ℝ)) *
        (((N : ℝ) / P ^ 2) *
          (∫ t in P..2 * P, w ((N : ℝ) / t))) :=
      mul_le_mul_of_nonneg_left hIneq (by positivity)
    _ = ∫ t in P..2 * P, w ((N : ℝ) / t) := by
      field_simp

/-- Integrability of the logarithmically weighted lifted plateau integrand on
the prime scale. -/
theorem integrableOn_factorialPlateauPrimeIntegralIntegrand
    {N : ℕ} {P : ℝ} (hP : 2 ≤ P) {w : ℝ → ℝ}
    (hw : IsFactorialPlateauWeight N w) :
    IntegrableOn (fun t : ℝ =>
      factorialPlateauWeightLift w
        ((N : ℝ) / t, (N : ℝ) / t ^ 2) / Real.log t)
      (Ioo P (2 * P)) := by
  have hPPos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hcont : ContinuousOn (fun t : ℝ =>
      factorialPlateauWeightLift w
        ((N : ℝ) / t, (N : ℝ) / t ^ 2) / Real.log t)
      (Icc P (2 * P)) := by
    intro t ht
    have htOne : (1 : ℝ) < t := lt_of_lt_of_le (by norm_num)
      (hP.trans ht.1)
    have htne : t ≠ 0 := ne_of_gt (lt_trans (by norm_num) htOne)
    have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos htOne)
    apply ContinuousAt.continuousWithinAt
    have hpair : ContinuousAt (fun u : ℝ =>
        ((N : ℝ) / u, (N : ℝ) / u ^ 2)) t :=
      (continuousAt_const.div continuousAt_id htne).prodMk
        (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 htne))
    have hnum : ContinuousAt (fun u : ℝ =>
        factorialPlateauWeightLift w
          ((N : ℝ) / u, (N : ℝ) / u ^ 2)) t :=
      hw.lift_contDiff.continuous.continuousAt.comp hpair
    have hden : ContinuousAt (fun u : ℝ => (Real.log u : ℂ)) t := by
      fun_prop
    exact hnum.div hden (by simpa only [Complex.ofReal_ne_zero] using hlogne)
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- The real part of the complex Theorem 2.5 integral is exactly the real
one-dimensional logarithmic interval integral. -/
theorem factorialPlateauPrimeEquidistributionIntegral_re_eq
    {N : ℕ} {P : ℝ} (hP : 2 ≤ P) {w : ℝ → ℝ}
    (hw : IsFactorialPlateauWeight N w) :
    (primeEquidistributionIntegral (Ioo P (2 * P))
      (factorialPlateauWeightLift w) (N : ℝ) (N : ℝ) 2).re =
      ∫ t in P..2 * P, w ((N : ℝ) / t) / Real.log t := by
  have hPtwoP : P ≤ 2 * P := by linarith
  rw [primeEquidistributionIntegral, ← Complex.reCLM_apply,
    ← Complex.reCLM.integral_comp_comm
      (integrableOn_factorialPlateauPrimeIntegralIntegrand hP hw)]
  have hpoint : ∀ t : ℝ,
      (factorialPlateauWeightLift w
          ((N : ℝ) / t, (N : ℝ) / t ^ 2) / Real.log t).re =
        w ((N : ℝ) / t) / Real.log t := by
    intro t
    change ((w ((N : ℝ) / t) : ℂ) / (Real.log t : ℂ)).re = _
    rw [← Complex.ofReal_div, Complex.ofReal_re]
  rw [intervalIntegral.integral_of_le hPtwoP, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards with t
  exact hpoint t

/-- Removing the logarithmic weight costs at most `log(2P)` for a nonnegative
plateau weight on `[P,2P]`. -/
theorem factorialPlateauWeight_unweightedIntegral_le_log_mul_weightedIntegral
    {N : ℕ} {P : ℝ} (hP : 2 ≤ P) {w : ℝ → ℝ}
    (hw : IsFactorialPlateauWeight N w) :
    (∫ t in P..2 * P, w ((N : ℝ) / t)) ≤
      Real.log (2 * P) *
        ∫ t in P..2 * P, w ((N : ℝ) / t) / Real.log t := by
  have hPPos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hPtwoP : P ≤ 2 * P := by linarith
  have hcompCont : ContinuousOn (fun t : ℝ => w ((N : ℝ) / t))
      (uIcc P (2 * P)) := by
    rw [uIcc_of_le hPtwoP]
    apply hw.contDiff.continuous.comp_continuousOn
    intro t ht
    exact (continuousAt_const.div continuousAt_id
      (ne_of_gt (hPPos.trans_le ht.1))).continuousWithinAt
  have hunweighted : IntervalIntegrable
      (fun t : ℝ => w ((N : ℝ) / t)) volume P (2 * P) :=
    hcompCont.intervalIntegrable
  have hweightedCont : ContinuousOn
      (fun t : ℝ => Real.log (2 * P) *
        (w ((N : ℝ) / t) / Real.log t)) (uIcc P (2 * P)) := by
    have hcompContIcc : ContinuousOn (fun t : ℝ => w ((N : ℝ) / t))
        (Icc P (2 * P)) := by
      simpa only [uIcc_of_le hPtwoP] using hcompCont
    have hlogContIcc : ContinuousOn Real.log (Icc P (2 * P)) :=
      Real.continuousOn_log.mono (fun t ht =>
        ne_of_gt (hPPos.trans_le ht.1))
    rw [uIcc_of_le hPtwoP]
    exact continuousOn_const.mul (hcompContIcc.div hlogContIcc
      (fun t ht => by
        have htOne : (1 : ℝ) < t := lt_of_lt_of_le (by norm_num)
          (hP.trans ht.1)
        exact ne_of_gt (Real.log_pos htOne)))
  have hweighted : IntervalIntegrable
      (fun t : ℝ => Real.log (2 * P) *
        (w ((N : ℝ) / t) / Real.log t)) volume P (2 * P) :=
    hweightedCont.intervalIntegrable
  have hpoint : ∀ t ∈ Icc P (2 * P),
      w ((N : ℝ) / t) ≤ Real.log (2 * P) *
        (w ((N : ℝ) / t) / Real.log t) := by
    intro t ht
    have htOne : (1 : ℝ) < t := lt_of_lt_of_le (by norm_num)
      (hP.trans ht.1)
    have hlogPos : 0 < Real.log t := Real.log_pos htOne
    have hlogLe : Real.log t ≤ Real.log (2 * P) :=
      Real.strictMonoOn_log.monotoneOn (lt_trans (by norm_num) htOne)
        (mul_pos (by norm_num) hPPos) ht.2
    have hwNonneg := hw.nonneg ((N : ℝ) / t)
    calc
      w ((N : ℝ) / t) =
          (w ((N : ℝ) / t) * Real.log t) / Real.log t := by
        field_simp
      _ ≤ (w ((N : ℝ) / t) * Real.log (2 * P)) / Real.log t :=
        (div_le_div_iff_of_pos_right hlogPos).2
          (mul_le_mul_of_nonneg_left hlogLe hwNonneg)
      _ = Real.log (2 * P) *
          (w ((N : ℝ) / t) / Real.log t) := by ring
  have hmono := intervalIntegral.integral_mono_on hPtwoP hunweighted
    hweighted hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

/-- Quantitative lower bound for the norm of the complex prime-scale integral
obtained from the plateau mass and the reciprocal substitution. -/
theorem factorialPlateauWeight_primeEquidistributionIntegral_norm_lower
    {N : ℕ} {P : ℝ} {w : ℝ → ℝ}
    (hN : 0 < N) (hP : 2 ≤ P) (hlog : 1 < Real.log (N : ℝ))
    (hw : IsFactorialPlateauWeight N w)
    (hlength : 2 ≤ (N : ℝ) / (2 * P)) :
    P / (240 * (Real.log N) ^ 2) ≤
      Real.log (2 * P) *
        ‖primeEquidistributionIntegral (Ioo P (2 * P))
          (factorialPlateauWeightLift w) (N : ℝ) (N : ℝ) 2‖ := by
  have hlower := factorialPlateauWeight_primeScaleIntegral_lower
    hN (lt_of_lt_of_le (by norm_num) hP) hlog hw hlength
  have hremove :=
    factorialPlateauWeight_unweightedIntegral_le_log_mul_weightedIntegral
      hP hw
  have hre := factorialPlateauPrimeEquidistributionIntegral_re_eq hP hw
  rw [← hre] at hremove
  exact hlower.trans (hremove.trans (mul_le_mul_of_nonneg_left
    (Complex.re_le_norm _) (Real.log_nonneg (by linarith))))

/-- The stretched-log contradiction hypothesis puts the frequency `N` in the
Theorem 2.5 range at the larger factorial prime scale `P=H log² N`. -/
theorem factorialVinogradovParameterBound_of_growth
    {N H : ℕ} {η : ℝ} (hN : 2 ≤ N) (hH : 2 ≤ H) (hη : 0 < η)
    (hlog : 1 < Real.log (N : ℝ))
    (hgrowth : Real.exp ((Real.log N) ^ (2 / 3 + η)) < H) :
    VinogradovParameterBound (veryBadTheorem25Epsilon η) 1
      (factorialPrimeScale N H) (N : ℝ) := by
  have hbase := vinogradovParameterBound_of_veryBad_growth
    hN hH hη hgrowth
  have hHReal : (0 : ℝ) < H := by positivity
  have hlogSqOne : (1 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by nlinarith
  have hscale : (H : ℝ) ≤ factorialPrimeScale N H := by
    rw [factorialPrimeScale]
    nlinarith
  have hPReal : 0 < factorialPrimeScale N H := lt_of_lt_of_le hHReal hscale
  have hlogMono :
      Real.log (H : ℝ) ≤ Real.log (factorialPrimeScale N H) :=
    Real.strictMonoOn_log.monotoneOn hHReal hPReal hscale
  have hexponent : 0 ≤ ((2 / 3 + η)⁻¹ : ℝ) := by positivity
  have hrpow :
      (Real.log (H : ℝ)) ^ ((2 / 3 + η)⁻¹ : ℝ) ≤
        (Real.log (factorialPrimeScale N H)) ^
          ((2 / 3 + η)⁻¹ : ℝ) :=
    Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast
      (show 1 ≤ H by omega))) hlogMono hexponent
  rw [VinogradovParameterBound,
    abs_of_nonneg (Nat.cast_nonneg N), one_mul,
    threeHalves_sub_veryBadTheorem25Epsilon] at hbase ⊢
  exact hbase.trans (Real.exp_le_exp.mpr hrpow)

/-- A weight has arithmetic support on primes which divide the consecutive
product.  This is the exact interface between a smooth cutoff and the
large-`P` exclusion theorem. -/
def IsSupportedOnFactorialIntervalDivisors
    (N H : ℕ) (W : ℝ × ℝ → ℂ) : Prop :=
  ∀ p : ℕ, p.Prime →
    factorialPrimeScale N H < (p : ℝ) →
    (p : ℝ) < 2 * factorialPrimeScale N H →
    W ((N : ℝ) / (p : ℝ), (N : ℝ) / (p : ℝ) ^ 2) ≠ 0 →
    p ∣ consecutiveProduct N H

/-- The source final-arc support implies arithmetic support on interval
divisors throughout the dyadic range `(P,2P)`. -/
theorem IsSupportedInFactorialFinalArc.onIntervalDivisors
    {N H : ℕ} (hlog : 1 < Real.log (N : ℝ)) (hH : 1 ≤ H)
    {W : ℝ × ℝ → ℂ}
    (hW : IsSupportedInFactorialFinalArc N W) :
    IsSupportedOnFactorialIntervalDivisors N H W := by
  intro p hp _hPp hpUpper hWne
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hHReal : (0 : ℝ) < H := by exact_mod_cast hH
  have hlogPos : 0 < Real.log (N : ℝ) := lt_trans (by norm_num) hlog
  have hlogSqPos : 0 < (Real.log (N : ℝ)) ^ 2 := sq_pos_of_pos hlogPos
  have hpUpper' :
      (p : ℝ) < 2 * ((H : ℝ) * (Real.log (N : ℝ)) ^ 2) := by
    simpa only [factorialPrimeScale] using hpUpper
  have htenBound :
      (p : ℝ) ≤ (H : ℝ) * (10 * (Real.log (N : ℝ)) ^ 2) := by
    nlinarith
  have hreciprocal :
      (1 : ℝ) / (10 * (Real.log (N : ℝ)) ^ 2) ≤
        (H : ℝ) / (p : ℝ) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) <
      10 * (Real.log (N : ℝ)) ^ 2) hpReal]
    simpa only [one_mul] using htenBound
  have hfinal := hW ((N : ℝ) / (p : ℝ))
    ((N : ℝ) / (p : ℝ) ^ 2) hWne
  have hregion : InFactorialDivisorFractionalRegion N H p := by
    rw [InFactorialDivisorFractionalRegion]
    exact le_trans (by linarith :
      1 - (H : ℝ) / (p : ℝ) ≤
        1 - 1 / (10 * (Real.log (N : ℝ)) ^ 2)) hfinal
  have hHltpReal : (H : ℝ) < p := by
    have hHP : (H : ℝ) < factorialPrimeScale N H := by
      rw [factorialPrimeScale]
      have hlogSqOne : (1 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by
        nlinarith
      nlinarith
    exact lt_trans hHP _hPp
  have hHltp : H < p := by exact_mod_cast hHltpReal
  obtain ⟨h, hhPos, hhLe, hpDvd⟩ :=
    exists_intervalElement_dvd_of_factorialDivisorFractionalRegion
      hp.pos hHltp hregion
  have hk : N + h ∈ consecutiveInterval N H := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    omega
  change p ∣ (consecutiveInterval N H).prod id
  exact dvd_trans hpDvd (Finset.dvd_prod_of_mem id hk)

/-- In the large-`P` branch, every weight supported on interval divisors has
zero prime sum over the dyadic range `(P,2P)`. -/
theorem eventually_primeEquidistributionSum_eq_zero_of_factorialThree
    : ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      1 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      Real.sqrt (2 * N) < factorialPrimeScale N H →
      2 ≤ factorialPrimeScale N H →
      ∀ {W : ℝ × ℝ → ℂ},
        IsSupportedOnFactorialIntervalDivisors N H W →
        primeEquidistributionSum (factorialPrimeScale N H)
          (Ioo (factorialPrimeScale N H)
            (2 * factorialPrimeScale N H)) W
          (N : ℝ) (N : ℝ) 2 = 0 := by
  filter_upwards
    [eventually_not_prime_dvd_factorialThree_of_large_scale] with
    N hnot H a hH ha haN hcomponent hlarge hP W hWsupport
  unfold primeEquidistributionSum
  apply Finset.sum_eq_zero
  intro p hpMem
  have hsubset :
      Ioo (factorialPrimeScale N H) (2 * factorialPrimeScale N H) ⊆
        Icc (factorialPrimeScale N H) (2 * factorialPrimeScale N H) := by
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hpData := (mem_primesInScaleSet hP hsubset).mp hpMem
  by_contra hWne
  have hpDvd : p ∣ consecutiveProduct N H :=
    hWsupport p hpData.1 hpData.2.1 hpData.2.2 (by simpa using hWne)
  exact (hnot hH ha haN hcomponent hpData.1 hlarge hpData.2.1) hpDvd

/-- Concrete source-facing version of the preceding zero-sum theorem: support
in the final arc of width `1/(10 log² N)` is sufficient. -/
theorem eventually_primeEquidistributionSum_eq_zero_of_factorialThree_finalArc
    : ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      1 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      Real.sqrt (2 * N) < factorialPrimeScale N H →
      2 ≤ factorialPrimeScale N H →
      ∀ {W : ℝ × ℝ → ℂ}, IsSupportedInFactorialFinalArc N W →
        primeEquidistributionSum (factorialPrimeScale N H)
          (Ioo (factorialPrimeScale N H)
            (2 * factorialPrimeScale N H)) W
          (N : ℝ) (N : ℝ) 2 = 0 := by
  filter_upwards
    [eventually_primeEquidistributionSum_eq_zero_of_factorialThree,
      eventually_one_lt_log_nat] with N hzero hlog
  intro H a hH ha haN hcomponent hlarge hP W hW
  exact hzero hH ha haN hcomponent hlarge hP
    (hW.onIntervalDivisors hlog hH)

/-- Exact prime-sum vanishing for the two-coordinate cutoff needed in the
low-`P` branch.  Unlike the large-`P` argument, primes may divide the
interval, but equality of squarefree components forces a square divisor;
the second cutoff coordinate rules that out. -/
theorem eventually_primeEquidistributionSum_eq_zero_of_factorialThree_lowObstruction :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      1 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      2 ≤ factorialPrimeScale N H →
      ∀ {W : ℝ × ℝ → ℂ}, IsSupportedInFactorialLowObstruction N W →
        primeEquidistributionSum (factorialPrimeScale N H)
          (Ioo (factorialPrimeScale N H)
            (2 * factorialPrimeScale N H)) W
          (N : ℝ) (N : ℝ) 2 = 0 := by
  have hlogTwo : ∀ᶠ N : ℕ in atTop, 2 < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop 2)
  filter_upwards [eventually_factorialPrimeScale_lt_prime, hlogTwo] with
    N hprimeScale hlog H a hH ha haN hcomponent hP W hW
  unfold primeEquidistributionSum
  apply Finset.sum_eq_zero
  intro p hpMem
  have hsubset :
      Ioo (factorialPrimeScale N H) (2 * factorialPrimeScale N H) ⊆
        Icc (factorialPrimeScale N H) (2 * factorialPrimeScale N H) := by
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hpData := (mem_primesInScaleSet hP hsubset).mp hpMem
  by_contra hWne
  have hsupport := hW ((N : ℝ) / (p : ℝ))
    ((N : ℝ) / (p : ℝ) ^ 2) (by simpa using hWne)
  have hfinalSupport : IsSupportedInFactorialFinalArc N W := by
    intro x y hne
    exact (hW x y hne).1
  have hpDvdProduct : p ∣ consecutiveProduct N H :=
    hfinalSupport.onIntervalDivisors (by linarith) hH p hpData.1
      hpData.2.1 hpData.2.2 (by simpa using hWne)
  obtain ⟨haLtp, hHLtp⟩ :=
    hprimeScale hH ha haN hcomponent hpData.2.1
  change p ∣ (consecutiveInterval N H).prod id at hpDvdProduct
  obtain ⟨k, hk, hpk⟩ :=
    (hpData.1.prime.dvd_finsetProd_iff id).mp hpDvdProduct
  have hpNotDvdFactorial : ¬p ∣ a.factorial := by
    rw [hpData.1.dvd_factorial, not_le]
    exact haLtp
  have hpSqK : p ^ 2 ∣ k :=
    prime_sq_dvd_intervalElement_of_factorialThree
      hcomponent hk hpData.1 hHLtp hpk hpNotDvdFactorial
  let h := k - N
  have hh : 1 ≤ h := by
    dsimp [h]
    have := (Finset.mem_Ioc.mp hk).1
    omega
  have hhH : h ≤ H := by
    dsimp [h]
    have := (Finset.mem_Ioc.mp hk).2
    omega
  have hadd : N + h = k := by
    dsimp [h]
    have := (Finset.mem_Ioc.mp hk).1
    omega
  have hfourHltP : (4 : ℝ) * H < factorialPrimeScale N H := by
    rw [factorialPrimeScale]
    have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
    have hlogSq : (4 : ℝ) < (Real.log (N : ℝ)) ^ 2 := by nlinarith
    nlinarith
  have hfourHLtp : 4 * H < p := by
    exact_mod_cast (hfourHltP.trans hpData.2.1)
  have hlarge : 10 * H < p ^ 2 := by
    nlinarith
  have hpSqAdd : p ^ 2 ∣ N + h := by
    rw [hadd]
    exact hpSqK
  exact (not_prime_sq_dvd_add_of_quadraticFract_lt_nineTenths
    hpData.1.pos hh hhH hlarge (by simpa only [Nat.cast_pow] using hsupport.2))
    hpSqAdd

/-- Concrete low-`P` zero sum for the explicit two-coordinate shrinking
cutoff. -/
theorem eventually_primeEquidistributionSum_eq_zero_of_factorialThree_lowWeight :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      1 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      2 ≤ factorialPrimeScale N H →
      primeEquidistributionSum (factorialPrimeScale N H)
        (Ioo (factorialPrimeScale N H)
          (2 * factorialPrimeScale N H))
        (factorialLowObstructionWeight N)
        (N : ℝ) (N : ℝ) 2 = 0 := by
  filter_upwards
    [eventually_primeEquidistributionSum_eq_zero_of_factorialThree_lowObstruction,
      eventually_one_lt_log_nat] with N hzero hlog
  intro H a hH ha haN hcomponent hP
  exact hzero hH ha haN hcomponent hP
    (factorialLowObstructionWeight_supported hlog)

/-- Uniform Theorem 2.5 upper bound for the explicit low-`P` cutoff.  Its
coefficient is chosen before the eventual threshold and before the interval
parameters. -/
theorem exists_eventually_factorialLowObstructionIntegralBound_of_taoTheorem25Specialized
    (h25 : TaoTheorem25SpecializedConclusion)
    {ε A K : ℝ} (hε : 0 < ε) (hA : 0 < A) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      1 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      2 ≤ factorialPrimeScale N H →
      VinogradovParameterBound ε K (factorialPrimeScale N H) (N : ℝ) →
      ‖primeEquidistributionIntegral
          (Ioo (factorialPrimeScale N H)
            (2 * factorialPrimeScale N H))
          (factorialLowObstructionWeight N)
          (N : ℝ) (N : ℝ) 2‖ ≤
        C * taoC3Norm (factorialLowObstructionWeight N) *
          factorialPrimeScale N H /
            (Real.log (factorialPrimeScale N H)) ^ A := by
  obtain ⟨C, hC, hbound⟩ := h25 ε hε A hA K hK
  refine ⟨C, hC, ?_⟩
  filter_upwards
    [eventually_primeEquidistributionSum_eq_zero_of_factorialThree_lowWeight]
      with N hzero
  intro H a hH ha haN hcomponent hP hNbound
  have hsubset :
      Ioo (factorialPrimeScale N H) (2 * factorialPrimeScale N H) ⊆
        Icc (factorialPrimeScale N H) (2 * factorialPrimeScale N H) := by
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hestimate := hbound (factorialPrimeScale N H)
    (Ioo (factorialPrimeScale N H) (2 * factorialPrimeScale N H))
    (factorialLowObstructionWeight N) (N : ℝ) hP measurableSet_Ioo
    ordConnected_Ioo hsubset (factorialLowObstructionWeight_contDiff N)
    (factorialLowObstructionWeight_isZ2Periodic N) hNbound
  rw [hzero hH ha haN hcomponent hP, zero_sub, norm_neg] at hestimate
  exact hestimate

/-- After inserting the explicit cutoff estimate, the low-`P` Theorem 2.5
upper bound has a single uniform coefficient and polynomial cost
`log^12 N`. -/
theorem exists_eventually_factorialLowObstructionPolynomialUpper_of_growth
    (h25 : TaoTheorem25SpecializedConclusion)
    {η A : ℝ} (hη : 0 < η) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      2 ≤ factorialPrimeScale N H →
      Real.exp ((Real.log N) ^ (2 / 3 + η)) < H →
      ‖primeEquidistributionIntegral
          (Ioo (factorialPrimeScale N H)
            (2 * factorialPrimeScale N H))
          (factorialLowObstructionWeight N)
          (N : ℝ) (N : ℝ) 2‖ ≤
        K * (Real.log N) ^ 12 * factorialPrimeScale N H /
          (Real.log (factorialPrimeScale N H)) ^ A := by
  obtain ⟨B, hB, htransition⟩ := exists_smoothTransition_C3_bound
  obtain ⟨C, hC, hupper⟩ :=
    exists_eventually_factorialLowObstructionIntegralBound_of_taoTheorem25Specialized
      h25 (ε := veryBadTheorem25Epsilon η) (A := A) (K := 1)
        (veryBadTheorem25Epsilon_pos hη) hA (by norm_num)
  let D : ℝ := max 1 (taoC3Norm factorialQuadraticBumpLift)
  let K : ℝ := C * 32 * 6 * B * (1200 : ℝ) ^ 3 * D
  have hD : 0 < D := by dsimp only [D]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hupper, eventually_one_lt_log_nat,
    eventually_ge_atTop (2 : ℕ)] with N hupperN hlog hN
  intro H a hH ha haN hcomponent hP hgrowth
  have hNbound := factorialVinogradovParameterBound_of_growth
    hN hH hη hlog hgrowth
  have hraw := hupperN (by omega) ha haN hcomponent hP hNbound
  have hc3 := taoC3Norm_factorialLowObstructionWeight_le
    hB htransition hlog.le (N := N)
  have hc3combined :
      C * taoC3Norm (factorialLowObstructionWeight N) ≤
        K * (Real.log N) ^ 12 := by
    calc
      C * taoC3Norm (factorialLowObstructionWeight N) ≤
          C * (32 * (6 * B * (1200 * (Real.log N) ^ 4) ^ 3) * D) :=
        mul_le_mul_of_nonneg_left hc3 hC.le
      _ = K * (Real.log N) ^ 12 := by
        dsimp only [K]
        ring
  have hPPos : 0 < factorialPrimeScale N H :=
    lt_of_lt_of_le (by norm_num) hP
  have hlogPPos : 0 < Real.log (factorialPrimeScale N H) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hP)
  have hdenPos : 0 < (Real.log (factorialPrimeScale N H)) ^ A :=
    Real.rpow_pos_of_pos hlogPPos A
  exact hraw.trans (by
    rw [div_le_div_iff_of_pos_right hdenPos]
    exact mul_le_mul_of_nonneg_right hc3combined hPPos.le)

/-- Direct Theorem 2.5 consumer for the large-`P` branch of Lemma 4.2.  The
prime sum has vanished; the conclusion is precisely the required analytic
upper bound for any smooth periodic cutoff supported in Tao's final arc. -/
theorem eventually_exists_factorialFinalArcIntegralBound_of_taoTheorem25Specialized
    (h25 : TaoTheorem25SpecializedConclusion) :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      1 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      Real.sqrt (2 * N) < factorialPrimeScale N H →
      2 ≤ factorialPrimeScale N H →
      ∀ {W : ℝ × ℝ → ℂ}, ContDiff ℝ ∞ W → IsZ2Periodic W →
        IsSupportedInFactorialFinalArc N W →
      ∀ {ε A K : ℝ}, 0 < ε → 0 < A → 0 < K →
        VinogradovParameterBound ε K (factorialPrimeScale N H) (N : ℝ) →
        ∃ C : ℝ, 0 < C ∧
          ‖primeEquidistributionIntegral
              (Ioo (factorialPrimeScale N H)
                (2 * factorialPrimeScale N H)) W
              (N : ℝ) (N : ℝ) 2‖ ≤
            C * taoC3Norm W * factorialPrimeScale N H /
              (Real.log (factorialPrimeScale N H)) ^ A := by
  filter_upwards
    [eventually_primeEquidistributionSum_eq_zero_of_factorialThree_finalArc]
      with N hzero
  intro H a hH ha haN hcomponent hlarge hP W hWdiff hWperiodic hWsupport
    ε A K hε hA hK hNbound
  obtain ⟨C, hC, hbound⟩ := h25 ε hε A hA K hK
  refine ⟨C, hC, ?_⟩
  have hsubset :
      Ioo (factorialPrimeScale N H) (2 * factorialPrimeScale N H) ⊆
        Icc (factorialPrimeScale N H) (2 * factorialPrimeScale N H) := by
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hestimate := hbound (factorialPrimeScale N H)
    (Ioo (factorialPrimeScale N H) (2 * factorialPrimeScale N H)) W
    (N : ℝ) hP measurableSet_Ioo ordConnected_Ioo hsubset hWdiff
    hWperiodic hNbound
  rw [hzero hH ha haN hcomponent hlarge hP hWsupport,
    zero_sub, norm_neg] at hestimate
  exact hestimate

/-- The preceding upper bound instantiated with the concrete shrinking
one-coordinate bump above. -/
theorem eventually_exists_factorialFinalArcSmoothCutoffIntegralBound_of_taoTheorem25Specialized
    (h25 : TaoTheorem25SpecializedConclusion) :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      1 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      Real.sqrt (2 * N) < factorialPrimeScale N H →
      2 ≤ factorialPrimeScale N H →
      ∀ {ε A K : ℝ}, 0 < ε → 0 < A → 0 < K →
        VinogradovParameterBound ε K (factorialPrimeScale N H) (N : ℝ) →
        ∃ C : ℝ, 0 < C ∧
          ‖primeEquidistributionIntegral
              (Ioo (factorialPrimeScale N H)
                (2 * factorialPrimeScale N H))
              (factorialFinalArcSmoothCutoff N)
              (N : ℝ) (N : ℝ) 2‖ ≤
            C * taoC3Norm (factorialFinalArcSmoothCutoff N) *
              factorialPrimeScale N H /
                (Real.log (factorialPrimeScale N H)) ^ A := by
  filter_upwards
    [eventually_exists_factorialFinalArcIntegralBound_of_taoTheorem25Specialized
      h25, eventually_one_lt_log_nat] with N hbound hlog
  intro H a hH ha haN hcomponent hlarge hP ε A K hε hA hK hNbound
  exact hbound hH ha haN hcomponent hlarge hP
    (factorialFinalArcSmoothCutoff_contDiff N)
    (factorialFinalArcSmoothCutoff_isZ2Periodic N)
    (factorialFinalArcSmoothCutoff_supported hlog)
    hε hA hK hNbound

/-- Source-growth form of the complete high-`P` integral upper-bound half.
The stretched-log contradiction hypothesis now supplies the Theorem 2.5
exponent and frequency range internally, with multiplier one. -/
theorem eventually_exists_factorialFinalArcSmoothCutoffIntegralBound_of_growth
    (h25 : TaoTheorem25SpecializedConclusion) :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      Real.sqrt (2 * N) < factorialPrimeScale N H →
      2 ≤ factorialPrimeScale N H →
      ∀ {η A : ℝ}, 0 < η → 0 < A →
        Real.exp ((Real.log N) ^ (2 / 3 + η)) < H →
        ∃ C : ℝ, 0 < C ∧
          ‖primeEquidistributionIntegral
              (Ioo (factorialPrimeScale N H)
                (2 * factorialPrimeScale N H))
              (factorialFinalArcSmoothCutoff N)
              (N : ℝ) (N : ℝ) 2‖ ≤
            C * taoC3Norm (factorialFinalArcSmoothCutoff N) *
              factorialPrimeScale N H /
                (Real.log (factorialPrimeScale N H)) ^ A := by
  filter_upwards
    [eventually_exists_factorialFinalArcSmoothCutoffIntegralBound_of_taoTheorem25Specialized
      h25, eventually_one_lt_log_nat, eventually_ge_atTop 2] with
      N hbound hlog hN
  intro H a hH ha haN hcomponent hlarge hP η A hη hA hgrowth
  exact hbound (by omega) ha haN hcomponent hlarge hP
    (veryBadTheorem25Epsilon_pos hη) hA (by norm_num)
    (factorialVinogradovParameterBound_of_growth
      hN hH hη hlog hgrowth)

/-- Source-growth integral upper bound for any weight satisfying the exact
plateau specification.  This is the analytic upper half needed by the eventual
normalized cutoff construction. -/
theorem eventually_exists_factorialPlateauIntegralBound_of_growth
    (h25 : TaoTheorem25SpecializedConclusion) :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ} {w : ℝ → ℝ},
      IsFactorialPlateauWeight N w →
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      Real.sqrt (2 * N) < factorialPrimeScale N H →
      2 ≤ factorialPrimeScale N H →
      ∀ {η A : ℝ}, 0 < η → 0 < A →
        Real.exp ((Real.log N) ^ (2 / 3 + η)) < H →
        ∃ C : ℝ, 0 < C ∧
          ‖primeEquidistributionIntegral
              (Ioo (factorialPrimeScale N H)
                (2 * factorialPrimeScale N H))
              (factorialPlateauWeightLift w)
              (N : ℝ) (N : ℝ) 2‖ ≤
            C * taoC3Norm (factorialPlateauWeightLift w) *
              factorialPrimeScale N H /
                (Real.log (factorialPrimeScale N H)) ^ A := by
  filter_upwards
    [eventually_exists_factorialFinalArcIntegralBound_of_taoTheorem25Specialized
      h25, eventually_one_lt_log_nat, eventually_ge_atTop 2] with
      N hbound hlog hN
  intro H a w hw hH ha haN hcomponent hlarge hP η A hη hA hgrowth
  exact hbound (by omega) ha haN hcomponent hlarge hP hw.lift_contDiff
    hw.lift_isZ2Periodic hw.lift_supported
    (veryBadTheorem25Epsilon_pos hη) hA (by norm_num)
    (factorialVinogradovParameterBound_of_growth
      hN hH hη hlog hgrowth)

/-- Combined lower/upper inequality for Tao's high-`P` contradiction.  The
remaining analytic construction only has to provide a plateau weight with a
polynomial `C³` norm and then contradict this displayed sandwich by choosing
`A` sufficiently large. -/
theorem eventually_exists_factorialPlateau_logarithmicSandwich_of_growth
    (h25 : TaoTheorem25SpecializedConclusion) :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ} {w : ℝ → ℝ},
      IsFactorialPlateauWeight N w →
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      Real.sqrt (2 * N) < factorialPrimeScale N H →
      2 ≤ factorialPrimeScale N H →
      4 * factorialPrimeScale N H ≤ (N : ℝ) →
      ∀ {η A : ℝ}, 0 < η → 0 < A →
        Real.exp ((Real.log N) ^ (2 / 3 + η)) < H →
        ∃ C : ℝ, 0 < C ∧
          factorialPrimeScale N H / (240 * (Real.log N) ^ 2) ≤
            Real.log (2 * factorialPrimeScale N H) *
              (C * taoC3Norm (factorialPlateauWeightLift w) *
                factorialPrimeScale N H /
                  (Real.log (factorialPrimeScale N H)) ^ A) := by
  filter_upwards
    [eventually_exists_factorialPlateauIntegralBound_of_growth h25,
      eventually_one_lt_log_nat, eventually_ge_atTop 1] with
      N hupper hlog hN
  intro H a w hw hH ha haN hcomponent hlarge hP hfour η A hη hA hgrowth
  obtain ⟨C, hC, hCupper⟩ :=
    hupper hw hH ha haN hcomponent hlarge hP hη hA hgrowth
  refine ⟨C, hC, ?_⟩
  have hPPos : 0 < factorialPrimeScale N H :=
    lt_of_lt_of_le (by norm_num) hP
  have hlength :
      2 ≤ (N : ℝ) / (2 * factorialPrimeScale N H) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hPPos)]
    nlinarith
  have hlower :=
    factorialPlateauWeight_primeEquidistributionIntegral_norm_lower
      (by omega : 0 < N) hP hlog hw hlength
  exact hlower.trans (mul_le_mul_of_nonneg_left hCupper
    (Real.log_nonneg (by nlinarith :
      1 ≤ 2 * factorialPrimeScale N H)))

/-- Uniform-constant version of the normalized plateau sandwich.  Unlike an
`∀ᶠ N, ∃ C` formulation, the Theorem 2.5 constant is chosen before `N`; this
is the quantifier order needed for the final logarithmic contradiction. -/
theorem exists_eventually_factorialNormalizedPlateau_logarithmicSandwich_of_growth
    (h25 : TaoTheorem25SpecializedConclusion)
    {η A : ℝ} (hη : 0 < η) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
        2 ≤ H → 1 ≤ a → a < N →
        squarefreeComponent (consecutiveProduct N H) =
          squarefreeComponent a.factorial →
        Real.sqrt (2 * N) < factorialPrimeScale N H →
        2 ≤ factorialPrimeScale N H →
        4 * factorialPrimeScale N H ≤ (N : ℝ) →
        Real.exp ((Real.log N) ^ (2 / 3 + η)) < H →
        factorialPrimeScale N H / (240 * (Real.log N) ^ 2) ≤
          Real.log (2 * factorialPrimeScale N H) *
            (C * taoC3Norm (factorialPlateauWeightLift
                (factorialNormalizedPlateauWeight N)) *
              factorialPrimeScale N H /
                (Real.log (factorialPrimeScale N H)) ^ A) := by
  obtain ⟨C, hC, hbound⟩ := h25 (veryBadTheorem25Epsilon η)
    (veryBadTheorem25Epsilon_pos hη) A hA 1 (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards
    [eventually_primeEquidistributionSum_eq_zero_of_factorialThree_finalArc,
      eventually_one_lt_log_nat, eventually_ge_atTop 2] with
      N hzero hlog hN
  intro H a hH ha haN hcomponent hlarge hP hfour hgrowth
  let w : ℝ → ℝ := factorialNormalizedPlateauWeight N
  have hw : IsFactorialPlateauWeight N w :=
    factorialNormalizedPlateauWeight_spec hlog
  have hNbound : VinogradovParameterBound
      (veryBadTheorem25Epsilon η) 1 (factorialPrimeScale N H) (N : ℝ) :=
    factorialVinogradovParameterBound_of_growth
      hN hH hη hlog hgrowth
  have hsubset :
      Ioo (factorialPrimeScale N H) (2 * factorialPrimeScale N H) ⊆
        Icc (factorialPrimeScale N H) (2 * factorialPrimeScale N H) := by
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hupper := hbound (factorialPrimeScale N H)
    (Ioo (factorialPrimeScale N H) (2 * factorialPrimeScale N H))
    (factorialPlateauWeightLift w) (N : ℝ) hP measurableSet_Ioo
    ordConnected_Ioo hsubset hw.lift_contDiff hw.lift_isZ2Periodic hNbound
  rw [hzero (by omega) ha haN hcomponent hlarge hP hw.lift_supported,
    zero_sub, norm_neg] at hupper
  have hPPos : 0 < factorialPrimeScale N H :=
    lt_of_lt_of_le (by norm_num) hP
  have hlength :
      2 ≤ (N : ℝ) / (2 * factorialPrimeScale N H) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) hPPos)]
    nlinarith
  have hlower :=
    factorialPlateauWeight_primeEquidistributionIntegral_norm_lower
      (by omega : 0 < N) hP hlog hw hlength
  change factorialPrimeScale N H / (240 * (Real.log N) ^ 2) ≤
    Real.log (2 * factorialPrimeScale N H) *
      (C * taoC3Norm (factorialPlateauWeightLift w) *
        factorialPrimeScale N H /
          (Real.log (factorialPrimeScale N H)) ^ A)
  exact hlower.trans (mul_le_mul_of_nonneg_left hupper
    (Real.log_nonneg (by nlinarith :
      1 ≤ 2 * factorialPrimeScale N H)))

/-- The normalized plateau sandwich with its `C³` norm eliminated.  All
dependence on Theorem 2.5 and on the fixed scalar transition is absorbed into
one constant chosen before `N`; the remaining loss is exactly `log^12 N`. -/
theorem exists_eventually_factorialNormalizedPlateau_polynomialSandwich_of_growth
    (h25 : TaoTheorem25SpecializedConclusion)
    {η A : ℝ} (hη : 0 < η) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
        2 ≤ H → 1 ≤ a → a < N →
        squarefreeComponent (consecutiveProduct N H) =
          squarefreeComponent a.factorial →
        Real.sqrt (2 * N) < factorialPrimeScale N H →
        2 ≤ factorialPrimeScale N H →
        4 * factorialPrimeScale N H ≤ (N : ℝ) →
        Real.exp ((Real.log N) ^ (2 / 3 + η)) < H →
        factorialPrimeScale N H / (240 * (Real.log N) ^ 2) ≤
          Real.log (2 * factorialPrimeScale N H) *
            (K * (Real.log N) ^ 12 * factorialPrimeScale N H /
              (Real.log (factorialPrimeScale N H)) ^ A) := by
  obtain ⟨B, hB, htransition⟩ := exists_smoothTransition_C3_bound
  obtain ⟨C, hC, hsandwich⟩ :=
    exists_eventually_factorialNormalizedPlateau_logarithmicSandwich_of_growth
      h25 hη hA
  let K : ℝ := C * 24 * B * (1200 : ℝ) ^ 3
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  filter_upwards [hsandwich, eventually_one_lt_log_nat] with N hsandwichN hlog
  intro H a hH ha haN hcomponent hlarge hP hfour hgrowth
  have hsandwich := hsandwichN hH ha haN hcomponent hlarge hP hfour hgrowth
  have hc3 := taoC3Norm_factorialNormalizedPlateauWeightLift_le
    hB htransition hlog.le (N := N)
  have hC3combined :
      C * taoC3Norm
          (factorialPlateauWeightLift (factorialNormalizedPlateauWeight N)) ≤
        K * (Real.log N) ^ 12 := by
    calc
      C * taoC3Norm
          (factorialPlateauWeightLift (factorialNormalizedPlateauWeight N)) ≤
          C * (24 * B * (1200 * (Real.log N) ^ 4) ^ 3) := by
        exact mul_le_mul_of_nonneg_left hc3 hC.le
      _ = K * (Real.log N) ^ 12 := by
        dsimp only [K]
        ring
  have hPPos : 0 < factorialPrimeScale N H :=
    lt_of_lt_of_le (by norm_num) hP
  have hlogPPos : 0 < Real.log (factorialPrimeScale N H) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hP)
  have hdenPos : 0 < (Real.log (factorialPrimeScale N H)) ^ A :=
    Real.rpow_pos_of_pos hlogPPos A
  have hinner :
      C * taoC3Norm
          (factorialPlateauWeightLift (factorialNormalizedPlateauWeight N)) *
            factorialPrimeScale N H /
              (Real.log (factorialPrimeScale N H)) ^ A ≤
        K * (Real.log N) ^ 12 * factorialPrimeScale N H /
          (Real.log (factorialPrimeScale N H)) ^ A := by
    rw [div_le_div_iff_of_pos_right hdenPos]
    exact mul_le_mul_of_nonneg_right hC3combined hPPos.le
  exact hsandwich.trans (mul_le_mul_of_nonneg_left hinner
    (Real.log_nonneg (by nlinarith :
      1 ≤ 2 * factorialPrimeScale N H)))

/-- A Baker--Harman--Pintz-sized interval automatically places the prime
scale `P = H log² N` below `N/4`.  This is the elementary exponent arithmetic
behind the source's use of Proposition 2.3(ii). -/
theorem eventually_four_factorialPrimeScale_le_of_twentyOneFortieth_bound
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop, ∀ {H : ℕ},
      (H : ℝ) ≤ C * (N : ℝ) ^ (21 / 40 : ℝ) →
      4 * factorialPrimeScale N H ≤ (N : ℝ) := by
  have hsmallO :=
    (isLittleO_log_rpow_rpow_atTop 2
      (by norm_num : (0 : ℝ) < 19 / 40)).const_mul_left (4 * C)
  have hdenPositive : ∀ᶠ x : ℝ in atTop,
      0 < ‖x ^ (19 / 40 : ℝ)‖ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]
    exact Real.rpow_pos_of_pos hx _
  have hreal : ∀ᶠ x : ℝ in atTop,
      4 * C * (Real.log x) ^ (2 : ℝ) < x ^ (19 / 40 : ℝ) := by
    filter_upwards
      [hsmallO.eventuallyLT_norm_of_eventually_pos hdenPositive,
        eventually_ge_atTop (1 : ℝ)] with x hxSmall hxOne
    have hright : ‖x ^ (19 / 40 : ℝ)‖ = x ^ (19 / 40 : ℝ) := by
      rw [Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hxOne) _)]
    rw [hright] at hxSmall
    have hleftNonneg : 0 ≤ 4 * C * (Real.log x) ^ (2 : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hC.le)
        (Real.rpow_nonneg (Real.log_nonneg hxOne) _)
    rw [Real.norm_of_nonneg hleftNonneg] at hxSmall
    exact hxSmall
  have hnat :=
    tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat, eventually_ge_atTop 1] with N hsmall hN
  intro H hHbound
  have hNPos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNpowPos : 0 < (N : ℝ) ^ (21 / 40 : ℝ) :=
    Real.rpow_pos_of_pos hNPos _
  have hsmallNat :
      4 * C * (Real.log (N : ℝ)) ^ (2 : ℕ) <
        (N : ℝ) ^ (19 / 40 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact hsmall
  rw [factorialPrimeScale]
  apply le_of_lt
  calc
    4 * ((H : ℝ) * (Real.log N) ^ 2) ≤
        4 * (C * (N : ℝ) ^ (21 / 40 : ℝ)) * (Real.log N) ^ 2 := by
      have hfourBound : 4 * (H : ℝ) ≤
          4 * (C * (N : ℝ) ^ (21 / 40 : ℝ)) :=
        mul_le_mul_of_nonneg_left hHbound (by norm_num)
      have hlogSq : 0 ≤ (Real.log (N : ℝ)) ^ 2 := sq_nonneg _
      have hmul := mul_le_mul_of_nonneg_right hfourBound hlogSq
      simpa only [mul_assoc] using hmul
    _ = (N : ℝ) ^ (21 / 40 : ℝ) *
        (4 * C * (Real.log N) ^ 2) := by ring
    _ < (N : ℝ) ^ (21 / 40 : ℝ) *
        (N : ℝ) ^ (19 / 40 : ℝ) :=
      mul_lt_mul_of_pos_left hsmallNat hNpowPos
    _ = (N : ℝ) ^ ((21 / 40 : ℝ) + 19 / 40) := by
      rw [Real.rpow_add hNPos]
    _ = (N : ℝ) := by norm_num

/-- Proposition 2.3(ii) supplies the upper-scale hypothesis required by the
large-`P` contradiction for every type-`F₃` interval. -/
theorem eventually_four_factorialPrimeScale_le_of_taoProposition23ii
    (h23ii : TaoProposition23iiConclusion) :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      4 * factorialPrimeScale N H ≤ (N : ℝ) := by
  obtain ⟨C, hC, hBHP⟩ := h23ii
  filter_upwards
    [eventually_four_factorialPrimeScale_le_of_twentyOneFortieth_bound hC]
      with N hscale
  intro H a hH ha haN hcomponent
  have hN : 1 ≤ N := by omega
  have hf3 : IsFactorialThreeInterval N H :=
    ⟨by omega, a, ha, haN, hcomponent⟩
  have hfree : ∀ p : ℕ, N < p → p ≤ N + H → ¬p.Prime := by
    intro p hpLower hpUpper
    apply hf3.not_prime_of_mem
    simpa only [consecutiveInterval, Finset.mem_Ioc] using
      (show N < p ∧ p ≤ N + H from ⟨hpLower, hpUpper⟩)
  exact hscale (hBHP N H hN (by omega) hfree)

/-- Completion of Tao's large-`P` contradiction, conditional only on the
source upper-scale inequality `4P ≤ N`.  The lower bound coming from
`P > √(2N)` gives `log P ≥ (log N)/2`; with `A = 20`, the polynomial sandwich
would force `log^5 N` to remain bounded. -/
theorem eventually_not_factorialThree_of_large_primeScale_and_growth
    (h25 : TaoTheorem25SpecializedConclusion) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      Real.sqrt (2 * N) < factorialPrimeScale N H →
      2 ≤ factorialPrimeScale N H →
      4 * factorialPrimeScale N H ≤ (N : ℝ) →
      Real.exp ((Real.log N) ^ (2 / 3 + η)) < H → False := by
  obtain ⟨K, hK, hsandwich⟩ :=
    exists_eventually_factorialNormalizedPlateau_polynomialSandwich_of_growth
      h25 hη (by norm_num : (0 : ℝ) < 20)
  have hlogPowTop : Tendsto (fun N : ℕ => (Real.log N) ^ 5) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlargeLog : ∀ᶠ N : ℕ in atTop,
      240 * K * (2 : ℝ) ^ 20 < (Real.log N) ^ 5 :=
    hlogPowTop.eventually (eventually_gt_atTop _)
  filter_upwards [hsandwich, hlargeLog, eventually_one_lt_log_nat] with
      N hsandwichN hlargeLogN hlog
  intro H a hH ha haN hcomponent hlarge hP hfour hgrowth
  have hs := hsandwichN hH ha haN hcomponent hlarge hP hfour hgrowth
  let P : ℝ := factorialPrimeScale N H
  let L : ℝ := Real.log N
  have hPPos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hNPos : 0 < (N : ℝ) := by
    nlinarith
  have hLPos : 0 < L := by
    dsimp only [L]
    linarith
  have hlogPPos : 0 < Real.log P :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hP)
  have hleftDen : 0 < 240 * L ^ 2 := by positivity
  have hrightDen : 0 < (Real.log P) ^ 20 := by positivity
  have hsqrtSq : (Real.sqrt (2 * (N : ℝ))) ^ 2 = 2 * (N : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hNPsq : (N : ℝ) < P ^ 2 := by
    have hsquare : (Real.sqrt (2 * (N : ℝ))) ^ 2 < P ^ 2 :=
      (sq_lt_sq₀ (Real.sqrt_nonneg _) hPPos.le).mpr (by
        simpa only [P] using hlarge)
    rw [hsqrtSq] at hsquare
    nlinarith
  have hlogLower : L / 2 < Real.log P := by
    have hlogNPsq : Real.log (N : ℝ) < Real.log (P ^ 2) :=
      Real.strictMonoOn_log hNPos (pow_pos hPPos 2) hNPsq
    rw [Real.log_pow] at hlogNPsq
    norm_num at hlogNPsq
    dsimp only [L]
    nlinarith
  have htwoPLe : 2 * P ≤ (N : ℝ) := by
    dsimp only [P] at hfour ⊢
    nlinarith
  have hlogUpper : Real.log (2 * P) ≤ L := by
    dsimp only [L]
    exact Real.strictMonoOn_log.monotoneOn (mul_pos (by norm_num) hPPos)
      hNPos htwoPLe
  have hs' : P / (240 * L ^ 2) ≤
      (Real.log (2 * P) * (K * L ^ 12 * P)) / (Real.log P) ^ 20 := by
    have hsourceRpow : P / (240 * L ^ 2) ≤
        Real.log (2 * P) *
          (K * L ^ 12 * P / (Real.log P) ^ (20 : ℝ)) := by
      simpa only [P, L] using hs
    have hsource : P / (240 * L ^ 2) ≤
        Real.log (2 * P) *
          (K * L ^ 12 * P / (Real.log P) ^ (20 : ℕ)) := by
      have heqPow : (Real.log P) ^ (20 : ℝ) =
          (Real.log P) ^ (20 : ℕ) := by
        exact Real.rpow_natCast (Real.log P) 20
      rw [heqPow] at hsourceRpow
      exact hsourceRpow
    calc
      P / (240 * L ^ 2) ≤ Real.log (2 * P) *
          (K * L ^ 12 * P / (Real.log P) ^ 20) := hsource
      _ = (Real.log (2 * P) * (K * L ^ 12 * P)) /
          (Real.log P) ^ 20 := by
        field_simp [hlogPPos.ne']
  have hcross : P * (Real.log P) ^ 20 ≤
      (Real.log (2 * P) * (K * L ^ 12 * P)) * (240 * L ^ 2) :=
    (div_le_div_iff₀ hleftDen hrightDen).mp hs'
  have hcancel : (Real.log P) ^ 20 ≤
      Real.log (2 * P) * (K * L ^ 12) * (240 * L ^ 2) := by
    apply (mul_le_mul_iff_of_pos_left hPPos).mp
    calc
      P * (Real.log P) ^ 20 ≤
          (Real.log (2 * P) * (K * L ^ 12 * P)) * (240 * L ^ 2) := hcross
      _ = P * (Real.log (2 * P) * (K * L ^ 12) * (240 * L ^ 2)) := by
        ring
  have hdenUpper : (Real.log P) ^ 20 ≤ 240 * K * L ^ 15 := by
    calc
      (Real.log P) ^ 20 ≤
          Real.log (2 * P) * (K * L ^ 12) * (240 * L ^ 2) := hcancel
      _ ≤ L * (K * L ^ 12) * (240 * L ^ 2) := by
        gcongr
      _ = 240 * K * L ^ 15 := by ring
  have hdenLower : (L / 2) ^ 20 ≤ (Real.log P) ^ 20 :=
    pow_le_pow_left₀ (by positivity) hlogLower.le 20
  have hmain : L ^ 20 ≤ (240 * K * L ^ 15) * (2 : ℝ) ^ 20 := by
    have hdiv : L ^ 20 / (2 : ℝ) ^ 20 ≤ 240 * K * L ^ 15 := by
      rw [← div_pow]
      exact hdenLower.trans hdenUpper
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 20)).mp hdiv
  have hfactor : L ^ 5 * L ^ 15 ≤
      (240 * K * (2 : ℝ) ^ 20) * L ^ 15 := by
    calc
      L ^ 5 * L ^ 15 = L ^ 20 := by ring
      _ ≤ (240 * K * L ^ 15) * (2 : ℝ) ^ 20 := hmain
      _ = (240 * K * (2 : ℝ) ^ 20) * L ^ 15 := by ring
  have hbounded : L ^ 5 ≤ 240 * K * (2 : ℝ) ^ 20 :=
    (mul_le_mul_iff_of_pos_right (pow_pos hLPos 15)).mp hfactor
  exact (not_lt_of_ge hbounded) (by simpa only [L] using hlargeLogN)

/-- Large-`P` half of Lemma 4.2 with the Baker--Harman--Pintz upper scale
discharged through the exact Proposition 2.3(ii) interface. -/
theorem eventually_not_factorialThree_of_large_primeScale_and_growth_of_inputs
    (h25 : TaoTheorem25SpecializedConclusion)
    (h23ii : TaoProposition23iiConclusion) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ {H a : ℕ},
      2 ≤ H → 1 ≤ a → a < N →
      squarefreeComponent (consecutiveProduct N H) =
        squarefreeComponent a.factorial →
      Real.sqrt (2 * N) < factorialPrimeScale N H →
      2 ≤ factorialPrimeScale N H →
      Real.exp ((Real.log N) ^ (2 / 3 + η)) < H → False := by
  filter_upwards
    [eventually_not_factorialThree_of_large_primeScale_and_growth h25 hη,
      eventually_four_factorialPrimeScale_le_of_taoProposition23ii h23ii] with
      N hcontra hupper
  intro H a hH ha haN hcomponent hlarge hP hgrowth
  exact hcontra hH ha haN hcomponent hlarge hP
    (hupper hH ha haN hcomponent) hgrowth

end

end Tao2026
