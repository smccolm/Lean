import Tao2026.PowerfulExtraction
import Tao2026.PrimeEquidistribution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The equidistribution obstruction for very bad intervals

This module formalizes the arithmetic half of Tao's proof of Lemma 3.1.  If
`H < p ≤ 2H` and the first reciprocal residue lies in the final tenth of a
period while the quadratic reciprocal residue lies in the first nine tenths,
then some `N+h`, `1 ≤ h ≤ H`, is divisible by `p` but not by `p²`.  A very bad
interval forbids this.  Consequently every smooth periodic weight supported
in that rectangle has zero prime sum, and Theorem 2.5 converts this exact
vanishing into the source integral upper bound.
-/

open Set MeasureTheory
open scoped ContDiff

namespace Tao2026

noncomputable section

/-- Integer form of the source rectangle
`{N/p} ≥ 0.9`, `{N/p²} < 0.9`. -/
def InVeryBadForbiddenResidueRegion (N p : ℕ) : Prop :=
  9 * p ≤ 10 * (N % p) ∧
    10 * (N % (p ^ 2)) < 9 * (p ^ 2)

/-- Membership in the forbidden residue rectangle produces the interval
element which is divisible by `p` exactly to exponent one or less. -/
theorem exists_nonsquare_intervalElement_of_forbiddenResidues
    {N H p : ℕ} (hp : p.Prime) (hHltp : H < p) (hpLe : p ≤ 2 * H)
    (hregion : InVeryBadForbiddenResidueRegion N p) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ p ∣ N + h ∧ ¬p ^ 2 ∣ N + h := by
  let r := N % p
  let h := p - r
  have hrLt : r < p := Nat.mod_lt N hp.pos
  have hrPos : 0 < r := by
    dsimp [InVeryBadForbiddenResidueRegion, r] at hregion
    omega
  have hhPos : 1 ≤ h := by
    dsimp [h]
    omega
  have hten : 10 * h ≤ p := by
    dsimp [InVeryBadForbiddenResidueRegion, h, r] at hregion ⊢
    omega
  have hhLe : h ≤ H := by omega
  have hpDvd : p ∣ N + h := by
    refine ⟨N / p + 1, ?_⟩
    rw [mul_add, mul_one]
    have hdecomp := Nat.mod_add_div N p
    dsimp [h, r]
    omega
  refine ⟨h, hhPos, hhLe, hpDvd, ?_⟩
  intro hpSqDvd
  let r₂ := N % (p ^ 2)
  have hpSqPos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hr₂Lt : r₂ < p ^ 2 := Nat.mod_lt N hpSqPos
  have hdecomp₂ := Nat.mod_add_div N (p ^ 2)
  have hrewrite :
      N + h = (r₂ + h) + p ^ 2 * (N / p ^ 2) := by
    dsimp [r₂] at hdecomp₂ ⊢
    omega
  have hpSqDvdSum : p ^ 2 ∣ r₂ + h := by
    rw [hrewrite] at hpSqDvd
    exact (Nat.dvd_add_iff_left (dvd_mul_right (p ^ 2) (N / p ^ 2))).mpr
      hpSqDvd
  have hpLeSq : p ≤ p ^ 2 := by
    nlinarith [hp.two_le]
  have hr₂Bound : 10 * r₂ < 9 * (p ^ 2) := by
    simpa only [InVeryBadForbiddenResidueRegion, r₂] using hregion.2
  have hsumLt : r₂ + h < p ^ 2 := by
    omega
  have hhLeSum : h ≤ r₂ + h := by omega
  have hsumPos : 0 < r₂ + h :=
    lt_of_lt_of_le (by omega : 0 < 1) (le_trans hhPos hhLeSum)
  have := Nat.le_of_dvd hsumPos hpSqDvdSum
  omega

/-- A very bad interval excludes the complete discrete source rectangle for
every prime in the dyadic range immediately above its length. -/
theorem not_forbiddenResidues_of_veryBad
    {N H p : ℕ} (hveryBad : IsVeryBadInterval N H) (hp : p.Prime)
    (hHltp : H < p) (hpLe : p ≤ 2 * H) :
    ¬InVeryBadForbiddenResidueRegion N p := by
  intro hregion
  obtain ⟨h, hhPos, hhLe, hpDvd, hpSqNotDvd⟩ :=
    exists_nonsquare_intervalElement_of_forbiddenResidues hp hHltp hpLe hregion
  have hk : N + h ∈ consecutiveInterval N H := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    omega
  exact hpSqNotDvd
    (prime_sq_dvd_intervalElement_of_veryBad hveryBad hk hp hHltp hpDvd)

/-- A large prime factor of a very bad consecutive product forces Tao's
quadratic scale inequality. This isolates the use of Sylvester--Schur from
the local powerfulness argument. -/
theorem IsVeryBadInterval.square_length_le_two_mul_start_of_large_prime
    {N H : ℕ} (hN : 1 ≤ N) (hveryBad : IsVeryBadInterval N H)
    (hlarge : ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H) :
    H ^ 2 ≤ 2 * N := by
  obtain ⟨p, hp, hHltp, hpProduct⟩ := hlarge
  change p ∣ (consecutiveInterval N H).prod id at hpProduct
  obtain ⟨k, hk, hpk⟩ :=
    (hp.prime.dvd_finsetProd_iff id).mp hpProduct
  have hkPos : 0 < k := by
    have := (Finset.mem_Ioc.mp hk).1
    omega
  have hkLe : k ≤ N + H := (Finset.mem_Ioc.mp hk).2
  have hpSq : p ^ 2 ∣ k :=
    prime_sq_dvd_intervalElement_of_veryBad hveryBad hk hp hHltp hpk
  have hpSqLe : p ^ 2 ≤ k := Nat.le_of_dvd hkPos hpSq
  have hHltN : H < N := hveryBad.length_lt_start_of_pos hN
  nlinarith

/-- Real quotient form of the scale inequality used by the geometric lower
bound in Lemma 3.1. -/
theorem IsVeryBadInterval.one_half_le_start_div_length_sq_of_large_prime
    {N H : ℕ} (hN : 1 ≤ N) (hveryBad : IsVeryBadInterval N H)
    (hlarge : ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H) :
    (1 / 2 : ℝ) ≤ (N : ℝ) / H ^ 2 := by
  have hHPos : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hveryBad.1
  have hHReal : (0 : ℝ) < H := by exact_mod_cast hHPos
  have hsq := hveryBad.square_length_le_two_mul_start_of_large_prime hN hlarge
  have hsqReal : (H : ℝ) ^ 2 ≤ 2 * N := by exact_mod_cast hsq
  rw [le_div_iff₀ (sq_pos_of_pos hHReal)]
  nlinarith

/-- Sylvester--Schur supplies the exact scale hypothesis required by Tao's
quadratic slice argument for every positive-start very bad interval. -/
theorem IsVeryBadInterval.one_half_le_start_div_length_sq_of_sylvesterSchur
    (hSS : SylvesterSchurConclusion) {N H : ℕ} (hN : 1 ≤ N)
    (hveryBad : IsVeryBadInterval N H) :
    (1 / 2 : ℝ) ≤ (N : ℝ) / H ^ 2 := by
  have hHltN := hveryBad.length_lt_start_of_pos hN
  exact hveryBad.one_half_le_start_div_length_sq_of_large_prime hN
    (hSS hveryBad.1 hHltN)

/-- Standard binomial Sylvester--Schur supplies the same exact scale bound. -/
theorem IsVeryBadInterval.one_half_le_start_div_length_sq_of_binomial_sylvesterSchur
    (hSS : BinomialSylvesterSchurConclusion) {N H : ℕ} (hN : 1 ≤ N)
    (hveryBad : IsVeryBadInterval N H) :
    (1 / 2 : ℝ) ≤ (N : ℝ) / H ^ 2 :=
  hveryBad.one_half_le_start_div_length_sq_of_sylvesterSchur
    (sylvesterSchurConclusion_of_binomial hSS) hN

/-- The quadratic-window form is sufficient because failure of the desired
scale bound is exactly the hypothesis `2N < H²`. -/
theorem IsVeryBadInterval.one_half_le_start_div_length_sq_of_quadraticWindow_sylvesterSchur
    (hSS : QuadraticWindowSylvesterSchurConclusion) {N H : ℕ} (hN : 1 ≤ N)
    (hveryBad : IsVeryBadInterval N H) :
    (1 / 2 : ℝ) ≤ (N : ℝ) / H ^ 2 := by
  have hHPos : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hveryBad.1
  have hHReal : (0 : ℝ) < H := by exact_mod_cast hHPos
  have hHltN := hveryBad.length_lt_start_of_pos hN
  have hsq : H ^ 2 ≤ 2 * N := by
    by_contra hnot
    have hwindow : 2 * N < H ^ 2 := Nat.lt_of_not_ge hnot
    exact hnot (hveryBad.square_length_le_two_mul_start_of_large_prime hN
      (hSS hveryBad.1 hHltN hwindow))
  have hsqReal : (H : ℝ) ^ 2 ≤ 2 * N := by exact_mod_cast hsq
  rw [le_div_iff₀ (sq_pos_of_pos hHReal)]
  nlinarith

/-- Unconditional eventual form of the exact quadratic scale bound.  The
large prime is supplied by the frozen PNT and binomial-factorization argument
in `VeryBadIntervals`, rather than by an imported Sylvester--Schur theorem. -/
theorem eventually_one_half_le_start_div_length_sq_of_veryBad :
    ∀ᶠ H : ℕ in Filter.atTop, ∀ N : ℕ, 1 ≤ N → IsVeryBadInterval N H →
      (1 / 2 : ℝ) ≤ (N : ℝ) / H ^ 2 := by
  filter_upwards
    [eventually_exists_large_prime_dvd_consecutiveProduct_quadraticWindow]
      with H hlarge N hN hveryBad
  have hHPos : 0 < H := lt_of_lt_of_le Nat.zero_lt_one hveryBad.1
  have hHReal : (0 : ℝ) < H := by exact_mod_cast hHPos
  have hHltN := hveryBad.length_lt_start_of_pos hN
  have hsq : H ^ 2 ≤ 2 * N := by
    by_contra hnot
    have hwindow : 2 * N < H ^ 2 := Nat.lt_of_not_ge hnot
    exact hnot (hveryBad.square_length_le_two_mul_start_of_large_prime hN
      (hlarge N hHltN hwindow))
  have hsqReal : (H : ℝ) ^ 2 ≤ 2 * N := by exact_mod_cast hsq
  rw [le_div_iff₀ (sq_pos_of_pos hHReal)]
  nlinarith

/-- Real fractional-part form of the rectangle used in the paper. -/
def InVeryBadForbiddenFractionalRegion (N p : ℕ) : Prop :=
  (9 / 10 : ℝ) ≤ Int.fract ((N : ℝ) / (p : ℝ)) ∧
    Int.fract ((N : ℝ) / ((p ^ 2 : ℕ) : ℝ)) < (9 / 10 : ℝ)

theorem forbiddenFractionalRegion_iff_residues
    {N p : ℕ} (hp : 0 < p) :
    InVeryBadForbiddenFractionalRegion N p ↔
      InVeryBadForbiddenResidueRegion N p := by
  rw [InVeryBadForbiddenFractionalRegion,
    Int.fract_div_natCast_eq_div_natCast_mod,
    Int.fract_div_natCast_eq_div_natCast_mod]
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have hpSq : 0 < p ^ 2 := pow_pos hp 2
  have hpSqReal : (0 : ℝ) < (p ^ 2 : ℕ) := by exact_mod_cast hpSq
  constructor
  · rintro ⟨hfirst, hsecond⟩
    rw [le_div_iff₀ hpReal] at hfirst
    rw [div_lt_iff₀ hpSqReal] at hsecond
    have hfirstReal :
        (9 : ℝ) * (p : ℝ) ≤ 10 * ((N % p : ℕ) : ℝ) := by
      nlinarith
    have hsecondReal :
        (10 : ℝ) * ((N % (p ^ 2) : ℕ) : ℝ) <
          9 * ((p ^ 2 : ℕ) : ℝ) := by
      nlinarith
    constructor
    · exact_mod_cast hfirstReal
    · exact_mod_cast hsecondReal
  · rintro ⟨hfirst, hsecond⟩
    have hfirstReal :
        (9 : ℝ) * (p : ℝ) ≤ 10 * ((N % p : ℕ) : ℝ) := by
      exact_mod_cast hfirst
    have hsecondReal :
        (10 : ℝ) * ((N % (p ^ 2) : ℕ) : ℝ) <
          9 * ((p ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hsecond
    constructor
    · rw [le_div_iff₀ hpReal]
      nlinarith
    · rw [div_lt_iff₀ hpSqReal]
      nlinarith

/-- A weight is supported in the closed/open rectangle used by Tao to detect
a prime divisor which does not occur twice. -/
def IsSupportedInVeryBadForbiddenRegion (W : ℝ × ℝ → ℂ) : Prop :=
  ∀ x y : ℝ, W (x, y) ≠ 0 →
    (9 / 10 : ℝ) ≤ Int.fract x ∧ Int.fract y < (9 / 10 : ℝ)

/-- A smooth period-one bump supported, modulo one, between `a` and `b`.
The two sine factors change sign together under an integral translation. -/
def smoothPeriodicIntervalBump (a b x : ℝ) : ℝ :=
  expNegInvGlue
    (Real.sin (Real.pi * (x - a)) * Real.sin (Real.pi * (b - x)))

theorem smoothPeriodicIntervalBump_contDiff (a b : ℝ) :
    ContDiff ℝ ∞ (smoothPeriodicIntervalBump a b) := by
  rw [contDiff_infty]
  intro n
  have hinner : ContDiff ℝ n (fun x : ℝ =>
      Real.sin (Real.pi * (x - a)) *
        Real.sin (Real.pi * (b - x))) := by
    apply ContDiff.mul
    · exact Real.contDiff_sin.comp
        (contDiff_const.mul (contDiff_id.sub contDiff_const))
    · exact Real.contDiff_sin.comp
        (contDiff_const.mul (contDiff_const.sub contDiff_id))
  have hout : ContDiff ℝ n expNegInvGlue := expNegInvGlue.contDiff
  simpa only [smoothPeriodicIntervalBump, Function.comp_apply] using
    hout.comp hinner

theorem smoothPeriodicIntervalBump_add_int
    (a b x : ℝ) (m : ℤ) :
    smoothPeriodicIntervalBump a b (x + m) =
      smoothPeriodicIntervalBump a b x := by
  unfold smoothPeriodicIntervalBump
  congr 1
  have hfirst :
      Real.pi * (x + (m : ℝ) - a) =
        Real.pi * (x - a) + (m : ℝ) * Real.pi := by ring
  have hsecond :
      Real.pi * (b - (x + (m : ℝ))) =
        Real.pi * (b - x) - (m : ℝ) * Real.pi := by ring
  rw [hfirst, Real.sin_add_int_mul_pi, hsecond,
    Real.sin_sub_int_mul_pi]
  have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    have habs : |(-1 : ℝ) ^ m| = 1 := abs_neg_one_zpow m
    have hsquare := sq_abs ((-1 : ℝ) ^ m)
    rw [habs] at hsquare
    nlinarith
  calc
    (-1 : ℝ) ^ m * Real.sin (Real.pi * (x - a)) *
        ((-1 : ℝ) ^ m * Real.sin (Real.pi * (b - x))) =
      (((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) *
        (Real.sin (Real.pi * (x - a)) *
          Real.sin (Real.pi * (b - x)))) := by ring
    _ = _ := by rw [hsign, one_mul]

theorem fract_mem_finalTenth_of_smoothPeriodicIntervalBump_ne_zero
    {x : ℝ} (hx : smoothPeriodicIntervalBump (9 / 10) 1 x ≠ 0) :
    (9 / 10 : ℝ) ≤ Int.fract x := by
  let f := Int.fract x
  have heq : smoothPeriodicIntervalBump (9 / 10) 1 x =
      smoothPeriodicIntervalBump (9 / 10) 1 f := by
    simpa only [f, Int.fract_add_floor] using
      smoothPeriodicIntervalBump_add_int (9 / 10) 1 f ⌊x⌋
  have hfne : smoothPeriodicIntervalBump (9 / 10) 1 f ≠ 0 := by
    rwa [heq] at hx
  have hproductPos :
      0 < Real.sin (Real.pi * (f - 9 / 10)) *
        Real.sin (Real.pi * (1 - f)) := by
    apply lt_of_not_ge
    intro hnonpos
    exact hfne (expNegInvGlue.zero_of_nonpos hnonpos)
  have hfNonneg : 0 ≤ f := Int.fract_nonneg x
  have hfLtOne : f < 1 := Int.fract_lt_one x
  by_contra hnot
  have hfLt : f < 9 / 10 := lt_of_not_ge hnot
  have hfirstNonpos : Real.sin (Real.pi * (f - 9 / 10)) ≤ 0 := by
    have hz : Real.pi * (9 / 10 - f) ∈ Icc 0 Real.pi := by
      constructor
      · positivity
      · nlinarith [Real.pi_pos]
    have hsin := Real.sin_nonneg_of_mem_Icc hz
    rw [show Real.pi * (f - 9 / 10) =
      -(Real.pi * (9 / 10 - f)) by ring, Real.sin_neg]
    linarith
  have hsecondNonneg : 0 ≤ Real.sin (Real.pi * (1 - f)) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg
    hfirstNonpos hsecondNonneg)) hproductPos

theorem fract_lt_nineTenths_of_smoothPeriodicIntervalBump_ne_zero
    {x : ℝ} (hx : smoothPeriodicIntervalBump 0 (9 / 10) x ≠ 0) :
    Int.fract x < (9 / 10 : ℝ) := by
  let f := Int.fract x
  have heq : smoothPeriodicIntervalBump 0 (9 / 10) x =
      smoothPeriodicIntervalBump 0 (9 / 10) f := by
    simpa only [f, Int.fract_add_floor] using
      smoothPeriodicIntervalBump_add_int 0 (9 / 10) f ⌊x⌋
  have hfne : smoothPeriodicIntervalBump 0 (9 / 10) f ≠ 0 := by
    rwa [heq] at hx
  have hproductPos :
      0 < Real.sin (Real.pi * (f - 0)) *
        Real.sin (Real.pi * (9 / 10 - f)) := by
    apply lt_of_not_ge
    intro hnonpos
    exact hfne (expNegInvGlue.zero_of_nonpos hnonpos)
  have hfNonneg : 0 ≤ f := Int.fract_nonneg x
  have hfLtOne : f < 1 := Int.fract_lt_one x
  by_contra hnot
  have hfLower : 9 / 10 ≤ f := le_of_not_gt hnot
  have hfirstNonneg : 0 ≤ Real.sin (Real.pi * (f - 0)) := by
    apply Real.sin_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_pos]
  have hsecondNonpos : Real.sin (Real.pi * (9 / 10 - f)) ≤ 0 := by
    have hz : Real.pi * (f - 9 / 10) ∈ Icc 0 Real.pi := by
      constructor <;> nlinarith [Real.pi_pos]
    have hsin := Real.sin_nonneg_of_mem_Icc hz
    rw [show Real.pi * (9 / 10 - f) =
      -(Real.pi * (f - 9 / 10)) by ring, Real.sin_neg]
    linarith
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
    hfirstNonneg hsecondNonpos)) hproductPos

/-- An explicit fixed smooth cutoff for the forbidden rectangle in Lemma 3.1. -/
def veryBadSmoothCutoff (z : ℝ × ℝ) : ℂ :=
  ((smoothPeriodicIntervalBump (9 / 10) 1 z.1 *
    smoothPeriodicIntervalBump 0 (9 / 10) z.2 : ℝ) : ℂ)

theorem veryBadSmoothCutoff_contDiff : ContDiff ℝ ∞ veryBadSmoothCutoff := by
  rw [contDiff_infty]
  intro n
  have hn : (n : ℕ∞ω) < ∞ :=
    WithTop.coe_lt_coe.mpr (ENat.coe_lt_top n)
  have hx : ContDiff ℝ n (fun z : ℝ × ℝ =>
      smoothPeriodicIntervalBump (9 / 10) 1 z.1) :=
    ((smoothPeriodicIntervalBump_contDiff (9 / 10) 1).of_le hn.le).comp
      contDiff_fst
  have hy : ContDiff ℝ n (fun z : ℝ × ℝ =>
      smoothPeriodicIntervalBump 0 (9 / 10) z.2) :=
    ((smoothPeriodicIntervalBump_contDiff 0 (9 / 10)).of_le hn.le).comp
      contDiff_snd
  have hreal := hx.mul hy
  simpa only [veryBadSmoothCutoff, Function.comp_apply,
    Complex.ofRealCLM_apply] using Complex.ofRealCLM.contDiff.comp hreal

theorem veryBadSmoothCutoff_isZ2Periodic :
    IsZ2Periodic veryBadSmoothCutoff := by
  intro x y m n
  unfold veryBadSmoothCutoff
  rw [smoothPeriodicIntervalBump_add_int (9 / 10) 1 x m,
    smoothPeriodicIntervalBump_add_int 0 (9 / 10) y n]

theorem veryBadSmoothCutoff_supported :
    IsSupportedInVeryBadForbiddenRegion veryBadSmoothCutoff := by
  intro x y hne
  have hprod :
      smoothPeriodicIntervalBump (9 / 10) 1 x *
        smoothPeriodicIntervalBump 0 (9 / 10) y ≠ 0 := by
    simpa only [veryBadSmoothCutoff, Complex.ofReal_ne_zero] using hne
  exact ⟨
    fract_mem_finalTenth_of_smoothPeriodicIntervalBump_ne_zero
      (left_ne_zero_of_mul hprod),
    fract_lt_nineTenths_of_smoothPeriodicIntervalBump_ne_zero
      (right_ne_zero_of_mul hprod)⟩

theorem veryBadSmoothCutoff_re_nonneg (z : ℝ × ℝ) :
    0 ≤ (veryBadSmoothCutoff z).re := by
  simp only [veryBadSmoothCutoff, Complex.ofReal_re]
  exact mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

theorem veryBadSmoothCutoff_at_center_ne_zero :
    veryBadSmoothCutoff ((19 / 20 : ℝ), (9 / 20 : ℝ)) ≠ 0 := by
  rw [veryBadSmoothCutoff, Complex.ofReal_ne_zero, mul_ne_zero_iff]
  constructor
  · apply ne_of_gt
    apply expNegInvGlue.pos_of_pos
    apply mul_pos <;> apply Real.sin_pos_of_pos_of_lt_pi <;>
      nlinarith [Real.pi_pos]
  · apply ne_of_gt
    apply expNegInvGlue.pos_of_pos
    apply mul_pos <;> apply Real.sin_pos_of_pos_of_lt_pi <;>
      nlinarith [Real.pi_pos]

/-- Tao's closed inner rectangle, separated from every edge of the support. -/
def veryBadInnerRectangle : Set (ℝ × ℝ) :=
  Icc (91 / 100 : ℝ) (99 / 100) ×ˢ
    Icc (1 / 100 : ℝ) (89 / 100)

theorem veryBadSmoothCutoff_re_pos_of_mem_innerRectangle
    {z : ℝ × ℝ} (hz : z ∈ veryBadInnerRectangle) :
    0 < (veryBadSmoothCutoff z).re := by
  rcases hz with ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩
  simp only [veryBadSmoothCutoff, Complex.ofReal_re]
  apply mul_pos <;> apply expNegInvGlue.pos_of_pos <;> apply mul_pos
  · apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos (by norm_num at hxlo ⊢; linarith)
    · have := mul_lt_mul_of_pos_left
        (show z.1 - 9 / 10 < (1 : ℝ) by norm_num at hxhi ⊢; linarith)
        Real.pi_pos
      simpa using this
  · apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos (by norm_num at hxhi ⊢; linarith)
    · have := mul_lt_mul_of_pos_left
        (show 1 - z.1 < (1 : ℝ) by norm_num at hxlo ⊢; linarith)
        Real.pi_pos
      simpa using this
  · apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos (by norm_num at hylo ⊢; linarith)
    · have := mul_lt_mul_of_pos_left
        (show z.2 - 0 < (1 : ℝ) by norm_num at hyhi ⊢; linarith)
        Real.pi_pos
      simpa using this
  · apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos (by norm_num at hyhi ⊢; linarith)
    · have := mul_lt_mul_of_pos_left
        (show 9 / 10 - z.2 < (1 : ℝ) by norm_num at hylo ⊢; linarith)
        Real.pi_pos
      simpa using this

theorem veryBadSmoothCutoff_eq_fract (x y : ℝ) :
    veryBadSmoothCutoff (x, y) =
      veryBadSmoothCutoff (Int.fract x, Int.fract y) := by
  simpa only [Int.fract_add_floor] using
    veryBadSmoothCutoff_isZ2Periodic (Int.fract x) (Int.fract y) ⌊x⌋ ⌊y⌋

/-- The fixed cutoff is uniformly bounded below by a positive constant on
all integral translates of Tao's inner rectangle. -/
theorem exists_pos_le_veryBadSmoothCutoff_re_of_innerFractionalRegion :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : ℝ,
      (91 / 100 : ℝ) ≤ Int.fract x → Int.fract x ≤ 99 / 100 →
      (1 / 100 : ℝ) ≤ Int.fract y → Int.fract y ≤ 89 / 100 →
      c ≤ (veryBadSmoothCutoff (x, y)).re := by
  have hcompact : IsCompact veryBadInnerRectangle :=
    isCompact_Icc.prod isCompact_Icc
  have hne : veryBadInnerRectangle.Nonempty := by
    refine ⟨((19 / 20 : ℝ), (9 / 20 : ℝ)), ?_⟩
    constructor <;> constructor <;> norm_num
  have hcont : Continuous (fun z => (veryBadSmoothCutoff z).re) := by
    simpa only [Function.comp_apply] using
      Complex.continuous_re.comp veryBadSmoothCutoff_contDiff.continuous
  obtain ⟨z, hz, hmin⟩ :=
    hcompact.exists_isMinOn hne hcont.continuousOn
  refine ⟨(veryBadSmoothCutoff z).re,
    veryBadSmoothCutoff_re_pos_of_mem_innerRectangle hz, ?_⟩
  intro x y hxlo hxhi hylo hyhi
  have hmem : (Int.fract x, Int.fract y) ∈ veryBadInnerRectangle :=
    ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩
  calc
    (veryBadSmoothCutoff z).re ≤
        (veryBadSmoothCutoff (Int.fract x, Int.fract y)).re := hmin hmem
    _ = (veryBadSmoothCutoff (x, y)).re :=
      congrArg Complex.re (veryBadSmoothCutoff_eq_fract x y).symm

theorem veryBadPrimeIntegralIntegrand_re_nonneg
    (N : ℝ) {t : ℝ} (ht : 1 < t) :
    0 ≤ (veryBadSmoothCutoff (N / t, N / t ^ 2) / Real.log t).re := by
  change 0 ≤ (Complex.ofReal
    (smoothPeriodicIntervalBump (9 / 10) 1 (N / t) *
      smoothPeriodicIntervalBump 0 (9 / 10) (N / t ^ 2)) /
        Complex.ofReal (Real.log t)).re
  rw [← Complex.ofReal_div, Complex.ofReal_re]
  simp only [smoothPeriodicIntervalBump]
  exact div_nonneg
    (mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _))
    (Real.log_nonneg ht.le)

theorem integrableOn_veryBadPrimeIntegralIntegrand
    {N H : ℕ} (hH : 2 ≤ H) :
    IntegrableOn (fun t : ℝ =>
      veryBadSmoothCutoff ((N : ℝ) / t, (N : ℝ) / t ^ 2) / Real.log t)
      (Ioo (H : ℝ) (2 * H)) := by
  have hcont : ContinuousOn (fun t : ℝ =>
      veryBadSmoothCutoff ((N : ℝ) / t, (N : ℝ) / t ^ 2) / Real.log t)
      (Icc (H : ℝ) (2 * H)) := by
    intro t ht
    have htOne : (1 : ℝ) < t := by
      have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
      linarith [ht.1]
    have htne : t ≠ 0 := ne_of_gt (lt_trans (by norm_num) htOne)
    have hlogne : Real.log t ≠ 0 := ne_of_gt (Real.log_pos htOne)
    apply ContinuousAt.continuousWithinAt
    have hpair : ContinuousAt (fun u : ℝ =>
        ((N : ℝ) / u, (N : ℝ) / u ^ 2)) t :=
      (continuousAt_const.div continuousAt_id htne).prodMk
        (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 htne))
    have hnum : ContinuousAt (fun u : ℝ =>
        veryBadSmoothCutoff ((N : ℝ) / u, (N : ℝ) / u ^ 2)) t :=
      veryBadSmoothCutoff_contDiff.continuous.continuousAt.comp hpair
    have hden : ContinuousAt (fun u : ℝ => (Real.log u : ℂ)) t := by
      fun_prop
    exact hnum.div hden (by simpa only [Complex.ofReal_ne_zero] using hlogne)
  exact (hcont.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

theorem veryBadPrimeEquidistributionIntegral_im_eq_zero
    {N H : ℕ} (hH : 2 ≤ H) :
    (primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H))
      veryBadSmoothCutoff (N : ℝ) (N : ℝ) 2).im = 0 := by
  rw [primeEquidistributionIntegral, ← Complex.imCLM_apply]
  rw [← Complex.imCLM.integral_comp_comm
    (integrableOn_veryBadPrimeIntegralIntegrand hH)]
  rw [← integral_zero]
  apply integral_congr_ae
  filter_upwards with t
  simp [veryBadSmoothCutoff]

theorem veryBadPrimeEquidistributionIntegral_re_nonneg
    {N H : ℕ} (hH : 2 ≤ H) :
    0 ≤ (primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H))
      veryBadSmoothCutoff (N : ℝ) (N : ℝ) 2).re := by
  rw [primeEquidistributionIntegral, ← Complex.reCLM_apply]
  rw [← Complex.reCLM.integral_comp_comm
    (integrableOn_veryBadPrimeIntegralIntegrand hH)]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  apply veryBadPrimeIntegralIntegrand_re_nonneg
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
  linarith [ht.1]

theorem norm_veryBadPrimeEquidistributionIntegral_eq_re
    {N H : ℕ} (hH : 2 ≤ H) :
    ‖primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H))
      veryBadSmoothCutoff (N : ℝ) (N : ℝ) 2‖ =
    (primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H))
      veryBadSmoothCutoff (N : ℝ) (N : ℝ) 2).re := by
  rw [Complex.norm_def, Complex.normSq_apply,
    veryBadPrimeEquidistributionIntegral_im_eq_zero hH, mul_zero, add_zero,
    ← pow_two, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (veryBadPrimeEquidistributionIntegral_re_nonneg hH)]

/-- The prime-scale points at which both coordinates lie in the closed inner
rectangle on which the fixed cutoff has a positive uniform lower bound. -/
def veryBadInnerPrimeScaleSet (N H : ℕ) : Set ℝ :=
  Ioo (H : ℝ) (2 * H) ∩
    {t | (91 / 100 : ℝ) ≤ Int.fract ((N : ℝ) / t) ∧
      Int.fract ((N : ℝ) / t) ≤ 99 / 100 ∧
      (1 / 100 : ℝ) ≤ Int.fract ((N : ℝ) / t ^ 2) ∧
      Int.fract ((N : ℝ) / t ^ 2) ≤ 89 / 100}

theorem measurableSet_veryBadInnerPrimeScaleSet (N H : ℕ) :
    MeasurableSet (veryBadInnerPrimeScaleSet N H) := by
  unfold veryBadInnerPrimeScaleSet
  measurability

theorem veryBadInnerPrimeScaleSet_subset (N H : ℕ) :
    veryBadInnerPrimeScaleSet N H ⊆ Ioo (H : ℝ) (2 * H) := by
  intro t ht
  exact ht.1

/-- Tao's first transformed good set after the reciprocal substitution
`s = N / t`. -/
def veryBadInnerReciprocalScaleSet (N H : ℕ) : Set ℝ :=
  Ioo ((N : ℝ) / (2 * H)) ((N : ℝ) / H) ∩
    {s | (91 / 100 : ℝ) ≤ Int.fract s ∧ Int.fract s ≤ 99 / 100 ∧
      (1 / 100 : ℝ) ≤ Int.fract (s ^ 2 / N) ∧
      Int.fract (s ^ 2 / N) ≤ 89 / 100}

theorem measurableSet_veryBadInnerReciprocalScaleSet (N H : ℕ) :
    MeasurableSet (veryBadInnerReciprocalScaleSet N H) := by
  unfold veryBadInnerReciprocalScaleSet
  measurability

/-- The one-coordinate set used after forgetting the first fractional
coordinate and shrinking the second coordinate away from its support edges. -/
def veryBadQuadraticReciprocalScaleSet (N H : ℕ) : Set ℝ :=
  Ioo ((N : ℝ) / (2 * H)) ((N : ℝ) / H) ∩
    {s | (2 / 100 : ℝ) ≤ Int.fract (s ^ 2 / N) ∧
      Int.fract (s ^ 2 / N) ≤ 88 / 100}

/-- The final one-dimensional periodic slice after `u = s² / N`. -/
def veryBadQuadraticSliceSet (N H : ℕ) : Set ℝ :=
  Ioo ((N : ℝ) / (4 * H ^ 2)) ((N : ℝ) / H ^ 2) ∩
    {u | (2 / 100 : ℝ) ≤ Int.fract u ∧ Int.fract u ≤ 88 / 100}

theorem measurableSet_veryBadQuadraticReciprocalScaleSet (N H : ℕ) :
    MeasurableSet (veryBadQuadraticReciprocalScaleSet N H) := by
  unfold veryBadQuadraticReciprocalScaleSet
  measurability

theorem measurableSet_veryBadQuadraticSliceSet (N H : ℕ) :
    MeasurableSet (veryBadQuadraticSliceSet N H) := by
  unfold veryBadQuadraticSliceSet
  measurability

/-- Exact interval and fractional-band transport under Tao's second change of
variables `u = s² / N`. -/
theorem mem_veryBadQuadraticReciprocalScaleSet_iff_square_div_mem
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) {s : ℝ} (hs : 0 < s) :
    s ∈ veryBadQuadraticReciprocalScaleSet N H ↔
      s ^ 2 / (N : ℝ) ∈ veryBadQuadraticSliceSet N H := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have h2Hr : (0 : ℝ) < 2 * H := by positivity
  have hlow : 0 ≤ (N : ℝ) / (2 * H) := (div_pos hNr h2Hr).le
  have hupp : 0 ≤ (N : ℝ) / H := (div_pos hNr hHr).le
  have hlowerId : ((N : ℝ) / (4 * H ^ 2)) =
      (((N : ℝ) / (2 * H)) ^ 2) / N := by field_simp; ring
  have hupperId : ((N : ℝ) / H ^ 2) =
      (((N : ℝ) / H) ^ 2) / N := by field_simp
  rw [veryBadQuadraticReciprocalScaleSet, veryBadQuadraticSliceSet]
  constructor
  · rintro ⟨hsI, hylo, hyhi⟩
    refine ⟨⟨?_, ?_⟩, hylo, hyhi⟩
    · rw [hlowerId, div_lt_div_iff_of_pos_right hNr]
      exact (sq_lt_sq₀ hlow hs.le).mpr hsI.1
    · rw [hupperId, div_lt_div_iff_of_pos_right hNr]
      exact (sq_lt_sq₀ hs.le hupp).mpr hsI.2
  · rintro ⟨huI, hylo, hyhi⟩
    refine ⟨⟨?_, ?_⟩, hylo, hyhi⟩
    · have huLower := huI.1
      rw [hlowerId, div_lt_div_iff_of_pos_right hNr] at huLower
      exact (sq_lt_sq₀ hlow hs.le).mp huLower
    · have huUpper := huI.2
      rw [hupperId, div_lt_div_iff_of_pos_right hNr] at huUpper
      exact (sq_lt_sq₀ hs.le hupp).mp huUpper

theorem hasDerivAt_square_div_const (N s : ℝ) :
    HasDerivAt (fun u : ℝ => u ^ 2 / N) (2 * s / N) s := by
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_id s).pow 2
  exact hsq.div_const N

/-- Exact measure transport under Tao's second change of variables
`u = s² / N`. -/
theorem volume_veryBadQuadraticSliceSet_eq_integral_squareJacobian
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) :
    (volume (veryBadQuadraticSliceSet N H)).toReal =
      ∫ s in veryBadQuadraticReciprocalScaleSet N H,
        2 * s / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have h2Hr : (0 : ℝ) < 2 * H := by positivity
  have hlowPos : (0 : ℝ) < (N : ℝ) / (2 * H) := div_pos hNr h2Hr
  have hab : (N : ℝ) / (2 * H) ≤ (N : ℝ) / H :=
    div_le_div_of_nonneg_left hNr.le hHr (by linarith)
  have hfcont : ContinuousOn (fun s : ℝ => s ^ 2 / (N : ℝ))
      (uIcc ((N : ℝ) / (2 * H)) ((N : ℝ) / H)) := by fun_prop
  have hfderiv : ∀ s ∈ Ioo
      (min ((N : ℝ) / (2 * H)) ((N : ℝ) / H))
      (max ((N : ℝ) / (2 * H)) ((N : ℝ) / H)),
      HasDerivAt (fun u : ℝ => u ^ 2 / (N : ℝ)) (2 * s / N) s := by
    intro s hs
    exact hasDerivAt_square_div_const (N : ℝ) s
  have hfnonneg : ∀ s ∈ Ioo
      (min ((N : ℝ) / (2 * H)) ((N : ℝ) / H))
      (max ((N : ℝ) / (2 * H)) ((N : ℝ) / H)),
      (0 : ℝ) ≤ 2 * s / N := by
    intro s hs
    rw [min_eq_left hab, max_eq_right hab] at hs
    exact div_nonneg (mul_nonneg (by norm_num) (hlowPos.trans hs.1).le) hNr.le
  have hfa : (((N : ℝ) / (2 * H)) ^ 2 / N) =
      (N : ℝ) / (4 * H ^ 2) := by field_simp; ring
  have hfb : (((N : ℝ) / H) ^ 2 / N) =
      (N : ℝ) / H ^ 2 := by field_simp
  have hsubst :
      (∫ s in (N : ℝ) / (2 * H)..(N : ℝ) / H,
        (2 * s / N : ℝ) *
          (veryBadQuadraticSliceSet N H).indicator (fun _ => (1 : ℝ))
            (s ^ 2 / (N : ℝ))) =
      ∫ u in (N : ℝ) / (4 * H ^ 2)..(N : ℝ) / H ^ 2,
        (veryBadQuadraticSliceSet N H).indicator (fun _ => (1 : ℝ)) u := by
    simpa only [smul_eq_mul, Function.comp_apply, hfa, hfb] using
      (intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
        (g := (veryBadQuadraticSliceSet N H).indicator (fun _ => (1 : ℝ)))
        hfcont hfderiv hfnonneg)
  have huab : (N : ℝ) / (4 * H ^ 2) ≤ (N : ℝ) / H ^ 2 := by
    rw [← hfa, ← hfb]
    exact div_le_div_of_nonneg_right (sq_le_sq₀
      (div_nonneg hNr.le h2Hr.le) (div_nonneg hNr.le hHr.le) |>.mpr
        (div_le_div_of_nonneg_left hNr.le hHr (by linarith))) hNr.le
  have hUsubsetIoc : veryBadQuadraticSliceSet N H ⊆
      Ioc ((N : ℝ) / (4 * H ^ 2)) ((N : ℝ) / H ^ 2) := by
    intro u hu
    exact ⟨hu.1.1, hu.1.2.le⟩
  have hright :
      (∫ u in (N : ℝ) / (4 * H ^ 2)..(N : ℝ) / H ^ 2,
        (veryBadQuadraticSliceSet N H).indicator (fun _ => (1 : ℝ)) u) =
      (volume (veryBadQuadraticSliceSet N H)).toReal := by
    rw [intervalIntegral.integral_of_le huab,
      MeasureTheory.integral_indicator (measurableSet_veryBadQuadraticSliceSet N H),
      setIntegral_const, Measure.real_def,
      Measure.restrict_apply (measurableSet_veryBadQuadraticSliceSet N H),
      inter_eq_left.mpr hUsubsetIoc]
    simp
  have hYsubsetIoc : veryBadQuadraticReciprocalScaleSet N H ⊆
      Ioc ((N : ℝ) / (2 * H)) ((N : ℝ) / H) := by
    intro s hs
    exact ⟨hs.1.1, hs.1.2.le⟩
  have hweightedInterval :
      (∫ s in (N : ℝ) / (2 * H)..(N : ℝ) / H,
        (veryBadQuadraticReciprocalScaleSet N H).indicator
          (fun s => 2 * s / (N : ℝ)) s) =
      ∫ s in veryBadQuadraticReciprocalScaleSet N H,
        2 * s / (N : ℝ) := by
    rw [intervalIntegral.integral_of_le hab,
      MeasureTheory.integral_indicator
        (measurableSet_veryBadQuadraticReciprocalScaleSet N H),
      Measure.restrict_restrict
        (measurableSet_veryBadQuadraticReciprocalScaleSet N H),
      inter_eq_left.mpr hYsubsetIoc]
  have hleft :
      (∫ s in (N : ℝ) / (2 * H)..(N : ℝ) / H,
        (2 * s / N : ℝ) *
          (veryBadQuadraticSliceSet N H).indicator (fun _ => (1 : ℝ))
            (s ^ 2 / (N : ℝ))) =
      ∫ s in veryBadQuadraticReciprocalScaleSet N H,
        2 * s / (N : ℝ) := by
    calc
      _ = ∫ s in (N : ℝ) / (2 * H)..(N : ℝ) / H,
          (veryBadQuadraticReciprocalScaleSet N H).indicator
            (fun s => 2 * s / (N : ℝ)) s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hab] at hs
        have hspos : 0 < s := hlowPos.trans_le hs.1
        have hmem :=
          mem_veryBadQuadraticReciprocalScaleSet_iff_square_div_mem hN hH hspos
        by_cases hsY : s ∈ veryBadQuadraticReciprocalScaleSet N H
        · have huU := hmem.mp hsY
          simp [Set.indicator_of_mem hsY, Set.indicator_of_mem huU]
        · have huU : s ^ 2 / (N : ℝ) ∉ veryBadQuadraticSliceSet N H :=
            fun hu => hsY (hmem.mpr hu)
          simp [Set.indicator, hsY, huU]
      _ = _ := hweightedInterval
  rw [hleft, hright] at hsubst
  exact hsubst.symm

/-- On the source interval for `u = s² / N`, the square Jacobian is at most
`2 / H`. -/
theorem squareJacobian_upper_on_sourceInterval
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) {s : ℝ}
    (hsle : s ≤ (N : ℝ) / H) :
    2 * s / (N : ℝ) ≤ 2 / (H : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hmul : s * (H : ℝ) ≤ N := (le_div_iff₀ hHr).mp hsle
  rw [div_le_div_iff₀ hNr hHr]
  nlinarith

theorem integrableOn_squareJacobian_quadraticReciprocalScaleSet
    {N H : ℕ} (hN : 0 < N) :
    IntegrableOn (fun s : ℝ => 2 * s / (N : ℝ))
      (veryBadQuadraticReciprocalScaleSet N H) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcont : Continuous (fun s : ℝ => 2 * s / (N : ℝ)) := by fun_prop
  apply (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
  intro s hs
  exact ⟨hs.1.1.le, hs.1.2.le⟩

/-- Quantitative consequence of the second change of variables: the periodic
slice has at most `2 / H` times the measure of its reciprocal-scale preimage. -/
theorem quadraticSlice_measure_le_two_div_length_mul_reciprocalScale_measure
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) :
    (volume (veryBadQuadraticSliceSet N H)).toReal ≤
      2 / (H : ℝ) *
        (volume (veryBadQuadraticReciprocalScaleSet N H)).toReal := by
  have hjac : Integrable (fun s : ℝ => 2 * s / (N : ℝ))
      (volume.restrict (veryBadQuadraticReciprocalScaleSet N H)) :=
    integrableOn_squareJacobian_quadraticReciprocalScaleSet hN
  have hconst : Integrable (fun _ : ℝ => 2 / (H : ℝ))
      (volume.restrict (veryBadQuadraticReciprocalScaleSet N H)) :=
    (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set (by
      intro s hs
      exact ⟨hs.1.1.le, hs.1.2.le⟩)
  have hmono : (fun s : ℝ => 2 * s / (N : ℝ)) ≤ᶠ[ae
      (volume.restrict (veryBadQuadraticReciprocalScaleSet N H))]
      (fun _ : ℝ => 2 / (H : ℝ)) := by
    filter_upwards [ae_restrict_mem
      (measurableSet_veryBadQuadraticReciprocalScaleSet N H)] with s hs
    exact squareJacobian_upper_on_sourceInterval hN hH hs.1.2.le
  have hmain := integral_mono_ae hjac hconst hmono
  rw [setIntegral_const, Measure.real_def, smul_eq_mul] at hmain
  rw [volume_veryBadQuadraticSliceSet_eq_integral_squareJacobian hN hH]
  simpa [mul_comm] using hmain

/-- The periodic fractional band retained in the second coordinate. -/
def veryBadQuadraticFractionalBand : Set ℝ :=
  {u | (2 / 100 : ℝ) ≤ Int.fract u ∧ Int.fract u ≤ 88 / 100}

def veryBadQuadraticBandIndicator (u : ℝ) : ℝ :=
  veryBadQuadraticFractionalBand.indicator (fun _ => (1 : ℝ)) u

theorem measurableSet_veryBadQuadraticFractionalBand :
    MeasurableSet veryBadQuadraticFractionalBand := by
  unfold veryBadQuadraticFractionalBand
  measurability

theorem veryBadQuadraticBandIndicator_periodic :
    Function.Periodic veryBadQuadraticBandIndicator 1 := by
  intro u
  have hmem : u + 1 ∈ veryBadQuadraticFractionalBand ↔
      u ∈ veryBadQuadraticFractionalBand := by
    simp only [veryBadQuadraticFractionalBand, mem_setOf_eq]
    rw [Int.fract_add_one]
  by_cases hu : u ∈ veryBadQuadraticFractionalBand
  · rw [veryBadQuadraticBandIndicator, veryBadQuadraticBandIndicator,
      Set.indicator_of_mem hu, Set.indicator_of_mem (hmem.mpr hu)]
  · rw [veryBadQuadraticBandIndicator, veryBadQuadraticBandIndicator,
      Set.indicator_of_notMem hu,
      Set.indicator_of_notMem (fun h => hu (hmem.mp h))]

theorem veryBadQuadraticFractionalBand_inter_Ioc_zero_one :
    veryBadQuadraticFractionalBand ∩ Ioc (0 : ℝ) 1 =
      Icc (2 / 100 : ℝ) (88 / 100) := by
  ext u
  constructor
  · rintro ⟨huBand, huI⟩
    have huIco : u ∈ Ico (0 : ℝ) 1 := ⟨huI.1.le, huI.2.lt_of_ne (by
      intro h
      subst u
      norm_num [veryBadQuadraticFractionalBand] at huBand)⟩
    simpa [veryBadQuadraticFractionalBand, Int.fract_eq_self.2 huIco] using huBand
  · intro hu
    have huIco : u ∈ Ico (0 : ℝ) 1 := by
      constructor <;> norm_num at hu ⊢ <;> linarith [hu.1, hu.2]
    refine ⟨?_, ?_⟩
    · simpa [veryBadQuadraticFractionalBand, Int.fract_eq_self.2 huIco] using hu
    · constructor <;> norm_num at hu ⊢ <;> linarith [hu.1, hu.2]

/-- The retained band has exact mass `43 / 50` in every unit period. -/
theorem integral_veryBadQuadraticBandIndicator_zero_one :
    (∫ u in (0 : ℝ)..1, veryBadQuadraticBandIndicator u) = 43 / 50 := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  simp only [veryBadQuadraticBandIndicator]
  rw [MeasureTheory.integral_indicator
      measurableSet_veryBadQuadraticFractionalBand,
    Measure.restrict_restrict measurableSet_veryBadQuadraticFractionalBand,
    veryBadQuadraticFractionalBand_inter_Ioc_zero_one,
    setIntegral_const, Measure.real_def, Real.volume_Icc]
  norm_num

theorem intervalIntegrable_veryBadQuadraticBandIndicator (a b : ℝ) :
    IntervalIntegrable veryBadQuadraticBandIndicator volume a b := by
  apply veryBadQuadraticBandIndicator_periodic.intervalIntegrable₀ (by norm_num)
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) 1) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hind : IntegrableOn
      (veryBadQuadraticFractionalBand.indicator (fun _ => (1 : ℝ)))
      (Icc (0 : ℝ) 1) :=
    hconst.indicator measurableSet_veryBadQuadraticFractionalBand
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2
  simpa only [veryBadQuadraticBandIndicator] using hind

theorem integral_veryBadQuadraticBandIndicator_eq_volume
    {a b : ℝ} (hab : a ≤ b) :
    (∫ u in a..b, veryBadQuadraticBandIndicator u) =
      (volume (veryBadQuadraticFractionalBand ∩ Ioc a b)).toReal := by
  rw [intervalIntegral.integral_of_le hab]
  simp only [veryBadQuadraticBandIndicator]
  rw [MeasureTheory.integral_indicator
      measurableSet_veryBadQuadraticFractionalBand,
    Measure.restrict_restrict measurableSet_veryBadQuadraticFractionalBand,
    setIntegral_const, Measure.real_def]
  simp

/-- Every interval of length at least one retains at least one quarter of its
length in the fractional band.  The exact period mass is `43 / 50`; the weaker
quarter is convenient for the endpoint-uniform estimate. -/
theorem quarter_intervalLength_le_volume_quadraticBand_inter_Ioc
    {a b : ℝ} (hab : a ≤ b) (hlength : 1 ≤ b - a) :
    (b - a) / 4 ≤
      (volume (veryBadQuadraticFractionalBand ∩ Ioc a b)).toReal := by
  let n : ℤ := ⌊b - a⌋
  have hnle : (n : ℝ) ≤ b - a := by
    dsimp [n]
    exact Int.floor_le (b - a)
  have hnOne : (1 : ℝ) ≤ n := by
    exact_mod_cast (Int.le_floor.mpr (by simpa using hlength) :
      (1 : ℤ) ≤ ⌊b - a⌋)
  have hnLower : (b - a) / 2 ≤ (n : ℝ) := by
    have hlt : b - a < (n : ℝ) + 1 := by
      simpa only [n, Int.cast_add, Int.cast_one] using
        (Int.lt_floor_add_one (b - a))
    rcases le_total (b - a) 2 with hsmall | hlarge <;> linarith
  have hanb : a ≤ a + (n : ℝ) := by linarith
  have hanb_le : a + (n : ℝ) ≤ b := by linarith
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)]
      veryBadQuadraticBandIndicator :=
    Filter.Eventually.of_forall (fun u => by
      exact Set.indicator_apply_nonneg
        (fun _ => (by norm_num : (0 : ℝ) ≤ 1)))
  have hmono := intervalIntegral.integral_mono_interval
    (f := veryBadQuadraticBandIndicator) (μ := volume)
    (a := a) (b := a + (n : ℝ)) (c := a) (d := b)
    le_rfl hanb hanb_le hnonneg
    (intervalIntegrable_veryBadQuadraticBandIndicator a b)
  have hperiod :=
    veryBadQuadraticBandIndicator_periodic.intervalIntegral_add_zsmul_eq
      n a intervalIntegrable_veryBadQuadraticBandIndicator
  have hperiodOne :=
    veryBadQuadraticBandIndicator_periodic.intervalIntegral_add_eq a 0
  simp only [zsmul_eq_mul, mul_one, hperiodOne, zero_add,
    integral_veryBadQuadraticBandIndicator_zero_one] at hperiod
  rw [hperiod] at hmono
  rw [integral_veryBadQuadraticBandIndicator_eq_volume hab] at hmono
  nlinarith

theorem quarter_intervalLength_le_volume_quadraticBand_inter_Ioo
    {a b : ℝ} (hab : a ≤ b) (hlength : 1 ≤ b - a) :
    (b - a) / 4 ≤
      (volume (Ioo a b ∩ veryBadQuadraticFractionalBand)).toReal := by
  have hae : (Ioo a b ∩ veryBadQuadraticFractionalBand : Set ℝ) =ᵐ[volume]
      (Ioc a b ∩ veryBadQuadraticFractionalBand : Set ℝ) :=
    ae_eq_set_inter Ioo_ae_eq_Ioc
      (ae_eq_refl veryBadQuadraticFractionalBand)
  rw [measure_congr hae, inter_comm]
  exact quarter_intervalLength_le_volume_quadraticBand_inter_Ioc hab hlength

def veryBadNormalizedQuadraticSliceSet (X : ℝ) : Set ℝ :=
  Ioo (X / 4) X ∩ veryBadQuadraticFractionalBand

/-- Uniform periodic-slice lower bound at every normalized scale `X ≥ 1/2`.
This includes the short range where the interval contains no full period. -/
theorem normalizedQuadraticSlice_measure_lower
    {X : ℝ} (hX : (1 / 2 : ℝ) ≤ X) :
    X / 8 ≤ (volume (veryBadNormalizedQuadraticSliceSet X)).toReal := by
  by_cases hsmall : X ≤ (22 / 25 : ℝ)
  · have hsub : Ioo (X / 4) X ⊆ veryBadNormalizedQuadraticSliceSet X := by
      intro u hu
      have huIco : u ∈ Ico (0 : ℝ) 1 := by
        constructor <;> norm_num at hX hsmall hu ⊢ <;> linarith
      refine ⟨hu, ?_⟩
      simp only [veryBadQuadraticFractionalBand, mem_setOf_eq,
        Int.fract_eq_self.2 huIco]
      constructor <;> norm_num at hX hsmall hu ⊢ <;> linarith
    have hfinite : volume (veryBadNormalizedQuadraticSliceSet X) ≠ ⊤ := (calc
      volume (veryBadNormalizedQuadraticSliceSet X) ≤ volume (Ioo (X / 4) X) :=
        measure_mono inter_subset_left
      _ < ⊤ := measure_Ioo_lt_top).ne
    have hmeasure := measureReal_mono (μ := volume) hsub hfinite
    simp only [Measure.real_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by nlinarith : 0 ≤ X - X / 4)] at hmeasure
    norm_num at hmeasure ⊢
    nlinarith
  · by_cases hmedium : X ≤ (4 / 3 : ℝ)
    · have hsub : Ioo (X / 4) (22 / 25 : ℝ) ⊆
          veryBadNormalizedQuadraticSliceSet X := by
        intro u hu
        have huIco : u ∈ Ico (0 : ℝ) 1 := by
          constructor <;> norm_num at hX hmedium hu ⊢ <;> linarith
        refine ⟨⟨hu.1, ?_⟩, ?_⟩
        · norm_num at hsmall hu ⊢
          linarith
        · simp only [veryBadQuadraticFractionalBand, mem_setOf_eq,
            Int.fract_eq_self.2 huIco]
          constructor <;> norm_num at hX hmedium hu ⊢ <;> linarith
      have hfinite : volume (veryBadNormalizedQuadraticSliceSet X) ≠ ⊤ := (calc
        volume (veryBadNormalizedQuadraticSliceSet X) ≤ volume (Ioo (X / 4) X) :=
          measure_mono inter_subset_left
        _ < ⊤ := measure_Ioo_lt_top).ne
      have hmeasure := measureReal_mono (μ := volume) hsub hfinite
      simp only [Measure.real_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal
          (by nlinarith : 0 ≤ (22 / 25 : ℝ) - X / 4)] at hmeasure
      norm_num at hmeasure ⊢
      nlinarith
    · have hab : X / 4 ≤ X := by nlinarith
      have hlength : (1 : ℝ) ≤ X - X / 4 := by
        norm_num at hmedium ⊢
        linarith
      have hlong :=
        quarter_intervalLength_le_volume_quadraticBand_inter_Ioo hab hlength
      change X / 8 ≤
        (volume (Ioo (X / 4) X ∩ veryBadQuadraticFractionalBand)).toReal
      nlinarith

theorem veryBadQuadraticSliceSet_eq_normalized
    {N H : ℕ} (hH : 0 < H) :
    veryBadQuadraticSliceSet N H =
      veryBadNormalizedQuadraticSliceSet ((N : ℝ) / H ^ 2) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hleft : (N : ℝ) / (4 * H ^ 2) = ((N : ℝ) / H ^ 2) / 4 := by
    field_simp
  unfold veryBadQuadraticSliceSet veryBadNormalizedQuadraticSliceSet
    veryBadQuadraticFractionalBand
  rw [hleft]

/-- The periodic slice occurring after `u = s² / N` has measure at least
`N / (8H²)` as soon as the source lower bound `N / H² ≥ 1/2` is available. -/
theorem veryBadQuadraticSlice_measure_lower
    {N H : ℕ} (hH : 0 < H)
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / H ^ 2) :
    (N : ℝ) / (8 * H ^ 2) ≤
      (volume (veryBadQuadraticSliceSet N H)).toReal := by
  have hmain := normalizedQuadraticSlice_measure_lower hscale
  rw [← veryBadQuadraticSliceSet_eq_normalized hH] at hmain
  calc
    (N : ℝ) / (8 * H ^ 2) = ((N : ℝ) / H ^ 2) / 8 := by field_simp
    _ ≤ (volume (veryBadQuadraticSliceSet N H)).toReal := hmain

/-- Combining the periodic slice lower bound with the exact square-Jacobian
comparison gives a fixed positive proportion of the original scale in the
one-coordinate reciprocal set. -/
theorem veryBadQuadraticReciprocalScale_measure_lower
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / H ^ 2) :
    (H : ℝ) / 32 ≤
      (volume (veryBadQuadraticReciprocalScaleSet N H)).toReal := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hlower := veryBadQuadraticSlice_measure_lower hH hscale
  have hupper :=
    quadraticSlice_measure_le_two_div_length_mul_reciprocalScale_measure hN hH
  have hchain : (N : ℝ) / (8 * H ^ 2) ≤
      2 / (H : ℝ) *
        (volume (veryBadQuadraticReciprocalScaleSet N H)).toReal :=
    hlower.trans hupper
  have hscale' : (H : ℝ) ^ 2 / 2 ≤ N := by
    rw [le_div_iff₀ (sq_pos_of_pos hHr)] at hscale
    nlinarith
  have hchain' : (N : ℝ) ≤ 16 * H *
      (volume (veryBadQuadraticReciprocalScaleSet N H)).toReal := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * H ^ 2)] at hchain
    field_simp at hchain
    nlinarith
  nlinarith

/-- A point within `1/100` of a value whose fractional part lies in
`[2/100,88/100]` has fractional part in `[1/100,89/100]`.  The margins force
the two points to have the same floor. -/
theorem fract_mem_veryBad_innerBand_of_abs_sub_le
    {u v : ℝ} (hdist : |u - v| ≤ 1 / 100)
    (hvlo : (2 / 100 : ℝ) ≤ Int.fract v)
    (hvhi : Int.fract v ≤ 88 / 100) :
    (1 / 100 : ℝ) ≤ Int.fract u ∧ Int.fract u ≤ 89 / 100 := by
  have huvlo : v - 1 / 100 ≤ u := by
    rw [abs_le] at hdist
    linarith [hdist.1]
  have huvhi : u ≤ v + 1 / 100 := by
    rw [abs_le] at hdist
    linarith [hdist.2]
  have hvId : Int.fract v + (⌊v⌋ : ℝ) = v := Int.fract_add_floor v
  have huCell : u ∈ Ico (⌊v⌋ : ℝ) ((⌊v⌋ : ℝ) + 1) := by
    constructor <;> norm_num at hvlo hvhi ⊢ <;> linarith
  have hfloor : ⌊u⌋ = ⌊v⌋ := Int.floor_eq_iff.mpr huCell
  have hfloorR : (⌊u⌋ : ℝ) = (⌊v⌋ : ℝ) := congrArg Int.cast hfloor
  have huId : Int.fract u + (⌊u⌋ : ℝ) = u := Int.fract_add_floor u
  constructor <;> norm_num at hvlo hvhi ⊢ <;> linarith

/-- On the reciprocal source interval, `s ↦ s²/N` varies by at most `2/H`
between two points at distance at most one. -/
theorem abs_square_div_sub_square_div_le_two_div_length
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    {s t : ℝ} (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hs : s ≤ (N : ℝ) / H) (ht : t ≤ (N : ℝ) / H)
    (hst : |s - t| ≤ 1) :
    |s ^ 2 / (N : ℝ) - t ^ 2 / N| ≤ 2 / (H : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hs' : s * (H : ℝ) ≤ N := (le_div_iff₀ hHr).mp hs
  have ht' : t * (H : ℝ) ≤ N := (le_div_iff₀ hHr).mp ht
  have hsum : s + t ≤ 2 * (N : ℝ) / H := by
    rw [le_div_iff₀ hHr]
    nlinarith
  have hsum0 : 0 ≤ s + t := add_nonneg hs0 ht0
  rw [← sub_div, sq_sub_sq, abs_div, abs_mul,
    abs_of_pos hNr, abs_of_nonneg hsum0]
  calc
    (s + t) * |s - t| / (N : ℝ) ≤
        (2 * (N : ℝ) / H) * 1 / N := by gcongr
    _ = 2 / (H : ℝ) := by field_simp

/-- For `H≥200`, the quadratic fractional coordinate stays inside the larger
inner band throughout any unit cell meeting the narrower quadratic set. -/
theorem quadratic_fract_mem_veryBad_innerBand_of_same_unit_cell
    {N H : ℕ} (hN : 0 < N) (hH : 200 ≤ H)
    {s t : ℝ} (hs0 : 0 ≤ s) (ht0 : 0 ≤ t)
    (hs : s ≤ (N : ℝ) / H) (ht : t ≤ (N : ℝ) / H)
    (hst : |s - t| ≤ 1)
    (htlo : (2 / 100 : ℝ) ≤ Int.fract (t ^ 2 / N))
    (hthi : Int.fract (t ^ 2 / N) ≤ 88 / 100) :
    (1 / 100 : ℝ) ≤ Int.fract (s ^ 2 / N) ∧
      Int.fract (s ^ 2 / N) ≤ 89 / 100 := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hslow := abs_square_div_sub_square_div_le_two_div_length
    hN hHpos hs0 ht0 hs ht hst
  have htwo : 2 / (H : ℝ) ≤ (1 / 100 : ℝ) := by
    have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
    have hHreal : (200 : ℝ) ≤ H := by exact_mod_cast hH
    rw [div_le_iff₀ hHr]
    calc
      (2 : ℝ) = (1 / 100 : ℝ) * 200 := by norm_num
      _ ≤ (1 / 100 : ℝ) * H :=
        mul_le_mul_of_nonneg_left hHreal (by norm_num)
  exact fract_mem_veryBad_innerBand_of_abs_sub_le
    (hslow.trans htwo) htlo hthi

/-- A unit cell meeting the narrowed quadratic set contributes its fixed
`[0.91,0.99]` slice to the inner two-coordinate reciprocal set, away from the
two source-interval endpoint cells. -/
theorem firstBandCell_subset_innerReciprocal_of_witness {N H : ℕ} (hN : 0 < N) (hH : 200 ≤ H)
    {t : ℝ} (htY : t ∈ veryBadQuadraticReciprocalScaleSet N H)
    (htLower : (N : ℝ) / (2 * H) + 1 < t)
    (htUpper : t < (N : ℝ) / H - 1) :
    Icc ((⌊t⌋ : ℝ) + 91 / 100) ((⌊t⌋ : ℝ) + 99 / 100) ⊆
      veryBadInnerReciprocalScaleSet N H := by
  intro s hsCell
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have htId : Int.fract t + (⌊t⌋ : ℝ) = t := Int.fract_add_floor t
  have htFract0 : (0 : ℝ) ≤ Int.fract t := Int.fract_nonneg t
  have htFract1 : Int.fract t < 1 := Int.fract_lt_one t
  have hdist : |s - t| ≤ 1 := by
    rw [abs_le]
    constructor <;> norm_num at hsCell ⊢ <;> linarith
  have hsLower : (N : ℝ) / (2 * H) < s := by
    rw [abs_le] at hdist
    linarith [hdist.1]
  have hsUpper : s < (N : ℝ) / H := by
    rw [abs_le] at hdist
    linarith [hdist.2]
  have hsCellIco : s ∈ Ico (⌊t⌋ : ℝ) ((⌊t⌋ : ℝ) + 1) := by
    constructor <;> norm_num at hsCell ⊢ <;> linarith
  have hsFloor : ⌊s⌋ = ⌊t⌋ := Int.floor_eq_iff.mpr hsCellIco
  have hsFloorR : (⌊s⌋ : ℝ) = (⌊t⌋ : ℝ) := congrArg Int.cast hsFloor
  have hsId : Int.fract s + (⌊s⌋ : ℝ) = s := Int.fract_add_floor s
  have hsFractLo : (91 / 100 : ℝ) ≤ Int.fract s := by
    norm_num at hsCell ⊢
    linarith
  have hsFractHi : Int.fract s ≤ (99 / 100 : ℝ) := by
    norm_num at hsCell ⊢
    linarith
  have hsourceLower0 : (0 : ℝ) ≤ (N : ℝ) / (2 * H) := by positivity
  have hs0 : (0 : ℝ) ≤ s := hsourceLower0.trans hsLower.le
  have ht0 : (0 : ℝ) ≤ t := hsourceLower0.trans htY.1.1.le
  have hquad := quadratic_fract_mem_veryBad_innerBand_of_same_unit_cell
    hN hH hs0 ht0 hsUpper.le htY.1.2.le hdist htY.2.1 htY.2.2
  exact ⟨⟨hsLower, hsUpper⟩, hsFractLo, hsFractHi, hquad.1, hquad.2⟩

def veryBadQuadraticReciprocalInteriorSet (N H : ℕ) : Set ℝ :=
  Ioo ((N : ℝ) / (2 * H) + 1) ((N : ℝ) / H - 1) ∩
    {s | (2 / 100 : ℝ) ≤ Int.fract (s ^ 2 / N) ∧
      Int.fract (s ^ 2 / N) ≤ 88 / 100}

theorem measurableSet_veryBadQuadraticReciprocalInterior (N H : ℕ) : MeasurableSet (veryBadQuadraticReciprocalInteriorSet N H) := by
  unfold veryBadQuadraticReciprocalInteriorSet
  measurability

theorem quadraticReciprocal_measure_le_interior_add_two {N H : ℕ} :
    (volume (veryBadQuadraticReciprocalScaleSet N H)).toReal ≤
      (volume (veryBadQuadraticReciprocalInteriorSet N H)).toReal + 2 := by
  let a : ℝ := (N : ℝ) / (2 * H)
  let b : ℝ := (N : ℝ) / H
  let L : Set ℝ := Icc a (a + 1)
  let R : Set ℝ := Icc (b - 1) b
  have hcover : veryBadQuadraticReciprocalScaleSet N H ⊆
      (veryBadQuadraticReciprocalInteriorSet N H ∪ L) ∪ R := by
    intro t ht
    by_cases htI : a + 1 < t ∧ t < b - 1
    · left
      left
      exact ⟨htI, ht.2⟩
    · simp only [not_and_or, not_lt] at htI
      rcases htI with htleft | htright
      · left
        right
        exact ⟨ht.1.1.le, htleft⟩
      · right
        exact ⟨htright, ht.1.2.le⟩
  have hIfinite : volume (veryBadQuadraticReciprocalInteriorSet N H) ≠ ⊤ := (calc
    volume (veryBadQuadraticReciprocalInteriorSet N H) ≤
        volume (Ioo (a + 1) (b - 1)) := measure_mono inter_subset_left
    _ < ⊤ := measure_Ioo_lt_top).ne
  have hLfinite : volume L ≠ ⊤ := by
    dsimp [L]
    exact measure_Icc_lt_top.ne
  have hRfinite : volume R ≠ ⊤ := by
    dsimp [R]
    exact measure_Icc_lt_top.ne
  have hunionfinite : volume ((veryBadQuadraticReciprocalInteriorSet N H ∪ L) ∪ R) ≠ ⊤ :=
    measure_union_ne_top (measure_union_ne_top hIfinite hLfinite) hRfinite
  calc
    (volume (veryBadQuadraticReciprocalScaleSet N H)).toReal ≤
        (volume ((veryBadQuadraticReciprocalInteriorSet N H ∪ L) ∪ R)).toReal :=
      measureReal_mono hcover hunionfinite
    _ ≤ (volume (veryBadQuadraticReciprocalInteriorSet N H ∪ L)).toReal + (volume R).toReal :=
      measureReal_union_le _ _
    _ ≤ ((volume (veryBadQuadraticReciprocalInteriorSet N H)).toReal + (volume L).toReal) +
        (volume R).toReal := by
      gcongr
      exact measureReal_union_le _ _
    _ = (volume (veryBadQuadraticReciprocalInteriorSet N H)).toReal + 2 := by
      dsimp [L, R, a, b]
      simp [Real.volume_Icc]
      ring

theorem veryBadQuadraticReciprocalScale_measure_lower_source {N H : ℕ} (hN : 0 < N) (hH : 0 < H)
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / H ^ 2) :
    (N : ℝ) / (16 * H) ≤
      (volume (veryBadQuadraticReciprocalScaleSet N H)).toReal := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hlower := veryBadQuadraticSlice_measure_lower hH hscale
  have hupper :=
    quadraticSlice_measure_le_two_div_length_mul_reciprocalScale_measure hN hH
  have hchain : (N : ℝ) / (8 * H ^ 2) ≤
      2 / (H : ℝ) *
        (volume (veryBadQuadraticReciprocalScaleSet N H)).toReal :=
    hlower.trans hupper
  have hchain' : (N : ℝ) ≤ 16 * H *
      (volume (veryBadQuadraticReciprocalScaleSet N H)).toReal := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 8 * H ^ 2)] at hchain
    field_simp at hchain
    nlinarith
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * H)]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hchain'

theorem veryBadQuadraticReciprocalInterior_measure_lower {N H : ℕ} (hN : 0 < N) (hH : 200 ≤ H)
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / H ^ 2) :
    (N : ℝ) / (32 * H) ≤ (volume (veryBadQuadraticReciprocalInteriorSet N H)).toReal := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hHlarge : (200 : ℝ) ≤ H := by exact_mod_cast hH
  have hy := veryBadQuadraticReciprocalScale_measure_lower_source hN hHpos hscale
  have htrim := quadraticReciprocal_measure_le_interior_add_two (N := N) (H := H)
  have hscale' : (H : ℝ) ^ 2 / 2 ≤ N := by
    rw [le_div_iff₀ (sq_pos_of_pos hHr)] at hscale
    nlinarith
  have hratio : (64 : ℝ) ≤ (N : ℝ) / H := by
    rw [le_div_iff₀ hHr]
    nlinarith
  have hNH : (64 : ℝ) * H ≤ N := (le_div_iff₀ hHr).mp hratio
  have hdiff : (N : ℝ) / (32 * H) + 2 ≤ (N : ℝ) / (16 * H) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * H)]
    field_simp
    nlinarith
  linarith

noncomputable def veryBadOccupiedInteriorCells (N H : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc
      ⌊(N : ℝ) / (2 * H) + 1⌋
      ⌊(N : ℝ) / H - 1⌋).filter
        (fun k => ∃ t ∈ veryBadQuadraticReciprocalInteriorSet N H, ⌊t⌋ = k)

def veryBadUnitCell (k : ℤ) : Set ℝ := Ico (k : ℝ) ((k : ℝ) + 1)

def veryBadFirstBandCell (k : ℤ) : Set ℝ :=
  Ioo ((k : ℝ) + 91 / 100) ((k : ℝ) + 99 / 100)

theorem quadraticInterior_subset_occupiedCells {N H : ℕ} :
    veryBadQuadraticReciprocalInteriorSet N H ⊆ ⋃ k ∈ veryBadOccupiedInteriorCells N H, veryBadUnitCell k := by
  classical
  intro t ht
  have hklo : ⌊(N : ℝ) / (2 * H) + 1⌋ ≤ ⌊t⌋ :=
    Int.floor_mono ht.1.1.le
  have hkhi : ⌊t⌋ ≤ ⌊(N : ℝ) / H - 1⌋ :=
    Int.floor_mono ht.1.2.le
  have hk : ⌊t⌋ ∈ veryBadOccupiedInteriorCells N H := by
    simp only [veryBadOccupiedInteriorCells, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hklo, hkhi⟩, t, ht, rfl⟩
  simp only [mem_iUnion]
  refine ⟨⌊t⌋, ⟨hk, ?_⟩⟩
  exact ⟨Int.floor_le t, Int.lt_floor_add_one t⟩

theorem quadraticInterior_measure_le_occupiedCell_card {N H : ℕ} :
    (volume (veryBadQuadraticReciprocalInteriorSet N H)).toReal ≤ (veryBadOccupiedInteriorCells N H).card := by
  classical
  let U : Set ℝ := ⋃ k ∈ veryBadOccupiedInteriorCells N H, veryBadUnitCell k
  have hUfinite : volume U ≠ ⊤ := (measure_biUnion_finset_le
      (μ := volume) (veryBadOccupiedInteriorCells N H) veryBadUnitCell).trans_lt
    (ENNReal.sum_lt_top.mpr (fun k hk => measure_Ico_lt_top)) |>.ne
  calc
    (volume (veryBadQuadraticReciprocalInteriorSet N H)).toReal ≤ (volume U).toReal :=
      measureReal_mono quadraticInterior_subset_occupiedCells hUfinite
    _ ≤ ∑ k ∈ veryBadOccupiedInteriorCells N H, (volume (veryBadUnitCell k)).toReal :=
      measureReal_biUnion_finset_le _ _
    _ = (veryBadOccupiedInteriorCells N H).card := by
      simp [veryBadUnitCell, Real.volume_Ico]

theorem firstBandCells_pairwiseDisjoint {N H : ℕ} :
    Set.PairwiseDisjoint (↑(veryBadOccupiedInteriorCells N H)) veryBadFirstBandCell := by
  intro k hk l hl hkl
  change Disjoint (veryBadFirstBandCell k) (veryBadFirstBandCell l)
  rw [Set.disjoint_left]
  intro s hsk hsl
  rcases lt_or_gt_of_ne hkl with hkl' | hlk'
  · have hcast : (k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hkl'
    norm_num [veryBadFirstBandCell] at hsk hsl
    linarith
  · have hcast : (l : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hlk'
    norm_num [veryBadFirstBandCell] at hsk hsl
    linarith

theorem firstBandUnion_measure {N H : ℕ} :
    (volume (⋃ k ∈ veryBadOccupiedInteriorCells N H, veryBadFirstBandCell k)).toReal =
      (2 / 25 : ℝ) * (veryBadOccupiedInteriorCells N H).card := by
  classical
  change volume.real (⋃ k ∈ veryBadOccupiedInteriorCells N H, veryBadFirstBandCell k) = _
  rw [measureReal_biUnion_finset firstBandCells_pairwiseDisjoint
    (fun k hk => measurableSet_Ioo)
    (h := fun k hk => measure_Ioo_lt_top.ne)]
  simp [veryBadFirstBandCell]
  norm_num [max_def]
  ring

theorem firstBandUnion_subset_innerReciprocal
    {N H : ℕ} (hN : 0 < N) (hH : 200 ≤ H) :
    (⋃ k ∈ veryBadOccupiedInteriorCells N H, veryBadFirstBandCell k) ⊆
      veryBadInnerReciprocalScaleSet N H := by
  classical
  intro s hs
  simp only [mem_iUnion] at hs
  obtain ⟨k, hk, hsBand⟩ := hs
  have hkOcc := (Finset.mem_filter.mp hk).2
  obtain ⟨t, ht, htfloor⟩ := hkOcc
  have htY : t ∈ veryBadQuadraticReciprocalScaleSet N H := by
    exact ⟨⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩, ht.2⟩
  have hcell := firstBandCell_subset_innerReciprocal_of_witness hN hH htY ht.1.1 ht.1.2
  rw [htfloor] at hcell
  exact hcell ⟨hsBand.1.le, hsBand.2.le⟩

theorem innerReciprocal_measure_lower_by_quadraticInterior
    {N H : ℕ} (hN : 0 < N) (hH : 200 ≤ H) :
    (2 / 25 : ℝ) * (volume (veryBadQuadraticReciprocalInteriorSet N H)).toReal ≤
      (volume (veryBadInnerReciprocalScaleSet N H)).toReal := by
  have hSfinite : volume (veryBadInnerReciprocalScaleSet N H) ≠ ⊤ := (calc
    volume (veryBadInnerReciprocalScaleSet N H) ≤
        volume (Ioo ((N : ℝ) / (2 * H)) ((N : ℝ) / H)) :=
      measure_mono inter_subset_left
    _ < ⊤ := measure_Ioo_lt_top).ne
  have hmono := measureReal_mono
    (firstBandUnion_subset_innerReciprocal hN hH) hSfinite
  change (volume (⋃ k ∈ veryBadOccupiedInteriorCells N H, veryBadFirstBandCell k)).toReal ≤
    (volume (veryBadInnerReciprocalScaleSet N H)).toReal at hmono
  rw [firstBandUnion_measure] at hmono
  have hcard := quadraticInterior_measure_le_occupiedCell_card (N := N) (H := H)
  nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 25)
    (measureReal_nonneg : 0 ≤ volume.real (veryBadQuadraticReciprocalInteriorSet N H))]

theorem veryBadInnerReciprocalScale_measure_lower
    {N H : ℕ} (hN : 0 < N) (hH : 200 ≤ H)
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / H ^ 2) :
    (N : ℝ) / (400 * H) ≤
      (volume (veryBadInnerReciprocalScaleSet N H)).toReal := by
  have hInterior := veryBadQuadraticReciprocalInterior_measure_lower hN hH hscale
  have hInsert := innerReciprocal_measure_lower_by_quadraticInterior hN hH
  calc
    (N : ℝ) / (400 * H) = (2 / 25 : ℝ) * (N / (32 * H)) := by
      field_simp
      ring
    _ ≤ (2 / 25 : ℝ) * (volume (veryBadQuadraticReciprocalInteriorSet N H)).toReal := by
      gcongr
    _ ≤ (volume (veryBadInnerReciprocalScaleSet N H)).toReal := hInsert

/-- Exact pointwise transport of the inner good set by `s = N / t`. -/
theorem mem_veryBadInnerPrimeScaleSet_iff_reciprocal_mem
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) {t : ℝ} (ht : 0 < t) :
    t ∈ veryBadInnerPrimeScaleSet N H ↔
      (N : ℝ) / t ∈ veryBadInnerReciprocalScaleSet N H := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have h2Hr : (0 : ℝ) < 2 * H := by positivity
  have hcoord :
      (((N : ℝ) / t) ^ 2 / (N : ℝ)) = (N : ℝ) / t ^ 2 := by
    field_simp
  rw [veryBadInnerPrimeScaleSet, veryBadInnerReciprocalScaleSet]
  constructor
  · rintro ⟨htI, hxlo, hxhi, hylo, hyhi⟩
    refine ⟨⟨?_, ?_⟩, hxlo, hxhi, ?_, ?_⟩
    · exact (div_lt_div_iff_of_pos_left hNr h2Hr ht).mpr htI.2
    · exact (div_lt_div_iff_of_pos_left hNr ht hHr).mpr htI.1
    · simpa only [hcoord] using hylo
    · simpa only [hcoord] using hyhi
  · rintro ⟨hsI, hxlo, hxhi, hylo, hyhi⟩
    refine ⟨⟨?_, ?_⟩, hxlo, hxhi, ?_, ?_⟩
    · exact (div_lt_div_iff_of_pos_left hNr ht hHr).mp hsI.2
    · exact (div_lt_div_iff_of_pos_left hNr h2Hr ht).mp hsI.1
    · simpa only [hcoord] using hylo
    · simpa only [hcoord] using hyhi

theorem hasDerivAt_real_const_div (N : ℝ) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun u : ℝ => N / u) (-N / s ^ 2) s := by
  convert (hasDerivAt_const s N).div (hasDerivAt_id s) hs using 1
  simp [id, div_eq_mul_inv, pow_two]

theorem reciprocal_mem_veryBadInnerPrimeScaleSet_iff
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) {s : ℝ} (hs : 0 < s) :
    (N : ℝ) / s ∈ veryBadInnerPrimeScaleSet N H ↔
      s ∈ veryBadInnerReciprocalScaleSet N H := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := mem_veryBadInnerPrimeScaleSet_iff_reciprocal_mem
    hN hH (div_pos hNr hs)
  have hinv : (N : ℝ) / ((N : ℝ) / s) = s := by field_simp
  simpa only [hinv] using h

/-- Exact measure transport under Tao's first change of variables
`s = N / t`. -/
theorem volume_veryBadInnerPrimeScaleSet_eq_integral_reciprocal
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) :
    (volume (veryBadInnerPrimeScaleSet N H)).toReal =
      ∫ s in veryBadInnerReciprocalScaleSet N H, (N : ℝ) / s ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have h2Hr : (0 : ℝ) < 2 * H := by positivity
  have hlowPos : (0 : ℝ) < (N : ℝ) / (2 * H) := div_pos hNr h2Hr
  have hab : (N : ℝ) / (2 * H) ≤ (N : ℝ) / H :=
    div_le_div_of_nonneg_left hNr.le hHr (by linarith)
  have hfa : (N : ℝ) / ((N : ℝ) / (2 * H)) = 2 * H := by field_simp
  have hfb : (N : ℝ) / ((N : ℝ) / H) = H := by field_simp
  have hfcont : ContinuousOn (fun s : ℝ => (N : ℝ) / s)
      (uIcc ((N : ℝ) / (2 * H)) ((N : ℝ) / H)) := by
    rw [uIcc_of_le hab]
    intro s hs
    exact (continuousAt_const.div continuousAt_id
      (ne_of_gt (hlowPos.trans_le hs.1))).continuousWithinAt
  have hfderiv : ∀ s ∈ Ioo
      (min ((N : ℝ) / (2 * H)) ((N : ℝ) / H))
      (max ((N : ℝ) / (2 * H)) ((N : ℝ) / H)),
      HasDerivAt (fun u : ℝ => (N : ℝ) / u) (-N / s ^ 2) s := by
    intro s hs
    rw [min_eq_left hab, max_eq_right hab] at hs
    exact hasDerivAt_real_const_div (N : ℝ)
      (ne_of_gt (hlowPos.trans hs.1))
  have hfnonpos : ∀ s ∈ Ioo
      (min ((N : ℝ) / (2 * H)) ((N : ℝ) / H))
      (max ((N : ℝ) / (2 * H)) ((N : ℝ) / H)),
      (-N / s ^ 2 : ℝ) ≤ 0 := by
    intro s hs
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg N)) (sq_nonneg s)
  have hsubst :
      (∫ s in (N : ℝ) / (2 * H)..(N : ℝ) / H,
        (-N / s ^ 2 : ℝ) *
          (veryBadInnerPrimeScaleSet N H).indicator (fun _ => (1 : ℝ))
            ((N : ℝ) / s)) =
      ∫ t in 2 * (H : ℝ)..(H : ℝ),
        (veryBadInnerPrimeScaleSet N H).indicator (fun _ => (1 : ℝ)) t := by
    simpa only [smul_eq_mul, Function.comp_apply, hfa, hfb] using
      (intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos
        (g := (veryBadInnerPrimeScaleSet N H).indicator (fun _ => (1 : ℝ)))
        hfcont hfderiv hfnonpos)
  have hTsubsetIoc : veryBadInnerPrimeScaleSet N H ⊆
      Ioc (H : ℝ) (2 * H) :=
    (veryBadInnerPrimeScaleSet_subset N H).trans Ioo_subset_Ioc_self
  have hpositiveInterval :
      (∫ t in (H : ℝ)..2 * H,
        (veryBadInnerPrimeScaleSet N H).indicator (fun _ => (1 : ℝ)) t) =
      (volume (veryBadInnerPrimeScaleSet N H)).toReal := by
    rw [intervalIntegral.integral_of_le (by linarith),
      MeasureTheory.integral_indicator
        (measurableSet_veryBadInnerPrimeScaleSet N H),
      setIntegral_const, Measure.real_def,
      Measure.restrict_apply (measurableSet_veryBadInnerPrimeScaleSet N H),
      inter_eq_left.mpr hTsubsetIoc]
    simp
  have hright :
      (∫ t in 2 * (H : ℝ)..(H : ℝ),
        (veryBadInnerPrimeScaleSet N H).indicator (fun _ => (1 : ℝ)) t) =
      -(volume (veryBadInnerPrimeScaleSet N H)).toReal := by
    rw [intervalIntegral.integral_symm, hpositiveInterval]
  have hSsubsetIoc : veryBadInnerReciprocalScaleSet N H ⊆
      Ioc ((N : ℝ) / (2 * H)) ((N : ℝ) / H) := by
    intro s hs
    exact ⟨hs.1.1, hs.1.2.le⟩
  have hweightedInterval :
      (∫ s in (N : ℝ) / (2 * H)..(N : ℝ) / H,
        (veryBadInnerReciprocalScaleSet N H).indicator
          (fun s => (N : ℝ) / s ^ 2) s) =
      ∫ s in veryBadInnerReciprocalScaleSet N H, (N : ℝ) / s ^ 2 := by
    rw [intervalIntegral.integral_of_le hab,
      MeasureTheory.integral_indicator
        (measurableSet_veryBadInnerReciprocalScaleSet N H),
      Measure.restrict_restrict
        (measurableSet_veryBadInnerReciprocalScaleSet N H),
      inter_eq_left.mpr hSsubsetIoc]
  have hleft :
      (∫ s in (N : ℝ) / (2 * H)..(N : ℝ) / H,
        (-N / s ^ 2 : ℝ) *
          (veryBadInnerPrimeScaleSet N H).indicator (fun _ => (1 : ℝ))
            ((N : ℝ) / s)) =
      -(∫ s in veryBadInnerReciprocalScaleSet N H, (N : ℝ) / s ^ 2) := by
    calc
      _ = ∫ s in (N : ℝ) / (2 * H)..(N : ℝ) / H,
          -((veryBadInnerReciprocalScaleSet N H).indicator
            (fun s => (N : ℝ) / s ^ 2) s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hab] at hs
        have hspos : 0 < s := hlowPos.trans_le hs.1
        have hmem := reciprocal_mem_veryBadInnerPrimeScaleSet_iff hN hH hspos
        by_cases hsS : s ∈ veryBadInnerReciprocalScaleSet N H
        · have htT := hmem.mpr hsS
          simp [Set.indicator_of_mem hsS, Set.indicator_of_mem htT, neg_div]
        · have htT : (N : ℝ) / s ∉ veryBadInnerPrimeScaleSet N H :=
            fun ht => hsS (hmem.mp ht)
          simp [Set.indicator, hsS, htT]
      _ = -(∫ s in (N : ℝ) / (2 * H)..(N : ℝ) / H,
          (veryBadInnerReciprocalScaleSet N H).indicator
            (fun s => (N : ℝ) / s ^ 2) s) := by
        rw [intervalIntegral.integral_neg]
      _ = _ := by rw [hweightedInterval]
  rw [hleft, hright] at hsubst
  linarith

theorem reciprocalJacobian_lower_on_sourceInterval
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) {s : ℝ}
    (hspos : 0 < s) (hsle : s ≤ (N : ℝ) / H) :
    (H : ℝ) ^ 2 / N ≤ (N : ℝ) / s ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hmul : s * (H : ℝ) ≤ N := (le_div_iff₀ hHr).mp hsle
  rw [div_le_div_iff₀ hNr (sq_pos_of_pos hspos)]
  nlinarith [mul_self_le_mul_self (mul_nonneg hspos.le hHr.le) hmul]

theorem integrableOn_reciprocalJacobian_innerScaleSet
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) :
    IntegrableOn (fun s : ℝ => (N : ℝ) / s ^ 2)
      (veryBadInnerReciprocalScaleSet N H) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have h2Hr : (0 : ℝ) < 2 * H := by positivity
  have hlowPos : (0 : ℝ) < (N : ℝ) / (2 * H) := div_pos hNr h2Hr
  have hcont : ContinuousOn (fun s : ℝ => (N : ℝ) / s ^ 2)
      (Icc ((N : ℝ) / (2 * H)) ((N : ℝ) / H)) := by
    intro s hs
    exact (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 (ne_of_gt (hlowPos.trans_le hs.1)))).continuousWithinAt
  apply (hcont.integrableOn_compact isCompact_Icc).mono_set
  intro s hs
  exact ⟨hs.1.1.le, hs.1.2.le⟩

/-- The Jacobian in the first source substitution turns a reciprocal-scale
measure lower bound of order `N/H` into a prime-scale lower bound of order
`H`. -/
theorem reciprocalScale_measure_mul_jacobian_le_primeScale_measure
    {N H : ℕ} (hN : 0 < N) (hH : 0 < H) :
    (H : ℝ) ^ 2 / N *
        (volume (veryBadInnerReciprocalScaleSet N H)).toReal ≤
      (volume (veryBadInnerPrimeScaleSet N H)).toReal := by
  have hconst : Integrable (fun _ : ℝ => (H : ℝ) ^ 2 / N)
      (volume.restrict (veryBadInnerReciprocalScaleSet N H)) :=
    (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set (by
      intro s hs
      exact ⟨hs.1.1.le, hs.1.2.le⟩)
  have hjac : Integrable (fun s : ℝ => (N : ℝ) / s ^ 2)
      (volume.restrict (veryBadInnerReciprocalScaleSet N H)) :=
    integrableOn_reciprocalJacobian_innerScaleSet hN hH
  have hmono : (fun _ : ℝ => (H : ℝ) ^ 2 / N) ≤ᶠ[ae
      (volume.restrict (veryBadInnerReciprocalScaleSet N H))]
      (fun s : ℝ => (N : ℝ) / s ^ 2) := by
    filter_upwards [ae_restrict_mem
      (measurableSet_veryBadInnerReciprocalScaleSet N H)] with s hs
    have hlow : (0 : ℝ) < (N : ℝ) / (2 * H) := by positivity
    exact reciprocalJacobian_lower_on_sourceInterval hN hH
      (hlow.trans hs.1.1) hs.1.2.le
  have hmain := integral_mono_ae hconst hjac hmono
  rw [setIntegral_const, Measure.real_def, smul_eq_mul] at hmain
  rw [volume_veryBadInnerPrimeScaleSet_eq_integral_reciprocal hN hH]
  simpa [mul_comm] using hmain

/-- The complete geometric lower bound in Tao's Lemma 3.1: after the two
changes of variables, endpoint trimming, and unit-cell insertion, the exact
inner prime-scale good set occupies at least `H / 400`. -/
theorem veryBadInnerPrimeScale_measure_lower
    {N H : ℕ} (hN : 0 < N) (hH : 200 ≤ H)
    (hscale : (1 / 2 : ℝ) ≤ (N : ℝ) / H ^ 2) :
    (H : ℝ) / 400 ≤
      (volume (veryBadInnerPrimeScaleSet N H)).toReal := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  have hreciprocal := veryBadInnerReciprocalScale_measure_lower hN hH hscale
  have hjac := reciprocalScale_measure_mul_jacobian_le_primeScale_measure
    hN hHpos
  calc
    (H : ℝ) / 400 = (H : ℝ) ^ 2 / N * (N / (400 * H)) := by
      field_simp
    _ ≤ (H : ℝ) ^ 2 / N *
        (volume (veryBadInnerReciprocalScaleSet N H)).toReal := by
      gcongr
    _ ≤ (volume (veryBadInnerPrimeScaleSet N H)).toReal := hjac

/-- The complete geometric lower bound with its source arithmetic input
packaged as the exact Sylvester--Schur contract. -/
theorem veryBadInnerPrimeScale_measure_lower_of_sylvesterSchur
    (hSS : SylvesterSchurConclusion) {N H : ℕ} (hN : 1 ≤ N)
    (hH : 200 ≤ H) (hveryBad : IsVeryBadInterval N H) :
    (H : ℝ) / 400 ≤
      (volume (veryBadInnerPrimeScaleSet N H)).toReal :=
  veryBadInnerPrimeScale_measure_lower hN hH
    (hveryBad.one_half_le_start_div_length_sq_of_sylvesterSchur hSS hN)

/-- The complete geometric lower bound stated directly from the standard
binomial Sylvester--Schur theorem. -/
theorem veryBadInnerPrimeScale_measure_lower_of_binomial_sylvesterSchur
    (hSS : BinomialSylvesterSchurConclusion) {N H : ℕ} (hN : 1 ≤ N)
    (hH : 200 ≤ H) (hveryBad : IsVeryBadInterval N H) :
    (H : ℝ) / 400 ≤
      (volume (veryBadInnerPrimeScaleSet N H)).toReal :=
  veryBadInnerPrimeScale_measure_lower_of_sylvesterSchur
    (sylvesterSchurConclusion_of_binomial hSS) hN hH hveryBad

/-- The complete geometric lower bound from only the quadratic-window
Sylvester--Schur input actually required by Tao's proof. -/
theorem veryBadInnerPrimeScale_measure_lower_of_quadraticWindow_sylvesterSchur
    (hSS : QuadraticWindowSylvesterSchurConclusion) {N H : ℕ} (hN : 1 ≤ N)
    (hH : 200 ≤ H) (hveryBad : IsVeryBadInterval N H) :
    (H : ℝ) / 400 ≤
      (volume (veryBadInnerPrimeScaleSet N H)).toReal :=
  veryBadInnerPrimeScale_measure_lower hN hH
    (hveryBad.one_half_le_start_div_length_sq_of_quadraticWindow_sylvesterSchur hSS hN)

/-- Unconditional eventual geometric lower bound for every positive-start
very bad interval. -/
theorem eventually_veryBadInnerPrimeScale_measure_lower :
    ∀ᶠ H : ℕ in Filter.atTop, ∀ N : ℕ, 1 ≤ N → IsVeryBadInterval N H →
      (H : ℝ) / 400 ≤
        (volume (veryBadInnerPrimeScaleSet N H)).toReal := by
  filter_upwards [eventually_one_half_le_start_div_length_sq_of_veryBad,
    Filter.eventually_ge_atTop (200 : ℕ)] with H hscale hH N hN hveryBad
  exact veryBadInnerPrimeScale_measure_lower hN hH (hscale N hN hveryBad)

/-- The weighted cutoff integral dominates the Lebesgue measure of the exact
inner good set, with a fixed lower-bound constant for the cutoff.  Keeping
the constant explicit is what permits a uniform eventual contradiction. -/
theorem norm_veryBadPrimeEquidistributionIntegral_lower_bound_by_innerMeasure
    (c : ℝ) (hcW : ∀ x y : ℝ,
      (91 / 100 : ℝ) ≤ Int.fract x → Int.fract x ≤ 99 / 100 →
      (1 / 100 : ℝ) ≤ Int.fract y → Int.fract y ≤ 89 / 100 →
      c ≤ (veryBadSmoothCutoff (x, y)).re)
    {N H : ℕ} (hH : 2 ≤ H) :
    c / Real.log (2 * H) *
        (volume (veryBadInnerPrimeScaleSet N H)).toReal ≤
      ‖primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H))
        veryBadSmoothCutoff (N : ℝ) (N : ℝ) 2‖ := by
  let f : ℝ → ℝ := fun t =>
    (veryBadSmoothCutoff ((N : ℝ) / t, (N : ℝ) / t ^ 2) /
      Real.log t).re
  let g : ℝ → ℝ := (veryBadInnerPrimeScaleSet N H).indicator
    (fun _ => c / Real.log (2 * H))
  have hf : Integrable f (volume.restrict (Ioo (H : ℝ) (2 * H))) :=
    (integrableOn_veryBadPrimeIntegralIntegrand hH).re
  have hg : Integrable g (volume.restrict (Ioo (H : ℝ) (2 * H))) :=
    (integrable_const (c / Real.log (2 * H))).indicator
      (measurableSet_veryBadInnerPrimeScaleSet N H)
  have hmono : g ≤ᶠ[ae (volume.restrict (Ioo (H : ℝ) (2 * H)))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t htI
    by_cases htGood : t ∈ veryBadInnerPrimeScaleSet N H
    · dsimp [g]
      rw [Set.indicator_of_mem htGood]
      rcases htGood.2 with ⟨hxlo, hxhi, hylo, hyhi⟩
      have hcutoff := hcW ((N : ℝ) / t) ((N : ℝ) / t ^ 2)
        hxlo hxhi hylo hyhi
      have htOne : (1 : ℝ) < t := by
        have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
        linarith [htI.1]
      have htTwoH : t ≤ (2 * H : ℕ) := by
        exact_mod_cast htI.2.le
      have hlogt : 0 < Real.log t := Real.log_pos htOne
      have hlogLe : Real.log t ≤ Real.log (2 * H) :=
        Real.strictMonoOn_log.monotoneOn
          (show 0 < t by linarith)
          (show (0 : ℝ) < 2 * H by positivity)
          (by exact_mod_cast htTwoH)
      dsimp [f]
      change c / Real.log (2 * H) ≤
        (Complex.ofReal (veryBadSmoothCutoff ((N : ℝ) / t,
          (N : ℝ) / t ^ 2)).re / Complex.ofReal (Real.log t)).re
      rw [← Complex.ofReal_div, Complex.ofReal_re]
      exact div_le_div₀ (veryBadSmoothCutoff_re_nonneg _)
        hcutoff hlogt hlogLe
    · dsimp [g]
      simp only [Set.indicator, htGood, ↓reduceIte]
      dsimp [f]
      apply veryBadPrimeIntegralIntegrand_re_nonneg
      have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
      linarith [htI.1]
  have hmain := integral_mono_ae hg hf hmono
  dsimp [g] at hmain
  rw [integral_indicator (measurableSet_veryBadInnerPrimeScaleSet N H),
    setIntegral_const, Measure.real_def,
    Measure.restrict_apply (measurableSet_veryBadInnerPrimeScaleSet N H),
    inter_eq_left.mpr (veryBadInnerPrimeScaleSet_subset N H)] at hmain
  simp only [smul_eq_mul] at hmain
  rw [norm_veryBadPrimeEquidistributionIntegral_eq_re hH]
  calc
    c / Real.log (2 * H) *
        (volume (veryBadInnerPrimeScaleSet N H)).toReal =
      (volume (veryBadInnerPrimeScaleSet N H)).toReal *
        (c / Real.log (2 * H)) := by ring
    _ ≤ ∫ t in Ioo (H : ℝ) (2 * H), f t := hmain
    _ = (primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H))
          veryBadSmoothCutoff (N : ℝ) (N : ℝ) 2).re := by
      rw [primeEquidistributionIntegral, ← Complex.reCLM_apply,
        ← Complex.reCLM.integral_comp_comm
          (integrableOn_veryBadPrimeIntegralIntegrand hH)]
      rfl

/-- Existential form of the fixed-cutoff integral lower bound. -/
theorem exists_norm_veryBadPrimeEquidistributionIntegral_lower_bound_by_innerMeasure
    {N H : ℕ} (hH : 2 ≤ H) :
    ∃ c : ℝ, 0 < c ∧
      c / Real.log (2 * H) *
          (volume (veryBadInnerPrimeScaleSet N H)).toReal ≤
        ‖primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H))
          veryBadSmoothCutoff (N : ℝ) (N : ℝ) 2‖ := by
  obtain ⟨c, hc, hcW⟩ :=
    exists_pos_le_veryBadSmoothCutoff_re_of_innerFractionalRegion
  exact ⟨c, hc,
    norm_veryBadPrimeEquidistributionIntegral_lower_bound_by_innerMeasure
      c hcW hH⟩

/-- The exponent supplied to Theorem 2.5 when Lemma 3.1 is contradicted at
the scale `exp ((log N) ^ (2 / 3 + η))`. -/
def veryBadTheorem25Epsilon (η : ℝ) : ℝ :=
  3 / 2 - (2 / 3 + η)⁻¹

theorem veryBadTheorem25Epsilon_pos {η : ℝ} (hη : 0 < η) :
    0 < veryBadTheorem25Epsilon η := by
  have ha : 0 < (2 / 3 : ℝ) + η := by positivity
  rw [veryBadTheorem25Epsilon, sub_pos, inv_lt_iff_one_lt_mul₀ ha]
  nlinarith

theorem threeHalves_sub_veryBadTheorem25Epsilon (η : ℝ) :
    3 / 2 - veryBadTheorem25Epsilon η = ((2 / 3 + η)⁻¹ : ℝ) := by
  rw [veryBadTheorem25Epsilon]
  ring

/-- For every fixed positive source slack, Tao's contradiction growth
hypothesis eventually exceeds the absolute unit-cell threshold `H ≥ 200`. -/
theorem eventually_two_hundred_le_of_veryBad_growth {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ H : ℕ,
      Real.exp ((Real.log N) ^ (2 / 3 + η)) < H → 200 ≤ H := by
  have ha : 0 < (2 / 3 : ℝ) + η := by positivity
  have ht : Filter.Tendsto
      (fun N : ℕ => (Real.log (N : ℝ)) ^ (2 / 3 + η))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop ha).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually
      (Filter.eventually_ge_atTop (Real.log 200))] with N hN H hGrowth
  have hExp : (200 : ℝ) ≤
      Real.exp ((Real.log N) ^ (2 / 3 + η)) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 200)]
    exact Real.exp_le_exp.mpr hN
  have hReal : (200 : ℝ) < H :=
    hExp.trans_lt (by exact_mod_cast hGrowth)
  exact_mod_cast hReal.le

/-- The contradiction hypothesis in Lemma 3.1 implies the exact frequency
range required by the specialized Theorem 2.5, with hidden multiplier one. -/
theorem vinogradovParameterBound_of_veryBad_growth
    {N H : ℕ} {η : ℝ} (hN : 2 ≤ N) (hH : 2 ≤ H) (hη : 0 < η)
    (hgrowth : Real.exp ((Real.log N) ^ (2 / 3 + η)) < H) :
    VinogradovParameterBound (veryBadTheorem25Epsilon η) 1
      (H : ℝ) (N : ℝ) := by
  have ha : 0 < (2 / 3 : ℝ) + η := by positivity
  have hb : 0 < ((2 / 3 + η)⁻¹ : ℝ) := inv_pos.mpr ha
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
  have hHreal : (0 : ℝ) < H := by positivity
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  have hpowlt :
      (Real.log (N : ℝ)) ^ (2 / 3 + η) < Real.log (H : ℝ) :=
    (Real.lt_log_iff_exp_lt hHreal).mpr (by exact_mod_cast hgrowth)
  have hraised := Real.rpow_lt_rpow
    (Real.rpow_nonneg hlogNpos.le (2 / 3 + η)) hpowlt hb
  rw [← Real.rpow_mul hlogNpos.le,
    mul_inv_cancel₀ ha.ne', Real.rpow_one] at hraised
  have hexp :
      Real.exp (Real.log (N : ℝ)) <
        Real.exp ((Real.log (H : ℝ)) ^ ((2 / 3 + η)⁻¹ : ℝ)) :=
    Real.exp_lt_exp.mpr hraised
  rw [Real.exp_log (by positivity : (0 : ℝ) < N)] at hexp
  rw [VinogradovParameterBound, abs_of_nonneg (Nat.cast_nonneg N),
    one_mul, threeHalves_sub_veryBadTheorem25Epsilon]
  exact hexp.le

/-- Exact vanishing of the prime sum in the proof of Lemma 3.1. -/
theorem primeEquidistributionSum_eq_zero_of_veryBad
    {N H : ℕ} {W : ℝ × ℝ → ℂ} (hH : 2 ≤ H)
    (hveryBad : IsVeryBadInterval N H)
    (hWsupport : IsSupportedInVeryBadForbiddenRegion W) :
    primeEquidistributionSum (H : ℝ) (Ioo (H : ℝ) (2 * H)) W
      (N : ℝ) (N : ℝ) 2 = 0 := by
  unfold primeEquidistributionSum
  apply Finset.sum_eq_zero
  intro p hpMem
  have hHReal : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hsubset : Ioo (H : ℝ) (2 * H) ⊆ Icc (H : ℝ) (2 * H) := by
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hpData :=
    (mem_primesInScaleSet hHReal hsubset).mp hpMem
  by_contra hWne
  have hpRange := hpData.2
  have hHltp : H < p := by exact_mod_cast hpRange.1
  have hpLe : p ≤ 2 * H := by exact_mod_cast hpRange.2.le
  have hfractional : InVeryBadForbiddenFractionalRegion N p := by
    rw [InVeryBadForbiddenFractionalRegion]
    simpa only [Nat.cast_pow] using
      hWsupport ((N : ℝ) / (p : ℝ))
        ((N : ℝ) / (p : ℝ) ^ 2) (by simpa using hWne)
  have hresidues : InVeryBadForbiddenResidueRegion N p :=
    (forbiddenFractionalRegion_iff_residues hpData.1.pos).mp hfractional
  exact (not_forbiddenResidues_of_veryBad hveryBad hpData.1 hHltp hpLe)
    hresidues

/-- Direct Theorem 2.5 consumer for a very bad interval.  The arithmetic
prime sum has disappeared completely; the remaining work in Lemma 3.1 is the
construction of a fixed smooth cutoff and the lower bound for this integral. -/
theorem exists_veryBadIntegralBound_of_taoTheorem25Specialized
    (h25 : TaoTheorem25SpecializedConclusion)
    {N H : ℕ} (hH : 2 ≤ H) (hveryBad : IsVeryBadInterval N H)
    {W : ℝ × ℝ → ℂ} (hWdiff : ContDiff ℝ ∞ W)
    (hWperiodic : IsZ2Periodic W)
    (hWsupport : IsSupportedInVeryBadForbiddenRegion W)
    {ε A K : ℝ} (hε : 0 < ε) (hA : 0 < A) (hK : 0 < K)
    (hNbound : VinogradovParameterBound ε K (H : ℝ) (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ‖primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H)) W
          (N : ℝ) (N : ℝ) 2‖ ≤
        C * taoC3Norm W * (H : ℝ) / (Real.log H) ^ A := by
  obtain ⟨C, hC, hbound⟩ := h25 ε hε A hA K hK
  refine ⟨C, hC, ?_⟩
  have hHReal : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hsubset : Ioo (H : ℝ) (2 * H) ⊆ Icc (H : ℝ) (2 * H) := by
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hestimate := hbound (H : ℝ) (Ioo (H : ℝ) (2 * H)) W
    (N : ℝ) hHReal measurableSet_Ioo ordConnected_Ioo hsubset hWdiff
    hWperiodic hNbound
  rw [primeEquidistributionSum_eq_zero_of_veryBad hH hveryBad hWsupport,
    zero_sub, norm_neg] at hestimate
  exact hestimate

/-- The source integral upper bound with no cutoff left as user-supplied data:
the fixed `veryBadSmoothCutoff` above is smooth, periodic, nonnegative, and
supported in the forbidden rectangle. -/
theorem exists_veryBadSmoothCutoffIntegralBound_of_taoTheorem25Specialized
    (h25 : TaoTheorem25SpecializedConclusion)
    {N H : ℕ} (hH : 2 ≤ H) (hveryBad : IsVeryBadInterval N H)
    {ε A K : ℝ} (hε : 0 < ε) (hA : 0 < A) (hK : 0 < K)
    (hNbound : VinogradovParameterBound ε K (H : ℝ) (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ‖primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H))
          veryBadSmoothCutoff (N : ℝ) (N : ℝ) 2‖ ≤
        C * taoC3Norm veryBadSmoothCutoff * (H : ℝ) /
          (Real.log H) ^ A := by
  exact exists_veryBadIntegralBound_of_taoTheorem25Specialized h25 hH
    hveryBad veryBadSmoothCutoff_contDiff
    veryBadSmoothCutoff_isZ2Periodic veryBadSmoothCutoff_supported
    hε hA hK hNbound

/-- The complete upper-bound half of Tao's Lemma 3.1 contradiction.  Its
subexponential contradiction hypothesis automatically supplies the exponent
and parameter range used by Theorem 2.5. -/
theorem exists_veryBadSmoothCutoffIntegralBound_of_growth
    (h25 : TaoTheorem25SpecializedConclusion)
    {N H : ℕ} (hN : 2 ≤ N) (hH : 2 ≤ H)
    (hveryBad : IsVeryBadInterval N H) {η A : ℝ}
    (hη : 0 < η) (hA : 0 < A)
    (hgrowth : Real.exp ((Real.log N) ^ (2 / 3 + η)) < H) :
    ∃ C : ℝ, 0 < C ∧
      ‖primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H))
          veryBadSmoothCutoff (N : ℝ) (N : ℝ) 2‖ ≤
        C * taoC3Norm veryBadSmoothCutoff * (H : ℝ) /
          (Real.log H) ^ A := by
  exact exists_veryBadSmoothCutoffIntegralBound_of_taoTheorem25Specialized
    h25 hH hveryBad (veryBadTheorem25Epsilon_pos hη) hA
    (by norm_num) (vinogradovParameterBound_of_veryBad_growth hN hH hη hgrowth)

/-- Two powers of logarithmic saving eventually beat the fixed-cutoff lower
bound, uniformly after the common factor `H` is restored. -/
theorem eventually_logarithmic_integral_gap (D : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ H : ℕ in Filter.atTop,
      D * (H : ℝ) / (Real.log H) ^ 2 <
        c / Real.log (2 * H) * ((H : ℝ) / 400) := by
  let D₀ : ℝ := max D 0
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_gt_atTop (800 * D₀ / c))
  filter_upwards [hlog, Filter.eventually_ge_atTop (2 : ℕ)] with H hlarge hH
  have hHr : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by positivity
  have hlogH : 0 < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hlogTwoLe : Real.log 2 ≤ Real.log (H : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hHpos hHr
  have hlogTwoH : Real.log (2 * (H : ℝ)) =
      Real.log 2 + Real.log (H : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hHpos.ne']
  have hlogTwoHPos : 0 < Real.log (2 * (H : ℝ)) :=
    Real.log_pos (by nlinarith)
  have hlogTwoHLe : Real.log (2 * (H : ℝ)) ≤
      2 * Real.log (H : ℝ) := by
    rw [hlogTwoH]
    linarith
  have hD₀ : 0 ≤ D₀ := le_max_right D 0
  have hDle : D ≤ D₀ := le_max_left D 0
  have hthreshold : 800 * D₀ < c * Real.log (H : ℝ) := by
    have hlarge' : 800 * D₀ / c < Real.log (H : ℝ) := by
      simpa only [Function.comp_apply] using hlarge
    simpa [mul_comm] using (div_lt_iff₀ hc).mp hlarge'
  have hnum : D * (400 * Real.log (2 * (H : ℝ))) <
      c * (Real.log (H : ℝ)) ^ 2 := by
    calc
      D * (400 * Real.log (2 * (H : ℝ))) ≤
          D₀ * (400 * Real.log (2 * (H : ℝ))) := by
            gcongr
      _ ≤ D₀ * (400 * (2 * Real.log (H : ℝ))) := by
            gcongr
      _ = (800 * D₀) * Real.log (H : ℝ) := by ring
      _ < (c * Real.log (H : ℝ)) * Real.log (H : ℝ) :=
        mul_lt_mul_of_pos_right hthreshold hlogH
      _ = c * (Real.log (H : ℝ)) ^ 2 := by ring
  have hscalar : D / (Real.log (H : ℝ)) ^ 2 <
      c / (400 * Real.log (2 * (H : ℝ))) := by
    rw [div_lt_div_iff₀ (sq_pos_of_pos hlogH)
      (mul_pos (by norm_num) hlogTwoHPos)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hnum
  have hmul := mul_lt_mul_of_pos_left hscalar hHpos
  convert hmul using 1 <;> ring

/-- An eventual property of integer scales transfers uniformly to every
`H` above Tao's subexponential growth threshold. -/
theorem eventually_of_veryBad_growth {η : ℝ} (hη : 0 < η)
    {P : ℕ → Prop} (hP : ∀ᶠ H : ℕ in Filter.atTop, P H) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ H : ℕ,
      Real.exp ((Real.log N) ^ (2 / 3 + η)) < H → P H := by
  obtain ⟨H₀, hH₀⟩ := (Filter.eventually_atTop.1 hP)
  have ha : 0 < (2 / 3 : ℝ) + η := by positivity
  have ht : Filter.Tendsto
      (fun N : ℕ => Real.exp ((Real.log (N : ℝ)) ^ (2 / 3 + η)))
      Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  filter_upwards [ht.eventually
      (Filter.eventually_ge_atTop (H₀ : ℝ))] with N hN H hGrowth
  apply hH₀ H
  have hreal : (H₀ : ℝ) < H := hN.trans_lt (by exact_mod_cast hGrowth)
  exact_mod_cast hreal.le

/-- Conditional completion of Tao's Lemma 3.1 contradiction: assuming the
specialized Theorem 2.5 estimate, sufficiently large positive-start very bad
intervals cannot lie above the source's subexponential length threshold. -/
theorem eventually_not_isVeryBadInterval_of_growth_of_taoTheorem25Specialized
    (h25 : TaoTheorem25SpecializedConclusion) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ H : ℕ,
      Real.exp ((Real.log N) ^ (2 / 3 + η)) < H →
        ¬ IsVeryBadInterval N H := by
  obtain ⟨c, hc, hcW⟩ :=
    exists_pos_le_veryBadSmoothCutoff_re_of_innerFractionalRegion
  obtain ⟨C, hC, hbound⟩ := h25 (veryBadTheorem25Epsilon η)
    (veryBadTheorem25Epsilon_pos hη) 2 (by norm_num) 1 (by norm_num)
  let D : ℝ := C * taoC3Norm veryBadSmoothCutoff
  have hgapN := eventually_of_veryBad_growth hη
    (eventually_logarithmic_integral_gap D hc)
  have hmeasureN := eventually_of_veryBad_growth hη
    eventually_veryBadInnerPrimeScale_measure_lower
  have hlargeN := eventually_two_hundred_le_of_veryBad_growth hη
  filter_upwards [hgapN, hmeasureN, hlargeN,
    Filter.eventually_ge_atTop (2 : ℕ)] with N hgap hmeasure hlarge hN H hGrowth
  intro hveryBad
  have hH200 : 200 ≤ H := hlarge H hGrowth
  have hH : 2 ≤ H := le_trans (by norm_num) hH200
  have hNpos : 1 ≤ N := le_trans (by norm_num) hN
  have hmeasureLower := hmeasure H hGrowth N hNpos hveryBad
  have hintegralLower :=
    norm_veryBadPrimeEquidistributionIntegral_lower_bound_by_innerMeasure
      c hcW hH (N := N)
  have hlogTwoHNonneg : 0 ≤ Real.log (2 * (H : ℝ)) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 2 * H by omega)
  have hfullLower :
      c / Real.log (2 * H) * ((H : ℝ) / 400) ≤
        ‖primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H))
          veryBadSmoothCutoff (N : ℝ) (N : ℝ) 2‖ :=
    (mul_le_mul_of_nonneg_left hmeasureLower
      (div_nonneg hc.le hlogTwoHNonneg)).trans hintegralLower
  have hHReal : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hsubset : Ioo (H : ℝ) (2 * H) ⊆ Icc (H : ℝ) (2 * H) := by
    intro x hx
    exact ⟨hx.1.le, hx.2.le⟩
  have hestimate := hbound (H : ℝ) (Ioo (H : ℝ) (2 * H))
    veryBadSmoothCutoff (N : ℝ) hHReal measurableSet_Ioo ordConnected_Ioo
    hsubset veryBadSmoothCutoff_contDiff veryBadSmoothCutoff_isZ2Periodic
    (vinogradovParameterBound_of_veryBad_growth hN hH hη hGrowth)
  rw [primeEquidistributionSum_eq_zero_of_veryBad hH hveryBad
      veryBadSmoothCutoff_supported,
    zero_sub, norm_neg] at hestimate
  have hfullUpper :
      ‖primeEquidistributionIntegral (Ioo (H : ℝ) (2 * H))
          veryBadSmoothCutoff (N : ℝ) (N : ℝ) 2‖ ≤
        D * (H : ℝ) / (Real.log H) ^ 2 := by
    simpa [D] using hestimate
  exact (not_lt_of_ge (hfullLower.trans hfullUpper)) (hgap H hGrowth)

/-- Exact corrected contract for Tao's Lemma 3.1.  The elementary clause
classifies `(N,H)=(0,1)` as the unique exception to `H < N` under the paper's
literal conventions.  The second clause is the precise fixed-slack meaning of
`H ≤ exp (log^(2/3+o(1)) N)`. -/
def TaoLemma31Conclusion : Prop :=
  (∀ {N H : ℕ}, IsVeryBadInterval N H →
      (N = 0 ∧ H = 1) ∨ H < N) ∧
    ∀ η : ℝ, 0 < η →
      ∀ᶠ N : ℕ in Filter.atTop, ∀ H : ℕ,
        IsVeryBadInterval N H →
          (H : ℝ) ≤ Real.exp ((Real.log N) ^ (2 / 3 + η))

/-- Conditional closure of the full corrected Lemma 3.1 contract from the
only specialization of Theorem 2.5 used in its proof. -/
theorem taoLemma31_of_taoTheorem25Specialized
    (h25 : TaoTheorem25SpecializedConclusion) : TaoLemma31Conclusion := by
  refine ⟨?_, ?_⟩
  · intro N H hveryBad
    exact hveryBad.eq_zero_one_or_length_lt_start
  · intro η hη
    have hnot :=
      eventually_not_isVeryBadInterval_of_growth_of_taoTheorem25Specialized h25 hη
    filter_upwards [hnot] with N hN H hveryBad
    apply le_of_not_gt
    intro hgrowth
    exact hN H hgrowth hveryBad

/-- Source-facing conditional closure of Lemma 3.1 from the full Theorem 2.5
contract. -/
theorem taoLemma31_of_taoTheorem25
    (h25 : TaoTheorem25Conclusion) : TaoLemma31Conclusion :=
  taoLemma31_of_taoTheorem25Specialized
    (taoTheorem25Specialized_of_full h25)

end

end Tao2026
