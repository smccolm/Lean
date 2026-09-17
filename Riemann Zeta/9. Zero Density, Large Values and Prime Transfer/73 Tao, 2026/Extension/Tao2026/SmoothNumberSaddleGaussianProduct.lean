import Tao2026.SmoothNumberSaddleCurvatureLower

/-!
# Finite-product transfer to the Gaussian characteristic function

This file isolates the deterministic triangular-array step in the saddle
local-limit argument.  A product of centered characteristic factors converges
to the Gaussian characteristic function once each factor has its quadratic
variance approximation, the total approximation error vanishes, and the
largest variance share vanishes.
-/

open Filter Topology

namespace Tao2026

noncomputable section

/-- Products of contractions are Lipschitz, with the sum of the coordinate
errors as Lipschitz bound. -/
theorem norm_finsetProd_sub_finsetProd_le_sum
    {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤
      ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.sum_insert ha]
      calc
        ‖f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i‖ =
            ‖f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
              (f a - g a) * ∏ i ∈ s, g i‖ := by
                congr 1
                ring
        _ ≤ ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ +
              ‖f a - g a‖ * ‖∏ i ∈ s, g i‖ := by
                simpa only [norm_mul] using norm_add_le
                  (f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
                  ((f a - g a) * ∏ i ∈ s, g i)
        _ ≤ 1 * (∑ i ∈ s, ‖f i - g i‖) +
              ‖f a - g a‖ * 1 := by
                gcongr
                · exact hf a (Finset.mem_insert_self a s)
                · exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
                    (fun i hi => hg i (Finset.mem_insert_of_mem hi))
                · rw [norm_prod]
                  exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
                    (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        _ = ‖f a - g a‖ + ∑ i ∈ s, ‖f i - g i‖ := by ring

/-- On the unit interval, the linear Euler factor `1 - x` differs from
`exp (-x)` by at most `x^2`. -/
theorem abs_one_sub_sub_exp_neg_le_sq {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |(1 - x) - Real.exp (-x)| ≤ x ^ 2 := by
  have hnorm : ‖-x‖ ≤ 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hx0]
  have h := Real.norm_exp_sub_one_sub_id_le hnorm
  rw [Real.norm_eq_abs] at h
  have heq : Real.exp (-x) - 1 - (-x) = -((1 - x) - Real.exp (-x)) := by
    ring
  rw [heq, abs_neg] at h
  simpa using h

/-- Deterministic comparison between a product of linearized factors and the
exponential of their sum. -/
theorem norm_prod_one_sub_sub_exp_neg_sum_le_sum_sq
    {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    ‖(∏ i ∈ s, ((1 - x i : ℝ) : ℂ)) -
        Complex.exp ((-(∑ i ∈ s, x i) : ℝ) : ℂ)‖ ≤
      ∑ i ∈ s, (x i) ^ 2 := by
  classical
  have hlin : ∀ i ∈ s, ‖((1 - x i : ℝ) : ℂ)‖ ≤ 1 := by
    intro i hi
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hnonneg : 0 ≤ 1 - x i := sub_nonneg.mpr (hx1 i hi)
    rw [abs_of_nonneg hnonneg]
    linarith [hx0 i hi]
  have hexp : ∀ i ∈ s, ‖Complex.exp ((-x i : ℝ) : ℂ)‖ ≤ 1 := by
    intro i hi
    rw [Complex.norm_exp]
    simp only [Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hx0 i hi))
  calc
    ‖(∏ i ∈ s, ((1 - x i : ℝ) : ℂ)) -
        Complex.exp ((-(∑ i ∈ s, x i) : ℝ) : ℂ)‖ =
        ‖(∏ i ∈ s, ((1 - x i : ℝ) : ℂ)) -
          ∏ i ∈ s, Complex.exp ((-x i : ℝ) : ℂ)‖ := by
            rw [← Complex.exp_sum]
            congr 3
            push_cast
            rw [Finset.sum_neg_distrib]
    _ ≤ ∑ i ∈ s,
          ‖((1 - x i : ℝ) : ℂ) - Complex.exp ((-x i : ℝ) : ℂ)‖ :=
      norm_finsetProd_sub_finsetProd_le_sum s _ _ hlin hexp
    _ = ∑ i ∈ s, |(1 - x i) - Real.exp (-x i)| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
    _ ≤ ∑ i ∈ s, (x i) ^ 2 :=
      Finset.sum_le_sum fun i hi =>
        abs_one_sub_sub_exp_neg_le_sq (hx0 i hi) (hx1 i hi)

/-- A convenient bound for the quadratic error in terms of the largest
variance share and the total variance. -/
theorem sum_sq_le_max_mul_sum
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) {M : ℝ}
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hxM : ∀ i ∈ s, x i ≤ M) :
    ∑ i ∈ s, (x i) ^ 2 ≤ M * ∑ i ∈ s, x i := by
  calc
    ∑ i ∈ s, (x i) ^ 2 ≤ ∑ i ∈ s, M * x i := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [hx0 i hi, hxM i hi]
    _ = M * ∑ i ∈ s, x i := by rw [Finset.mul_sum]

/-- Quantitative finite-product Gaussian transfer.  Here `v i` is the
variance share of coordinate `i`, and `c` will be `t^2 / 2`. -/
theorem norm_prod_sub_gaussian_le
    {ι : Type*} (s : Finset ι) (z : ι → ℂ) (v : ι → ℝ) (c M : ℝ)
    (hc : 0 ≤ c) (hv0 : ∀ i ∈ s, 0 ≤ v i)
    (hvM : ∀ i ∈ s, v i ≤ M) (hcv : ∀ i ∈ s, c * v i ≤ 1)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ 1)
    (hsum : ∑ i ∈ s, v i = 1) :
    ‖(∏ i ∈ s, z i) - Complex.exp ((-c : ℝ) : ℂ)‖ ≤
      (∑ i ∈ s, ‖z i - ((1 - c * v i : ℝ) : ℂ)‖) + c ^ 2 * M := by
  classical
  let x : ι → ℝ := fun i => c * v i
  have hx0 : ∀ i ∈ s, 0 ≤ x i := fun i hi =>
    mul_nonneg hc (hv0 i hi)
  have hlin : ∀ i ∈ s, ‖((1 - x i : ℝ) : ℂ)‖ ≤ 1 := by
    intro i hi
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hcv i hi))]
    linarith [hx0 i hi]
  have hfirst := norm_finsetProd_sub_finsetProd_le_sum s z
    (fun i => ((1 - x i : ℝ) : ℂ)) hz hlin
  have hsecond := norm_prod_one_sub_sub_exp_neg_sum_le_sum_sq
    s x hx0 hcv
  have hsumx : ∑ i ∈ s, x i = c := by
    simp only [x, ← Finset.mul_sum, hsum, mul_one]
  have hsq : ∑ i ∈ s, (x i) ^ 2 ≤ c ^ 2 * M := by
    calc
      ∑ i ∈ s, (x i) ^ 2 = c ^ 2 * ∑ i ∈ s, (v i) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [x]
        ring
      _ ≤ c ^ 2 * (M * ∑ i ∈ s, v i) := by
        gcongr
        exact sum_sq_le_max_mul_sum s v hv0 hvM
      _ = c ^ 2 * M := by rw [hsum]; ring
  rw [hsumx] at hsecond
  calc
    ‖(∏ i ∈ s, z i) - Complex.exp ((-c : ℝ) : ℂ)‖ ≤
        ‖(∏ i ∈ s, z i) - ∏ i ∈ s, ((1 - x i : ℝ) : ℂ)‖ +
          ‖(∏ i ∈ s, ((1 - x i : ℝ) : ℂ)) -
            Complex.exp ((-c : ℝ) : ℂ)‖ := by
              exact norm_sub_le_norm_sub_add_norm_sub
                (∏ i ∈ s, z i)
                (∏ i ∈ s, ((1 - x i : ℝ) : ℂ))
                (Complex.exp ((-c : ℝ) : ℂ))
    _ ≤ (∑ i ∈ s, ‖z i - ((1 - x i : ℝ) : ℂ)‖) +
          ∑ i ∈ s, (x i) ^ 2 := add_le_add hfirst hsecond
    _ ≤ (∑ i ∈ s, ‖z i - ((1 - c * v i : ℝ) : ℂ)‖) +
          c ^ 2 * M := by
            dsimp [x]
            gcongr

/-- Asymptotic triangular-array form of the finite-product transfer.  The
hypotheses are deliberately stated for varying finite sets, so the theorem
can be applied directly to the primes up to `y n`. -/
theorem tendsto_finsetProd_gaussian
    {ι : Type*} (s : ℕ → Finset ι) (z : ℕ → ι → ℂ)
    (v : ℕ → ι → ℝ) (c : ℝ) (M : ℕ → ℝ)
    (hc : 0 ≤ c)
    (hv0 : ∀ᶠ n in atTop, ∀ i ∈ s n, 0 ≤ v n i)
    (hvM : ∀ᶠ n in atTop, ∀ i ∈ s n, v n i ≤ M n)
    (hcv : ∀ᶠ n in atTop, ∀ i ∈ s n, c * v n i ≤ 1)
    (hz : ∀ᶠ n in atTop, ∀ i ∈ s n, ‖z n i‖ ≤ 1)
    (hsum : ∀ᶠ n in atTop, ∑ i ∈ s n, v n i = 1)
    (herror : Tendsto (fun n =>
      ∑ i ∈ s n,
        ‖z n i - ((1 - c * v n i : ℝ) : ℂ)‖) atTop (nhds 0))
    (hM : Tendsto M atTop (nhds 0)) :
    Tendsto (fun n => ∏ i ∈ s n, z n i) atTop
      (nhds (Complex.exp ((-c : ℝ) : ℂ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
  · filter_upwards [hv0, hvM, hcv, hz, hsum] with n hv0n hvMn hcvn hzn hsumn
    exact norm_prod_sub_gaussian_le (s n) (z n) (v n) c (M n)
      hc hv0n hvMn hcvn hzn hsumn
  · have hscaled : Tendsto (fun n => c ^ 2 * M n) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hM)
    simpa using herror.add hscaled

/-- The share of the total saddle variance contributed by one prime. -/
noncomputable def smoothSaddlePrimeVarianceShare
    (X y p : ℕ) : ℝ :=
  smoothSaddleSecondPrimeTerm p (smoothSaddlePoint X y) /
    smoothSaddlePhiTwo y (smoothSaddlePoint X y)

/-- A prime-local tilted characteristic factor after centering by its exact
prime-local mean and normalizing by the full saddle standard deviation. -/
noncomputable def smoothSaddleCenteredPrimeCharacteristic
    (X y p : ℕ) (t : ℝ) : ℂ :=
  Complex.exp
      ((-(t * smoothSaddlePrimeTerm p (smoothSaddlePoint X y) /
        smoothSaddleStandardDeviation X y) : ℝ) * Complex.I) *
    smoothTiltedPrimeCharacteristic p (smoothSaddlePoint X y)
      (t / smoothSaddleStandardDeviation X y)

/-- The variance shares over the source primes are nonnegative. -/
theorem smoothSaddlePrimeVarianceShare_nonneg
    {X y p : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (hp : 2 ≤ p) :
    0 ≤ smoothSaddlePrimeVarianceShare X y p := by
  exact div_nonneg
    (smoothSaddleSecondPrimeTerm_pos hp
      (smoothSaddlePoint_pos hX hy)).le
    (smoothSaddlePhiTwo_pos hy
      (smoothSaddlePoint_pos hX hy)).le

/-- The prime variance shares sum exactly to one. -/
theorem sum_smoothSaddlePrimeVarianceShare
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        smoothSaddlePrimeVarianceShare X y p = 1 := by
  have hphi : smoothSaddlePhiTwo y (smoothSaddlePoint X y) ≠ 0 :=
    (smoothSaddlePhiTwo_pos hy (smoothSaddlePoint_pos hX hy)).ne'
  unfold smoothSaddlePrimeVarianceShare smoothSaddlePhiTwo
  rw [← Finset.sum_div]
  apply div_self
  simpa only [smoothSaddlePhiTwo] using hphi

/-- Exact factorization of the normalized saddle characteristic function
into its centered prime-local factors. -/
theorem smoothSaddleNormalizedCharacteristic_eq_centeredPrimeProduct
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ) :
    smoothSaddleNormalizedCharacteristic X y t =
      ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        smoothSaddleCenteredPrimeCharacteristic X y p t := by
  let S := (Finset.Icc 2 y).filter Nat.Prime
  have hreal :
      (∑ p ∈ S,
        -(t * smoothSaddlePrimeTerm p (smoothSaddlePoint X y) /
          smoothSaddleStandardDeviation X y)) =
        -(t * Real.log X / smoothSaddleStandardDeviation X y) := by
    calc
      (∑ p ∈ S,
          -(t * smoothSaddlePrimeTerm p (smoothSaddlePoint X y) /
            smoothSaddleStandardDeviation X y)) =
          -(t * (∑ p ∈ S,
            smoothSaddlePrimeTerm p (smoothSaddlePoint X y)) /
              smoothSaddleStandardDeviation X y) := by
                rw [Finset.sum_neg_distrib, Finset.mul_sum,
                  Finset.sum_div]
      _ = -(t * Real.log X / smoothSaddleStandardDeviation X y) := by
        change -(t * smoothSaddlePhiOne y (smoothSaddlePoint X y) /
          smoothSaddleStandardDeviation X y) = _
        rw [smoothSaddlePhiOne_smoothSaddlePoint hX hy]
  have hcomplex :
      (∑ p ∈ S,
        ((-(t * smoothSaddlePrimeTerm p (smoothSaddlePoint X y) /
          smoothSaddleStandardDeviation X y) : ℝ) : ℂ) * Complex.I) =
        ((-(t * Real.log X / smoothSaddleStandardDeviation X y) : ℝ) : ℂ) *
          Complex.I := by
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, hreal]
  rw [smoothSaddleNormalizedCharacteristic_eq_sourcePrimeProduct hX hy]
  unfold smoothSaddleCenteredPrimeCharacteristic
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  rw [hcomplex]

/-- On the half-plane `sigma ≥ 1/2`, one prime contributes at most a fixed
multiple of `log(y)^2` to the saddle curvature. -/
theorem smoothSaddleSecondPrimeTerm_le_twenty_log_sq
    {p y : ℕ} (hp : 2 ≤ p) (hpy : p ≤ y)
    {sigma : ℝ} (hsigma : (1 / 2 : ℝ) ≤ sigma) :
    smoothSaddleSecondPrimeTerm p sigma ≤
      20 * Real.log (y : ℝ) ^ 2 := by
  have hpReal : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpyReal : (p : ℝ) ≤ y := by exact_mod_cast hpy
  have hyTwo : 2 ≤ y := hp.trans hpy
  have hpPos : (0 : ℝ) < p := by positivity
  have hyPos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hlogp0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by linarith)
  have hlogpy : Real.log (p : ℝ) ≤ Real.log (y : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hpPos hyPos hpyReal
  have hlogSq : Real.log (p : ℝ) ^ 2 ≤ Real.log (y : ℝ) ^ 2 := by
    nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ y)]
  let a : ℝ := (p : ℝ) ^ (-sigma)
  have ha0 : 0 ≤ a := Real.rpow_nonneg hpPos.le _
  have hsqrt : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hinvSqrt : (Real.sqrt 2)⁻¹ ≤ (4 / 5 : ℝ) := by
    rw [inv_le_comm₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
      (by norm_num : (0 : ℝ) < 4 / 5)]
    norm_num
    exact hsqrt
  have haHalf : a ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg hsigma)
  have hpHalf : (p : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hpReal (by norm_num)
  have htwoHalf : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (4 / 5 : ℝ) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.sqrt_eq_rpow]
    exact hinvSqrt
  have ha : a ≤ (4 / 5 : ℝ) := haHalf.trans (hpHalf.trans htwoHalf)
  have hden : (1 / 5 : ℝ) ≤ 1 - a := by linarith
  have hdenPos : 0 < 1 - a := lt_of_lt_of_le (by norm_num) hden
  have hdenSq : (1 / 25 : ℝ) ≤ (1 - a) ^ 2 := by nlinarith
  have hnum : a * Real.log (p : ℝ) ^ 2 ≤
      (4 / 5 : ℝ) * Real.log (y : ℝ) ^ 2 := by
    exact mul_le_mul ha hlogSq (sq_nonneg _) (by norm_num)
  rw [← rpow_neg_mul_log_sq_div_one_sub_sq_eq_secondPrimeTerm
    (show 1 < p by omega) (show 0 < sigma by linarith)]
  change a * Real.log (p : ℝ) ^ 2 / (1 - a) ^ 2 ≤ _
  rw [div_le_iff₀ (sq_pos_of_pos hdenPos)]
  calc
    a * Real.log (p : ℝ) ^ 2 ≤
        (4 / 5 : ℝ) * Real.log (y : ℝ) ^ 2 := hnum
    _ ≤ 20 * Real.log (y : ℝ) ^ 2 * (1 - a) ^ 2 := by
      have hlogySq : 0 ≤ Real.log (y : ℝ) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hdenSq
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) hlogySq)]

/-- Every prime variance share is bounded by the normalized maximal-prime
scale `20 log(y)^2 / phiTwo`. -/
theorem smoothSaddlePrimeVarianceShare_le_normalized_log_sq
    {X y p : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigma : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hp : p ∈ (Finset.Icc 2 y).filter Nat.Prime) :
    smoothSaddlePrimeVarianceShare X y p ≤
      20 * Real.log (y : ℝ) ^ 2 /
        smoothSaddlePhiTwo y (smoothSaddlePoint X y) := by
  have hphi := smoothSaddlePhiTwo_pos hy (smoothSaddlePoint_pos hX hy)
  unfold smoothSaddlePrimeVarianceShare
  exact (div_le_div_iff_of_pos_right hphi).2
    (smoothSaddleSecondPrimeTerm_le_twenty_log_sq
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2 hsigma)

/-- The explicit uniform upper bound for all prime variance shares tends to
zero in every critical smooth regime. -/
theorem IsTaoCriticalSmoothRegime.tendsto_maxPrimeVarianceShareBound_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      20 * Real.log (y n : ℝ) ^ 2 /
        smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)))
      atTop (nhds 0) := by
  have htop := hregime.tendsto_normalized_saddle_curvature_atTop hα
  have hinv : Tendsto (fun n =>
      (smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) /
        Real.log (y n : ℝ) ^ 2)⁻¹) atTop (nhds 0) :=
    htop.inv_tendsto_atTop
  have hscaled : Tendsto (fun n => 20 *
      (smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) /
        Real.log (y n : ℝ) ^ 2)⁻¹) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hinv :
      Tendsto (fun n => (20 : ℝ) *
        (smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) /
          Real.log (y n : ℝ) ^ 2)⁻¹) atTop (nhds (20 * 0)))
  apply hscaled.congr'
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  have hphi := smoothSaddlePhiTwo_pos hy (smoothSaddlePoint_pos hX hy)
  have hlog : 0 < Real.log (y n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y n by omega))
  field_simp [hphi.ne', hlog.ne']

/-- Conditional fixed-frequency Gaussian convergence, with every global
triangular-array step discharged.  The sole analytic input left explicit is
the sum of the prime-local quadratic Taylor remainders. -/
theorem IsTaoCriticalSmoothRegime.tendsto_normalizedCharacteristic_gaussian_of_localError
    {X y : ℕ → ℕ} {α t : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (M : ℕ → ℝ)
    (hshare : ∀ᶠ n in atTop,
      ∀ p ∈ (Finset.Icc 2 (y n)).filter Nat.Prime,
        smoothSaddlePrimeVarianceShare (X n) (y n) p ≤ M n)
    (hM : Tendsto M atTop (nhds 0))
    (herror : Tendsto (fun n =>
      ∑ p ∈ (Finset.Icc 2 (y n)).filter Nat.Prime,
        ‖smoothSaddleCenteredPrimeCharacteristic (X n) (y n) p t -
          ((1 - (t ^ 2 / 2) *
            smoothSaddlePrimeVarianceShare (X n) (y n) p : ℝ) : ℂ)‖)
      atTop (nhds 0)) :
    Tendsto (fun n =>
      smoothSaddleNormalizedCharacteristic (X n) (y n) t)
      atTop (nhds (Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ))) := by
  have hX := hregime.eventually_two_le_X
  have hy := hregime.eventually_two_le_y hα
  have hv0 : ∀ᶠ n in atTop,
      ∀ p ∈ (Finset.Icc 2 (y n)).filter Nat.Prime,
        0 ≤ smoothSaddlePrimeVarianceShare (X n) (y n) p := by
    filter_upwards [hX, hy] with n hXn hyn
    intro p hp
    exact smoothSaddlePrimeVarianceShare_nonneg hXn hyn
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hsum : ∀ᶠ n in atTop,
      ∑ p ∈ (Finset.Icc 2 (y n)).filter Nat.Prime,
        smoothSaddlePrimeVarianceShare (X n) (y n) p = 1 := by
    filter_upwards [hX, hy] with n hXn hyn
    exact sum_smoothSaddlePrimeVarianceShare hXn hyn
  have hz : ∀ᶠ n in atTop,
      ∀ p ∈ (Finset.Icc 2 (y n)).filter Nat.Prime,
        ‖smoothSaddleCenteredPrimeCharacteristic (X n) (y n) p t‖ ≤ 1 := by
    filter_upwards [hX, hy] with n hXn hyn
    intro p hp
    unfold smoothSaddleCenteredPrimeCharacteristic
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact norm_smoothTiltedPrimeCharacteristic_le_one
      (Finset.mem_filter.mp hp).2.one_lt
      (smoothSaddlePoint_pos hXn hyn) _
  have hcv : ∀ᶠ n in atTop,
      ∀ p ∈ (Finset.Icc 2 (y n)).filter Nat.Prime,
        (t ^ 2 / 2) *
          smoothSaddlePrimeVarianceShare (X n) (y n) p ≤ 1 := by
    have hscaled : Tendsto (fun n => (t ^ 2 / 2) * M n)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hM
    have hevent := (tendsto_order.1 hscaled).2 1 (by norm_num)
    filter_upwards [hevent, hshare, hv0] with n hn hsharen hv0n
    intro p hp
    have hc : 0 ≤ t ^ 2 / 2 := by positivity
    exact (mul_le_mul_of_nonneg_left (hsharen p hp) hc).trans hn.le
  have hprod := tendsto_finsetProd_gaussian
    (fun n => (Finset.Icc 2 (y n)).filter Nat.Prime)
    (fun n p => smoothSaddleCenteredPrimeCharacteristic (X n) (y n) p t)
    (fun n p => smoothSaddlePrimeVarianceShare (X n) (y n) p)
    (t ^ 2 / 2) M (by positivity) hv0 hshare hcv hz hsum herror hM
  apply hprod.congr'
  filter_upwards [hX, hy] with n hXn hyn
  exact (smoothSaddleNormalizedCharacteristic_eq_centeredPrimeProduct
    hXn hyn t).symm

/-- Fixed-frequency Gaussian convergence reduced solely to the summed
prime-local Taylor remainder.  Curvature growth supplies the infinitesimal
variance-share condition automatically. -/
theorem IsTaoCriticalSmoothRegime.tendsto_normalizedCharacteristic_gaussian_of_primeLocalError
    {X y : ℕ → ℕ} {α t : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (herror : Tendsto (fun n =>
      ∑ p ∈ (Finset.Icc 2 (y n)).filter Nat.Prime,
        ‖smoothSaddleCenteredPrimeCharacteristic (X n) (y n) p t -
          ((1 - (t ^ 2 / 2) *
            smoothSaddlePrimeVarianceShare (X n) (y n) p : ℝ) : ℂ)‖)
      atTop (nhds 0)) :
    Tendsto (fun n =>
      smoothSaddleNormalizedCharacteristic (X n) (y n) t)
      atTop (nhds (Complex.exp ((-(t ^ 2 / 2) : ℝ) : ℂ))) := by
  let M : ℕ → ℝ := fun n =>
    20 * Real.log (y n : ℝ) ^ 2 /
      smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n))
  have hM : Tendsto M atTop (nhds 0) := by
    simpa only [M] using
      hregime.tendsto_maxPrimeVarianceShareBound_zero hα
  have hsigma : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ smoothSaddlePoint (X n) (y n) :=
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hshare : ∀ᶠ n in atTop,
      ∀ p ∈ (Finset.Icc 2 (y n)).filter Nat.Prime,
        smoothSaddlePrimeVarianceShare (X n) (y n) p ≤ M n := by
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα, hsigma] with n hX hy hs
    intro p hp
    exact smoothSaddlePrimeVarianceShare_le_normalized_log_sq
      hX hy hs hp
  exact hregime.tendsto_normalizedCharacteristic_gaussian_of_localError
    hα M hshare hM herror

end

end Tao2026
