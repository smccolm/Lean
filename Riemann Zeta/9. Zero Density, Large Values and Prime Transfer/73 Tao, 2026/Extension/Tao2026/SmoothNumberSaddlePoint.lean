import Tao2026.SmoothNumberRankin
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The exact smooth-number saddle point

This file introduces the genuine saddle parameter used in the
Hildebrand--Tenenbaum/Granville smooth-number asymptotic.  Unlike the elementary
Rankin proxy `smoothRankinSigma`, it is the unique positive solution of

`sum_{p <= y} log p / (p^sigma - 1) = log X`.

The construction below is unconditional: the finite prime sum is continuous
and strictly decreasing, with endpoint limits `+infinity` and `0`.  The second
saddle sum is also defined exactly and identified as the negative derivative
of the first.
-/

open Filter Topology

namespace Tao2026

noncomputable section

/-- A single summand in the first logarithmic derivative of the finite smooth
Euler product. -/
noncomputable def smoothSaddlePrimeTerm (p : ℕ) (sigma : ℝ) : ℝ :=
  Real.log p / ((p : ℝ) ^ sigma - 1)

/-- A single summand in the positive second logarithmic derivative of the
finite smooth Euler product. -/
noncomputable def smoothSaddleSecondPrimeTerm (p : ℕ) (sigma : ℝ) : ℝ :=
  (Real.log p) ^ 2 * (p : ℝ) ^ sigma /
    (((p : ℝ) ^ sigma - 1) ^ 2)

/-- The first saddle sum `sum_{p <= y} log p / (p^sigma - 1)`. -/
noncomputable def smoothSaddlePhiOne (y : ℕ) (sigma : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
    smoothSaddlePrimeTerm p sigma

/-- The positive second saddle sum
`sum_{p <= y} (log p)^2 p^sigma / (p^sigma - 1)^2`. -/
noncomputable def smoothSaddlePhiTwo (y : ℕ) (sigma : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
    smoothSaddleSecondPrimeTerm p sigma

/-- Every prime denominator in the saddle equation is positive on the
positive real axis. -/
theorem smoothSaddle_denominator_pos {p : ℕ} (hp : 2 ≤ p)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < (p : ℝ) ^ sigma - 1 := by
  rw [sub_pos]
  exact Real.one_lt_rpow
    (by exact_mod_cast (show 1 < p by omega)) hsigma

/-- Each summand of the first saddle sum is positive. -/
theorem smoothSaddlePrimeTerm_pos {p : ℕ} (hp : 2 ≤ p)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < smoothSaddlePrimeTerm p sigma := by
  exact div_pos
    (Real.log_pos (by exact_mod_cast (show 1 < p by omega)))
    (smoothSaddle_denominator_pos hp hsigma)

/-- Each summand of the second saddle sum is positive. -/
theorem smoothSaddleSecondPrimeTerm_pos {p : ℕ} (hp : 2 ≤ p)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < smoothSaddleSecondPrimeTerm p sigma := by
  unfold smoothSaddleSecondPrimeTerm
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast (show 1 < p by omega)
  exact div_pos
    (mul_pos (sq_pos_of_pos (Real.log_pos hp1))
      (Real.rpow_pos_of_pos (by positivity) _))
    (sq_pos_of_pos (smoothSaddle_denominator_pos hp hsigma))

/-- A single first-saddle summand is strictly decreasing on the positive
axis. -/
theorem smoothSaddlePrimeTerm_strictAntiOn {p : ℕ} (hp : 2 ≤ p) :
    StrictAntiOn (smoothSaddlePrimeTerm p) (Set.Ioi 0) := by
  intro a ha b hb hab
  unfold smoothSaddlePrimeTerm
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast (show 1 < p by omega)
  have hrpow : (p : ℝ) ^ a < (p : ℝ) ^ b :=
    Real.rpow_lt_rpow_of_exponent_lt hp1 hab
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  exact (div_lt_div_iff_of_pos_left hlog
    (smoothSaddle_denominator_pos hp hb)
    (smoothSaddle_denominator_pos hp ha)).2
      (sub_lt_sub_right hrpow 1)

/-- A single first-saddle summand is continuous on the positive axis. -/
theorem continuousOn_smoothSaddlePrimeTerm {p : ℕ} (hp : 2 ≤ p) :
    ContinuousOn (smoothSaddlePrimeTerm p) (Set.Ioi 0) := by
  exact continuousOn_const.div
    ((Real.continuous_const_rpow
      (by positivity : (p : ℝ) ≠ 0)).continuousOn.sub continuousOn_const)
    (fun sigma hsigma =>
      (smoothSaddle_denominator_pos hp hsigma).ne')

/-- The derivative of a first-saddle summand is the negative corresponding
second-saddle summand. -/
theorem hasDerivAt_smoothSaddlePrimeTerm {p : ℕ} (hp : 2 ≤ p)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    HasDerivAt (smoothSaddlePrimeTerm p)
      (-smoothSaddleSecondPrimeTerm p sigma) sigma := by
  unfold smoothSaddlePrimeTerm smoothSaddleSecondPrimeTerm
  convert (hasDerivAt_const sigma (Real.log (p : ℝ))).div
    (((hasDerivAt_id sigma).const_rpow
      (by positivity : (0 : ℝ) < p)).sub_const 1)
    (smoothSaddle_denominator_pos hp hsigma).ne' using 1
  simp only [id_eq]
  ring

/-- Every first-saddle summand vanishes as the parameter tends to infinity. -/
theorem tendsto_smoothSaddlePrimeTerm_atTop {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (smoothSaddlePrimeTerm p) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast (show 1 < p by omega)
  have hpow : Tendsto (fun sigma : ℝ => (p : ℝ) ^ sigma)
      atTop atTop := by
    rw [show (fun sigma : ℝ => (p : ℝ) ^ sigma) =
      fun sigma => Real.exp (Real.log p * sigma) by
        funext sigma
        exact Real.rpow_def_of_pos (by positivity) sigma]
    exact Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (Real.log_pos hp1))
  have hdenominator :
      Tendsto (fun sigma : ℝ => (p : ℝ) ^ sigma - 1) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro B
    filter_upwards [hpow.eventually_ge_atTop (B + 1)] with sigma hsigma
    linarith
  simpa [smoothSaddlePrimeTerm] using
    tendsto_const_nhds.div_atTop hdenominator

/-- Every first-saddle summand diverges to infinity as the parameter tends to
zero through positive values. -/
theorem tendsto_smoothSaddlePrimeTerm_nhdsGT_zero {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (smoothSaddlePrimeTerm p) (𝓝[>] (0 : ℝ)) atTop := by
  have hpow : Tendsto (fun sigma : ℝ => (p : ℝ) ^ sigma)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (Real.continuous_const_rpow
      (by positivity : (p : ℝ) ≠ 0)).tendsto 0
    simpa using h.mono_left inf_le_left
  have hdenominatorNhds :
      Tendsto (fun sigma : ℝ => (p : ℝ) ^ sigma - 1)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hpow.sub_const 1
  have hdenominator :
      Tendsto (fun sigma : ℝ => (p : ℝ) ^ sigma - 1)
        (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hdenominatorNhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact smoothSaddle_denominator_pos hp hsigma
  have hinverse := hdenominator.inv_tendsto_nhdsGT_zero
  simpa [smoothSaddlePrimeTerm, div_eq_mul_inv] using
    hinverse.const_mul_atTop
      (Real.log_pos (by exact_mod_cast (show 1 < p by omega)))

/-- For `y >= 2`, the full first saddle sum is strictly decreasing on the
positive axis.  The prime `2` guarantees that the finite prime set is
nonempty. -/
theorem smoothSaddlePhiOne_strictAntiOn {y : ℕ} (hy : 2 ≤ y) :
    StrictAntiOn (smoothSaddlePhiOne y) (Set.Ioi 0) := by
  intro a ha b hb hab
  unfold smoothSaddlePhiOne
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨2, by simp [hy, Nat.prime_two]⟩
  · intro p hp
    have hp2 : 2 ≤ p :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    exact smoothSaddlePrimeTerm_strictAntiOn hp2 ha hb hab

/-- The full first saddle sum is continuous on the positive axis. -/
theorem continuousOn_smoothSaddlePhiOne (y : ℕ) :
    ContinuousOn (smoothSaddlePhiOne y) (Set.Ioi 0) := by
  unfold smoothSaddlePhiOne
  apply continuousOn_finsetSum
  intro p hp
  exact continuousOn_smoothSaddlePrimeTerm
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1

/-- The second saddle sum is strictly positive for `y >= 2` and positive
parameter. -/
theorem smoothSaddlePhiTwo_pos {y : ℕ} (hy : 2 ≤ y)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < smoothSaddlePhiTwo y sigma := by
  unfold smoothSaddlePhiTwo
  have hle : smoothSaddleSecondPrimeTerm 2 sigma ≤
      Finset.sum ((Finset.Icc 2 y).filter Nat.Prime)
        (fun p => smoothSaddleSecondPrimeTerm p sigma) :=
    Finset.single_le_sum
      (fun p hp => (smoothSaddleSecondPrimeTerm_pos
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1 hsigma).le)
      (by simp [hy, Nat.prime_two] :
        2 ∈ (Finset.Icc 2 y).filter Nat.Prime)
  exact (smoothSaddleSecondPrimeTerm_pos (by omega) hsigma).trans_le hle

/-- The derivative of the first saddle sum is the negative second saddle
sum. -/
theorem hasDerivAt_smoothSaddlePhiOne (y : ℕ)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    HasDerivAt (smoothSaddlePhiOne y) (-smoothSaddlePhiTwo y sigma) sigma := by
  unfold smoothSaddlePhiOne smoothSaddlePhiTwo
  convert HasDerivAt.fun_sum (u := (Finset.Icc 2 y).filter Nat.Prime)
    (fun p hp => hasDerivAt_smoothSaddlePrimeTerm
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1 hsigma) using 1
  rw [Finset.sum_neg_distrib]

/-- Exact finite mean-value identity for the first and second saddle sums. -/
theorem exists_smoothSaddlePhiTwo_secant (y : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ∃ xi ∈ Set.Ioo a b,
      smoothSaddlePhiOne y a - smoothSaddlePhiOne y b =
        smoothSaddlePhiTwo y xi * (b - a) := by
  have hcontinuous :
      ContinuousOn (smoothSaddlePhiOne y) (Set.Icc a b) :=
    fun x hx =>
      (hasDerivAt_smoothSaddlePhiOne y (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  obtain ⟨xi, hxi, hderiv⟩ := exists_hasDerivAt_eq_slope
    (smoothSaddlePhiOne y) (fun x => -smoothSaddlePhiTwo y x)
    hab hcontinuous
    (fun x hx => hasDerivAt_smoothSaddlePhiOne y (ha.trans hx.1))
  refine ⟨xi, hxi, ?_⟩
  rw [eq_div_iff (sub_ne_zero.mpr hab.ne')] at hderiv
  linarith

/-- Pointwise derivative form of the exact saddle identity. -/
theorem deriv_smoothSaddlePhiOne (y : ℕ) {sigma : ℝ}
    (hsigma : 0 < sigma) :
    deriv (smoothSaddlePhiOne y) sigma = -smoothSaddlePhiTwo y sigma :=
  (hasDerivAt_smoothSaddlePhiOne y hsigma).deriv

/-- The full first saddle sum vanishes at infinity. -/
theorem tendsto_smoothSaddlePhiOne_atTop (y : ℕ) :
    Tendsto (smoothSaddlePhiOne y) atTop (𝓝 0) := by
  unfold smoothSaddlePhiOne
  simpa using tendsto_finsetSum ((Finset.Icc 2 y).filter Nat.Prime)
    (fun p hp => tendsto_smoothSaddlePrimeTerm_atTop
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1)

/-- For `y >= 2`, the full first saddle sum diverges to infinity at the
positive-side origin. -/
theorem tendsto_smoothSaddlePhiOne_nhdsGT_zero {y : ℕ} (hy : 2 ≤ y) :
    Tendsto (smoothSaddlePhiOne y) (𝓝[>] (0 : ℝ)) atTop := by
  refine Filter.tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) ?_
    (tendsto_smoothSaddlePrimeTerm_nhdsGT_zero (p := 2) (by omega))
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  unfold smoothSaddlePhiOne
  change smoothSaddlePrimeTerm 2 sigma ≤
    Finset.sum ((Finset.Icc 2 y).filter Nat.Prime)
      (fun p => smoothSaddlePrimeTerm p sigma)
  exact Finset.single_le_sum
    (fun p hp => (smoothSaddlePrimeTerm_pos
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1 hsigma).le)
    (by simp [hy, Nat.prime_two] :
      2 ∈ (Finset.Icc 2 y).filter Nat.Prime)

/-- The exact smooth-number saddle equation has a positive solution whenever
`X,y >= 2`. -/
theorem exists_smoothSaddlePhiOne_eq_log {X y : ℕ}
    (hX : 2 ≤ X) (hy : 2 ≤ y) :
    ∃ sigma : ℝ, 0 < sigma ∧
      smoothSaddlePhiOne y sigma = Real.log X := by
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hleft :=
    (tendsto_smoothSaddlePhiOne_nhdsGT_zero hy).eventually_gt_atTop
      (Real.log X)
  have hleft' : ∀ᶠ sigma : ℝ in 𝓝[>] 0,
      0 < sigma ∧ Real.log X < smoothSaddlePhiOne y sigma := by
    filter_upwards [self_mem_nhdsWithin, hleft] with sigma hsigma hvalue
    exact ⟨hsigma, hvalue⟩
  obtain ⟨a, ha0, haValue⟩ := hleft'.exists
  have hright : ∀ᶠ sigma : ℝ in atTop,
      smoothSaddlePhiOne y sigma < Real.log X :=
    (tendsto_smoothSaddlePhiOne_atTop y).eventually
      (Iio_mem_nhds hlogX)
  have hright' : ∀ᶠ sigma : ℝ in atTop,
      a ≤ sigma ∧ smoothSaddlePhiOne y sigma < Real.log X := by
    filter_upwards [eventually_ge_atTop a, hright] with sigma has hvalue
    exact ⟨has, hvalue⟩
  obtain ⟨b, hab, hbValue⟩ := hright'.exists
  have hcontinuous :
      ContinuousOn (smoothSaddlePhiOne y) (Set.Icc a b) :=
    (continuousOn_smoothSaddlePhiOne y).mono
      (fun sigma hsigma => ha0.trans_le hsigma.1)
  have hmem : Real.log X ∈
      Set.Icc (smoothSaddlePhiOne y b) (smoothSaddlePhiOne y a) :=
    ⟨hbValue.le, haValue.le⟩
  obtain ⟨sigma, hsigma, heq⟩ :=
    intermediate_value_Icc' hab hcontinuous hmem
  exact ⟨sigma, ha0.trans_le hsigma.1, heq⟩

/-- Positive solutions to a fixed saddle equation are unique. -/
theorem smoothSaddlePhiOne_eq_unique {y : ℕ} (hy : 2 ≤ y)
    {sigma tau L : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau)
    (hsigmaEq : smoothSaddlePhiOne y sigma = L)
    (htauEq : smoothSaddlePhiOne y tau = L) :
    sigma = tau := by
  exact (smoothSaddlePhiOne_strictAntiOn hy).injOn hsigma htau
    (hsigmaEq.trans htauEq.symm)

/-- The exact saddle parameter.  Outside the source-relevant range
`X,y >= 2`, it is assigned the harmless default value `1`. -/
noncomputable def smoothSaddlePoint (X y : ℕ) : ℝ :=
  if h : 2 ≤ X ∧ 2 ≤ y then
    Classical.choose (exists_smoothSaddlePhiOne_eq_log h.1 h.2)
  else 1

/-- The exact saddle parameter is positive in its defining range. -/
theorem smoothSaddlePoint_pos {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    0 < smoothSaddlePoint X y := by
  rw [smoothSaddlePoint, dif_pos ⟨hX, hy⟩]
  exact (Classical.choose_spec
    (exists_smoothSaddlePhiOne_eq_log hX hy)).1

/-- The chosen saddle parameter satisfies the exact finite prime equation. -/
theorem smoothSaddlePhiOne_smoothSaddlePoint {X y : ℕ}
    (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddlePhiOne y (smoothSaddlePoint X y) = Real.log X := by
  rw [smoothSaddlePoint, dif_pos ⟨hX, hy⟩]
  exact (Classical.choose_spec
    (exists_smoothSaddlePhiOne_eq_log hX hy)).2

/-- Any positive solution of the finite prime equation is the chosen exact
saddle parameter. -/
theorem eq_smoothSaddlePoint_of_pos_of_phiOne_eq {X y : ℕ}
    (hX : 2 ≤ X) (hy : 2 ≤ y) {sigma : ℝ}
    (hsigma : 0 < sigma)
    (heq : smoothSaddlePhiOne y sigma = Real.log X) :
    sigma = smoothSaddlePoint X y :=
  smoothSaddlePhiOne_eq_unique hy hsigma
    (smoothSaddlePoint_pos hX hy) heq
    (smoothSaddlePhiOne_smoothSaddlePoint hX hy)

/-- For fixed `y`, the exact saddle parameter strictly decreases as the
ambient cutoff increases. -/
theorem smoothSaddlePoint_strictAnti_left {X₁ X₂ y : ℕ}
    (hX₁ : 2 ≤ X₁) (hX : X₁ < X₂) (hy : 2 ≤ y) :
    smoothSaddlePoint X₂ y < smoothSaddlePoint X₁ y := by
  have hX₂ : 2 ≤ X₂ := hX₁.trans hX.le
  have hlog : Real.log (X₁ : ℝ) < Real.log (X₂ : ℝ) :=
    Real.strictMonoOn_log
      (show 0 < (X₁ : ℝ) by
        exact_mod_cast (show 0 < X₁ by omega))
      (show 0 < (X₂ : ℝ) by
        exact_mod_cast (show 0 < X₂ by omega))
      (by exact_mod_cast hX)
  apply lt_of_not_ge
  intro hsaddles
  have hphi := (smoothSaddlePhiOne_strictAntiOn hy).antitoneOn
    (smoothSaddlePoint_pos hX₁ hy) (smoothSaddlePoint_pos hX₂ hy)
    hsaddles
  rw [smoothSaddlePhiOne_smoothSaddlePoint hX₁ hy,
    smoothSaddlePhiOne_smoothSaddlePoint hX₂ hy] at hphi
  exact (not_le_of_gt hlog) hphi

/-- Exact sensitivity identity for saddle points at two ambient cutoffs.  It
is the finite mean-value bridge used to control the change in the saddle under
fixed multiplicative dilation. -/
theorem exists_smoothSaddlePoint_secant {X₁ X₂ y : ℕ}
    (hX₁ : 2 ≤ X₁) (hX : X₁ < X₂) (hy : 2 ≤ y) :
    ∃ xi ∈ Set.Ioo (smoothSaddlePoint X₂ y) (smoothSaddlePoint X₁ y),
      Real.log X₂ - Real.log X₁ =
        smoothSaddlePhiTwo y xi *
          (smoothSaddlePoint X₁ y - smoothSaddlePoint X₂ y) := by
  have hX₂ : 2 ≤ X₂ := hX₁.trans hX.le
  obtain ⟨xi, hxi, hsecant⟩ := exists_smoothSaddlePhiTwo_secant y
    (smoothSaddlePoint_pos hX₂ hy)
    (smoothSaddlePoint_strictAnti_left hX₁ hX hy)
  refine ⟨xi, hxi, ?_⟩
  simpa [smoothSaddlePhiOne_smoothSaddlePoint hX₂ hy,
    smoothSaddlePhiOne_smoothSaddlePoint hX₁ hy] using hsecant

end

end Tao2026
