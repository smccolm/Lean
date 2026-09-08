import RiemannZeta.External.PNT.ZetaAppendix

open Complex Finset Set Filter Topology
open scoped BigOperators FourierTransform

namespace RiemannZeta.GuthMaynard

/-!
# Medium-length zeta reflection

This module exposes the exact Poisson identity underlying the medium-block
van der Corput B-transform.  The remaining analytic step is the uniform
stationary-phase evaluation of the cosine integrals in the dual range.
-/

/-- Compactly supported power weight used in the Poisson transform of a
finite partial-zeta block. -/
noncomputable def partialZetaPoissonWeight
    (a b : ℝ) (s : ℂ) (y : ℝ) : ℂ :=
  if a ≤ y ∧ y ≤ b then
    (y ^ (-s.re) : ℝ) *
      Complex.exp (2 * Real.pi * I *
        ((-(s.im / (2 * Real.pi)) * Real.log y : ℝ) : ℂ))
  else 0

/-- The logarithmic phase appearing in the positive-frequency Fourier
integrals. -/
noncomputable def reflectionPhase (t m x : ℝ) : ℝ :=
  m * x - (t / (2 * Real.pi)) * Real.log x

/-- The unique positive stationary point of `reflectionPhase` when `t,m>0`. -/
noncomputable def reflectionStationaryPoint (t m : ℝ) : ℝ :=
  t / (2 * Real.pi * m)

/-- Universal phase obtained after rescaling a logarithmic stationary point
to `1`. -/
noncomputable def stationaryNormalPhase (z : ℝ) : ℝ :=
  z - 1 - Real.log z

/-- The positive-frequency oscillatory integrand in a reflected zeta block. -/
noncomputable def reflectionOscillatoryIntegrand
    (s : ℂ) (m y : ℝ) : ℂ :=
  (y : ℂ) ^ (-s) *
    Complex.exp (2 * Real.pi * I * ((m * y : ℝ) : ℂ))

theorem hasDerivAt_reflectionPhase
    (t m x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (reflectionPhase t m)
      (m - t / (2 * Real.pi * x)) x := by
  have hLinear : HasDerivAt (fun y : ℝ => m * y) m x := by
    simpa using (hasDerivAt_id x).const_mul m
  have hLog : HasDerivAt
      (fun y : ℝ => (t / (2 * Real.pi)) * Real.log y)
      ((t / (2 * Real.pi)) * x⁻¹) x :=
    (Real.hasDerivAt_log hx).const_mul (t / (2 * Real.pi))
  have hSub := hLinear.sub hLog
  change HasDerivAt
    (fun y : ℝ => m * y - (t / (2 * Real.pi)) * Real.log y)
    (m - t / (2 * Real.pi * x)) x
  convert hSub using 1
  field_simp [Real.pi_ne_zero, hx]

theorem deriv_reflectionPhase
    (t m x : ℝ) (hx : x ≠ 0) :
    deriv (reflectionPhase t m) x = m - t / (2 * Real.pi * x) :=
  (hasDerivAt_reflectionPhase t m x hx).deriv

/-- The curvature of the logarithmic reflection phase. -/
theorem hasDerivAt_deriv_reflectionPhase
    (t m x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (deriv (reflectionPhase t m))
      (t / (2 * Real.pi * x ^ 2)) x := by
  have hFormula : ∀ᶠ y in 𝓝 x,
      deriv (reflectionPhase t m) y = m - t / (2 * Real.pi * y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact deriv_reflectionPhase t m y hy
  have hScaled : HasDerivAt
      (fun y : ℝ => m - (t / (2 * Real.pi)) * y⁻¹)
      (t / (2 * Real.pi * x ^ 2)) x := by
    convert ((hasDerivAt_inv hx).const_mul
      (t / (2 * Real.pi))).const_sub m using 1
    all_goals field_simp [Real.pi_ne_zero, hx]
  apply HasDerivAt.congr_of_eventuallyEq hScaled
  · filter_upwards [hFormula] with y hy
    rw [hy]
    field_simp [Real.pi_ne_zero]

theorem secondDeriv_reflectionPhase
    (t m x : ℝ) (hx : x ≠ 0) :
    deriv (deriv (reflectionPhase t m)) x =
      t / (2 * Real.pi * x ^ 2) :=
  (hasDerivAt_deriv_reflectionPhase t m x hx).deriv

theorem reflectionStationaryPoint_pos
    {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    0 < reflectionStationaryPoint t m := by
  unfold reflectionStationaryPoint
  positivity

theorem deriv_reflectionPhase_stationary
    {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    deriv (reflectionPhase t m) (reflectionStationaryPoint t m) = 0 := by
  rw [deriv_reflectionPhase]
  · unfold reflectionStationaryPoint
    field_simp
    ring
  · exact (reflectionStationaryPoint_pos ht hm).ne'

/-- Left of the stationary point the reflection phase has negative slope. -/
theorem deriv_reflectionPhase_neg_of_lt_stationary
    {t m x : ℝ} (hm : 0 < m) (hx : 0 < x)
    (hxm : x < reflectionStationaryPoint t m) :
    deriv (reflectionPhase t m) x < 0 := by
  rw [deriv_reflectionPhase t m x hx.ne']
  unfold reflectionStationaryPoint at hxm
  have hTwoPi : 0 < 2 * Real.pi := by positivity
  have hScaled := (lt_div_iff₀ (mul_pos hTwoPi hm)).mp hxm
  rw [sub_neg]
  apply (lt_div_iff₀ (mul_pos hTwoPi hx)).2
  nlinarith

/-- Right of the stationary point the reflection phase has positive slope. -/
theorem deriv_reflectionPhase_pos_of_stationary_lt
    {t m x : ℝ} (hm : 0 < m) (hx : 0 < x)
    (hmx : reflectionStationaryPoint t m < x) :
    0 < deriv (reflectionPhase t m) x := by
  rw [deriv_reflectionPhase t m x hx.ne']
  unfold reflectionStationaryPoint at hmx
  have hTwoPi : 0 < 2 * Real.pi := by positivity
  have hScaled := (div_lt_iff₀ (mul_pos hTwoPi hm)).mp hmx
  rw [sub_pos]
  apply (div_lt_iff₀ (mul_pos hTwoPi hx)).2
  nlinarith

/-- A negative Fourier frequency has no stationary point on the positive
axis when the height is positive. -/
theorem deriv_reflectionPhase_neg_frequency_neg
    {t m x : ℝ} (ht : 0 < t) (hm : 0 < m) (hx : 0 < x) :
    deriv (reflectionPhase t (-m)) x < 0 := by
  rw [deriv_reflectionPhase t (-m) x hx.ne']
  have : 0 < t / (2 * Real.pi * x) := by positivity
  linarith

/-- For positive height the logarithmic reflection phase is strictly convex
away from the origin. -/
theorem secondDeriv_reflectionPhase_pos
    {t m x : ℝ} (ht : 0 < t) (hx : x ≠ 0) :
    0 < deriv (deriv (reflectionPhase t m)) x := by
  rw [secondDeriv_reflectionPhase t m x hx]
  positivity

/-- Exact value of the logarithmic phase at its positive stationary point. -/
theorem reflectionPhase_stationary_value
    {t m : ℝ} (hm : 0 < m) :
    reflectionPhase t m (reflectionStationaryPoint t m) =
      (t / (2 * Real.pi)) *
        (1 - Real.log (reflectionStationaryPoint t m)) := by
  unfold reflectionPhase reflectionStationaryPoint
  field_simp [Real.pi_ne_zero, hm.ne']

/-- Exact normalization of the phase around its stationary point.  All
dependence on the Fourier frequency moves into the spatial scale, while the
phase difference becomes `(t/2π) * (z - 1 - log z)`. -/
theorem reflectionPhase_stationary_rescale
    {t m z : ℝ} (ht : 0 < t) (hm : 0 < m) (hz : 0 < z) :
    reflectionPhase t m (reflectionStationaryPoint t m * z) -
        reflectionPhase t m (reflectionStationaryPoint t m) =
      (t / (2 * Real.pi)) * stationaryNormalPhase z := by
  have hx0 : 0 < reflectionStationaryPoint t m :=
    reflectionStationaryPoint_pos ht hm
  rw [reflectionPhase_stationary_value hm]
  unfold reflectionPhase stationaryNormalPhase
  rw [Real.log_mul hx0.ne' hz.ne']
  unfold reflectionStationaryPoint
  field_simp [Real.pi_ne_zero, hm.ne']
  ring

/-- Exact change of scale from a physical zeta block to coordinates centered
at the logarithmic stationary point.  This is the measure-theoretic
rescaling required before the uniform stationary-phase estimate is applied. -/
theorem reflectionOscillatoryIntegral_stationary_rescale
    {s : ℂ} {m a b : ℝ} (ht : 0 < s.im) (hm : 0 < m) :
    (∫ y in a..b, reflectionOscillatoryIntegrand s m y) =
      (reflectionStationaryPoint s.im m : ℂ) *
        ∫ z in a / reflectionStationaryPoint s.im m..
            b / reflectionStationaryPoint s.im m,
          reflectionOscillatoryIntegrand s m
            (reflectionStationaryPoint s.im m * z) := by
  let x₀ := reflectionStationaryPoint s.im m
  have hx₀ : 0 < x₀ := reflectionStationaryPoint_pos ht hm
  have hChange := intervalIntegral.smul_integral_comp_mul_left
    (f := reflectionOscillatoryIntegrand s m)
    (a := a / x₀) (b := b / x₀) x₀
  rw [Complex.real_smul] at hChange
  have ha : x₀ * (a / x₀) = a := by field_simp [hx₀.ne']
  have hb : x₀ * (b / x₀) = b := by field_simp [hx₀.ne']
  rw [ha, hb] at hChange
  simpa only [x₀] using hChange.symm

theorem hasDerivAt_stationaryNormalPhase
    {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt stationaryNormalPhase (1 - z⁻¹) z := by
  unfold stationaryNormalPhase
  convert ((hasDerivAt_id z).sub_const 1).sub (Real.hasDerivAt_log hz) using 1

theorem hasDerivAt_deriv_stationaryNormalPhase
    {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt (deriv stationaryNormalPhase) (z⁻¹ ^ 2) z := by
  have hFormula : ∀ᶠ y in 𝓝 z,
      deriv stationaryNormalPhase y = 1 - y⁻¹ := by
    filter_upwards [eventually_ne_nhds hz] with y hy
    exact (hasDerivAt_stationaryNormalPhase hy).deriv
  have hBase : HasDerivAt (fun y : ℝ => 1 - y⁻¹) (z⁻¹ ^ 2) z := by
    convert (hasDerivAt_inv hz).const_sub 1 using 1
    ring
  apply HasDerivAt.congr_of_eventuallyEq hBase
  filter_upwards [hFormula] with y hy
  exact hy

/-- The normalized phase is nonnegative on the positive axis and vanishes at
the stationary point `z=1`. -/
theorem stationaryNormalPhase_nonneg {z : ℝ} (hz : 0 < z) :
    0 ≤ stationaryNormalPhase z := by
  unfold stationaryNormalPhase
  linarith [Real.log_le_sub_one_of_pos hz]

/-- A rational quadratic upper bound for the normalized logarithmic phase. -/
theorem stationaryNormalPhase_le_sq_div {z : ℝ} (hz : 0 < z) :
    stationaryNormalPhase z ≤ (z - 1) ^ 2 / z := by
  have hlog := Real.one_sub_inv_le_log_of_pos hz
  unfold stationaryNormalPhase
  calc
    z - 1 - Real.log z ≤ z - 1 - (1 - z⁻¹) := by linarith
    _ = (z - 1) ^ 2 / z := by
      field_simp [hz.ne']

/-- On the standard rescaled dyadic range, the normalized phase has a
uniform quadratic upper bound. -/
theorem stationaryNormalPhase_le_two_mul_sq
    {z : ℝ} (hzLower : 1 / 2 ≤ z) :
    stationaryNormalPhase z ≤ 2 * (z - 1) ^ 2 := by
  have hz : 0 < z := by linarith
  refine (stationaryNormalPhase_le_sq_div hz).trans ?_
  rw [div_le_iff₀ hz]
  nlinarith [sq_nonneg (z - 1)]

/-- Uniform quadratic lower bound for the normalized phase on `[1/2,2]`.
Together with `stationaryNormalPhase_le_two_mul_sq`, this supplies the local
quadratic comparability required for stationary localization. -/
theorem stationaryNormalPhase_sq_div_eight_le
    {z : ℝ} (hzLower : 1 / 2 ≤ z) (hzUpper : z ≤ 2) :
    (z - 1) ^ 2 / 8 ≤ stationaryNormalPhase z := by
  let g : ℝ → ℝ := fun x => stationaryNormalPhase x - (x - 1) ^ 2 / 8
  have hgDeriv : ∀ x : ℝ, 0 < x →
      HasDerivAt g ((x - 1) * (4 - x) / (4 * x)) x := by
    intro x hx
    dsimp only [g]
    have hQuad := (((hasDerivAt_id x).sub_const 1).pow 2).div_const 8
    have hQuad' : HasDerivAt (fun y : ℝ => (y - 1) ^ 2 / 8)
        ((x - 1) / 4) x := by
      convert hQuad using 1
      norm_num [id_eq]
      ring
    convert (hasDerivAt_stationaryNormalPhase hx.ne').sub hQuad' using 1
    field_simp [hx.ne']
  have hgOne : g 1 = 0 := by simp [g, stationaryNormalPhase]
  by_cases hzOne : z ≤ 1
  · have hAnti : AntitoneOn g (Set.Icc (1 / 2) 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc (1 / 2) 1)
      · intro x hx
        exact (hgDeriv x (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        exact (hgDeriv x (by
          rw [interior_Icc, Set.mem_Ioo] at hx
          linarith [hx.1])).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hgDeriv x (by
          rw [interior_Icc, Set.mem_Ioo] at hx
          linarith [hx.1])).deriv]
        rw [interior_Icc, Set.mem_Ioo] at hx
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
          (by nlinarith [hx.1])
    have hCompare := hAnti (show z ∈ Set.Icc (1 / 2) 1 from ⟨hzLower, hzOne⟩)
      (show (1 : ℝ) ∈ Set.Icc (1 / 2) 1 by norm_num) hzOne
    have hgNonneg : 0 ≤ g z := by simpa only [hgOne] using hCompare
    dsimp only [g] at hgNonneg
    linarith
  · have hzOne' : 1 ≤ z := le_of_not_ge hzOne
    have hMono : MonotoneOn g (Set.Icc 1 2) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 1 2)
      · intro x hx
        exact (hgDeriv x (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        exact (hgDeriv x (by
          rw [interior_Icc, Set.mem_Ioo] at hx
          linarith [hx.1])).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hgDeriv x (by
          rw [interior_Icc, Set.mem_Ioo] at hx
          linarith [hx.1])).deriv]
        rw [interior_Icc, Set.mem_Ioo] at hx
        exact div_nonneg
          (mul_nonneg (by linarith) (by linarith)) (by nlinarith [hx.1])
    have hCompare := hMono (show (1 : ℝ) ∈ Set.Icc 1 2 by norm_num)
      (show z ∈ Set.Icc 1 2 from ⟨hzOne', hzUpper⟩) hzOne'
    have hgNonneg : 0 ≤ g z := by simpa only [hgOne] using hCompare
    dsimp only [g] at hgNonneg
    linarith

/-- The normalized phase has its unique positive zero at the stationary
point. -/
theorem stationaryNormalPhase_eq_zero_iff {z : ℝ} (hz : 0 < z) :
    stationaryNormalPhase z = 0 ↔ z = 1 := by
  constructor
  · intro hzero
    by_contra hne
    have hstrict := Real.log_lt_sub_one_of_pos hz hne
    unfold stationaryNormalPhase at hzero
    linarith
  · rintro rfl
    simp [stationaryNormalPhase]

/-- Exact curvature at the stationary point; this is the scale producing the
dual factor `sqrt (t / m^2)` in the B-process. -/
theorem secondDeriv_reflectionPhase_stationary
    {t m : ℝ} (ht : 0 < t) (hm : 0 < m) :
    deriv (deriv (reflectionPhase t m))
        (reflectionStationaryPoint t m) =
      2 * Real.pi * m ^ 2 / t := by
  rw [secondDeriv_reflectionPhase]
  · unfold reflectionStationaryPoint
    field_simp [Real.pi_ne_zero, ht.ne', hm.ne']
  · exact (reflectionStationaryPoint_pos ht hm).ne'

/-- The exact pointwise decomposition that turns the positive Fourier mode
of a zeta block into the logarithmic stationary phase. -/
theorem cpow_mul_fourier_exp_eq_reflectionPhase
    (y : ℝ) (s : ℂ) (m : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ (-s) *
        Complex.exp (2 * Real.pi * I * ((m * y : ℝ) : ℂ)) =
      ((y ^ (-s.re) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * I *
          ((reflectionPhase s.im m y : ℝ) : ℂ)) := by
  simpa only [reflectionPhase] using
    ZetaAppendix.cpow_mul_fourier_exp_eq_log_phase y s m hy

theorem reflectionStationaryPoint_mem_Icc_iff
    {t m a b : ℝ} (hm : 0 < m)
    (ha : 0 < a) (hab : a ≤ b) :
    reflectionStationaryPoint t m ∈ Set.Icc a b ↔
      t / (2 * Real.pi * b) ≤ m ∧
        m ≤ t / (2 * Real.pi * a) := by
  unfold reflectionStationaryPoint
  rw [Set.mem_Icc]
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hTwoPi : 0 < 2 * Real.pi := by positivity
  constructor
  · rintro ⟨hLower, hUpper⟩
    constructor
    · rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi * b)]
      have hUpper' :=
        (div_le_iff₀ (mul_pos hTwoPi hm)).mp hUpper
      nlinarith
    · rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi * a)]
      have hLower' :=
        (le_div_iff₀ (mul_pos hTwoPi hm)).mp hLower
      nlinarith
  · rintro ⟨hLower, hUpper⟩
    constructor
    · rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi * m)]
      have hUpper' :=
        (le_div_iff₀ (mul_pos hTwoPi ha)).mp hUpper
      nlinarith
    · rw [div_le_iff₀ (by positivity : 0 < 2 * Real.pi * m)]
      have hLower' :=
        (div_le_iff₀ (mul_pos hTwoPi hb)).mp hLower
      nlinarith

/-- On a dyadic block `[A,2A]`, the stationary Fourier frequencies are
exactly those in the dual interval of size comparable to `t/A`. -/
theorem reflectionStationaryPoint_mem_dyadic_iff
    {t m A : ℝ} (hm : 0 < m) (hA : 0 < A) :
    reflectionStationaryPoint t m ∈ Set.Icc A (2 * A) ↔
      t / (2 * Real.pi * (2 * A)) ≤ m ∧
        m ≤ t / (2 * Real.pi * A) := by
  exact reflectionStationaryPoint_mem_Icc_iff hm hA (by linarith)

/-- Uniform curvature bounds on a positive dyadic block.  They identify the
quadratic scale used by the stationary-phase main term. -/
theorem secondDeriv_reflectionPhase_dyadic_bounds
    {t m A x : ℝ} (ht : 0 < t) (hA : 0 < A)
    (hx : x ∈ Set.Icc A (2 * A)) :
    t / (8 * Real.pi * A ^ 2) ≤
        deriv (deriv (reflectionPhase t m)) x ∧
      deriv (deriv (reflectionPhase t m)) x ≤
        t / (2 * Real.pi * A ^ 2) := by
  have hxPos : 0 < x := hA.trans_le hx.1
  rw [secondDeriv_reflectionPhase t m x hxPos.ne']
  have hPi : 0 < Real.pi := Real.pi_pos
  have hASq : 0 < A ^ 2 := sq_pos_of_pos hA
  have hxSq : 0 < x ^ 2 := sq_pos_of_pos hxPos
  have hxUpperSq : x ^ 2 ≤ (2 * A) ^ 2 :=
    (sq_le_sq₀ hxPos.le (by positivity)).mpr hx.2
  have hxLowerSq : A ^ 2 ≤ x ^ 2 :=
    (sq_le_sq₀ hA.le hxPos.le).mpr hx.1
  constructor
  · apply div_le_div_of_nonneg_left ht.le
      (by positivity : 0 < 2 * Real.pi * x ^ 2)
    calc
      2 * Real.pi * x ^ 2 ≤ 2 * Real.pi * (2 * A) ^ 2 :=
        mul_le_mul_of_nonneg_left hxUpperSq (by positivity)
      _ = 8 * Real.pi * A ^ 2 := by ring
  · apply div_le_div_of_nonneg_left ht.le
      (by positivity : 0 < 2 * Real.pi * A ^ 2)
    exact mul_le_mul_of_nonneg_left hxLowerSq (by positivity)

/-- Exact Poisson-summation representation of a finite partial-zeta block. -/
theorem partial_zeta_block_poisson
    {a b : ℝ} (ha : ¬∃ n : ℤ, a = n) (hb : ¬∃ n : ℤ, b = n)
    (hab : b > a) (ha' : 0 < a) {s : ℂ} (hs1 : s ≠ 1) :
    ∃ L : ℂ, Tendsto
      (fun N : ℕ => ∑ n ∈ Icc 1 N,
        (FourierTransform.fourier (partialZetaPoissonWeight a b s) n +
          FourierTransform.fourier (partialZetaPoissonWeight a b s) (-n)))
      atTop (𝓝 L) ∧
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℂ) ^ (-s) =
        ((b ^ (1 - s) : ℂ) - (a ^ (1 - s) : ℂ)) / (1 - s) + L := by
  simpa only [partialZetaPoissonWeight] using
    ZetaAppendix.poisson_partial_zeta_sum ha hb hab ha' hs1

/-- The same exact reflection identity with every paired Fourier coefficient
written as its cosine oscillatory integral. -/
theorem partial_zeta_block_cosine_limit
    {a b : ℝ} (ha : ¬∃ n : ℤ, a = n) (hb : ¬∃ n : ℤ, b = n)
    (hab : b > a) (ha' : 0 < a) {s : ℂ} (hs1 : s ≠ 1) :
    ∃ L : ℂ, Tendsto
      (fun N : ℕ => ∑ n ∈ Icc 1 N,
        2 * ∫ y in a..b,
          (y : ℂ) ^ (-s) * Real.cos (2 * Real.pi * n * y))
      atTop (𝓝 L) ∧
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, (n : ℂ) ^ (-s) =
        ((b ^ (1 - s) : ℂ) - (a ^ (1 - s) : ℂ)) / (1 - s) + L := by
  obtain ⟨L, hL, hEq⟩ := partial_zeta_block_poisson ha hb hab ha' hs1
  refine ⟨L, hL.congr' ?_, hEq⟩
  filter_upwards [] with N
  apply Finset.sum_congr rfl
  intro n hn
  have hnOne : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hPred : n - 1 + 1 = n := Nat.sub_add_cancel hnOne
  have hPredReal : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hPred
  have hPredInt : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by
    exact_mod_cast hPred
  have hPair := ZetaAppendix.partial_zeta_fourier_pair_eq_cosine_integral
    s ha' hab (n - 1)
  rw [hPredReal, hPredInt] at hPair
  simpa only [partialZetaPoissonWeight] using hPair

end RiemannZeta.GuthMaynard
