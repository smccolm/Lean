import Tao2026.SmoothNumberStability

/-!
# Stability of the exact saddle curvature

This file controls the second logarithmic derivative of the finite smooth
Euler product when its saddle is moved by a fixed dilation of the ambient
cutoff.  The key point is uniformity in the prime: on `sigma ≥ 1/2`, the
logarithmic derivative of each second-saddle summand is bounded by
`7 * log y` for every prime `p ≤ y`.
-/

open Filter Topology

namespace Tao2026

noncomputable section

/-- A logarithmic presentation of one positive second-saddle summand. -/
noncomputable def smoothSaddleSecondPrimeLog (p : ℕ) (sigma : ℝ) : ℝ :=
  2 * Real.log (Real.log p) + sigma * Real.log p -
    2 * Real.log ((p : ℝ) ^ sigma - 1)

/-- On the half-plane used below, every prime power is uniformly separated
from one. -/
theorem four_thirds_le_prime_rpow {p : ℕ} (hp : 2 ≤ p)
    {sigma : ℝ} (hsigma : (1 / 2 : ℝ) ≤ sigma) :
    (4 / 3 : ℝ) ≤ (p : ℝ) ^ sigma := by
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.sqrt_nonneg 2
    nlinarith
  rw [Real.sqrt_eq_rpow] at hsqrt
  calc
    (4 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := hsqrt
    _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) (by norm_num)
    _ ≤ (p : ℝ) ^ sigma :=
      Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ p by omega)) hsigma

/-- The rational factor in the logarithmic derivative of a second-saddle
summand has an absolute uniform bound on `sigma ≥ 1/2`. -/
theorem prime_rpow_add_one_div_sub_one_le_seven
    {p : ℕ} (hp : 2 ≤ p) {sigma : ℝ} (hsigma : (1 / 2 : ℝ) ≤ sigma) :
    ((p : ℝ) ^ sigma + 1) / ((p : ℝ) ^ sigma - 1) ≤ 7 := by
  have hpow := four_thirds_le_prime_rpow hp hsigma
  have hden : 0 < (p : ℝ) ^ sigma - 1 := by linarith
  rw [div_le_iff₀ hden]
  linarith

/-- Exact logarithmic derivative of one second-saddle summand. -/
theorem hasDerivAt_smoothSaddleSecondPrimeLog
    {p : ℕ} (hp : 2 ≤ p) {sigma : ℝ} (hsigma : 0 < sigma) :
    HasDerivAt (smoothSaddleSecondPrimeLog p)
      (-Real.log p * (((p : ℝ) ^ sigma + 1) /
        ((p : ℝ) ^ sigma - 1))) sigma := by
  have hpPos : (0 : ℝ) < p := by positivity
  have hden := smoothSaddle_denominator_pos hp hsigma
  unfold smoothSaddleSecondPrimeLog
  convert (((hasDerivAt_const sigma (2 * Real.log (Real.log p))).add
      ((hasDerivAt_id sigma).mul_const (Real.log p))).sub
        (((((hasDerivAt_id sigma).const_rpow hpPos).sub_const 1).log
          hden.ne').const_mul 2)) using 1
  simp only [id_eq]
  field_simp [hden.ne']
  ring

/-- The absolute logarithmic derivative of one second-saddle summand is
bounded uniformly for primes below `y`. -/
theorem abs_smoothSaddleSecondPrimeLog_deriv_le
    {p y : ℕ} (hp : 2 ≤ p) (hpy : p ≤ y)
    {sigma : ℝ} (hsigma : (1 / 2 : ℝ) ≤ sigma) :
    |(-Real.log p * (((p : ℝ) ^ sigma + 1) /
      ((p : ℝ) ^ sigma - 1)))| ≤ 7 * Real.log y := by
  have hsigmaPos : 0 < sigma := by linarith
  have hden := smoothSaddle_denominator_pos hp hsigmaPos
  have hratioPos : 0 < ((p : ℝ) ^ sigma + 1) /
      ((p : ℝ) ^ sigma - 1) := by positivity
  have hlogpPos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hlogyNonneg : 0 ≤ Real.log (y : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ y by omega)
  have hlogpy : Real.log (p : ℝ) ≤ Real.log (y : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by exact_mod_cast (show 0 < p by omega) : (0 : ℝ) < p)
      (by exact_mod_cast (show 0 < y by omega) : (0 : ℝ) < y)
      (by exact_mod_cast hpy)
  rw [abs_mul, abs_of_neg (neg_neg_of_pos hlogpPos), abs_of_pos hratioPos,
    neg_neg]
  calc
    Real.log (p : ℝ) * (((p : ℝ) ^ sigma + 1) /
        ((p : ℝ) ^ sigma - 1)) ≤ Real.log (y : ℝ) * 7 :=
      mul_le_mul hlogpy
        (prime_rpow_add_one_div_sub_one_le_seven hp hsigma)
        hratioPos.le hlogyNonneg
    _ = 7 * Real.log (y : ℝ) := by ring

/-- The logarithms of any one second-saddle summand are Lipschitz on the
half-line `sigma ≥ 1/2`, uniformly over primes `p ≤ y`. -/
theorem abs_smoothSaddleSecondPrimeLog_sub_le
    {p y : ℕ} (hp : 2 ≤ p) (hpy : p ≤ y)
    {a b : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (hb : (1 / 2 : ℝ) ≤ b) :
    |smoothSaddleSecondPrimeLog p a -
        smoothSaddleSecondPrimeLog p b| ≤
      7 * Real.log y * |a - b| := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have hcontinuous : ContinuousOn (smoothSaddleSecondPrimeLog p)
        (Set.Icc a b) := fun s hs =>
      (hasDerivAt_smoothSaddleSecondPrimeLog hp
        (by linarith [ha, hs.1])).continuousAt.continuousWithinAt
    obtain ⟨xi, hxi, hderiv⟩ := exists_hasDerivAt_eq_slope
      (smoothSaddleSecondPrimeLog p)
      (fun s => -Real.log p * (((p : ℝ) ^ s + 1) /
        ((p : ℝ) ^ s - 1))) hab hcontinuous
      (fun s hs => hasDerivAt_smoothSaddleSecondPrimeLog hp
        (by linarith [ha, hs.1]))
    rw [eq_div_iff (sub_ne_zero.mpr hab.ne')] at hderiv
    have hxiHalf : (1 / 2 : ℝ) ≤ xi := ha.trans hxi.1.le
    have hderivBound := abs_smoothSaddleSecondPrimeLog_deriv_le
      hp hpy hxiHalf
    have hlength : 0 ≤ b - a := sub_nonneg.mpr hab.le
    have habsLength : |a - b| = b - a := by
      rw [abs_of_nonpos (sub_nonpos.mpr hab.le)]
      ring
    rw [abs_sub_comm, ← hderiv, abs_mul, abs_of_nonneg hlength,
      habsLength]
    exact mul_le_mul_of_nonneg_right hderivBound hlength
  · subst b
    simp
  · have hcontinuous : ContinuousOn (smoothSaddleSecondPrimeLog p)
        (Set.Icc b a) := fun s hs =>
      (hasDerivAt_smoothSaddleSecondPrimeLog hp
        (by linarith [hb, hs.1])).continuousAt.continuousWithinAt
    obtain ⟨xi, hxi, hderiv⟩ := exists_hasDerivAt_eq_slope
      (smoothSaddleSecondPrimeLog p)
      (fun s => -Real.log p * (((p : ℝ) ^ s + 1) /
        ((p : ℝ) ^ s - 1))) hab hcontinuous
      (fun s hs => hasDerivAt_smoothSaddleSecondPrimeLog hp
        (by linarith [hb, hs.1]))
    rw [eq_div_iff (sub_ne_zero.mpr hab.ne')] at hderiv
    have hxiHalf : (1 / 2 : ℝ) ≤ xi := hb.trans hxi.1.le
    have hderivBound := abs_smoothSaddleSecondPrimeLog_deriv_le
      hp hpy hxiHalf
    have hlength : 0 ≤ a - b := sub_nonneg.mpr hab.le
    rw [← hderiv, abs_mul, abs_of_nonneg hlength]
    exact mul_le_mul_of_nonneg_right hderivBound hlength

/-- Exponentiating the logarithmic presentation recovers the second-saddle
summand exactly. -/
theorem exp_smoothSaddleSecondPrimeLog
    {p : ℕ} (hp : 2 ≤ p) {sigma : ℝ} (hsigma : 0 < sigma) :
    Real.exp (smoothSaddleSecondPrimeLog p sigma) =
      smoothSaddleSecondPrimeTerm p sigma := by
  have hpPos : (0 : ℝ) < p := by positivity
  have hlogpPos : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hden := smoothSaddle_denominator_pos hp hsigma
  rw [smoothSaddleSecondPrimeLog,
    show 2 * Real.log (Real.log p) + sigma * Real.log p -
        2 * Real.log ((p : ℝ) ^ sigma - 1) =
      (Real.log (Real.log p) + Real.log (Real.log p)) +
        (Real.log p * sigma) -
          (Real.log ((p : ℝ) ^ sigma - 1) +
            Real.log ((p : ℝ) ^ sigma - 1)) by ring,
    Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_add,
    Real.exp_log hlogpPos, Real.exp_log hden,
    ← Real.rpow_def_of_pos hpPos]
  unfold smoothSaddleSecondPrimeTerm
  ring

/-- Uniform exponential comparison of a second-saddle summand at two
parameters on `sigma ≥ 1/2`. -/
theorem smoothSaddleSecondPrimeTerm_between
    {p y : ℕ} (hp : 2 ≤ p) (hpy : p ≤ y)
    {a b : ℝ} (ha : (1 / 2 : ℝ) ≤ a) (hb : (1 / 2 : ℝ) ≤ b) :
    Real.exp (-(7 * Real.log y * |a - b|)) *
        smoothSaddleSecondPrimeTerm p b ≤
      smoothSaddleSecondPrimeTerm p a ∧
      smoothSaddleSecondPrimeTerm p a ≤
        Real.exp (7 * Real.log y * |a - b|) *
          smoothSaddleSecondPrimeTerm p b := by
  have haPos : 0 < a := by linarith
  have hbPos : 0 < b := by linarith
  have hlog := abs_smoothSaddleSecondPrimeLog_sub_le hp hpy ha hb
  have hlower : smoothSaddleSecondPrimeLog p b -
      7 * Real.log y * |a - b| ≤ smoothSaddleSecondPrimeLog p a := by
    rw [abs_le] at hlog
    linarith [hlog.1]
  have hupper : smoothSaddleSecondPrimeLog p a ≤
      smoothSaddleSecondPrimeLog p b +
        7 * Real.log y * |a - b| := by
    rw [abs_le] at hlog
    linarith [hlog.2]
  constructor
  · have := Real.exp_le_exp.mpr hlower
    rw [Real.exp_sub, exp_smoothSaddleSecondPrimeLog hp hbPos,
      exp_smoothSaddleSecondPrimeLog hp haPos] at this
    simpa [Real.exp_neg, div_eq_inv_mul, mul_comm] using this
  · have := Real.exp_le_exp.mpr hupper
    rw [exp_smoothSaddleSecondPrimeLog hp haPos, Real.exp_add,
      exp_smoothSaddleSecondPrimeLog hp hbPos] at this
    nlinarith [Real.exp_pos (7 * Real.log (y : ℝ) * |a - b|)]

/-- Summing the prime-local estimates gives the same exponential comparison
for the exact curvature sum. -/
theorem smoothSaddlePhiTwo_between
    {y : ℕ} {a b : ℝ} (ha : (1 / 2 : ℝ) ≤ a)
    (hb : (1 / 2 : ℝ) ≤ b) :
    Real.exp (-(7 * Real.log y * |a - b|)) *
        smoothSaddlePhiTwo y b ≤ smoothSaddlePhiTwo y a ∧
      smoothSaddlePhiTwo y a ≤
        Real.exp (7 * Real.log y * |a - b|) *
          smoothSaddlePhiTwo y b := by
  unfold smoothSaddlePhiTwo
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hpMem =>
      (smoothSaddleSecondPrimeTerm_between
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hpMem).1).1
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hpMem).1).2 ha hb).1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hpMem =>
      (smoothSaddleSecondPrimeTerm_between
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hpMem).1).1
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hpMem).1).2 ha hb).2

/-- The exact saddle curvature is asymptotically unchanged by any fixed
positive dilation of the ambient cutoff. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddlePhiTwo_dilation_div
    {X y : ℕ → ℕ} {α c : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hc : 0 < c) :
    Tendsto (fun n =>
      smoothSaddlePhiTwo (y n)
          (smoothSaddlePoint (taoNaturalDilation c (X n)) (y n)) /
        smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)))
      atTop (𝓝 1) := by
  let eps : ℕ → ℝ := fun n =>
    7 * Real.log (y n) *
      |smoothSaddlePoint (taoNaturalDilation c (X n)) (y n) -
        smoothSaddlePoint (X n) (y n)|
  have hweighted :=
    hregime.tendsto_abs_smoothSaddlePoint_dilation_sub_mul_log_y hα hc
  have heps : Tendsto eps atTop (𝓝 0) := by
    have hraw := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (7 : ℝ))
      atTop (𝓝 7)).mul hweighted
    simpa [eps, mul_assoc, mul_comm, mul_left_comm] using hraw
  have hepsNeg : Tendsto (fun n => -(eps n)) atTop (𝓝 0) := by
    simpa using heps.neg
  have hlower : Tendsto (fun n => Real.exp (-(eps n))) atTop (𝓝 1) := by
    simpa using (Real.continuous_exp.tendsto 0).comp hepsNeg
  have hupper : Tendsto (fun n => Real.exp (eps n)) atTop (𝓝 1) := by
    simpa using (Real.continuous_exp.tendsto 0).comp heps
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [
      (hregime.naturalDilation hc).tendsto_smoothSaddlePoint_one hα |>.eventually
        (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hregime.tendsto_smoothSaddlePoint_one hα |>.eventually
        (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n ha hb hX hy
    have hphiPos := smoothSaddlePhiTwo_pos hy
      (smoothSaddlePoint_pos hX hy)
    have hbounds := smoothSaddlePhiTwo_between (y := y n) ha.le hb.le
    exact (le_div_iff₀ hphiPos).2 hbounds.1
  · filter_upwards [
      (hregime.naturalDilation hc).tendsto_smoothSaddlePoint_one hα |>.eventually
        (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hregime.tendsto_smoothSaddlePoint_one hα |>.eventually
        (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n ha hb hX hy
    have hphiPos := smoothSaddlePhiTwo_pos hy
      (smoothSaddlePoint_pos hX hy)
    have hbounds := smoothSaddlePhiTwo_between (y := y n) ha.le hb.le
    exact (div_le_iff₀ hphiPos).2 hbounds.2

/-- Exact factorization of the quotient of two saddle main terms with a
common smoothness cutoff. -/
theorem smoothSaddleMainTerm_div_eq
    {X₁ X₂ y : ℕ} (hX₁ : 2 ≤ X₁) (hX₂ : 2 ≤ X₂) (hy : 2 ≤ y) :
    smoothSaddleMainTerm X₁ y / smoothSaddleMainTerm X₂ y =
      (Real.exp (smoothSaddlePhase X₁ y (smoothSaddlePoint X₁ y)) /
        Real.exp (smoothSaddlePhase X₂ y (smoothSaddlePoint X₂ y))) *
      (smoothSaddlePoint X₂ y / smoothSaddlePoint X₁ y) *
      (Real.sqrt (smoothSaddlePhiTwo y (smoothSaddlePoint X₂ y)) /
        Real.sqrt (smoothSaddlePhiTwo y (smoothSaddlePoint X₁ y))) := by
  have hs₁ := smoothSaddlePoint_pos hX₁ hy
  have hs₂ := smoothSaddlePoint_pos hX₂ hy
  have hphi₁ := smoothSaddlePhiTwo_pos hy hs₁
  have hphi₂ := smoothSaddlePhiTwo_pos hy hs₂
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  unfold smoothSaddleMainTerm
  rw [Real.sqrt_mul hpi, Real.sqrt_mul hpi]
  field_simp [hs₁.ne', hs₂.ne', (Real.sqrt_pos.2 hphi₁).ne',
    (Real.sqrt_pos.2 hphi₂).ne', (Real.sqrt_pos.2 (by positivity :
      0 < 2 * Real.pi)).ne', (Real.exp_pos _).ne']

/-- The complete Gaussian saddle main term, including its curvature
prefactor, scales by `c` under fixed positive dilation. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleMainTerm_ratio
    {X y : ℕ → ℕ} {α c : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hc : 0 < c) :
    Tendsto (fun n =>
      smoothSaddleMainTerm (taoNaturalDilation c (X n)) (y n) /
        smoothSaddleMainTerm (X n) (y n)) atTop (𝓝 c) := by
  have hphase := hregime.tendsto_exp_smoothSaddlePhase_ratio hα hc
  have hsaddle : Tendsto (fun n =>
      smoothSaddlePoint (X n) (y n) /
        smoothSaddlePoint (taoNaturalDilation c (X n)) (y n))
      atTop (𝓝 1) := by
    simpa using (hregime.tendsto_smoothSaddlePoint_one hα).div
      (hregime.tendsto_smoothSaddlePoint_naturalDilation hα hc)
      (by norm_num : (1 : ℝ) ≠ 0)
  have hcurvature :=
    hregime.tendsto_smoothSaddlePhiTwo_dilation_div hα hc
  have hcurvatureInvRaw := hcurvature.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hcurvatureInvRaw' : Tendsto (fun n =>
      (smoothSaddlePhiTwo (y n)
          (smoothSaddlePoint (taoNaturalDilation c (X n)) (y n)) /
        smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)))⁻¹)
      atTop (𝓝 1) := by
    simpa using hcurvatureInvRaw
  have hcurvatureInv : Tendsto (fun n =>
      smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) /
        smoothSaddlePhiTwo (y n)
          (smoothSaddlePoint (taoNaturalDilation c (X n)) (y n)))
      atTop (𝓝 1) := by
    apply hcurvatureInvRaw'.congr'
    filter_upwards [hregime.eventually_two_le_X,
      (hregime.naturalDilation hc).eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hD hy
    have hbase := smoothSaddlePhiTwo_pos hy
      (smoothSaddlePoint_pos hX hy)
    have hdilated := smoothSaddlePhiTwo_pos hy
      (smoothSaddlePoint_pos hD hy)
    field_simp [hbase.ne', hdilated.ne']
  have hsqrtRaw := (Real.continuous_sqrt.tendsto 1).comp hcurvatureInv
  have hsqrtRaw' : Tendsto (fun n => Real.sqrt
      (smoothSaddlePhiTwo (y n) (smoothSaddlePoint (X n) (y n)) /
        smoothSaddlePhiTwo (y n)
          (smoothSaddlePoint (taoNaturalDilation c (X n)) (y n))))
      atTop (𝓝 1) := by
    simpa using hsqrtRaw
  have hsqrt : Tendsto (fun n =>
      Real.sqrt (smoothSaddlePhiTwo (y n)
          (smoothSaddlePoint (X n) (y n))) /
        Real.sqrt (smoothSaddlePhiTwo (y n)
          (smoothSaddlePoint (taoNaturalDilation c (X n)) (y n))))
      atTop (𝓝 1) := by
    apply hsqrtRaw'.congr'
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hX hy
    rw [Real.sqrt_div (smoothSaddlePhiTwo_pos hy
      (smoothSaddlePoint_pos hX hy)).le]
  have hproduct := hphase.mul (hsaddle.mul hsqrt)
  have hproduct' : Tendsto (fun n =>
      (Real.exp (smoothSaddlePhase (taoNaturalDilation c (X n)) (y n)
          (smoothSaddlePoint (taoNaturalDilation c (X n)) (y n))) /
        Real.exp (smoothSaddlePhase (X n) (y n)
          (smoothSaddlePoint (X n) (y n)))) *
      (smoothSaddlePoint (X n) (y n) /
        smoothSaddlePoint (taoNaturalDilation c (X n)) (y n)) *
      (Real.sqrt (smoothSaddlePhiTwo (y n)
          (smoothSaddlePoint (X n) (y n))) /
        Real.sqrt (smoothSaddlePhiTwo (y n)
          (smoothSaddlePoint (taoNaturalDilation c (X n)) (y n)))))
      atTop (𝓝 c) := by
    simpa only [mul_assoc, mul_one] using hproduct
  apply hproduct'.congr'
  filter_upwards [(hregime.naturalDilation hc).eventually_two_le_X,
    hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hD hX hy
  exact (smoothSaddleMainTerm_div_eq hD hX hy).symm

/-- The exact remaining uniform analytic input: in every critical regime,
the smooth-number count is asymptotic to the finite Gaussian saddle main
term.  This is a proposition-valued target, not an assumed theorem. -/
def TaoCriticalSmoothSaddleAsymptoticConclusion : Prop :=
  ∀ (α : ℝ) (X y : ℕ → ℕ), 0 < α →
    IsTaoCriticalSmoothRegime X y α →
      Tendsto (fun n =>
        (psiNat (X n) (y n) : ℝ) /
          smoothSaddleMainTerm (X n) (y n)) atTop (𝓝 1)

/-- The uniform saddle asymptotic plus the now-proved complete main-term
stability gives Granville's fixed-dilation quotient limit. -/
theorem criticalSmoothDilationLimit_of_saddleAsymptotic
    (hasymptotic : TaoCriticalSmoothSaddleAsymptoticConclusion) :
    TaoCriticalSmoothDilationLimitConclusion := by
  intro c α X y hc hα hregime
  have hbase := hasymptotic α X y hα hregime
  have hdilated := hasymptotic α
    (fun n => taoNaturalDilation c (X n)) y hα
    (hregime.naturalDilation hc)
  have hmain := hregime.tendsto_smoothSaddleMainTerm_ratio hα hc
  have hraw := (hdilated.mul hmain).div hbase
    (by norm_num : (1 : ℝ) ≠ 0)
  simp only [one_mul, div_one] at hraw
  have hresult : Tendsto (fun n =>
      (psiNat (taoNaturalDilation c (X n)) (y n) : ℝ) /
        (psiNat (X n) (y n) : ℝ)) atTop (𝓝 c) := by
    apply hraw.congr'
    filter_upwards [(hregime.naturalDilation hc).eventually_two_le_X,
      hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα] with n hD hX hy
    have hmD := smoothSaddleMainTerm_pos hD hy
    have hmX := smoothSaddleMainTerm_pos hX hy
    have hpsiX : (0 : ℝ) < psiNat (X n) (y n) := by
      exact_mod_cast one_le_psiNat (show 1 ≤ X n by omega)
    change ((((psiNat (taoNaturalDilation c (X n)) (y n) : ℝ) /
          smoothSaddleMainTerm (taoNaturalDilation c (X n)) (y n)) *
        (smoothSaddleMainTerm (taoNaturalDilation c (X n)) (y n) /
          smoothSaddleMainTerm (X n) (y n))) /
        ((psiNat (X n) (y n) : ℝ) /
          smoothSaddleMainTerm (X n) (y n))) =
      (psiNat (taoNaturalDilation c (X n)) (y n) : ℝ) /
        (psiNat (X n) (y n) : ℝ)
    field_simp [hmD.ne', hmX.ne', hpsiX.ne']
  exact hresult

/-- Consequently the same single analytic input also gives Tao's exact
constant-factor stability contract. -/
theorem criticalSmoothDilationStability_of_saddleAsymptotic
    (hasymptotic : TaoCriticalSmoothSaddleAsymptoticConclusion) :
    TaoCriticalSmoothDilationStabilityConclusion :=
  criticalSmoothDilationStability_of_limit
    (criticalSmoothDilationLimit_of_saddleAsymptotic hasymptotic)

end

end Tao2026
