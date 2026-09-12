import Tao2026.SmoothNumberSaddleRegimes

/-!
# The exact smooth-number saddle phase

This file supplies the logarithmic Euler-product phase used in the
Hildebrand--Tenenbaum/Granville saddle-point formula.  Its first derivative is
`log X - phiOne`; its second derivative is `phiTwo`, so the exact saddle
constructed in `SmoothNumberSaddlePoint` is precisely the stationary point of
this strictly convex phase.
-/

open Filter Topology

namespace Tao2026

noncomputable section

/-- The logarithm of the finite smooth Euler product. -/
noncomputable def smoothSaddlePhiZero (y : ℕ) (sigma : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
    -Real.log (1 - (p : ℝ) ^ (-sigma))

/-- The real saddle exponent `sigma log X + log zeta(sigma,y)`. -/
noncomputable def smoothSaddlePhase (X y : ℕ) (sigma : ℝ) : ℝ :=
  sigma * Real.log X + smoothSaddlePhiZero y sigma

/-- The real main term in the standard finite saddle-point approximation to
the smooth-number count. -/
noncomputable def smoothSaddleMainTerm (X y : ℕ) : ℝ :=
  Real.exp (smoothSaddlePhase X y (smoothSaddlePoint X y)) /
    (smoothSaddlePoint X y *
      Real.sqrt (2 * Real.pi *
        smoothSaddlePhiTwo y (smoothSaddlePoint X y)))

/-- Every Euler factor base lies strictly between zero and one on the
positive `sigma` axis. -/
theorem smoothEulerFactorBase_pos {p : ℕ} (hp : 2 ≤ p)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < 1 - (p : ℝ) ^ (-sigma) := by
  rw [sub_pos]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast (show 1 < p by omega)) (neg_neg_of_pos hsigma)

/-- Exponentiating `phiZero` recovers the literal finite Euler product. -/
theorem exp_smoothSaddlePhiZero (y : ℕ) {sigma : ℝ}
    (hsigma : 0 < sigma) :
    Real.exp (smoothSaddlePhiZero y sigma) =
      ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  unfold smoothSaddlePhiZero
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Real.exp_neg, Real.exp_log]
  exact smoothEulerFactorBase_pos
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1 hsigma

/-- The exact Rankin expression is the exponential of the saddle phase. -/
theorem rpow_mul_sourceEulerProduct_eq_exp_smoothSaddlePhase
    {X y : ℕ} (hX : 1 ≤ X) {sigma : ℝ} (hsigma : 0 < sigma) :
    (X : ℝ) ^ sigma *
        (∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
          (1 - (p : ℝ) ^ (-sigma))⁻¹) =
      Real.exp (smoothSaddlePhase X y sigma) := by
  rw [← exp_smoothSaddlePhiZero y hsigma]
  unfold smoothSaddlePhase
  rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < X by omega))]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The saddle main term is strictly positive in the defining range. -/
theorem smoothSaddleMainTerm_pos
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    0 < smoothSaddleMainTerm X y := by
  unfold smoothSaddleMainTerm
  have hphiTwo := smoothSaddlePhiTwo_pos hy
    (smoothSaddlePoint_pos hX hy)
  have hpi : 0 < Real.pi := Real.pi_pos
  exact div_pos (Real.exp_pos _)
    (mul_pos (smoothSaddlePoint_pos hX hy)
      (Real.sqrt_pos.2 (mul_pos (mul_pos (by norm_num) hpi) hphiTwo)))

/-- Rankin's inequality evaluated at the exact saddle. -/
theorem psiNat_cast_le_exp_smoothSaddlePhase_saddle
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    (psiNat X y : ℝ) ≤
      Real.exp (smoothSaddlePhase X y (smoothSaddlePoint X y)) := by
  have hrankin := psiNat_cast_le_rpow_mul_sourceEulerProduct
    (X := X) (y := y) (sigma := smoothSaddlePoint X y) (by omega)
      (smoothSaddlePoint_pos hX hy)
  rw [rpow_mul_sourceEulerProduct_eq_exp_smoothSaddlePhase
    (show 1 ≤ X by omega) (smoothSaddlePoint_pos hX hy)] at hrankin
  exact hrankin

/-- A single logarithmic Euler factor has derivative the negative first
saddle summand. -/
theorem hasDerivAt_smoothSaddlePhiZeroTerm
    {p : ℕ} (hp : 2 ≤ p) {sigma : ℝ} (hsigma : 0 < sigma) :
    HasDerivAt (fun s : ℝ => -Real.log (1 - (p : ℝ) ^ (-s)))
      (-smoothSaddlePrimeTerm p sigma) sigma := by
  have hpPos : (0 : ℝ) < p := by positivity
  have hpow := (hasDerivAt_neg sigma).const_rpow hpPos
  have hbasePos := smoothEulerFactorBase_pos hp hsigma
  have hderiv := (((hasDerivAt_const sigma (1 : ℝ)).sub hpow).log
    hbasePos.ne').neg
  convert hderiv using 1
  simp only [Pi.sub_apply]
  unfold smoothSaddlePrimeTerm
  rw [Real.rpow_neg (by positivity)]
  field_simp [hbasePos.ne', (Real.rpow_pos_of_pos hpPos sigma).ne']
  ring

/-- The derivative of `phiZero` is `-phiOne`. -/
theorem hasDerivAt_smoothSaddlePhiZero
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    HasDerivAt (smoothSaddlePhiZero y)
      (-smoothSaddlePhiOne y sigma) sigma := by
  unfold smoothSaddlePhiZero smoothSaddlePhiOne
  convert HasDerivAt.fun_sum (u := (Finset.Icc 2 y).filter Nat.Prime)
    (fun p hp => hasDerivAt_smoothSaddlePhiZeroTerm
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1 hsigma) using 1
  rw [Finset.sum_neg_distrib]

/-- The first derivative of the full saddle phase. -/
theorem hasDerivAt_smoothSaddlePhase
    (X y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    HasDerivAt (smoothSaddlePhase X y)
      (Real.log X - smoothSaddlePhiOne y sigma) sigma := by
  unfold smoothSaddlePhase
  simpa [sub_eq_add_neg] using
    ((hasDerivAt_id sigma).mul_const (Real.log X)).add
      (hasDerivAt_smoothSaddlePhiZero y hsigma)

/-- The exact chosen saddle is a stationary point of the phase. -/
theorem hasDerivAt_smoothSaddlePhase_saddle
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    HasDerivAt (smoothSaddlePhase X y) 0 (smoothSaddlePoint X y) := by
  convert hasDerivAt_smoothSaddlePhase X y (smoothSaddlePoint_pos hX hy)
  rw [smoothSaddlePhiOne_smoothSaddlePoint hX hy]
  ring

/-- The derivative of the saddle phase has derivative `phiTwo`. -/
theorem hasDerivAt_smoothSaddlePhaseDerivative
    (X y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    HasDerivAt (fun s => Real.log X - smoothSaddlePhiOne y s)
      (smoothSaddlePhiTwo y sigma) sigma := by
  simpa using (hasDerivAt_const sigma (Real.log X)).sub
    (hasDerivAt_smoothSaddlePhiOne y hsigma)

/-- Exact mean-value identity for the saddle phase on a positive interval. -/
theorem exists_smoothSaddlePhase_secant
    (X y : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ xi ∈ Set.Ioo a b,
      smoothSaddlePhase X y b - smoothSaddlePhase X y a =
        (Real.log X - smoothSaddlePhiOne y xi) * (b - a) := by
  have hcontinuous :
      ContinuousOn (smoothSaddlePhase X y) (Set.Icc a b) :=
    fun s hs =>
      (hasDerivAt_smoothSaddlePhase X y (ha.trans_le hs.1)).continuousAt.continuousWithinAt
  obtain ⟨xi, hxi, hderiv⟩ := exists_hasDerivAt_eq_slope
    (smoothSaddlePhase X y)
    (fun s => Real.log X - smoothSaddlePhiOne y s)
    hab hcontinuous
    (fun s hs => hasDerivAt_smoothSaddlePhase X y (ha.trans hs.1))
  refine ⟨xi, hxi, ?_⟩
  rw [eq_div_iff (sub_ne_zero.mpr hab.ne')] at hderiv
  linarith

/-- The chosen exact saddle uniquely minimizes the phase on the positive
axis. -/
theorem smoothSaddlePhase_saddle_lt_of_ne
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hne : sigma ≠ smoothSaddlePoint X y) :
    smoothSaddlePhase X y (smoothSaddlePoint X y) <
      smoothSaddlePhase X y sigma := by
  rcases lt_or_gt_of_ne hne with hsigmaLt | hsaddleLt
  · obtain ⟨xi, hxi, hsecant⟩ :=
      exists_smoothSaddlePhase_secant X y hsigma hsigmaLt
    have hxiPos : 0 < xi := hsigma.trans hxi.1
    have hphi : Real.log (X : ℝ) < smoothSaddlePhiOne y xi := by
      have hstrict := (smoothSaddlePhiOne_strictAntiOn hy)
        hxiPos (smoothSaddlePoint_pos hX hy) hxi.2
      simpa [smoothSaddlePhiOne_smoothSaddlePoint hX hy] using hstrict
    have hlength : 0 < smoothSaddlePoint X y - sigma :=
      sub_pos.mpr hsigmaLt
    have hderivNeg : Real.log (X : ℝ) - smoothSaddlePhiOne y xi < 0 :=
      sub_neg.mpr hphi
    have hprod := mul_neg_of_neg_of_pos hderivNeg hlength
    linarith
  · obtain ⟨xi, hxi, hsecant⟩ :=
      exists_smoothSaddlePhase_secant X y
        (smoothSaddlePoint_pos hX hy) hsaddleLt
    have hxiPos : 0 < xi := (smoothSaddlePoint_pos hX hy).trans hxi.1
    have hphi : smoothSaddlePhiOne y xi < Real.log (X : ℝ) := by
      have hstrict := (smoothSaddlePhiOne_strictAntiOn hy)
        (smoothSaddlePoint_pos hX hy) hxiPos hxi.1
      simpa [smoothSaddlePhiOne_smoothSaddlePoint hX hy] using hstrict
    have hlength : 0 < sigma - smoothSaddlePoint X y :=
      sub_pos.mpr hsaddleLt
    have hprod := mul_pos (sub_pos.mpr hphi) hlength
    linarith

/-- Non-strict global minimum form of the saddle property. -/
theorem smoothSaddlePhase_saddle_le
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    smoothSaddlePhase X y (smoothSaddlePoint X y) ≤
      smoothSaddlePhase X y sigma := by
  by_cases h : sigma = smoothSaddlePoint X y
  · rw [h]
  · exact (smoothSaddlePhase_saddle_lt_of_ne hX hy hsigma h).le

/-- Changing only `X` changes the phase by `sigma` times the logarithmic
increment. -/
theorem smoothSaddlePhase_sub_same_sigma
    (X₁ X₂ y : ℕ) (sigma : ℝ) :
    smoothSaddlePhase X₂ y sigma - smoothSaddlePhase X₁ y sigma =
      sigma * (Real.log X₂ - Real.log X₁) := by
  unfold smoothSaddlePhase
  ring

/-- The change of the minimized phase is bounded below by the new saddle
times the logarithmic increment. -/
theorem smoothSaddlePoint_mul_log_sub_le_phase_saddle_sub
    {X₁ X₂ y : ℕ} (hX₁ : 2 ≤ X₁) (hX₂ : 2 ≤ X₂) (hy : 2 ≤ y) :
    smoothSaddlePoint X₂ y * (Real.log X₂ - Real.log X₁) ≤
      smoothSaddlePhase X₂ y (smoothSaddlePoint X₂ y) -
        smoothSaddlePhase X₁ y (smoothSaddlePoint X₁ y) := by
  have hmin := smoothSaddlePhase_saddle_le hX₁ hy
    (smoothSaddlePoint_pos hX₂ hy)
  have hchange := smoothSaddlePhase_sub_same_sigma X₁ X₂ y
    (smoothSaddlePoint X₂ y)
  linarith

/-- The change of the minimized phase is bounded above by the old saddle
times the logarithmic increment. -/
theorem phase_saddle_sub_le_smoothSaddlePoint_mul_log_sub
    {X₁ X₂ y : ℕ} (hX₁ : 2 ≤ X₁) (hX₂ : 2 ≤ X₂) (hy : 2 ≤ y) :
    smoothSaddlePhase X₂ y (smoothSaddlePoint X₂ y) -
        smoothSaddlePhase X₁ y (smoothSaddlePoint X₁ y) ≤
      smoothSaddlePoint X₁ y * (Real.log X₂ - Real.log X₁) := by
  have hmin := smoothSaddlePhase_saddle_le hX₂ hy
    (smoothSaddlePoint_pos hX₁ hy)
  have hchange := smoothSaddlePhase_sub_same_sigma X₁ X₂ y
    (smoothSaddlePoint X₁ y)
  linarith

end

end Tao2026
