import Tao2026.SmoothNumberSaddlePhase

/-!
# The tilted smooth-number distribution

The finite Euler product at a positive real parameter is the normalizing
factor of a probability distribution on positive `y`-smooth integers.  This
file makes that elementary but important bridge exact.  It also rewrites the
finite count `Psi(X,y)` as the saddle exponential times a bounded cutoff
factor.  Consequently the missing saddle-point asymptotic is reduced to a
local-limit estimate for this explicit tilted distribution, rather than an
unconnected asymptotic interface.
-/

namespace Tao2026

noncomputable section

/-- The normalized tilted mass of a positive `y`-smooth integer. -/
noncomputable def smoothTiltedMass (y : ℕ) (sigma : ℝ)
    (n : Nat.smoothNumbers (y + 1)) : ℝ :=
  (n.1 : ℝ) ^ (-sigma) / smoothDirichletSeries (y + 1) sigma

/-- In the positive half-plane, the source smooth Dirichlet series is exactly
the exponential of the zeroth saddle sum. -/
theorem smoothDirichletSeries_source_eq_exp_phiZero
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    smoothDirichletSeries (y + 1) sigma =
      Real.exp (smoothSaddlePhiZero y sigma) := by
  rw [smoothDirichletSeries_source_eq_eulerProduct y hsigma,
    ← exp_smoothSaddlePhiZero y hsigma]

/-- The source smooth Dirichlet series is positive at every positive real
parameter. -/
theorem smoothDirichletSeries_source_pos
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < smoothDirichletSeries (y + 1) sigma := by
  rw [smoothDirichletSeries_source_eq_exp_phiZero y hsigma]
  exact Real.exp_pos _

/-- The tilted masses form a summable family. -/
theorem summable_smoothTiltedMass
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Summable (smoothTiltedMass y sigma) := by
  exact ((summable_smoothDirichletSeries_and_eq_eulerProduct
    (y + 1) hsigma).1).div_const _

/-- Every tilted mass is strictly positive. -/
theorem smoothTiltedMass_pos
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma)
    (n : Nat.smoothNumbers (y + 1)) :
    0 < smoothTiltedMass y sigma n := by
  unfold smoothTiltedMass
  have hn0 : n.1 ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers n.2
  exact div_pos (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0) _)
    (smoothDirichletSeries_source_pos y hsigma)

/-- Exact normalization of the tilted distribution. -/
theorem tsum_smoothTiltedMass_eq_one
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    ∑' n : Nat.smoothNumbers (y + 1), smoothTiltedMass y sigma n = 1 := by
  unfold smoothTiltedMass
  rw [tsum_div_const]
  change smoothDirichletSeries (y + 1) sigma /
      smoothDirichletSeries (y + 1) sigma = 1
  exact div_self (smoothDirichletSeries_source_pos y hsigma).ne'

/-- The logarithm of the normalizing factor of the tilted distribution. -/
noncomputable def smoothTiltedLogPartition (y : ℕ) (sigma : ℝ) : ℝ :=
  Real.log (smoothDirichletSeries (y + 1) sigma)

/-- On the positive half-plane the tilted log-partition function is exactly
the zeroth saddle sum. -/
theorem smoothTiltedLogPartition_eq_phiZero
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    smoothTiltedLogPartition y sigma = smoothSaddlePhiZero y sigma := by
  unfold smoothTiltedLogPartition
  rw [smoothDirichletSeries_source_eq_exp_phiZero y hsigma,
    Real.log_exp]

/-- The first logarithmic derivative of the tilted partition function is
minus the first saddle sum.  Probabilistically, its negative is the mean of
the logarithmic size. -/
theorem hasDerivAt_smoothTiltedLogPartition
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    HasDerivAt (smoothTiltedLogPartition y)
      (-smoothSaddlePhiOne y sigma) sigma := by
  have heq : smoothTiltedLogPartition y =ᶠ[nhds sigma]
      smoothSaddlePhiZero y := by
    filter_upwards [Ioi_mem_nhds hsigma] with s hs
    exact smoothTiltedLogPartition_eq_phiZero y hs
  exact (hasDerivAt_smoothSaddlePhiZero y hsigma).congr_of_eventuallyEq heq

/-- The second logarithmic derivative of the tilted partition function is
the positive second saddle sum.  This is the exact variance/curvature
identity used by the Gaussian approximation. -/
theorem hasDerivAt_deriv_smoothTiltedLogPartition
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    HasDerivAt (fun s => deriv (smoothTiltedLogPartition y) s)
      (smoothSaddlePhiTwo y sigma) sigma := by
  have heq : (fun s => deriv (smoothTiltedLogPartition y) s) =ᶠ[nhds sigma]
      (fun s => -smoothSaddlePhiOne y s) := by
    filter_upwards [Ioi_mem_nhds hsigma] with s hs
    exact (hasDerivAt_smoothTiltedLogPartition y hs).deriv
  simpa using
    ((hasDerivAt_smoothSaddlePhiOne y hsigma).neg).congr_of_eventuallyEq heq

/-- The cutoff expectation appearing after exponential tilting.  Its summand
is `(n/X)^sigma` times the normalized tilted mass of `n`. -/
noncomputable def smoothSaddleCutoffFactor
    (X y : ℕ) (sigma : ℝ) : ℝ :=
  (∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
      ((n : ℝ) / X) ^ sigma * (n : ℝ) ^ (-sigma)) /
    smoothDirichletSeries (y + 1) sigma

/-- A single cutoff summand untwists exactly after multiplication by
`X^sigma`. -/
theorem rpow_mul_cutoff_tilt_eq_one
    {X n : ℕ} (hX : 1 ≤ X) (hn : n ≠ 0) {sigma : ℝ} :
    (X : ℝ) ^ sigma *
        (((n : ℝ) / X) ^ sigma * (n : ℝ) ^ (-sigma)) = 1 := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [Real.div_rpow hnpos.le hXpos.le]
  calc
    (X : ℝ) ^ sigma *
        ((n : ℝ) ^ sigma / (X : ℝ) ^ sigma * (n : ℝ) ^ (-sigma)) =
        (n : ℝ) ^ sigma * (n : ℝ) ^ (-sigma) := by
          field_simp [(Real.rpow_pos_of_pos hXpos sigma).ne']
    _ = 1 := by
      rw [← Real.rpow_add hnpos]
      simp

/-- Exact exponential-tilting identity for the finite smooth-number count.
At the chosen saddle this is the probabilistic starting point of the local
central-limit calculation. -/
theorem psiNat_cast_eq_exp_phase_mul_smoothSaddleCutoffFactor
    {X y : ℕ} (hX : 1 ≤ X) {sigma : ℝ} (hsigma : 0 < sigma) :
    (psiNat X y : ℝ) =
      Real.exp (smoothSaddlePhase X y sigma) *
        smoothSaddleCutoffFactor X y sigma := by
  have hZne : smoothDirichletSeries (y + 1) sigma ≠ 0 :=
    (smoothDirichletSeries_source_pos y hsigma).ne'
  rw [← rpow_mul_sourceEulerProduct_eq_exp_smoothSaddlePhase hX hsigma]
  rw [← smoothDirichletSeries_source_eq_eulerProduct y hsigma]
  unfold smoothSaddleCutoffFactor
  symm
  calc
    (X : ℝ) ^ sigma * smoothDirichletSeries (y + 1) sigma *
        ((∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
          ((n : ℝ) / X) ^ sigma * (n : ℝ) ^ (-sigma)) /
            smoothDirichletSeries (y + 1) sigma) =
        (X : ℝ) ^ sigma *
          (∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
            ((n : ℝ) / X) ^ sigma * (n : ℝ) ^ (-sigma)) := by
          field_simp [hZne]
    _ = ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1), (1 : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [rpow_mul_cutoff_tilt_eq_one hX
        (Nat.ne_zero_of_mem_smoothNumbers
          (Nat.mem_smoothNumbersUpTo.mp hn).2)]
    _ = (psiNat X y : ℝ) := by simp [psiNat]

/-- Every summand of the cutoff expectation is nonnegative. -/
theorem smoothSaddleCutoffFactor_nonneg
    (X y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    0 ≤ smoothSaddleCutoffFactor X y sigma := by
  unfold smoothSaddleCutoffFactor
  exact div_nonneg (Finset.sum_nonneg fun n _ =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg (by positivity) _))
    (smoothDirichletSeries_source_pos y hsigma).le

/-- The cutoff expectation is at most one. -/
theorem smoothSaddleCutoffFactor_le_one
    {X y : ℕ} (hX : 1 ≤ X) {sigma : ℝ} (hsigma : 0 < sigma) :
    smoothSaddleCutoffFactor X y sigma ≤ 1 := by
  have hphasePos : 0 < Real.exp (smoothSaddlePhase X y sigma) := Real.exp_pos _
  have hrankin := psiNat_cast_le_rpow_mul_sourceEulerProduct
    (X := X) (y := y) (sigma := sigma) hX hsigma
  rw [rpow_mul_sourceEulerProduct_eq_exp_smoothSaddlePhase hX hsigma] at hrankin
  apply le_of_mul_le_mul_left (a := Real.exp (smoothSaddlePhase X y sigma)) _ hphasePos
  rw [← psiNat_cast_eq_exp_phase_mul_smoothSaddleCutoffFactor hX hsigma,
    mul_one]
  exact hrankin

/-- At the exact saddle, `Psi(X,y)` is the saddle exponential times an
explicit factor in `[0,1]`. -/
theorem psiNat_cast_eq_saddle_exp_mul_cutoffFactor
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    (psiNat X y : ℝ) =
      Real.exp (smoothSaddlePhase X y (smoothSaddlePoint X y)) *
        smoothSaddleCutoffFactor X y (smoothSaddlePoint X y) :=
  psiNat_cast_eq_exp_phase_mul_smoothSaddleCutoffFactor
    (show 1 ≤ X by omega) (smoothSaddlePoint_pos hX hy)

/-- The Gaussian scale multiplying the tilted cutoff factor at the exact
saddle.  Its reciprocal is the denominator in the saddle main term. -/
noncomputable def smoothSaddleGaussianScale (X y : ℕ) : ℝ :=
  smoothSaddlePoint X y *
    Real.sqrt (2 * Real.pi *
      smoothSaddlePhiTwo y (smoothSaddlePoint X y))

/-- The Gaussian scale is positive in the defining range. -/
theorem smoothSaddleGaussianScale_pos
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    0 < smoothSaddleGaussianScale X y := by
  unfold smoothSaddleGaussianScale
  exact mul_pos (smoothSaddlePoint_pos hX hy)
    (Real.sqrt_pos.2 (mul_pos
      (mul_pos (by norm_num) Real.pi_pos)
      (smoothSaddlePhiTwo_pos hy (smoothSaddlePoint_pos hX hy))))

/-- Exact local-limit reformulation of the saddle ratio.  The remaining
Gaussian analysis has the precise target that the right-hand side tends to
one in the critical regime. -/
theorem psiNat_div_smoothSaddleMainTerm_eq_cutoffFactor_mul_gaussianScale
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    (psiNat X y : ℝ) / smoothSaddleMainTerm X y =
      smoothSaddleCutoffFactor X y (smoothSaddlePoint X y) *
        smoothSaddleGaussianScale X y := by
  rw [psiNat_cast_eq_saddle_exp_mul_cutoffFactor hX hy]
  unfold smoothSaddleMainTerm smoothSaddleGaussianScale
  field_simp [Real.exp_ne_zero]

end

end Tao2026
