import GafniTao.ExplicitFormulaSetup
import GafniTao.LocalCover
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Finite supremum estimate for a zero strip

This file proves the exact finite inequality underneath Gafni--Tao Lemma 2.2.
It retains the physical variables and the analytic multiplicities.  The later
asymptotic consumer inserts the zero-density envelope and the relation
`T = J * log(X)^2 * tau`.
-/

open Asymptotics Complex Finset Filter Set
open scoped BigOperators

namespace GafniTao

/-- A zero in the smaller real-part strip belongs to the source zero set at
its lower edge. -/
theorem zerosInRect_strip_subset_zeroSet
    {sigmaLower sigmaUpper T : ℝ} (hsigmaUpper : sigmaUpper ≤ 1) :
    RiemannZeta.GuthMaynard.zerosInRect
        sigmaLower sigmaUpper (-T) T ⊆ zeroSet sigmaLower T := by
  apply RiemannZeta.GuthMaynard.zerosInRect_subset_of_rect_subset
  exact RiemannZeta.GuthMaynard.ZeroRectangle_subset
    sigmaLower sigmaUpper (-T) T sigmaLower 1 (-T) T
      le_rfl hsigmaUpper le_rfl le_rfl

/-- Exact multiplicity count of a real-part strip is bounded by the ordinary
zero count at its lower edge. -/
theorem strip_multiplicity_sum_le_zeroCount
    {sigmaLower sigmaUpper T : ℝ} (hsigmaUpper : sigmaUpper ≤ 1) :
    (∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect
        sigmaLower sigmaUpper (-T) T, zeroMultiplicity rho) ≤
      zeroCount sigmaLower T := by
  rw [zeroCount_eq_weighted_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact zerosInRect_strip_subset_zeroSet hsigmaUpper
  · intro rho _ _
    exact Nat.zero_le _

/-- The exact finite `L∞` estimate before asymptotic exponent substitution.
Every zero is counted with analytic multiplicity and every summand is the
literal short-increment coefficient from equation (2.4). -/
theorem norm_zeroStripIncrementSum_le_count
    {sigmaLower sigmaUpper T tau x : ℝ}
    (hsigmaLowerPos : 0 < sigmaLower)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (htau : 0 < tau) (hx : 1 ≤ x) :
    ‖zeroStripIncrementSum sigmaLower sigmaUpper T tau x‖ ≤
      (x ^ sigmaUpper / tau) * zeroCount sigmaLower T := by
  classical
  rw [zeroStripIncrementSum]
  calc
    ‖∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect
          sigmaLower sigmaUpper (-T) T,
        (zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho‖
        ≤ ∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect
            sigmaLower sigmaUpper (-T) T,
          ‖(zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect
            sigmaLower sigmaUpper (-T) T,
          (zeroMultiplicity rho : ℝ) * (x ^ sigmaUpper / tau) := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hrhoMem : rho ∈ RiemannZeta.GuthMaynard.zerosInRect
          sigmaLower sigmaUpper (-T) T := by simpa using hrho
      have hrhoRect : rho ∈ RiemannZeta.GuthMaynard.ZeroRectangle
          sigmaLower sigmaUpper (-T) T := by
        rw [RiemannZeta.GuthMaynard.zerosInRect,
          Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrhoMem
        exact hrhoMem.1
      have hrhoRe : rho.re ≤ sigmaUpper :=
        (RiemannZeta.GuthMaynard.mem_ZeroRectangle
          sigmaLower sigmaUpper (-T) T rho).mp hrhoRect |>.2.1
      have hrhoNe : rho ≠ 0 :=
        ne_zero_of_mem_zerosInRect_of_pos hsigmaLowerPos hrhoMem
      rw [norm_mul, RCLike.norm_natCast]
      gcongr
      calc
        ‖zeroIncrementTerm tau x rho‖ ≤ x ^ rho.re / tau :=
          norm_zeroIncrementTerm_le htau (lt_of_lt_of_le zero_lt_one hx)
            hrhoNe (hrhoRe.trans hsigmaUpper)
        _ ≤ x ^ sigmaUpper / tau := by
          gcongr
    _ = (x ^ sigmaUpper / tau) *
          (∑ rho ∈ RiemannZeta.GuthMaynard.zerosInRect
            sigmaLower sigmaUpper (-T) T, zeroMultiplicity rho : ℝ) := by
      rw [← Finset.sum_mul]
      exact mul_comm _ _
    _ ≤ (x ^ sigmaUpper / tau) * zeroCount sigmaLower T := by
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast strip_multiplicity_sum_le_zeroCount hsigmaUpper)
        (div_nonneg (Real.rpow_nonneg (by positivity) _) htau.le)

/-- The physical truncation height used throughout Gafni--Tao Section 2:
`T = J log(X)^2 tau`, with `tau = X^(1-theta)`. -/
noncomputable def explicitFormulaHeight (J theta X : ℝ) : ℝ :=
  J * (Real.log X) ^ 2 * localTau X theta

/-- The physical height is positive on the source range. -/
theorem explicitFormulaHeight_pos {J theta X : ℝ}
    (hJ : 0 < J) (hX : 1 < X) :
    0 < explicitFormulaHeight J theta X := by
  unfold explicitFormulaHeight
  exact mul_pos (mul_pos hJ (sq_pos_of_pos (Real.log_pos hX)))
    (localTau_pos (zero_lt_one.trans hX))

/-- For `theta < 1`, the source truncation height tends to infinity with the
physical scale.  This is the filter bridge needed to compose a zero-density
estimate in `T` with `T = J log(X)^2 X^(1-theta)`. -/
theorem tendsto_explicitFormulaHeight_atTop
    {J theta : ℝ} (hJ : 0 < J) (htheta : theta < 1) :
    Tendsto (explicitFormulaHeight J theta) atTop atTop := by
  have hr : 0 < 1 - theta := sub_pos.mpr htheta
  have hbase : Tendsto (fun X : ℝ => J * X ^ (1 - theta)) atTop atTop :=
    (tendsto_rpow_atTop hr).const_mul_atTop hJ
  apply tendsto_atTop_mono' atTop _ hbase
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with X hX
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hlog : 1 ≤ Real.log X := by
    simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlogSq : 1 ≤ (Real.log X) ^ 2 := by nlinarith
  rw [explicitFormulaHeight, localTau]
  calc
    J * X ^ (1 - theta) = J * 1 * X ^ (1 - theta) := by ring
    _ ≤ J * (Real.log X) ^ 2 * X ^ (1 - theta) := by gcongr

/-- A fixed logarithmic square is absorbed by every positive real power. -/
theorem eventually_log_sq_le_rpow {q : ℝ} (hq : 0 < q) :
    ∀ᶠ X : ℝ in atTop, (Real.log X) ^ 2 ≤ X ^ q := by
  have hLittle := isLittleO_log_rpow_rpow_atTop (2 : ℝ) hq
  filter_upwards [hLittle.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with X hBound hX
  have hLogNonneg : 0 ≤ Real.log X := Real.log_nonneg hX
  have hXNonneg : 0 ≤ X := by linarith
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hLogNonneg 2),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hXNonneg q)] at hBound
  simpa [Real.rpow_two] using hBound

/-- The two logarithms and the fixed multiplier in the source height cost an
arbitrarily small power of `X`. -/
theorem eventually_explicitFormulaHeight_le_rpow
    {J theta q : ℝ} (hq : 0 < q) :
    ∀ᶠ X : ℝ in atTop,
      explicitFormulaHeight J theta X ≤ X ^ (1 - theta + q) := by
  have hhalf : 0 < q / 2 := half_pos hq
  have hLog := eventually_log_sq_le_rpow hhalf
  have hPowTop := tendsto_rpow_atTop hhalf
  filter_upwards [hLog, hPowTop.eventually (eventually_ge_atTop J),
    eventually_ge_atTop (1 : ℝ)] with X hLog hJ hX
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hPowNonneg : 0 ≤ X ^ (1 - theta) := Real.rpow_nonneg hXPos.le _
  rw [explicitFormulaHeight, localTau]
  calc
    J * (Real.log X) ^ 2 * X ^ (1 - theta)
        ≤ X ^ (q / 2) * X ^ (q / 2) * X ^ (1 - theta) := by gcongr
    _ = X ^ (q / 2 + q / 2) * X ^ (1 - theta) := by
      rw [Real.rpow_add hXPos]
    _ = X ^ (1 - theta + q) := by
      rw [← Real.rpow_add hXPos]
      congr 1
      ring

/-- Composition of an actual zero-density envelope with the paper's physical
height.  The proof explicitly spends one small exponent on the density
estimate and one on the fixed `J log(X)^2` factor. -/
theorem zeroDensityEnvelope_at_explicitFormulaHeight
    {J theta sigma a : ℝ} (hJ : 0 < J) (htheta : theta < 1)
    (ha : 0 ≤ a) (hsigma : sigma ≤ 1)
    (hDensity : ZeroDensityEnvelope sigma a) :
    EpsilonExponentBound
      (fun X => (zeroCount sigma (explicitFormulaHeight J theta X) : ℝ))
      ((1 - theta) * (a * (1 - sigma))) := by
  let r : ℝ := 1 - theta
  let d : ℝ := a * (1 - sigma)
  have hr : 0 < r := sub_pos.mpr htheta
  have hd : 0 ≤ d := mul_nonneg ha (sub_nonneg.mpr hsigma)
  unfold ZeroDensityEnvelope at hDensity
  unfold EpsilonExponentBound at hDensity ⊢
  intro eps heps
  let eta : ℝ := min 1 (eps / (2 * (r + d + 1)))
  have hsum : 0 < r + d + 1 := by linarith
  have heta : 0 < eta := by
    exact lt_min zero_lt_one (div_pos heps (mul_pos two_pos hsum))
  have hetaOne : eta ≤ 1 := min_le_left _ _
  have hetaBudget : eta * (r + d + 1) ≤ eps / 2 := by
    have hEtaLe : eta ≤ eps / (2 * (r + d + 1)) := min_le_right _ _
    calc
      eta * (r + d + 1) ≤
          (eps / (2 * (r + d + 1))) * (r + d + 1) := by gcongr
      _ = eps / 2 := by field_simp
  have hExponent : (r + eta) * (d + eta) ≤ r * d + eps := by
    have hetaNonneg : 0 ≤ eta := heta.le
    nlinarith
  have hComposed :=
    (hDensity eta heta).comp_tendsto
      (tendsto_explicitFormulaHeight_atTop hJ htheta)
  have hCompare :
      (fun X : ℝ =>
          explicitFormulaHeight J theta X ^ eta *
            |explicitFormulaHeight J theta X ^ d|) =O[atTop]
        (fun X : ℝ => X ^ eps * |X ^ (r * d)|) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_explicitFormulaHeight_le_rpow
        (J := J) (theta := theta) heta,
      eventually_ge_atTop (Real.exp 1)] with X hHeightLe hX
    have hXPos : 0 < X := (Real.exp_pos 1).trans_le hX
    have hExpOne : (1 : ℝ) < Real.exp 1 := by
      have h : Real.exp 0 < Real.exp 1 := Real.exp_lt_exp.mpr zero_lt_one
      simpa only [Real.exp_zero] using h
    have hXOne : 1 ≤ X := hExpOne.le.trans hX
    have hHeightPos : 0 < explicitFormulaHeight J theta X :=
      explicitFormulaHeight_pos hJ (hExpOne.trans_le hX)
    have hPower : 0 ≤ d + eta := add_nonneg hd heta.le
    have hHeightPower :
        explicitFormulaHeight J theta X ^ (d + eta) ≤
          X ^ ((r + eta) * (d + eta)) := by
      calc
        explicitFormulaHeight J theta X ^ (d + eta) ≤
            (X ^ (r + eta)) ^ (d + eta) :=
          Real.rpow_le_rpow hHeightPos.le hHeightLe hPower
        _ = X ^ ((r + eta) * (d + eta)) :=
          (Real.rpow_mul hXPos.le _ _).symm
    have hToTarget : X ^ ((r + eta) * (d + eta)) ≤ X ^ (r * d + eps) :=
      Real.rpow_le_rpow_of_exponent_le hXOne hExponent
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hHeightPos.le eta)
        (abs_nonneg _)), one_mul,
      abs_of_nonneg (Real.rpow_nonneg hHeightPos.le d),
      ← Real.rpow_add hHeightPos,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hXPos.le eps)
        (abs_nonneg _)),
      abs_of_nonneg (Real.rpow_nonneg hXPos.le (r * d)),
      ← Real.rpow_add hXPos]
    simpa only [add_comm] using hHeightPower.trans hToTarget
  simpa only [Function.comp_def, r, d, mul_assoc] using hComposed.trans hCompare

/-- The physical majorant obtained after the finite strip estimate: the
factor `X^(theta+sigmaUpper-1)` is exactly `X^sigmaUpper / tau`. -/
noncomputable def zeroStripPhysicalMajorant
    (J theta sigmaLower sigmaUpper X : ℝ) : ℝ :=
  X ^ (theta + sigmaUpper - 1) *
    (zeroCount sigmaLower (explicitFormulaHeight J theta X) : ℝ)

/-- Source exponent form of Lemma 2.2 for the exact physical majorant.  This
theorem consumes the actual ordinary zero-density envelope and the proved
height-composition theorem above. -/
theorem zeroStripPhysicalMajorant_epsilonBound
    {J theta sigmaLower sigmaUpper a : ℝ}
    (hJ : 0 < J) (htheta : theta < 1) (ha : 0 ≤ a)
    (hsigmaLower : sigmaLower ≤ 1)
    (hDensity : ZeroDensityEnvelope sigmaLower a) :
    EpsilonExponentBound
      (zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper)
      ((1 - theta) * (a * (1 - sigmaLower)) + theta + sigmaUpper - 1) := by
  have hPhysical := zeroDensityEnvelope_at_explicitFormulaHeight
    hJ htheta ha hsigmaLower hDensity
  unfold EpsilonExponentBound at hPhysical ⊢
  have hScaled :=
    RiemannZeta.GuthMaynard.EpsilonPowerBound.mul_left_rpow
      hPhysical (theta + sigmaUpper - 1)
  intro eps heps
  have h := hScaled eps heps
  apply h.congr'
  · exact Eventually.of_forall fun X => by
      simp only [zeroStripPhysicalMajorant]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hpow :
        X ^ (theta + sigmaUpper - 1) *
            X ^ ((1 - theta) * (a * (1 - sigmaLower))) =
          X ^ ((1 - theta) * (a * (1 - sigmaLower)) +
            theta + sigmaUpper - 1) := by
      rw [← Real.rpow_add hX]
      congr 1
      ring
    rw [hpow]

/-- Exact exponent arithmetic for the physical factor `X^sigma / tau`. -/
theorem rpow_div_localTau
    {X theta sigma : ℝ} (hX : 0 < X) :
    X ^ sigma / localTau X theta = X ^ (theta + sigma - 1) := by
  rw [localTau, ← Real.rpow_sub hX]
  congr 1
  ring

/-- Uniform finite form of Lemma 2.2 on the physical interval
`X <= x <= 2X`.  The only fixed constant left outside the source majorant is
`2^sigmaUpper`; all zero multiplicities and the literal strip sum remain
visible in the conclusion. -/
theorem norm_zeroStripIncrementSum_le_physicalMajorant
    {J theta sigmaLower sigmaUpper X x : ℝ}
    (hX : 1 ≤ X) (hxLower : X ≤ x)
    (hxUpper : x ≤ 2 * X) (hsigmaLowerPos : 0 < sigmaLower)
    (hsigmaUpperNonneg : 0 ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    ‖zeroStripIncrementSum sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) x‖ ≤
      2 ^ sigmaUpper *
        zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X := by
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hxPos : 0 < x := hXPos.trans_le hxLower
  have htau : 0 < localTau X theta := localTau_pos hXPos
  have hFinite := norm_zeroStripIncrementSum_le_count
    (T := explicitFormulaHeight J theta X)
    hsigmaLowerPos hsigmaUpper htau (hX.trans hxLower)
  refine hFinite.trans ?_
  have hxPow : x ^ sigmaUpper ≤ (2 * X) ^ sigmaUpper :=
    Real.rpow_le_rpow hxPos.le hxUpper hsigmaUpperNonneg
  have hScale : x ^ sigmaUpper / localTau X theta ≤
      2 ^ sigmaUpper * X ^ (theta + sigmaUpper - 1) := by
    calc
      x ^ sigmaUpper / localTau X theta ≤
          (2 * X) ^ sigmaUpper / localTau X theta := by gcongr
      _ = (2 ^ sigmaUpper * X ^ sigmaUpper) / localTau X theta := by
        rw [Real.mul_rpow (by norm_num) hXPos.le]
      _ = 2 ^ sigmaUpper * (X ^ sigmaUpper / localTau X theta) := by ring
      _ = 2 ^ sigmaUpper * X ^ (theta + sigmaUpper - 1) := by
        rw [rpow_div_localTau hXPos]
  unfold zeroStripPhysicalMajorant
  have hCountNonneg :
      0 ≤ (zeroCount sigmaLower (explicitFormulaHeight J theta X) : ℝ) := by
    positivity
  calc
    (x ^ sigmaUpper / localTau X theta) *
        (zeroCount sigmaLower (explicitFormulaHeight J theta X) : ℝ)
        ≤ (2 ^ sigmaUpper * X ^ (theta + sigmaUpper - 1)) *
          (zeroCount sigmaLower (explicitFormulaHeight J theta X) : ℝ) := by
            gcongr
    _ = 2 ^ sigmaUpper *
        (X ^ (theta + sigmaUpper - 1) *
          (zeroCount sigmaLower (explicitFormulaHeight J theta X) : ℝ)) := by
            ring

/-- The literal source supremum over `X <= x <= 2X`. -/
noncomputable def zeroStripPhysicalSup
    (J theta sigmaLower sigmaUpper X : ℝ) : ℝ :=
  sSup ((fun x : ℝ =>
    ‖zeroStripIncrementSum sigmaLower sigmaUpper
      (explicitFormulaHeight J theta X) (localTau X theta) x‖) ''
        Set.Icc X (2 * X))

/-- Exact finite supremum inequality underlying Gafni--Tao Lemma 2.2. -/
theorem zeroStripPhysicalSup_le_majorant
    {J theta sigmaLower sigmaUpper X : ℝ}
    (hX : 1 ≤ X) (hsigmaLowerPos : 0 < sigmaLower)
    (hsigmaUpperNonneg : 0 ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    zeroStripPhysicalSup J theta sigmaLower sigmaUpper X ≤
      2 ^ sigmaUpper *
        zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X := by
  unfold zeroStripPhysicalSup
  apply csSup_le
  · refine ⟨‖zeroStripIncrementSum sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X‖, ?_⟩
    exact ⟨X, ⟨le_rfl, by nlinarith⟩, rfl⟩
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact norm_zeroStripIncrementSum_le_physicalMajorant
      hX hx.1 hx.2 hsigmaLowerPos hsigmaUpperNonneg hsigmaUpper

/-- Full source-form Lemma 2.2: the `L∞` supremum satisfies the exact
epsilon exponent, and the proof term consumes both the literal strip sum and
the actual ordinary zero-density envelope. -/
theorem zeroStripPhysicalSup_epsilonBound
    {J theta sigmaLower sigmaUpper a : ℝ}
    (hJ : 0 < J) (hthetaUpper : theta < 1)
    (ha : 0 ≤ a) (hsigmaLowerPos : 0 < sigmaLower)
    (hsigmaLowerUpper : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hDensity : ZeroDensityEnvelope sigmaLower a) :
    EpsilonExponentBound
      (zeroStripPhysicalSup J theta sigmaLower sigmaUpper)
      ((1 - theta) * (a * (1 - sigmaLower)) + theta + sigmaUpper - 1) := by
  have hsigmaUpperNonneg : 0 ≤ sigmaUpper :=
    hsigmaLowerPos.le.trans hsigmaLowerUpper
  have hMajorant := zeroStripPhysicalMajorant_epsilonBound
    (sigmaUpper := sigmaUpper) hJ hthetaUpper ha
      (hsigmaLowerUpper.trans hsigmaUpper) hDensity
  have hSupToMajorant :
      RiemannZeta.GuthMaynard.EpsilonPowerBound
        (zeroStripPhysicalSup J theta sigmaLower sigmaUpper)
        (zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper) := by
    intro eps heps
    have hFixed :
        (fun X : ℝ =>
          |zeroStripPhysicalSup J theta sigmaLower sigmaUpper X|) =O[atTop]
          (fun X : ℝ =>
            |zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X|) := by
      apply IsBigO.of_bound (2 ^ sigmaUpper)
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
      have hSupLe := zeroStripPhysicalSup_le_majorant
        (J := J) (theta := theta) hX hsigmaLowerPos
          hsigmaUpperNonneg hsigmaUpper
      have hMajorantNonneg :
          0 ≤ zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X := by
        unfold zeroStripPhysicalMajorant
        positivity
      have hSetBounded : BddAbove
          ((fun x : ℝ =>
            ‖zeroStripIncrementSum sigmaLower sigmaUpper
              (explicitFormulaHeight J theta X) (localTau X theta) x‖) ''
                Set.Icc X (2 * X)) := by
        refine ⟨2 ^ sigmaUpper *
          zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X, ?_⟩
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact norm_zeroStripIncrementSum_le_physicalMajorant
          (J := J) (theta := theta) hX hx.1 hx.2 hsigmaLowerPos
            hsigmaUpperNonneg hsigmaUpper
      have hSupNonneg :
          0 ≤ zeroStripPhysicalSup J theta sigmaLower sigmaUpper X := by
        unfold zeroStripPhysicalSup
        have hElem :
            ‖zeroStripIncrementSum sigmaLower sigmaUpper
              (explicitFormulaHeight J theta X) (localTau X theta) X‖ ∈
              ((fun x : ℝ =>
                ‖zeroStripIncrementSum sigmaLower sigmaUpper
                  (explicitFormulaHeight J theta X) (localTau X theta) x‖) ''
                    Set.Icc X (2 * X)) :=
          ⟨X, ⟨le_rfl, by nlinarith⟩, rfl⟩
        exact (norm_nonneg _).trans (le_csSup hSetBounded hElem)
      simp only [Real.norm_eq_abs,
        abs_of_nonneg hSupNonneg, abs_of_nonneg hMajorantNonneg]
      simpa only [mul_comm] using hSupLe
    exact hFixed.trans
      ((RiemannZeta.GuthMaynard.EpsilonPowerBound.refl
        (zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper)) eps heps)
  exact hSupToMajorant.trans hMajorant

end GafniTao
