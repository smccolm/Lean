import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import RiemannZeta.GuthMaynard.DFIEquation24
import RiemannZeta.GuthMaynard.DFIPointwise

/-!
# DFI equation (28): derivatives of the localized delta weight

This module develops the quantitative derivative input used for the Bessel
integration by parts in DFI equation (28).  The first results are exact:
they differentiate an individual delta-kernel summand and then the locally
finite delta series.  The uniform bounds are assembled from the explicit
derivative profile of equations (2) and (13).
-/

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff Topology
open Classical

namespace RiemannZeta.GuthMaynard

/-- Exact positive-order derivative of one summand of the DFI delta kernel. -/
theorem iteratedDeriv_dfiDeltaSummand
    {Q : ℝ} (w : DFIDeltaWeight Q) (q r k : ℕ) (hk : 0 < k) (u : ℝ) :
    iteratedDeriv k (dfiDeltaSummand w q r) u =
      -(((q * r : ℕ) : ℝ)⁻¹ ^ (k + 1) *
        iteratedDeriv k w.toFun (u / (q * r : ℕ))) := by
  unfold dfiDeltaSummand
  rw [iteratedDeriv_div_const]
  rw [iteratedDeriv_const_sub hk]
  rw [iteratedDeriv_neg]
  have hcomp := iteratedDeriv_comp_const_mul
    (n := k) (w.smooth.of_le (by exact_mod_cast le_top))
    (((q * r : ℕ) : ℝ)⁻¹)
  have hfun : (fun z : ℝ => w (z / (q * r : ℕ))) =
      fun z : ℝ => w ((((q * r : ℕ) : ℝ)⁻¹) * z) := by
    funext z
    rw [div_eq_mul_inv, mul_comm]
  rw [hfun, hcomp]
  rw [div_eq_mul_inv]
  ring

/-- The whole-line `L¹` norm of a positive derivative of one delta-kernel
summand has the exact scaling predicted by DFI (28).  The factor
`(qr)⁻¹` already present in the summand combines with the `k` chain-rule
factors and the change-of-variables Jacobian, leaving `(qr)⁻ᵏ`. -/
theorem integral_norm_iteratedDeriv_dfiDeltaSummand
    {Q : ℝ} (w : DFIDeltaWeight Q) (q r k : ℕ)
    (hq : 0 < q) (hr : 0 < r) (hk : 0 < k) :
    (∫ u : ℝ, ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖) =
      ((((q * r : ℕ) : ℝ) ^ k)⁻¹) *
        ∫ v : ℝ, ‖iteratedDeriv k w.toFun v‖ := by
  have hqr : (0 : ℝ) < ((q * r : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hq hr
  have hpoint (u : ℝ) :
      ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖ =
        ((((q * r : ℕ) : ℝ)⁻¹) ^ (k + 1)) *
          ‖iteratedDeriv k w.toFun
            (u * (((q * r : ℕ) : ℝ)⁻¹))‖ := by
    rw [iteratedDeriv_dfiDeltaSummand w q r k hk u, norm_neg,
      norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hqr.le) _)]
    congr 2
  rw [MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hpoint),
    MeasureTheory.integral_const_mul]
  rw [MeasureTheory.Measure.integral_comp_mul_right
    (fun v : ℝ => ‖iteratedDeriv k w.toFun v‖)
    (((q * r : ℕ) : ℝ)⁻¹)]
  have habs : |((((q * r : ℕ) : ℝ)⁻¹)⁻¹)| = ((q * r : ℕ) : ℝ) := by
    rw [inv_inv, abs_of_pos hqr]
  rw [habs, pow_succ]
  simp only [smul_eq_mul]
  field_simp [hqr.ne']
  rw [one_div, inv_pow]
  calc
    (((((q * r : ℕ) : ℝ) ^ k)⁻¹ *
        ∫ y : ℝ, ‖iteratedDeriv k w.toFun y‖) *
          ((q * r : ℕ) : ℝ) ^ k) =
        (((((q * r : ℕ) : ℝ) ^ k)⁻¹ *
          ((q * r : ℕ) : ℝ) ^ k) *
            ∫ y : ℝ, ‖iteratedDeriv k w.toFun y‖) := by ring
    _ = _ := by
      rw [inv_mul_cancel₀ (pow_ne_zero k hqr.ne'), one_mul]

/-- Around each point, one fixed finite sum represents the delta kernel. -/
theorem dfiDeltaKernel_eventuallyEq_fixedSum
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q) (u₀ : ℝ) :
    dfiDeltaKernel w q =ᶠ[nhds u₀]
      fun u => ∑ r ∈ Finset.Icc 1 (⌈2 * Q + (|u₀| + 1) / Q⌉₊ + 1),
        dfiDeltaSummand w q r u := by
  filter_upwards [dfiDeltaSummand_eq_zero_eventually_outside w q hq u₀] with u hu
  rw [dfiDeltaKernel_eq_tsum w q hq u]
  rw [tsum_eq_sum
    (s := Finset.Icc 1 (⌈2 * Q + (|u₀| + 1) / Q⌉₊ + 1))
    (fun r hr => by simpa [dfiDeltaSummand] using hu r hr)]
  rfl

/-- On the closed interval `[-U,U]`, every derivative of the delta kernel
is represented by one common finite sum.  Enlarging the source radius from
`U` to `U+1` supplies a neighborhood of every point, which is essential:
derivatives cannot be obtained from a merely pointwise identity. -/
theorem iteratedDeriv_dfiDeltaKernel_eq_uniform_sum
    {Q : ℝ} (w : DFIDeltaWeight Q) (q k U : ℕ) (hq : 0 < q)
    {u : ℝ} (hu : u ∈ Set.Icc (-(U : ℝ)) (U : ℝ)) :
    iteratedDeriv k (dfiDeltaKernel w q) u =
      ∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q (U + 1)),
        iteratedDeriv k (dfiDeltaSummand w q r) u := by
  let R := dfiDeltaRadius Q (U + 1)
  let fixed : ℝ → ℝ := fun z =>
    ∑ r ∈ Finset.Icc 1 R, dfiDeltaSummand w q r z
  have heq : dfiDeltaKernel w q =ᶠ[nhds u] fixed := by
    have hball : Metric.ball u 1 ∈ nhds u :=
      Metric.ball_mem_nhds u (by norm_num)
    filter_upwards [hball] with z hz
    have hzu : |z - u| < 1 := by simpa [Real.dist_eq] using hz
    have huabs : |u| ≤ U := by simpa [abs_le] using hu
    have hzabs : |z| ≤ (U + 1 : ℕ) := by
      calc
        |z| = |(z - u) + u| := by ring_nf
        _ ≤ |z - u| + |u| := abs_add_le _ _
        _ ≤ 1 + (U : ℝ) := by linarith
        _ = (U + 1 : ℕ) := by norm_num; ring
    simpa [fixed, R, dfiDeltaSummand] using
      dfiDeltaKernel_eq_uniform_sum w q hq z (U + 1) hzabs
  rw [Filter.EventuallyEq.iteratedDeriv_eq k heq]
  have hsum := iteratedDeriv_fun_sum
    (I := Finset.Icc 1 R) (f := fun r => dfiDeltaSummand w q r)
    (x := u) (n := k) (fun r _hr =>
      (contDiff_dfiDeltaSummand w q r).contDiffAt.of_le
        (by exact_mod_cast le_top))
  simpa [fixed, R] using hsum

/-- Exact finite-sum `L¹` majorant for a positive derivative of the DFI
delta kernel on its physical displacement interval.  No supremum bound is
used: every summand is integrated on the whole line and rescaled exactly,
which is what preserves the mass in DFI (30). -/
theorem integral_Icc_norm_iteratedDeriv_dfiDeltaKernel_le_sum
    {Q : ℝ} (w : DFIDeltaWeight Q) (q k U : ℕ)
    (hq : 0 < q) (hk : 0 < k) :
    (∫ u in Set.Icc (-(U : ℝ)) (U : ℝ),
        ‖iteratedDeriv k (dfiDeltaKernel w q) u‖) ≤
      (∫ v : ℝ, ‖iteratedDeriv k w.toFun v‖) *
        ∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q (U + 1)),
          ((((q * r : ℕ) : ℝ) ^ k)⁻¹) := by
  let R := dfiDeltaRadius Q (U + 1)
  let S := Finset.Icc 1 R
  let F : ℝ → ℝ := fun u =>
    ‖∑ r ∈ S, iteratedDeriv k (dfiDeltaSummand w q r) u‖
  let G : ℝ → ℝ := fun u =>
    ∑ r ∈ S, ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖
  have htermDerivCont (r : ℕ) : Continuous
      (iteratedDeriv k (dfiDeltaSummand w q r)) := by
    exact (contDiff_dfiDeltaSummand w q r).continuous_iteratedDeriv k
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top k)))
  have htermCont (r : ℕ) : Continuous
      (fun u : ℝ => ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖) :=
    (htermDerivCont r).norm
  have hFCont : Continuous F := by
    dsimp only [F]
    exact (continuous_finsetSum _ fun r _hr =>
      htermDerivCont r).norm
  have hGCont : Continuous G := by
    dsimp only [G]
    exact continuous_finsetSum _ fun r _hr => htermCont r
  have hFInt : IntegrableOn F (Set.Icc (-(U : ℝ)) (U : ℝ)) :=
    hFCont.continuousOn.integrableOn_compact isCompact_Icc
  have hGInt : IntegrableOn G (Set.Icc (-(U : ℝ)) (U : ℝ)) :=
    hGCont.continuousOn.integrableOn_compact isCompact_Icc
  have hkernel :
      (∫ u in Set.Icc (-(U : ℝ)) (U : ℝ),
          ‖iteratedDeriv k (dfiDeltaKernel w q) u‖) =
        ∫ u in Set.Icc (-(U : ℝ)) (U : ℝ), F u := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    intro u hu
    change ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ = F u
    rw [iteratedDeriv_dfiDeltaKernel_eq_uniform_sum w q k U hq hu]
  have htriangle :
      (∫ u in Set.Icc (-(U : ℝ)) (U : ℝ), F u) ≤
        ∫ u in Set.Icc (-(U : ℝ)) (U : ℝ), G u := by
    exact MeasureTheory.setIntegral_mono_on hFInt hGInt measurableSet_Icc
      (fun u _hu => by
        dsimp only [F, G]
        exact norm_sum_le _ _)
  have htermInt (r : ℕ) (hrS : r ∈ S) : Integrable
      (fun u : ℝ => ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖) := by
    have hr : 0 < r := (Finset.mem_Icc.mp hrS).1
    have hqr : (0 : ℝ) < ((q * r : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hq hr
    have hsupp : Function.support
        (iteratedDeriv k (dfiDeltaSummand w q r)) ⊆
          Set.Icc (-(2 * Q * ((q * r : ℕ) : ℝ)))
            (2 * Q * ((q * r : ℕ) : ℝ)) := by
      intro u hu
      change iteratedDeriv k (dfiDeltaSummand w q r) u ≠ 0 at hu
      rw [iteratedDeriv_dfiDeltaSummand w q r k hk u] at hu
      have hwne : iteratedDeriv k w.toFun (u / (q * r : ℕ)) ≠ 0 := by
        intro hw
        apply hu
        rw [hw, mul_zero, neg_zero]
      have hwmem := support_iteratedDeriv_dfiWeight_subset w k hwne
      rw [Set.mem_Icc, ← abs_le] at hwmem ⊢
      rw [abs_div, abs_of_pos hqr] at hwmem
      exact (div_le_iff₀ hqr).mp hwmem
    have hcompact : HasCompactSupport
        (iteratedDeriv k (dfiDeltaSummand w q r)) :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
    exact (htermCont r).integrable_of_hasCompactSupport hcompact.norm
  rw [hkernel]
  calc
    (∫ u in Set.Icc (-(U : ℝ)) (U : ℝ), F u) ≤
        ∫ u in Set.Icc (-(U : ℝ)) (U : ℝ), G u := htriangle
    _ = ∑ r ∈ S,
        ∫ u in Set.Icc (-(U : ℝ)) (U : ℝ),
          ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖ := by
      dsimp only [G]
      rw [MeasureTheory.integral_finsetSum S]
      intro r hr
      exact (htermInt r hr).integrableOn
    _ ≤ ∑ r ∈ S,
        ∫ u : ℝ, ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖ := by
      apply Finset.sum_le_sum
      intro r hr
      exact setIntegral_le_integral_of_nonneg _ (htermInt r hr)
        (fun _ => norm_nonneg _) _
    _ = ∑ r ∈ S,
        ((((q * r : ℕ) : ℝ) ^ k)⁻¹) *
          ∫ v : ℝ, ‖iteratedDeriv k w.toFun v‖ := by
      apply Finset.sum_congr rfl
      intro r hr
      exact integral_norm_iteratedDeriv_dfiDeltaSummand w q r k hq
        (Finset.mem_Icc.mp hr).1 hk
    _ = (∫ v : ℝ, ‖iteratedDeriv k w.toFun v‖) *
        ∑ r ∈ S, ((((q * r : ℕ) : ℝ) ^ k)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = _ := by rfl

/-- The frequency sum in the integrated delta derivative costs at most one
harmonic factor.  This is sharp at derivative order one; all higher orders
are dominated by it. -/
theorem sum_Icc_inv_pow_mul_le_harmonic
    (q k R : ℕ) (hq : 0 < q) (hk : 0 < k) :
    (∑ r ∈ Finset.Icc 1 R, ((((q * r : ℕ) : ℝ) ^ k)⁻¹)) ≤
      (((q : ℝ) ^ k)⁻¹) * (harmonic R : ℝ) := by
  calc
    (∑ r ∈ Finset.Icc 1 R, ((((q * r : ℕ) : ℝ) ^ k)⁻¹)) =
        ∑ r ∈ Finset.Icc 1 R,
          (((q : ℝ) ^ k)⁻¹) * (((r : ℝ) ^ k)⁻¹) := by
      apply Finset.sum_congr rfl
      intro r _hr
      push_cast
      rw [mul_pow, mul_inv_rev]
      ring
    _ ≤ ∑ r ∈ Finset.Icc 1 R,
        (((q : ℝ) ^ k)⁻¹) * (r : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro r hr
      have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
      have hrone : (1 : ℝ) ≤ r := by exact_mod_cast hrpos
      have hpow : (r : ℝ) ^ 1 ≤ (r : ℝ) ^ k :=
        pow_le_pow_right₀ hrone hk
      have hinv : (((r : ℝ) ^ k)⁻¹) ≤ (((r : ℝ) ^ 1)⁻¹) :=
        inv_anti₀ (by positivity) hpow
      exact mul_le_mul_of_nonneg_left (by simpa using hinv) (by positivity)
    _ = (((q : ℝ) ^ k)⁻¹) *
        ∑ r ∈ Finset.Icc 1 R, (r : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ = (((q : ℝ) ^ k)⁻¹) * (harmonic R : ℝ) := by
      congr 1
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- Integrated derivative profile for the DFI delta kernel.  Compared with
the pointwise equation-(28) bound, one power of `qQ` is recovered by exact
integration; the only endpoint loss is the explicit harmonic number of the
uniform source radius. -/
theorem integral_Icc_norm_iteratedDeriv_dfiDeltaKernel_le_of_profile
    {Q : ℝ} {w : DFIDeltaWeight Q} {D : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D) (q k U : ℕ)
    (hq : 0 < q) (hk : 0 < k) :
    (∫ u in Set.Icc (-(U : ℝ)) (U : ℝ),
        ‖iteratedDeriv k (dfiDeltaKernel w q) u‖) ≤
      (4 * D k * Q * (Q ^ (k + 1))⁻¹) *
        (((q : ℝ) ^ k)⁻¹) *
          (harmonic (dfiDeltaRadius Q (U + 1)) : ℝ) := by
  let R := dfiDeltaRadius Q (U + 1)
  have hraw := integral_Icc_norm_iteratedDeriv_dfiDeltaKernel_le_sum
    w q k U hq hk
  have hw := integral_abs_iteratedDeriv_dfiWeight_le_of_profile hD k
  have hsum := sum_Icc_inv_pow_mul_le_harmonic q k R hq hk
  have hsum0 : 0 ≤ ∑ r ∈ Finset.Icc 1 R,
      ((((q * r : ℕ) : ℝ) ^ k)⁻¹) := by positivity
  calc
    (∫ u in Set.Icc (-(U : ℝ)) (U : ℝ),
        ‖iteratedDeriv k (dfiDeltaKernel w q) u‖) ≤
      (∫ v : ℝ, ‖iteratedDeriv k w.toFun v‖) *
        ∑ r ∈ Finset.Icc 1 R,
          ((((q * r : ℕ) : ℝ) ^ k)⁻¹) := by simpa [R] using hraw
    _ ≤ (4 * D k * Q * (Q ^ (k + 1))⁻¹) *
        ∑ r ∈ Finset.Icc 1 R,
          ((((q * r : ℕ) : ℝ) ^ k)⁻¹) :=
      mul_le_mul_of_nonneg_right hw hsum0
    _ ≤ (4 * D k * Q * (Q ^ (k + 1))⁻¹) *
        ((((q : ℝ) ^ k)⁻¹) * (harmonic R : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hsum
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (hD.positive k).le)
          w.Q_pos.le)
        (inv_nonneg.mpr (pow_nonneg w.Q_pos.le _))
    _ = _ := by ring

/-- At the source choice `U = Q²`, the harmonic radius in the integrated
equation-(28) estimate is itself logarithmic in `Q`.  The natural ceiling of
the physical displacement is used so the result applies to real source
scales without an integrality hypothesis. -/
theorem harmonic_dfiDeltaRadius_ceil_sq_le_log
    {Q U : ℝ} (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ((harmonic (dfiDeltaRadius Q ((⌈U⌉₊ : ℝ) + 1)) : ℚ) : ℝ) ≤
      (1 / Real.log 2 + 4) * Real.log Q := by
  have hQpos : 0 < Q := by linarith
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hceil : (⌈U⌉₊ : ℝ) < U + 1 := Nat.ceil_lt_add_one hU0
  have harg0 : 0 ≤ 2 * Q + |((⌈U⌉₊ : ℝ) + 1)| / Q := by positivity
  have houter := Nat.ceil_lt_add_one harg0
  have hceilU0 : (0 : ℝ) ≤ (⌈U⌉₊ : ℝ) := Nat.cast_nonneg _
  have habs : |((⌈U⌉₊ : ℝ) + 1)| = (⌈U⌉₊ : ℝ) + 1 :=
    abs_of_nonneg (by positivity)
  have hdiv : ((⌈U⌉₊ : ℝ) + 1) / Q < Q + 1 := by
    have hnum : (⌈U⌉₊ : ℝ) + 1 < Q ^ 2 + 2 := by
      rw [← hU]
      linarith
    have hraw : ((⌈U⌉₊ : ℝ) + 1) / Q < (Q ^ 2 + 2) / Q :=
      (div_lt_div_iff_of_pos_right hQpos).2 hnum
    have htwo : 2 / Q ≤ 1 := (div_le_one hQpos).2 hQ
    calc
      ((⌈U⌉₊ : ℝ) + 1) / Q < (Q ^ 2 + 2) / Q := hraw
      _ = Q + 2 / Q := by field_simp [hQpos.ne']
      _ ≤ Q + 1 := by linarith
  let R := dfiDeltaRadius Q ((⌈U⌉₊ : ℝ) + 1)
  have hRpos : 0 < R := by
    dsimp [R, dfiDeltaRadius]
    omega
  have hRle : (R : ℝ) ≤ 5 * Q := by
    have hRlt : (R : ℝ) < 3 * Q + 3 := by
      rw [habs] at houter
      dsimp [R, dfiDeltaRadius]
      push_cast
      rw [habs]
      linarith
    have hthree : 3 * Q + 3 ≤ 5 * Q := by linarith
    exact hRlt.le.trans hthree
  have hHarmonic : ((harmonic R : ℚ) : ℝ) ≤ 1 + Real.log R :=
    harmonic_le_one_add_log R
  have hlogR : Real.log R ≤ Real.log (5 * Q) := by
    exact Real.log_le_log (by exact_mod_cast hRpos) hRle
  have hlog5 : Real.log 5 ≤ 3 * Real.log 2 := by
    calc
      Real.log 5 ≤ Real.log (2 ^ 3) :=
        Real.log_le_log (by norm_num) (by norm_num)
      _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hlogQ : Real.log 2 ≤ Real.log Q :=
    Real.log_le_log (by norm_num) hQ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hone : 1 ≤ (1 / Real.log 2) * Real.log Q := by
    calc
      1 = (1 / Real.log 2) * Real.log 2 := by field_simp [hlog2pos.ne']
      _ ≤ (1 / Real.log 2) * Real.log Q := by gcongr
  calc
    ((harmonic R : ℚ) : ℝ) ≤ 1 + Real.log R := hHarmonic
    _ ≤ 1 + Real.log (5 * Q) := by linarith
    _ = 1 + Real.log 5 + Real.log Q := by
      rw [Real.log_mul (by norm_num) hQpos.ne']
      ring
    _ ≤ (1 / Real.log 2) * Real.log Q + 3 * Real.log Q + Real.log Q := by
      have hlog5Q : Real.log 5 ≤ 3 * Real.log Q := by linarith
      linarith
    _ = (1 / Real.log 2 + 4) * Real.log Q := by ring

/-- Exact termwise positive-order derivative of the locally finite DFI
delta kernel. -/
theorem iteratedDeriv_dfiDeltaKernel
    {Q : ℝ} (w : DFIDeltaWeight Q) (q k : ℕ)
    (hq : 0 < q) (u : ℝ) :
    iteratedDeriv k (dfiDeltaKernel w q) u =
      ∑ r ∈ Finset.Icc 1 (⌈2 * Q + (|u| + 1) / Q⌉₊ + 1),
        iteratedDeriv k (dfiDeltaSummand w q r) u := by
  let R := ⌈2 * Q + (|u| + 1) / Q⌉₊ + 1
  let fixed : ℝ → ℝ := fun z =>
    ∑ r ∈ Finset.Icc 1 R, dfiDeltaSummand w q r z
  have heq : dfiDeltaKernel w q =ᶠ[nhds u] fixed := by
    simpa [fixed, R] using dfiDeltaKernel_eventuallyEq_fixedSum w q hq u
  rw [Filter.EventuallyEq.iteratedDeriv_eq k heq]
  have hsum := iteratedDeriv_fun_sum
    (I := Finset.Icc 1 R) (f := fun r => dfiDeltaSummand w q r)
    (x := u) (n := k) (fun r hr =>
      (contDiff_dfiDeltaSummand w q r).contDiffAt.of_le
        (by exact_mod_cast le_top))
  simpa [fixed, R] using hsum

/-- Uniform positive-order derivative bound for the DFI delta kernel.  The
The constant depends only on the derivative order and the normalized cutoff,
while the complete `q`- and `Q`-dependence is explicit. -/
theorem norm_iteratedDeriv_dfiDeltaKernel_le
    {Q : ℝ} (w : DFIDeltaWeight Q) (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q → ∀ u : ℝ,
      ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
        C * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) := by
  obtain ⟨Cw, hCw, hw⟩ := w.derivativeBound k
  let pseries : ℕ → ℝ := fun r => (((r : ℝ) ^ (k + 1))⁻¹)
  have hkpow : 1 < k + 1 := by omega
  have hpseries : Summable pseries := by
    simpa [pseries, one_div] using
      (Real.summable_nat_pow_inv.mpr hkpow)
  let S : ℝ := ∑' r : ℕ, pseries r
  have hS : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg (fun r => by
      dsimp [pseries]
      positivity)
  let C : ℝ := Cw * max 1 S
  have hC : 0 < C := mul_pos hCw (lt_of_lt_of_le zero_lt_one (le_max_left 1 S))
  refine ⟨C, hC, ?_⟩
  intro q hq u
  let R := ⌈2 * Q + (|u| + 1) / Q⌉₊ + 1
  have hterm : ∀ r ∈ Finset.Icc 1 R,
      ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖ ≤
        Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) *
          pseries r := by
    intro r hr
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    rw [iteratedDeriv_dfiDeltaSummand w q r k hk u]
    rw [norm_neg, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)]
    have hwbound := hw (u / (q * r : ℕ))
    rw [Real.norm_eq_abs] at hwbound
    calc
      (((q * r : ℕ) : ℝ)⁻¹ ^ (k + 1)) *
          |iteratedDeriv k w.toFun (u / (q * r : ℕ))| ≤
        (((q * r : ℕ) : ℝ)⁻¹ ^ (k + 1)) *
          (Cw * (Q ^ (k + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left hwbound
          (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)
      _ = Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) *
          pseries r := by
        simp only [pseries]
        push_cast
        rw [mul_inv_rev, mul_pow]
        ring
  rw [iteratedDeriv_dfiDeltaKernel w q k hq u]
  change ‖∑ r ∈ Finset.Icc 1 R,
      iteratedDeriv k (dfiDeltaSummand w q r) u‖ ≤ _
  calc
    ‖∑ r ∈ Finset.Icc 1 R,
        iteratedDeriv k (dfiDeltaSummand w q r) u‖ ≤
      ∑ r ∈ Finset.Icc 1 R,
        ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 R,
        Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) *
          pseries r := Finset.sum_le_sum hterm
    _ = (Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹)) *
        ∑ r ∈ Finset.Icc 1 R, pseries r := by
      rw [Finset.mul_sum]
    _ ≤ (Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹)) * S := by
      apply mul_le_mul_of_nonneg_left
      · exact hpseries.sum_le_tsum _ (fun r hr => by
          dsimp [pseries]
          positivity)
      · have hQ : 0 < Q := w.Q_pos
        positivity
    _ ≤ (Cw * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹)) *
        max 1 S := by
      apply mul_le_mul_of_nonneg_left (le_max_right 1 S)
      have hQ : 0 < Q := w.Q_pos
      positivity
    _ = C * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) := by
      dsimp [C]
      ring

/-- Positive-order delta-kernel derivative estimate with the exact
equation-(9) profile constant. -/
theorem norm_iteratedDeriv_dfiDeltaKernel_le_of_profile
    {Q : ℝ} {w : DFIDeltaWeight Q} {D : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D) (k : ℕ) (hk : 0 < k) :
    ∃ S : ℝ, 0 < S ∧
      (∀ (q : ℕ), 0 < q → ∀ u : ℝ,
        ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
          (D k * S) * (Q ^ (k + 1))⁻¹ *
            (((q : ℝ) ^ (k + 1))⁻¹)) := by
  let pseries : ℕ → ℝ := fun r ↦ (((r : ℝ) ^ (k + 1))⁻¹)
  have hkpow : 1 < k + 1 := by omega
  have hpseries : Summable pseries := by
    simpa [pseries, one_div] using (Real.summable_nat_pow_inv.mpr hkpow)
  let S : ℝ := max 1 (∑' r : ℕ, pseries r)
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨S, hS, ?_⟩
  intro q hq u
  let R := ⌈2 * Q + (|u| + 1) / Q⌉₊ + 1
  have hterm : ∀ r ∈ Finset.Icc 1 R,
      ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖ ≤
        D k * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) *
          pseries r := by
    intro r hr
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    rw [iteratedDeriv_dfiDeltaSummand w q r k hk u]
    rw [norm_neg, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)]
    have hwbound := hD.bound k (u / (q * r : ℕ))
    rw [Real.norm_eq_abs] at hwbound
    calc
      (((q * r : ℕ) : ℝ)⁻¹ ^ (k + 1)) *
          |iteratedDeriv k w.toFun (u / (q * r : ℕ))| ≤
        (((q * r : ℕ) : ℝ)⁻¹ ^ (k + 1)) *
          (D k * (Q ^ (k + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left hwbound
          (pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) _)
      _ = D k * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) *
          pseries r := by
        simp only [pseries]
        push_cast
        rw [mul_inv_rev, mul_pow]
        ring
  rw [iteratedDeriv_dfiDeltaKernel w q k hq u]
  change ‖∑ r ∈ Finset.Icc 1 R,
      iteratedDeriv k (dfiDeltaSummand w q r) u‖ ≤ _
  calc
    ‖∑ r ∈ Finset.Icc 1 R,
        iteratedDeriv k (dfiDeltaSummand w q r) u‖ ≤
      ∑ r ∈ Finset.Icc 1 R,
        ‖iteratedDeriv k (dfiDeltaSummand w q r) u‖ := norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 R,
        D k * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) *
          pseries r := Finset.sum_le_sum hterm
    _ = (D k * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹)) *
        ∑ r ∈ Finset.Icc 1 R, pseries r := by rw [Finset.mul_sum]
    _ ≤ (D k * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹)) * S := by
      apply mul_le_mul_of_nonneg_left
      · exact (hpseries.sum_le_tsum _ (fun r _hr ↦ by
          dsimp [pseries]
          positivity)).trans (le_max_right _ _)
      · exact mul_nonneg
          (mul_nonneg (hD.positive k).le (inv_nonneg.mpr (pow_nonneg w.Q_pos.le _)))
          (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg q) _))
    _ = (D k * S) * (Q ^ (k + 1))⁻¹ *
        (((q : ℝ) ^ (k + 1))⁻¹) := by ring

/-- Uniform form of the delta-kernel derivative estimate at every order,
including order zero.  This is the one-variable input to DFI equation (28):
each derivative costs one further factor `(qQ)⁻¹`. -/
theorem norm_iteratedDeriv_dfiDeltaKernel_le_product
    {Q : ℝ} (w : DFIDeltaWeight Q) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q → ∀ u : ℝ,
      ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
        C * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) := by
  by_cases hk : k = 0
  · subst k
    obtain ⟨K, hK, hbound⟩ := dfiEquation19 w
    refine ⟨2 * K, by positivity, ?_⟩
    intro q hq u
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    have hqQ : 0 < (q : ℝ) * Q := mul_pos hqR w.Q_pos
    have hfirst :
        (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤ (((q : ℝ) * Q)⁻¹) := by
      exact inv_anti₀ hqQ (le_add_of_nonneg_right (sq_nonneg Q))
    have hsecond :
        (((q : ℝ) * Q + |u|)⁻¹) ≤ (((q : ℝ) * Q)⁻¹) := by
      exact inv_anti₀ hqQ (le_add_of_nonneg_right (abs_nonneg u))
    rw [iteratedDeriv_zero]
    rw [Real.norm_eq_abs]
    calc
      |dfiDeltaKernel w q u| ≤
          K * ((((q : ℝ) * Q + Q ^ 2)⁻¹) +
            (((q : ℝ) * Q + |u|)⁻¹)) := hbound q hq u
      _ ≤ K * ((((q : ℝ) * Q)⁻¹) + (((q : ℝ) * Q)⁻¹)) := by
        gcongr
      _ = (2 * K) * ((((q : ℝ) * Q) ^ (0 + 1))⁻¹) := by ring
  · obtain ⟨C, hC, hbound⟩ :=
      norm_iteratedDeriv_dfiDeltaKernel_le w k (Nat.pos_of_ne_zero hk)
    refine ⟨C, hC, ?_⟩
    intro q hq u
    calc
      ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
          C * (Q ^ (k + 1))⁻¹ * (((q : ℝ) ^ (k + 1))⁻¹) :=
        hbound q hq u
      _ = C * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) := by
        rw [mul_pow, mul_inv_rev]
        ring

/-- One positive constant controls every delta-kernel derivative through a
fixed order. -/
theorem exists_uniform_norm_iteratedDeriv_dfiDeltaKernel_le_product
    {Q : ℝ} (w : DFIDeltaWeight Q) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ n, ∀ (q : ℕ), 0 < q → ∀ u : ℝ,
      ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
        C * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) := by
  choose C hC hbound using fun k =>
    norm_iteratedDeriv_dfiDeltaKernel_le_product w k
  let Cmax := ∑ k ∈ Finset.range (n + 1), C k
  have hCmax : 0 < Cmax := by
    dsimp [Cmax]
    exact Finset.sum_pos (fun k _ => hC k) ⟨0, by simp⟩
  refine ⟨Cmax, hCmax, ?_⟩
  intro k hk q hq u
  have hkmem : k ∈ Finset.range (n + 1) := by simp [hk]
  have hCle : C k ≤ Cmax := by
    dsimp [Cmax]
    exact Finset.single_le_sum (fun r _ => (hC r).le) hkmem
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqQ : 0 < (q : ℝ) * Q := mul_pos hqR w.Q_pos
  exact (hbound k q hq u).trans
    (mul_le_mul_of_nonneg_right hCle (by positivity))

/-- Profile-explicit form of the delta-kernel estimate through a fixed
order.  The resulting constant is assembled only from the equation-(9)
profile `D` and convergent numerical p-series; in particular its proof does
not invoke the scale-dependent existential field `w.derivativeBound`. -/
theorem exists_uniform_norm_iteratedDeriv_dfiDeltaKernel_le_product_of_profile
    {Q : ℝ} {w : DFIDeltaWeight Q} {D : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ n, ∀ (q : ℕ), 0 < q → ∀ u : ℝ,
      ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
        C * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) := by
  have hEach : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ), 0 < q → ∀ u : ℝ,
      ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
        C * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) := by
    intro k
    by_cases hk : k = 0
    · subst k
      let C : ℝ := 48 * max (D 0) (D 1)
      have hDmax : 0 < max (D 0) (D 1) :=
        (hD.positive 0).trans_le (le_max_left _ _)
      have hC : 0 < C := by
        dsimp [C]
        exact mul_pos (by norm_num) hDmax
      refine ⟨C, hC, ?_⟩
      intro q hq u
      have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
      have hqQ : 0 < (q : ℝ) * Q := mul_pos hqR w.Q_pos
      have hfirst :
          (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤ (((q : ℝ) * Q)⁻¹) :=
        inv_anti₀ hqQ (le_add_of_nonneg_right (sq_nonneg Q))
      have hsecond :
          (((q : ℝ) * Q + |u|)⁻¹) ≤ (((q : ℝ) * Q)⁻¹) :=
        inv_anti₀ hqQ (le_add_of_nonneg_right (abs_nonneg u))
      rw [iteratedDeriv_zero, Real.norm_eq_abs]
      calc
        |dfiDeltaKernel w q u| ≤
            (24 * max (D 0) (D 1)) *
              ((((q : ℝ) * Q + Q ^ 2)⁻¹) +
                (((q : ℝ) * Q + |u|)⁻¹)) :=
          dfiEquation19_of_profile hD q hq u
        _ ≤ (24 * max (D 0) (D 1)) *
              ((((q : ℝ) * Q)⁻¹) + (((q : ℝ) * Q)⁻¹)) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
            (mul_nonneg (by norm_num) hDmax.le)
        _ = C * ((((q : ℝ) * Q) ^ (0 + 1))⁻¹) := by
          dsimp [C]
          ring
    · obtain ⟨S, hS, hbound⟩ :=
        norm_iteratedDeriv_dfiDeltaKernel_le_of_profile hD k
          (Nat.pos_of_ne_zero hk)
      refine ⟨D k * S, mul_pos (hD.positive k) hS, ?_⟩
      intro q hq u
      calc
        ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ ≤
            (D k * S) * (Q ^ (k + 1))⁻¹ *
              (((q : ℝ) ^ (k + 1))⁻¹) := hbound q hq u
        _ = (D k * S) * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) := by
          rw [mul_pow, mul_inv_rev]
          ring
  choose C hC hbound using hEach
  let Cmax := ∑ k ∈ Finset.range (n + 1), C k
  have hCmax : 0 < Cmax := by
    dsimp [Cmax]
    exact Finset.sum_pos (fun k _ ↦ hC k) ⟨0, by simp⟩
  refine ⟨Cmax, hCmax, ?_⟩
  intro k hk q hq u
  have hkmem : k ∈ Finset.range (n + 1) := by simp [hk]
  have hCle : C k ≤ Cmax := by
    dsimp [Cmax]
    exact Finset.single_le_sum (fun r _ ↦ (hC r).le) hkmem
  exact (hbound k q hq u).trans
    (mul_le_mul_of_nonneg_right hCle
      (inv_nonneg.mpr (pow_nonneg
        (mul_nonneg (Nat.cast_nonneg q) w.Q_pos.le) _)))

/-- Exact mixed-derivative scaling under the affine change
`(x,y) ↦ (a*x,b*y)`. -/
theorem dfiMixedDeriv_affine_scale
    {F : ℝ → ℝ → ℂ}
    (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (a b : ℝ) (i j : ℕ) (x y : ℝ) :
    dfiMixedDeriv i j (fun x' y' => F (a * x') (b * y')) x y =
      (a ^ i * b ^ j) • dfiMixedDeriv i j F (a * x) (b * y) := by
  unfold dfiMixedDeriv
  have hyfun :
      (fun x' => iteratedDeriv j (fun y' => F (a * x') (b * y')) y) =
        fun x' => b ^ j • iteratedDeriv j (F (a * x')) (b * y) := by
    funext x'
    have hslice : ContDiff ℝ j (F (a * x')) :=
      (contDiff_slice_right hF (a * x')).of_le (by exact_mod_cast le_top)
    simpa using congrFun (iteratedDeriv_comp_const_smul hslice b) y
  rw [hyfun]
  rw [iteratedDeriv_fun_const_smul_field]
  have hxbase : ContDiff ℝ i (fun z => iteratedDeriv j (F z) (b * y)) :=
    (contDiff_iteratedDeriv_slice_right hF j (b * y)).of_le
      (by exact_mod_cast le_top)
  rw [show iteratedDeriv i
      (fun x' => iteratedDeriv j (F (a * x')) (b * y)) x =
        a ^ i • iteratedDeriv i
          (fun z => iteratedDeriv j (F z) (b * y)) (a * x) by
    simpa using congrFun (iteratedDeriv_comp_const_smul hxbase a) x]
  rw [smul_smul]
  rw [mul_comm]

/-- The equation-(21) derivative profile after the arithmetic scaling
`(x,y) ↦ (a*x,b*y)`, uniformly through a fixed mixed order. -/
theorem exists_uniform_norm_dfiMixedDeriv_affine_localized_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (h : ℝ)
    (a b i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ r ≤ i, ∀ s ≤ j, ∀ x y : ℝ,
        ‖dfiMixedDeriv r s
          (fun x' y' => dfiLocalizedWeight f φ h
            ((a : ℝ) * x') ((b : ℝ) * y')) x y‖ ≤
          C * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
  choose C hC hbound using fun r s =>
    dfiEquation21 hf hbox hφ hscale h r s
  let Cmax := ∑ r ∈ Finset.range (i + 1),
    ∑ s ∈ Finset.range (j + 1), C r s
  have hCmax : 0 < Cmax := by
    dsimp [Cmax]
    have hinner : ∀ r ∈ Finset.range (i + 1),
        0 < ∑ s ∈ Finset.range (j + 1), C r s := by
      intro r _hr
      exact Finset.sum_pos (fun s _ => hC r s) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  refine ⟨Cmax, hCmax, ?_⟩
  intro r hr s hs x y
  have hrmem : r ∈ Finset.range (i + 1) := by simp [hr]
  have hsmem : s ∈ Finset.range (j + 1) := by simp [hs]
  have hCle : C r s ≤ Cmax := by
    dsimp [Cmax]
    exact (Finset.single_le_sum (fun t _ => (hC r t).le) hsmem).trans
      (Finset.single_le_sum
        (fun t _ => Finset.sum_nonneg (fun u _ => (hC t u).le)) hrmem)
  have hU : 0 < U := hφ.U_pos
  have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hfactor : 0 ≤ ((a : ℝ) ^ r * (b : ℝ) ^ s) := by positivity
  rw [dfiMixedDeriv_affine_scale
    (contDiff_uncurry_dfiLocalizedWeight hf hφ)
    (a : ℝ) (b : ℝ) r s x y]
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg ha0 r), abs_of_nonneg (pow_nonneg hb0 s)]
  calc
    (a : ℝ) ^ r * (b : ℝ) ^ s *
        ‖dfiMixedDeriv r s (dfiLocalizedWeight f φ h)
          ((a : ℝ) * x) ((b : ℝ) * y)‖ ≤
      (a : ℝ) ^ r * (b : ℝ) ^ s *
        (C r s * U⁻¹ ^ (r + s)) :=
      mul_le_mul_of_nonneg_left
        ((hbound r s ((a : ℝ) * x) ((b : ℝ) * y)).2) hfactor
    _ = C r s * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
      simp only [pow_add, div_eq_mul_inv, mul_pow]
      ring
    _ ≤ Cmax * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
      gcongr

/-- Arithmetic-uniform version of the equation-(21) affine derivative
profile.  The constant is selected before the shift and both dilation
parameters, which is the quantifier order required by DFI's final error
term. -/
theorem exists_uniform_norm_dfiMixedDeriv_affine_localized_all
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b : ℕ), ∀ r ≤ i, ∀ s ≤ j, ∀ x y : ℝ,
        ‖dfiMixedDeriv r s
          (fun x' y' => dfiLocalizedWeight f φ h
            ((a : ℝ) * x') ((b : ℝ) * y')) x y‖ ≤
          C * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
  choose C hC hbound using fun r s =>
    dfiEquation21_uniform_in_shift hf hbox hφ hscale r s
  let Cmax := ∑ r ∈ Finset.range (i + 1),
    ∑ s ∈ Finset.range (j + 1), C r s
  have hCmax : 0 < Cmax := by
    dsimp [Cmax]
    have hinner : ∀ r ∈ Finset.range (i + 1),
        0 < ∑ s ∈ Finset.range (j + 1), C r s := by
      intro r _hr
      exact Finset.sum_pos (fun s _ => hC r s) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  refine ⟨Cmax, hCmax, ?_⟩
  intro h a b r hr s hs x y
  have hrmem : r ∈ Finset.range (i + 1) := by simp [hr]
  have hsmem : s ∈ Finset.range (j + 1) := by simp [hs]
  have hCle : C r s ≤ Cmax := by
    dsimp [Cmax]
    exact (Finset.single_le_sum (fun t _ => (hC r t).le) hsmem).trans
      (Finset.single_le_sum
        (fun t _ => Finset.sum_nonneg (fun u _ => (hC t u).le)) hrmem)
  have hU : 0 < U := hφ.U_pos
  have ha0 : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  have hb0 : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have hfactor : 0 ≤ ((a : ℝ) ^ r * (b : ℝ) ^ s) := by positivity
  rw [dfiMixedDeriv_affine_scale
    (contDiff_uncurry_dfiLocalizedWeight hf hφ)
    (a : ℝ) (b : ℝ) r s x y]
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg ha0 r), abs_of_nonneg (pow_nonneg hb0 s)]
  calc
    (a : ℝ) ^ r * (b : ℝ) ^ s *
        ‖dfiMixedDeriv r s (dfiLocalizedWeight f φ h)
          ((a : ℝ) * x) ((b : ℝ) * y)‖ ≤
      (a : ℝ) ^ r * (b : ℝ) ^ s *
        (C r s * U⁻¹ ^ (r + s)) :=
      mul_le_mul_of_nonneg_left
        ((hbound r s h ((a : ℝ) * x) ((b : ℝ) * y)).2) hfactor
    _ = C r s * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
      simp only [pow_add, div_eq_mul_inv, mul_pow]
      ring
    _ ≤ Cmax * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
      gcongr

/-- Profile-explicit affine equation-(21) bound.  Unlike
`exists_uniform_norm_dfiMixedDeriv_affine_localized_all`, every constituent
The constant is a finite expression in the profiles fixed before the physical
scales. -/
theorem exists_uniform_norm_dfiMixedDeriv_affine_localized_all_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (a b : ℕ), ∀ r ≤ i, ∀ s ≤ j, ∀ x y : ℝ,
        ‖dfiMixedDeriv r s
          (fun x' y' => dfiLocalizedWeight f φ h
            ((a : ℝ) * x') ((b : ℝ) * y')) x y‖ ≤
          C * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
  let C : ℕ → ℕ → ℝ := fun r s ↦
    dfiEquation2FiniteConstant Cf (max r s) *
      dfiCutoffFiniteConstant Cφ (r + s) * 2 ^ (r + s)
  have hC : ∀ r s, 0 < C r s := by
    intro r s
    have hCut : 0 < dfiCutoffFiniteConstant Cφ (r + s) := by
      unfold dfiCutoffFiniteConstant
      exact Finset.sum_pos (fun k _ ↦ hφC.positive k) ⟨0, by simp⟩
    dsimp [C]
    exact mul_pos
      (mul_pos (hfC.finiteConstant_pos _) hCut)
      (pow_pos (by norm_num) _)
  have hbound : ∀ r s h x y,
      ‖dfiMixedDeriv r s (dfiLocalizedWeight f φ h) x y‖ ≤
        C r s * U⁻¹ ^ (r + s) := by
    intro r s h x y
    exact (dfiEquation21_of_profiles_uniform_in_shift
      hf hfC hbox hφ hφC hscale r s h x y).2
  let Cmax := ∑ r ∈ Finset.range (i + 1),
    ∑ s ∈ Finset.range (j + 1), C r s
  have hCmax : 0 < Cmax := by
    dsimp [Cmax]
    have hinner : ∀ r ∈ Finset.range (i + 1),
        0 < ∑ s ∈ Finset.range (j + 1), C r s := by
      intro r _hr
      exact Finset.sum_pos (fun s _ ↦ hC r s) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  refine ⟨Cmax, hCmax, ?_⟩
  intro h a b r hr s hs x y
  have hrmem : r ∈ Finset.range (i + 1) := by simp [hr]
  have hsmem : s ∈ Finset.range (j + 1) := by simp [hs]
  have hCle : C r s ≤ Cmax := by
    dsimp [Cmax]
    exact (Finset.single_le_sum (fun t _ ↦ (hC r t).le) hsmem).trans
      (Finset.single_le_sum
        (fun t _ ↦ Finset.sum_nonneg (fun u _ ↦ (hC t u).le)) hrmem)
  have hfactor : 0 ≤ ((a : ℝ) ^ r * (b : ℝ) ^ s) := by positivity
  have hU : 0 < U := hφ.U_pos
  rw [dfiMixedDeriv_affine_scale
    (contDiff_uncurry_dfiLocalizedWeight hf hφ)
    (a : ℝ) (b : ℝ) r s x y]
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg a) r),
    abs_of_nonneg (pow_nonneg (Nat.cast_nonneg b) s)]
  calc
    (a : ℝ) ^ r * (b : ℝ) ^ s *
        ‖dfiMixedDeriv r s (dfiLocalizedWeight f φ h)
          ((a : ℝ) * x) ((b : ℝ) * y)‖ ≤
      (a : ℝ) ^ r * (b : ℝ) ^ s *
        (C r s * U⁻¹ ^ (r + s)) :=
      mul_le_mul_of_nonneg_left (hbound r s h _ _) hfactor
    _ = C r s * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
      simp only [pow_add, div_eq_mul_inv, mul_pow]
      ring
    _ ≤ Cmax * ((a : ℝ) / U) ^ r * ((b : ℝ) / U) ^ s := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCle
          (pow_nonneg (div_nonneg (Nat.cast_nonneg a) hU.le) r))
        (pow_nonneg (div_nonneg (Nat.cast_nonneg b) hU.le) s)

/-- DFI equation (28).  Under the source choice `U = Q²` and the active
modulus range `q ≤ 2Q`, the complete equation-(23) weight has one factor
`(qQ)⁻¹` and each mixed derivative costs at most `ab/(qQ)`. -/
theorem dfiEquation28
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2)
    (a b q : ℕ) (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (hqQ : (q : ℝ) ≤ 2 * Q) (h : ℤ) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ,
      ‖dfiMixedDeriv i j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) x y‖ ≤
        C * ((q : ℝ) * Q)⁻¹ *
          (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q)) ^ (i + j) := by
  obtain ⟨CF, hCF, hFbound⟩ :=
    exists_uniform_norm_dfiMixedDeriv_affine_localized_le
      hf hbox hφ hscale (h : ℝ) 1 1 i j
  obtain ⟨Cδ, hCδ, hδbound⟩ :=
    exists_uniform_norm_iteratedDeriv_dfiDeltaKernel_le_product w (i + j)
  let A : ℝ := (a : ℝ) * (b : ℝ)
  let qQ : ℝ := (q : ℝ) * Q
  let C : ℝ := CF * Cδ * 3 ^ (i + j)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro x y
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hQ : 0 < Q := w.Q_pos
  have hU : 0 < U := hφ.U_pos
  have hqQpos : 0 < qQ := by
    dsimp [qQ]
    positivity
  have hA : 1 ≤ A := by
    dsimp [A]
    have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
    simpa [A] using mul_le_mul ha1 hb1 zero_le_one haR.le
  have hbaseSmooth : ContDiff ℝ ∞
      (Function.uncurry (dfiLocalizedWeight f φ h)) :=
    contDiff_uncurry_dfiLocalizedWeight hf hφ
  have hdeltaSmooth : ContDiff ℝ ∞
      (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (contDiff_dfiDeltaKernel w q hq)
  have hFcoarse : ∀ r ∈ Finset.range (i + 1),
      ∀ s ∈ Finset.range (j + 1), ∀ x y : ℝ,
      ‖dfiMixedDeriv r s (dfiLocalizedWeight f φ h) x y‖ ≤
        CF * ((1 : ℝ) / U) ^ r * ((1 : ℝ) / U) ^ s := by
    intro r hr s hs x' y'
    have hrle : r ≤ i := by simpa using hr
    have hsle : s ≤ j := by simpa using hs
    simpa using hFbound r hrle s hsle x' y'
  have hδcoarse : ∀ k ≤ i + j, ∀ u : ℝ,
      ‖iteratedDeriv k (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) u‖ ≤
        (Cδ * qQ⁻¹) * qQ⁻¹ ^ k := by
    intro k hk u
    rw [iteratedDeriv_ofReal_comp (dfiDeltaKernel w q)
      (contDiff_dfiDeltaKernel w q hq) k]
    rw [Complex.norm_real]
    calc
      |iteratedDeriv k (dfiDeltaKernel w q) u| =
          ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ Cδ * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) :=
        hδbound k hk q hq u
      _ = (Cδ * qQ⁻¹) * qQ⁻¹ ^ k := by
        dsimp [qQ]
        rw [pow_succ, mul_inv_rev]
        ring
  have hphysicalSmooth : ContDiff ℝ ∞
      (Function.uncurry
        (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
          (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h)) := by
    unfold dfiLocalizedWeight Function.uncurry
    exact hbaseSmooth.mul (hdeltaSmooth.comp
      ((contDiff_fst.sub contDiff_snd).sub contDiff_const))
  have hraw : ∀ x' y' : ℝ,
      ‖dfiMixedDeriv i j
        (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
          (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h) x' y'‖ ≤
        CF * (Cδ * qQ⁻¹) * (((1 : ℝ) / U) + qQ⁻¹) ^ i *
          (((1 : ℝ) / U) + qQ⁻¹) ^ j := by
    intro x' y'
    exact norm_dfiMixedDeriv_localized_le
      hbaseSmooth hdeltaSmooth
      (P := (1 : ℝ)) (X := U) (Y := U) (U := qQ)
      (Cf := CF) (Cφ := Cδ * qQ⁻¹)
      zero_le_one hU hU hCF.le i j hFcoarse hδcoarse (h : ℝ) x' y'
  have hqQ_le_twoU : qQ ≤ 2 * U := by
    dsimp [qQ]
    rw [hUQ]
    nlinarith [mul_le_mul_of_nonneg_right hqQ hQ.le]
  have hinvU : U⁻¹ ≤ 2 * qQ⁻¹ := by
    have hhalf : 0 < qQ / 2 := by positivity
    have hhalf_le : qQ / 2 ≤ U := by linarith
    calc
      U⁻¹ ≤ (qQ / 2)⁻¹ := inv_anti₀ hhalf hhalf_le
      _ = 2 * qQ⁻¹ := by field_simp [hqQpos.ne']
  have hsum : (1 : ℝ) / U + qQ⁻¹ ≤ 3 * qQ⁻¹ := by
    rw [one_div]
    linarith
  have haA : (a : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ b by exact_mod_cast hb) haR.le]
  have hbA : (b : ℝ) ≤ A := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ a by exact_mod_cast ha) hbR.le]
  have heq :
      dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q =
        fun x' y' =>
          dfiLocalizedWeight (dfiLocalizedWeight f φ h)
            (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h
            ((a : ℝ) * x') ((b : ℝ) * y') := by
    rfl
  rw [heq, dfiMixedDeriv_affine_scale hphysicalSmooth
    (a : ℝ) (b : ℝ) i j x y]
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg haR.le i), abs_of_nonneg (pow_nonneg hbR.le j)]
  calc
    (a : ℝ) ^ i * (b : ℝ) ^ j *
        ‖dfiMixedDeriv i j
          (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
            (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h)
          ((a : ℝ) * x) ((b : ℝ) * y)‖ ≤
      (a : ℝ) ^ i * (b : ℝ) ^ j *
        (CF * (Cδ * qQ⁻¹) * (((1 : ℝ) / U) + qQ⁻¹) ^ i *
          (((1 : ℝ) / U) + qQ⁻¹) ^ j) := by
      gcongr
      exact hraw _ _
    _ ≤ (a : ℝ) ^ i * (b : ℝ) ^ j *
        (CF * (Cδ * qQ⁻¹) * (3 * qQ⁻¹) ^ i *
          (3 * qQ⁻¹) ^ j) := by gcongr
    _ = C * qQ⁻¹ * ((a : ℝ) / qQ) ^ i * ((b : ℝ) / qQ) ^ j := by
      dsimp [C]
      simp only [div_eq_mul_inv, mul_pow, pow_add]
      ring
    _ ≤ C * qQ⁻¹ * (A / qQ) ^ i * (A / qQ) ^ j := by
      gcongr
    _ = C * qQ⁻¹ * (A / qQ) ^ (i + j) := by
      rw [pow_add]
      ring
    _ = C * ((q : ℝ) * Q)⁻¹ *
        (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q)) ^ (i + j) := by
      rfl

/-- The variable-separated refinement of DFI equation (28).  This is the
estimate obtained directly from equations (21)--(22), before the harmless
coarsening `a,b ≤ ab` made in the displayed source equation (28).  Retaining
the two derivative scales separately is essential for the truncations (29). -/
theorem dfiEquation28_separated_uniform
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x y : ℝ),
        ‖dfiMixedDeriv i j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by
  obtain ⟨CF, hCF, hFbound⟩ :=
    exists_uniform_norm_dfiMixedDeriv_affine_localized_all
      hf hbox hφ hscale i j
  obtain ⟨Cδ, hCδ, hδbound⟩ :=
    exists_uniform_norm_iteratedDeriv_dfiDeltaKernel_le_product w (i + j)
  let C : ℝ := CF * Cδ * 3 ^ (i + j)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x y
  let qQ : ℝ := (q : ℝ) * Q
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hQ : 0 < Q := w.Q_pos
  have hU : 0 < U := hφ.U_pos
  have hqQpos : 0 < qQ := by
    dsimp [qQ]
    positivity
  have hbaseSmooth : ContDiff ℝ ∞
      (Function.uncurry (dfiLocalizedWeight f φ h)) :=
    contDiff_uncurry_dfiLocalizedWeight hf hφ
  have hdeltaSmooth : ContDiff ℝ ∞
      (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (contDiff_dfiDeltaKernel w q hq)
  have hFcoarse : ∀ r ∈ Finset.range (i + 1),
      ∀ s ∈ Finset.range (j + 1), ∀ x y : ℝ,
      ‖dfiMixedDeriv r s (dfiLocalizedWeight f φ h) x y‖ ≤
        CF * ((1 : ℝ) / U) ^ r * ((1 : ℝ) / U) ^ s := by
    intro r hr s hs x' y'
    have hrle : r ≤ i := by simpa using hr
    have hsle : s ≤ j := by simpa using hs
    simpa using hFbound h 1 1 r hrle s hsle x' y'
  have hδcoarse : ∀ k ≤ i + j, ∀ u : ℝ,
      ‖iteratedDeriv k (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) u‖ ≤
        (Cδ * qQ⁻¹) * qQ⁻¹ ^ k := by
    intro k hk u
    rw [iteratedDeriv_ofReal_comp (dfiDeltaKernel w q)
      (contDiff_dfiDeltaKernel w q hq) k]
    rw [Complex.norm_real]
    calc
      |iteratedDeriv k (dfiDeltaKernel w q) u| =
          ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ Cδ * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) :=
        hδbound k hk q hq u
      _ = (Cδ * qQ⁻¹) * qQ⁻¹ ^ k := by
        dsimp [qQ]
        rw [pow_succ, mul_inv_rev]
        ring
  have hphysicalSmooth : ContDiff ℝ ∞
      (Function.uncurry
        (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
          (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h)) := by
    unfold dfiLocalizedWeight Function.uncurry
    exact hbaseSmooth.mul (hdeltaSmooth.comp
      ((contDiff_fst.sub contDiff_snd).sub contDiff_const))
  have hraw : ∀ x' y' : ℝ,
      ‖dfiMixedDeriv i j
        (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
          (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h) x' y'‖ ≤
        CF * (Cδ * qQ⁻¹) * (((1 : ℝ) / U) + qQ⁻¹) ^ i *
          (((1 : ℝ) / U) + qQ⁻¹) ^ j := by
    intro x' y'
    exact norm_dfiMixedDeriv_localized_le
      hbaseSmooth hdeltaSmooth
      (P := (1 : ℝ)) (X := U) (Y := U) (U := qQ)
      (Cf := CF) (Cφ := Cδ * qQ⁻¹)
      zero_le_one hU hU hCF.le i j hFcoarse hδcoarse (h : ℝ) x' y'
  have hqQ_le_twoU : qQ ≤ 2 * U := by
    dsimp [qQ]
    rw [hUQ]
    nlinarith [mul_le_mul_of_nonneg_right hqQ hQ.le]
  have hinvU : U⁻¹ ≤ 2 * qQ⁻¹ := by
    have hhalf : 0 < qQ / 2 := by positivity
    have hhalf_le : qQ / 2 ≤ U := by linarith
    calc
      U⁻¹ ≤ (qQ / 2)⁻¹ := inv_anti₀ hhalf hhalf_le
      _ = 2 * qQ⁻¹ := by field_simp [hqQpos.ne']
  have hsum : (1 : ℝ) / U + qQ⁻¹ ≤ 3 * qQ⁻¹ := by
    rw [one_div]
    linarith
  have heq :
      dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q =
        fun x' y' =>
          dfiLocalizedWeight (dfiLocalizedWeight f φ h)
            (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h
            ((a : ℝ) * x') ((b : ℝ) * y') := by
    rfl
  rw [heq, dfiMixedDeriv_affine_scale hphysicalSmooth
    (a : ℝ) (b : ℝ) i j x y]
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg haR.le i), abs_of_nonneg (pow_nonneg hbR.le j)]
  calc
    (a : ℝ) ^ i * (b : ℝ) ^ j *
        ‖dfiMixedDeriv i j
          (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
            (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h)
          ((a : ℝ) * x) ((b : ℝ) * y)‖ ≤
      (a : ℝ) ^ i * (b : ℝ) ^ j *
        (CF * (Cδ * qQ⁻¹) * (((1 : ℝ) / U) + qQ⁻¹) ^ i *
          (((1 : ℝ) / U) + qQ⁻¹) ^ j) := by
      gcongr
      exact hraw _ _
    _ ≤ (a : ℝ) ^ i * (b : ℝ) ^ j *
        (CF * (Cδ * qQ⁻¹) * (3 * qQ⁻¹) ^ i *
          (3 * qQ⁻¹) ^ j) := by gcongr
    _ = C * qQ⁻¹ * ((a : ℝ) / qQ) ^ i * ((b : ℝ) / qQ) ^ j := by
      dsimp [C]
      simp only [div_eq_mul_inv, mul_pow, pow_add]
      ring
    _ = C * ((q : ℝ) * Q)⁻¹ *
        ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
        ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by
      rfl

/-- Variable-separated DFI equation (28) with every analytic constant
derived from profiles fixed before the arithmetic parameters. -/
theorem dfiEquation28_separated_uniform_of_profiles
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x y : ℝ),
        ‖dfiMixedDeriv i j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by
  obtain ⟨CF, hCF, hFbound⟩ :=
    exists_uniform_norm_dfiMixedDeriv_affine_localized_all_of_profiles
      hf hfC hbox hφ hφC hscale i j
  obtain ⟨Cδ, hCδ, hδbound⟩ :=
    exists_uniform_norm_iteratedDeriv_dfiDeltaKernel_le_product_of_profile
      hwC (i + j)
  let C : ℝ := CF * Cδ * 3 ^ (i + j)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x y
  let qQ : ℝ := (q : ℝ) * Q
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hQ : 0 < Q := w.Q_pos
  have hU : 0 < U := hφ.U_pos
  have hqQpos : 0 < qQ := by
    dsimp [qQ]
    positivity
  have hbaseSmooth : ContDiff ℝ ∞
      (Function.uncurry (dfiLocalizedWeight f φ h)) :=
    contDiff_uncurry_dfiLocalizedWeight hf hφ
  have hdeltaSmooth : ContDiff ℝ ∞
      (fun u : ℝ => (dfiDeltaKernel w q u : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (contDiff_dfiDeltaKernel w q hq)
  have hFcoarse : ∀ r ∈ Finset.range (i + 1),
      ∀ s ∈ Finset.range (j + 1), ∀ x y : ℝ,
      ‖dfiMixedDeriv r s (dfiLocalizedWeight f φ h) x y‖ ≤
        CF * ((1 : ℝ) / U) ^ r * ((1 : ℝ) / U) ^ s := by
    intro r hr s hs x' y'
    have hrle : r ≤ i := by simpa using hr
    have hsle : s ≤ j := by simpa using hs
    simpa using hFbound h 1 1 r hrle s hsle x' y'
  have hδcoarse : ∀ k ≤ i + j, ∀ u : ℝ,
      ‖iteratedDeriv k (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) u‖ ≤
        (Cδ * qQ⁻¹) * qQ⁻¹ ^ k := by
    intro k hk u
    rw [iteratedDeriv_ofReal_comp (dfiDeltaKernel w q)
      (contDiff_dfiDeltaKernel w q hq) k]
    rw [Complex.norm_real]
    calc
      |iteratedDeriv k (dfiDeltaKernel w q) u| =
          ‖iteratedDeriv k (dfiDeltaKernel w q) u‖ := by
            rw [Real.norm_eq_abs]
      _ ≤ Cδ * ((((q : ℝ) * Q) ^ (k + 1))⁻¹) :=
        hδbound k hk q hq u
      _ = (Cδ * qQ⁻¹) * qQ⁻¹ ^ k := by
        dsimp [qQ]
        rw [pow_succ, mul_inv_rev]
        ring
  have hphysicalSmooth : ContDiff ℝ ∞
      (Function.uncurry
        (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
          (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h)) := by
    unfold dfiLocalizedWeight Function.uncurry
    exact hbaseSmooth.mul (hdeltaSmooth.comp
      ((contDiff_fst.sub contDiff_snd).sub contDiff_const))
  have hraw : ∀ x' y' : ℝ,
      ‖dfiMixedDeriv i j
        (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
          (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h) x' y'‖ ≤
        CF * (Cδ * qQ⁻¹) * (((1 : ℝ) / U) + qQ⁻¹) ^ i *
          (((1 : ℝ) / U) + qQ⁻¹) ^ j := by
    intro x' y'
    exact norm_dfiMixedDeriv_localized_le
      hbaseSmooth hdeltaSmooth
      (P := (1 : ℝ)) (X := U) (Y := U) (U := qQ)
      (Cf := CF) (Cφ := Cδ * qQ⁻¹)
      zero_le_one hU hU hCF.le i j hFcoarse hδcoarse (h : ℝ) x' y'
  have hqQ_le_twoU : qQ ≤ 2 * U := by
    dsimp [qQ]
    rw [hUQ]
    nlinarith [mul_le_mul_of_nonneg_right hqQ hQ.le]
  have hinvU : U⁻¹ ≤ 2 * qQ⁻¹ := by
    have hhalf : 0 < qQ / 2 := by positivity
    have hhalf_le : qQ / 2 ≤ U := by linarith
    calc
      U⁻¹ ≤ (qQ / 2)⁻¹ := inv_anti₀ hhalf hhalf_le
      _ = 2 * qQ⁻¹ := by field_simp [hqQpos.ne']
  have hsum : (1 : ℝ) / U + qQ⁻¹ ≤ 3 * qQ⁻¹ := by
    rw [one_div]
    linarith
  have heq :
      dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q =
        fun x' y' =>
          dfiLocalizedWeight (dfiLocalizedWeight f φ h)
            (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h
            ((a : ℝ) * x') ((b : ℝ) * y') := by
    rfl
  rw [heq, dfiMixedDeriv_affine_scale hphysicalSmooth
    (a : ℝ) (b : ℝ) i j x y]
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg haR.le i), abs_of_nonneg (pow_nonneg hbR.le j)]
  calc
    (a : ℝ) ^ i * (b : ℝ) ^ j *
        ‖dfiMixedDeriv i j
          (dfiLocalizedWeight (dfiLocalizedWeight f φ h)
            (fun z : ℝ => (dfiDeltaKernel w q z : ℂ)) h)
          ((a : ℝ) * x) ((b : ℝ) * y)‖ ≤
      (a : ℝ) ^ i * (b : ℝ) ^ j *
        (CF * (Cδ * qQ⁻¹) * (((1 : ℝ) / U) + qQ⁻¹) ^ i *
          (((1 : ℝ) / U) + qQ⁻¹) ^ j) := by
      gcongr
      exact hraw _ _
    _ ≤ (a : ℝ) ^ i * (b : ℝ) ^ j *
        (CF * (Cδ * qQ⁻¹) * (3 * qQ⁻¹) ^ i *
          (3 * qQ⁻¹) ^ j) := by gcongr
    _ = C * qQ⁻¹ * ((a : ℝ) / qQ) ^ i * ((b : ℝ) / qQ) ^ j := by
      dsimp [C]
      simp only [div_eq_mul_inv, mul_pow, pow_add]
      ring
    _ = C * ((q : ℝ) * Q)⁻¹ *
        ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
        ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by
      rfl

/-- Fully arithmetic-uniform equation (28), in the coarsened form printed by
DFI.  Its constant is chosen before `a`, `b`, the shift, and the active
modulus; this is the source-level quantifier order needed when summing (24). -/
theorem dfiEquation28_uniform
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x y : ℝ),
        ‖dfiMixedDeriv i j
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q)) ^ (i + j) := by
  obtain ⟨C, hC, hsep⟩ :=
    dfiEquation28_separated_uniform hf hbox hφ hscale w hUQ i j
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x y
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hQ : 0 < Q := w.Q_pos
  have hqQpos : 0 < (q : ℝ) * Q := mul_pos hqR hQ
  have haab : (a : ℝ) ≤ (a : ℝ) * (b : ℝ) := by
    nlinarith [show (1 : ℝ) ≤ b by exact_mod_cast hb]
  have hbab : (b : ℝ) ≤ (a : ℝ) * (b : ℝ) := by
    nlinarith [show (1 : ℝ) ≤ a by exact_mod_cast ha]
  calc
    ‖dfiMixedDeriv i j
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) x y‖ ≤
        C * ((q : ℝ) * Q)⁻¹ *
          ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
          ((b : ℝ) / ((q : ℝ) * Q)) ^ j :=
      hsep a b q ha hb hq hqQ h x y
    _ ≤ C * ((q : ℝ) * Q)⁻¹ *
        (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q)) ^ i *
        (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q)) ^ j := by
      gcongr
    _ = C * ((q : ℝ) * Q)⁻¹ *
        (((a : ℝ) * (b : ℝ)) / ((q : ℝ) * Q)) ^ (i + j) := by
      rw [pow_add]
      ring

/-- Finite all-order first-slice profile extracted from the separated form
of DFI (28).  The constant is chosen before every arithmetic and slice
parameter, and depends only on the requested maximum derivative order and
the source data. -/
theorem exists_dfiEquation28_xSlice_derivative_profile
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ) (r : ℕ), r ≤ J →
        ∀ x : ℝ,
        ‖iteratedDeriv r
          (fun x => dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x y) x‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ r := by
  have hEach : ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x y : ℝ),
        ‖dfiMixedDeriv r 0
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ r := by
    intro r
    obtain ⟨C, hC, hbound⟩ :=
      dfiEquation28_separated_uniform hf hbox hφ hscale w hUQ r 0
    refine ⟨C, hC, ?_⟩
    intro a b q ha hb hq hqQ h x y
    simpa using hbound a b q ha hb hq hqQ h x y
  choose C hC hbound using hEach
  let Csum : ℝ := ∑ r ∈ Finset.range (J + 1), C r
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun r _ => hC r) ⟨0, by simp⟩
  refine ⟨Csum, hCsum, ?_⟩
  intro a b q ha hb hq hqQ h y r hr x
  have hrmem : r ∈ Finset.range (J + 1) := by simp [hr]
  have hCle : C r ≤ Csum := by
    dsimp [Csum]
    exact Finset.single_le_sum (fun s _ => (hC s).le) hrmem
  have hraw := hbound r a b q ha hb hq hqQ h x y
  have hQ : 0 < Q := w.Q_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcoarse : C r * ((q : ℝ) * Q)⁻¹ *
        ((a : ℝ) / ((q : ℝ) * Q)) ^ r ≤
      Csum * ((q : ℝ) * Q)⁻¹ *
        ((a : ℝ) / ((q : ℝ) * Q)) ^ r := by
    gcongr
  simpa [dfiMixedDeriv] using hraw.trans hcoarse

/-- Symmetric finite all-order second-slice profile extracted from DFI
(28).  This is the `b/(qQ)` derivative scale needed for the second cutoff
in equation (29). -/
theorem exists_dfiEquation28_ySlice_derivative_profile
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ) (r : ℕ), r ≤ J →
        ∀ y : ℝ,
        ‖iteratedDeriv r
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b h q x) y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ r := by
  have hEach : ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x y : ℝ),
        ‖dfiMixedDeriv 0 r
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ r := by
    intro r
    obtain ⟨C, hC, hbound⟩ :=
      dfiEquation28_separated_uniform hf hbox hφ hscale w hUQ 0 r
    refine ⟨C, hC, ?_⟩
    intro a b q ha hb hq hqQ h x y
    simpa using hbound a b q ha hb hq hqQ h x y
  choose C hC hbound using hEach
  let Csum : ℝ := ∑ r ∈ Finset.range (J + 1), C r
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos (fun r _ => hC r) ⟨0, by simp⟩
  refine ⟨Csum, hCsum, ?_⟩
  intro a b q ha hb hq hqQ h x r hr y
  have hrmem : r ∈ Finset.range (J + 1) := by simp [hr]
  have hCle : C r ≤ Csum := by
    dsimp [Csum]
    exact Finset.single_le_sum (fun s _ => (hC s).le) hrmem
  have hraw := hbound r a b q ha hb hq hqQ h x y
  have hQ : 0 < Q := w.Q_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcoarse : C r * ((q : ℝ) * Q)⁻¹ *
        ((b : ℝ) / ((q : ℝ) * Q)) ^ r ≤
      Csum * ((q : ℝ) * Q)⁻¹ *
        ((b : ℝ) / ((q : ℝ) * Q)) ^ r := by
    gcongr
  change ‖iteratedDeriv r
      (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q x) y‖ ≤
    C r * ((q : ℝ) * Q)⁻¹ *
      ((b : ℝ) / ((q : ℝ) * Q)) ^ r at hraw
  exact hraw.trans hcoarse

/-- A single source constant controls every mixed derivative in a prescribed
finite rectangle, while retaining the two separate DFI (28) scales.  This
is the input for simultaneous `x`- and `y`-Bessel recurrences in the corner
where both dual frequencies exceed the equation-(29) cutoffs. -/
theorem exists_dfiEquation28_mixed_derivative_profile
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hUQ : U = Q ^ 2) (I J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (i j : ℕ),
        i ≤ I → j ≤ J → ∀ (x y : ℝ),
        ‖dfiMixedDeriv i j
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by
  have hEach : ∀ i j : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x y : ℝ),
        ‖dfiMixedDeriv i j
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by
    intro i j
    exact dfiEquation28_separated_uniform
      hf hbox hψ hscale w hUQ i j
  choose C hC hbound using hEach
  let Csum : ℝ := ∑ i ∈ Finset.range (I + 1),
    ∑ j ∈ Finset.range (J + 1), C i j
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos
      (fun i hi ↦ Finset.sum_pos (fun j hj ↦ hC i j) ⟨0, by simp⟩)
      ⟨0, by simp⟩
  refine ⟨Csum, hCsum, ?_⟩
  intro a b q ha hb hq hqQ h i j hi hj x y
  have himem : i ∈ Finset.range (I + 1) := by simp [hi]
  have hjmem : j ∈ Finset.range (J + 1) := by simp [hj]
  have hCij : C i j ≤ Csum := by
    have hinner : C i j ≤ ∑ s ∈ Finset.range (J + 1), C i s :=
      Finset.single_le_sum (fun s hs ↦ (hC i s).le) hjmem
    have houter : (∑ s ∈ Finset.range (J + 1), C i s) ≤ Csum := by
      dsimp [Csum]
      exact Finset.single_le_sum
        (fun r hr ↦ Finset.sum_nonneg fun s hs ↦ (hC r s).le) himem
    exact hinner.trans houter
  have hraw := hbound i j a b q ha hb hq hqQ h x y
  have hqQpos : 0 < (q : ℝ) * Q := mul_pos (by exact_mod_cast hq) w.Q_pos
  have hInv : 0 ≤ ((q : ℝ) * Q)⁻¹ := inv_nonneg.mpr hqQpos.le
  have hAi : 0 ≤ ((a : ℝ) / ((q : ℝ) * Q)) ^ i := by positivity
  have hBj : 0 ≤ ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by positivity
  have hQ : 0 < Q := w.Q_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  calc
    ‖dfiMixedDeriv i j
        (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
          a b h q) x y‖ ≤
      C i j * ((q : ℝ) * Q)⁻¹ *
        ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
        ((b : ℝ) / ((q : ℝ) * Q)) ^ j := hraw
    _ ≤ Csum * ((q : ℝ) * Q)⁻¹ *
        ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
        ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCij hInv) hAi) hBj

/-- Finite mixed-derivative rectangle obtained exclusively from the fixed
source profiles. -/
theorem exists_dfiEquation28_mixed_derivative_profile_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (I J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (i j : ℕ),
        i ≤ I → j ≤ J → ∀ (x y : ℝ),
        ‖dfiMixedDeriv i j
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by
  have hEach : ∀ i j : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x y : ℝ),
        ‖dfiMixedDeriv i j
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q) x y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by
    intro i j
    exact dfiEquation28_separated_uniform_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ i j
  choose C hC hbound using hEach
  let Csum : ℝ := ∑ i ∈ Finset.range (I + 1),
    ∑ j ∈ Finset.range (J + 1), C i j
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    exact Finset.sum_pos
      (fun i hi ↦ Finset.sum_pos (fun j hj ↦ hC i j) ⟨0, by simp⟩)
      ⟨0, by simp⟩
  refine ⟨Csum, hCsum, ?_⟩
  intro a b q ha hb hq hqQ h i j hi hj x y
  have himem : i ∈ Finset.range (I + 1) := by simp [hi]
  have hjmem : j ∈ Finset.range (J + 1) := by simp [hj]
  have hCij : C i j ≤ Csum := by
    have hinner : C i j ≤ ∑ s ∈ Finset.range (J + 1), C i s :=
      Finset.single_le_sum (fun s hs ↦ (hC i s).le) hjmem
    have houter : (∑ s ∈ Finset.range (J + 1), C i s) ≤ Csum := by
      dsimp [Csum]
      exact Finset.single_le_sum
        (fun r hr ↦ Finset.sum_nonneg fun s hs ↦ (hC r s).le) himem
    exact hinner.trans houter
  have hraw := hbound i j a b q ha hb hq hqQ h x y
  have hqQpos' : 0 < (q : ℝ) * Q := mul_pos (by exact_mod_cast hq) w.Q_pos
  have hInv' : 0 ≤ ((q : ℝ) * Q)⁻¹ := inv_nonneg.mpr hqQpos'.le
  have hAi' : 0 ≤ ((a : ℝ) / ((q : ℝ) * Q)) ^ i := by positivity
  have hBj' : 0 ≤ ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by positivity
  calc
    ‖dfiMixedDeriv i j
        (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
          a b h q) x y‖ ≤
      C i j * ((q : ℝ) * Q)⁻¹ *
        ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
        ((b : ℝ) / ((q : ℝ) * Q)) ^ j := hraw
    _ ≤ Csum * ((q : ℝ) * Q)⁻¹ *
        ((a : ℝ) / ((q : ℝ) * Q)) ^ i *
        ((b : ℝ) / ((q : ℝ) * Q)) ^ j := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCij hInv') hAi') hBj'

theorem exists_dfiEquation28_xSlice_derivative_profile_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (y : ℝ) (r : ℕ), r ≤ J →
        ∀ x : ℝ,
        ‖iteratedDeriv r
          (fun x ↦ dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q x y) x‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((a : ℝ) / ((q : ℝ) * Q)) ^ r := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_dfiEquation28_mixed_derivative_profile_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ J 0
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h y r hr x
  simpa [dfiMixedDeriv] using
    hbound a b q ha hb hq hqQ h r 0 hr (by omega) x y

theorem exists_dfiEquation28_ySlice_derivative_profile_of_profiles
    {f : ℝ → ℝ → ℂ} {ψ : ℝ → ℂ} {P X Y U Q : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cψ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hψ : DFIRedundantCutoff ψ U) (hψC : DFIRedundantCutoffProfile hψ Cψ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (w : DFIDeltaWeight Q) (hwC : DFIDeltaWeightProfile w Cw)
    (hUQ : U = Q ^ 2) (J : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b q : ℕ), 0 < a → 0 < b → 0 < q →
        (q : ℝ) ≤ 2 * Q → ∀ (h : ℤ) (x : ℝ) (r : ℕ), r ≤ J →
        ∀ y : ℝ,
        ‖iteratedDeriv r
          (dfiEquation23Weight w (dfiLocalizedWeight f ψ h)
            a b h q x) y‖ ≤
          C * ((q : ℝ) * Q)⁻¹ *
            ((b : ℝ) / ((q : ℝ) * Q)) ^ r := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_dfiEquation28_mixed_derivative_profile_of_profiles
      hf hfC hbox hψ hψC hscale w hwC hUQ 0 J
  refine ⟨C, hC, ?_⟩
  intro a b q ha hb hq hqQ h x r hr y
  simpa [dfiMixedDeriv] using
    hbound a b q ha hb hq hqQ h 0 r (by omega) hr x y

end RiemannZeta.GuthMaynard
