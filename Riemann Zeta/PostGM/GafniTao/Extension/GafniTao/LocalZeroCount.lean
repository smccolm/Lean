import GafniTao.CriticalStripReflection

/-!
# Unit-window zeta-zero multiplicity

Gafni--Tao Lemma 2.3 uses the classical fact that every unit ordinate
interval inside `[-T,T]` contains `O(log T)` nontrivial zeros, counted with
analytic multiplicity.  This file proves the exact finite Jensen estimate for
the symmetric zero set used by the isolated project.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

/-- Zeros from the actual symmetric source set whose ordinates lie in the
half-open integer bin `[z,z+1)`. -/
noncomputable def zeroLocalUnitBin (sigma T : ℝ) (z : ℤ) : Finset ℂ :=
  (zeroSet sigma T).filter
    (fun rho => (z : ℝ) ≤ rho.im ∧ rho.im < (z : ℝ) + 1)

/-- The explicit Jensen majorant used for a unit bin. -/
noncomputable def localZeroJensenMajorant (T : ℝ) : ℝ :=
  Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
    Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))

/-- Polynomial zeta growth on the pole-safe Jensen circle for any integer
unit bin inside the symmetric height range, away from the finitely many bins
meeting the real axis. -/
theorem zeta_local_unit_sphere_bound
    (T : ℝ) (z : ℤ) (hT : 8 ≤ T)
    (hzLower : -T - 1 ≤ (z : ℝ)) (hzUpper : (z : ℝ) ≤ T)
    (hzFar : (3 : ℤ) ≤ z ∨ z ≤ -4) :
    ∀ w ∈ Metric.sphere
        (2 + I * (((z : ℝ) + 1 / 2 : ℝ) : ℂ)) (7 / 4),
      ‖riemannZeta w‖ ≤ 100 * T ^ (3 : ℝ) := by
  intro w hw
  rw [Metric.mem_sphere, dist_eq_norm] at hw
  let c : ℂ := 2 + I * (((z : ℝ) + 1 / 2 : ℝ) : ℂ)
  have hwc : ‖w - c‖ = 7 / 4 := by simpa [c] using hw
  have hreDiff : |w.re - 2| ≤ 7 / 4 := by
    calc
      |w.re - 2| = |(w - c).re| := by simp [c]
      _ ≤ ‖w - c‖ := abs_re_le_norm _
      _ = 7 / 4 := hwc
  have himDiff : |w.im - ((z : ℝ) + 1 / 2)| ≤ 7 / 4 := by
    calc
      |w.im - ((z : ℝ) + 1 / 2)| = |(w - c).im| := by simp [c]
      _ ≤ ‖w - c‖ := abs_im_le_norm _
      _ = 7 / 4 := hwc
  have hre : (1 / 4 : ℝ) ≤ w.re := by
    have h := (abs_le.mp hreDiff).1
    linarith
  have him : 1 ≤ |w.im| := by
    rcases hzFar with hzPos | hzNeg
    · have hzPosReal : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzPos
      have hLower := (abs_le.mp himDiff).1
      have hwIm : 1 ≤ w.im := by linarith
      exact hwIm.trans (le_abs_self w.im)
    · have hzNegReal : (z : ℝ) ≤ -4 := by exact_mod_cast hzNeg
      have hUpper := (abs_le.mp himDiff).2
      have hwIm : w.im ≤ -1 := by linarith
      rw [abs_of_nonpos (hwIm.trans (by norm_num))]
      linarith
  have hcNorm : ‖c‖ ≤ T + 7 / 2 := by
    calc
      ‖c‖ ≤ |c.re| + |c.im| := Complex.norm_le_abs_re_add_abs_im c
      _ = 2 + |(z : ℝ) + 1 / 2| := by simp [c]
      _ ≤ T + 7 / 2 := by
        have habs : |(z : ℝ) + 1 / 2| ≤ T + 3 / 2 := by
          rw [abs_le]
          constructor <;> linarith
        linarith
  have hwNorm : ‖w‖ ≤ 2 * T := by
    calc
      ‖w‖ = ‖(w - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le _ _
      _ = 7 / 4 + ‖c‖ := by rw [hwc]
      _ ≤ 7 / 4 + (T + 7 / 2) := by gcongr
      _ ≤ 2 * T := by linarith
  calc
    ‖riemannZeta w‖ ≤ 5 * ‖w‖ :=
      norm_riemannZeta_le_five_mul_norm hre him
    _ ≤ 10 * T := by nlinarith [norm_nonneg w]
    _ ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT0 : 0 ≤ T := by linarith
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        10 * T ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring

/-- Jensen's formula bounds every pole-safe unit ordinate bin in the actual
symmetric zero set.  The only omitted bins are the seven integer bins meeting
the fixed neighbourhood of the real axis; they are handled separately below. -/
theorem zeroLocalUnitBin_multiplicity_le_jensen_far
    (sigma T : ℝ) (z : ℤ)
    (hsigmaLower : 1 / 2 ≤ sigma) (hT : 8 ≤ T)
    (hzFar : (3 : ℤ) ≤ z ∨ z ≤ -4) :
    ((∑ rho ∈ zeroLocalUnitBin sigma T z,
        analyticVanishingOrder riemannZeta rho : ℕ) : ℝ) ≤
      localZeroJensenMajorant T := by
  let S := zeroLocalUnitBin sigma T z
  by_cases hSEmpty : S = ∅
  · change ((∑ rho ∈ S, analyticVanishingOrder riemannZeta rho : ℕ) : ℝ) ≤ _
    rw [hSEmpty]
    simp only [Finset.sum_empty, Nat.cast_zero]
    have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
      apply Real.log_pos
      norm_num
    have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        1 ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring
    have hRatio : 1 ≤ (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
      norm_num at hM ⊢
      nlinarith
    exact div_nonneg (Real.log_nonneg hRatio) hLogDen.le
  · have hSNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSEmpty
    obtain ⟨rho0, hrho0⟩ := hSNonempty
    have hrho0Data := Finset.mem_filter.mp hrho0
    have hrho0Rect : rho0 ∈ zerosInRect sigma 1 (-T) T := hrho0Data.1
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hrho0Rect
    have hzLower : -T - 1 ≤ (z : ℝ) := by
      linarith [hrho0Rect.1.2.2.1, hrho0Data.2.2]
    have hzUpper : (z : ℝ) ≤ T := by
      linarith [hrho0Rect.1.2.2.2, hrho0Data.2.1]
    let c : ℂ := 2 + I * (((z : ℝ) + 1 / 2 : ℝ) : ℂ)
    let U : Set ℂ := Metric.closedBall c (7 / 4 : ℝ)
    have hUAnalytic : AnalyticOnNhd ℂ riemannZeta U := by
      apply analyticOn_riemannZeta.mono
      intro w hw
      have hwNorm : ‖w - c‖ ≤ 7 / 4 := by
        simpa [U, Metric.mem_closedBall, dist_eq_norm] using hw
      have hwImDiff : |w.im - ((z : ℝ) + 1 / 2)| ≤ 7 / 4 := by
        calc
          |w.im - ((z : ℝ) + 1 / 2)| = |(w - c).im| := by simp [c]
          _ ≤ ‖w - c‖ := abs_im_le_norm _
          _ ≤ 7 / 4 := hwNorm
      intro hwOne
      subst w
      rcases hzFar with hzPos | hzNeg
      · have hzPosReal : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzPos
        have hLower := (abs_le.mp hwImDiff).1
        norm_num [c] at hLower
        linarith
      · have hzNegReal : (z : ℝ) ≤ -4 := by exact_mod_cast hzNeg
        have hUpper := (abs_le.mp hwImDiff).2
        norm_num [c] at hUpper
        linarith
    have hcLower : (0.6 : ℝ) ≤ ‖riemannZeta c‖ := by
      simpa [c] using euler_product_lower_bound_2 (z : ℝ)
    have hcNe : riemannZeta c ≠ 0 := by
      intro hcZero
      rw [hcZero, norm_zero] at hcLower
      norm_num at hcLower
    have hcOrder : analyticOrderAt riemannZeta c ≠ ⊤ := by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hcNe)]
      exact ENat.coe_ne_top 0
    have hSU : ∀ rho ∈ S, rho ∈ Metric.closedBall c (8 / 5 : ℝ) := by
      intro rho hrho
      have hrhoData := Finset.mem_filter.mp hrho
      have hrhoRect : rho ∈ zerosInRect sigma 1 (-T) T := hrhoData.1
      rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
        mem_ZeroRectangle] at hrhoRect
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hreLower : -(3 / 2 : ℝ) ≤ (rho - c).re := by
        norm_num [c]
        linarith [hsigmaLower, hrhoRect.1.1]
      have hreUpper : (rho - c).re ≤ -1 := by
        norm_num [c]
        linarith [hrhoRect.1.2.1]
      have himLower : -(1 / 2 : ℝ) ≤ (rho - c).im := by
        norm_num [c]
        linarith [hrhoData.2.1]
      have himUpper : (rho - c).im ≤ 1 / 2 := by
        norm_num [c]
        linarith [hrhoData.2.2]
      rw [mul_self_le_mul_self_iff (norm_nonneg _) (by norm_num)]
      rw [Complex.norm_mul_self_eq_normSq, normSq_apply]
      nlinarith [sq_nonneg ((rho - c).re + 3 / 2),
        sq_nonneg ((rho - c).im + 1 / 2),
        sq_nonneg ((rho - c).im - 1 / 2)]
    let V : Set ℂ := Metric.closedBall c (8 / 5 : ℝ)
    have hVAnalytic : AnalyticOnNhd ℂ riemannZeta V :=
      hUAnalytic.mono
        (Metric.closedBall_subset_closedBall (by norm_num : (8 / 5 : ℝ) ≤ 7 / 4))
    have hBridge := finset_analyticVanishingOrder_le_finsum_divisor hVAnalytic
      (isCompact_closedBall c (8 / 5 : ℝ))
      (convex_closedBall c (8 / 5 : ℝ)).isPreconnected (by
        simp only [V, Metric.mem_closedBall, dist_self]
        norm_num) hcOrder S
      (by simpa [V] using hSU)
    have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        1 ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring
    have hUAnalyticAbs : AnalyticOnNhd ℂ riemannZeta
        (Metric.closedBall c |(7 / 4 : ℝ)|) := by
      simpa [U, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using hUAnalytic
    have hJensen := hUAnalyticAbs.sum_divisor_le
      (r := (8 / 5 : ℝ)) (R := (7 / 4 : ℝ))
      (M := 100 * T ^ (3 : ℝ)) (by norm_num) (by norm_num) hM hcNe (by
        intro w hw
        exact zeta_local_unit_sphere_bound T z hT hzLower hzUpper hzFar w (by
          simpa [c, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using hw))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 8 / 5)] at hJensen
    change ((∑ rho ∈ S, analyticVanishingOrder riemannZeta rho : ℕ) : ℝ) ≤ _
    refine hBridge.trans (le_trans (by simpa [c, V] using hJensen) ?_)
    have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
      apply Real.log_pos
      norm_num
    apply div_le_div_of_nonneg_right _ hLogDen.le
    have hMPos : 0 < 100 * T ^ (3 : ℕ) := by positivity
    have hcNormPos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr hcNe
    have hRatioLe : (100 * T ^ (3 : ℕ)) / ‖riemannZeta c‖ ≤
        (100 * T ^ (3 : ℕ)) / (0.6 : ℝ) :=
      div_le_div_of_nonneg_left hMPos.le (by norm_num) hcLower
    exact Real.log_le_log
      (div_pos hMPos (by simpa [c] using hcNormPos)) (by simpa [c] using hRatioLe)

/-- The finitely many unit bins near the real axis inject into one fixed
compact zero rectangle.  This avoids placing a Jensen circle across the pole
at `s = 1` and keeps the exceptional contribution independent of `T`. -/
theorem zeroLocalUnitBin_subset_fixedZeroSet
    {sigma T : ℝ} {z : ℤ} (hsigmaLower : 0 ≤ sigma)
    (hzLower : (-3 : ℤ) ≤ z) (hzUpper : z ≤ 2) :
    zeroLocalUnitBin sigma T z ⊆ zeroSet 0 8 := by
  intro rho hrho
  have hrhoData := Finset.mem_filter.mp hrho
  have hrhoRect : rho ∈ zerosInRect sigma 1 (-T) T := hrhoData.1
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_ZeroRectangle] at hrhoRect
  change rho ∈ zerosInRect 0 1 (-8) 8
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_ZeroRectangle]
  refine ⟨?_, hrhoRect.2⟩
  refine ⟨?_, hrhoRect.1.2.1, ?_, ?_⟩
  · linarith
  · have hzLowerReal : (-3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hzLower
    linarith [hrhoData.2.1]
  · have hzUpperReal : (z : ℝ) ≤ 2 := by exact_mod_cast hzUpper
    linarith [hrhoData.2.2]

/-- Multiplicity in a near-axis unit bin is bounded by the fixed symmetric
zero count at height eight. -/
theorem zeroLocalUnitBin_multiplicity_le_fixed
    (sigma T : ℝ) (z : ℤ) (hsigmaLower : 0 ≤ sigma)
    (hzLower : (-3 : ℤ) ≤ z) (hzUpper : z ≤ 2) :
    ∑ rho ∈ zeroLocalUnitBin sigma T z,
        analyticVanishingOrder riemannZeta rho ≤ zeroCount 0 8 := by
  rw [zeroCount_eq_weighted_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact zeroLocalUnitBin_subset_fixedZeroSet hsigmaLower hzLower hzUpper
  · intro rho _ _
    exact Nat.zero_le _

/-- Uniform explicit unit-window bound for the actual symmetric zero set.
The fixed term is present only to cover the seven bins near the pole. -/
theorem zeroLocalUnitBin_multiplicity_le
    (sigma T : ℝ) (z : ℤ)
    (hsigmaLower : 1 / 2 ≤ sigma) (hT : 8 ≤ T) :
    ((∑ rho ∈ zeroLocalUnitBin sigma T z,
        analyticVanishingOrder riemannZeta rho : ℕ) : ℝ) ≤
      (zeroCount 0 8 : ℝ) + localZeroJensenMajorant T := by
  by_cases hzLower : (-3 : ℤ) ≤ z
  · by_cases hzUpper : z ≤ 2
    · have hFixed := zeroLocalUnitBin_multiplicity_le_fixed sigma T z
          (by linarith) hzLower hzUpper
      have hFixedReal :
          ((∑ rho ∈ zeroLocalUnitBin sigma T z,
              analyticVanishingOrder riemannZeta rho : ℕ) : ℝ) ≤
            (zeroCount 0 8 : ℝ) := by
        exact_mod_cast hFixed
      exact hFixedReal.trans (le_add_of_nonneg_right (by
        unfold localZeroJensenMajorant
        have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
          apply Real.log_pos
          norm_num
        have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
          norm_num [Real.rpow_natCast]
          have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
          calc
            1 ≤ 100 * T := by nlinarith
            _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
            _ = 100 * T ^ (3 : ℕ) := by ring
        have hRatio : 1 ≤ (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
          norm_num at hM ⊢
          nlinarith
        exact div_nonneg (Real.log_nonneg hRatio) hLogDen.le))
    · have hzFar : (3 : ℤ) ≤ z := by omega
      exact (zeroLocalUnitBin_multiplicity_le_jensen_far sigma T z
        hsigmaLower hT (Or.inl hzFar)).trans (le_add_of_nonneg_left (by positivity))
  · have hzFar : z ≤ -4 := by omega
    exact (zeroLocalUnitBin_multiplicity_le_jensen_far sigma T z
      hsigmaLower hT (Or.inr hzFar)).trans (le_add_of_nonneg_left (by positivity))

/-- An explicit constant for the source `O(log T)` local-zero estimate. -/
noncomputable def localZeroLogConstant : ℝ :=
  (zeroCount 0 8 : ℝ) +
    100 / Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))

theorem localZeroLogConstant_pos : 0 < localZeroLogConstant := by
  unfold localZeroLogConstant
  have hD : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    apply Real.log_pos
    norm_num
  have hQ : 0 < 100 / Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) :=
    div_pos (by norm_num) hD
  positivity

/-- Source-facing classical local zero count: every half-open unit ordinate
window in the symmetric set contains at most `C log T` zeros, with analytic
multiplicity and a single explicit constant `C`. -/
theorem zeroLocalUnitBin_multiplicity_le_log
    (sigma T : ℝ) (z : ℤ)
    (hsigmaLower : 1 / 2 ≤ sigma)
    (hT : max (Real.exp 2) 8 ≤ T) :
    ((∑ rho ∈ zeroLocalUnitBin sigma T z,
        analyticVanishingOrder riemannZeta rho : ℕ) : ℝ) ≤
      localZeroLogConstant * Real.log T := by
  have hTExp : Real.exp 2 ≤ T := le_trans (le_max_left _ _) hT
  have hTEight : 8 ≤ T := le_trans (le_max_right _ _) hT
  have hTPos : 0 < T := by linarith [Real.exp_pos 2]
  have hLogTwo : 2 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 2) hTExp
    simpa using h
  have hLogOne : 1 ≤ Real.log T := by linarith
  have hD : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    apply Real.log_pos
    norm_num
  have hRaw := zeroLocalUnitBin_multiplicity_le sigma T z hsigmaLower hTEight
  have hNumerator :
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) ≤
        100 * Real.log T := by
    have hConst := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 500 / 3 by norm_num)
    calc
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) =
          Real.log ((500 / 3 : ℝ) * T ^ (3 : ℝ)) := by
        congr 1
        ring
      _ = Real.log (500 / 3 : ℝ) + Real.log (T ^ (3 : ℝ)) := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hTPos 3).ne']
      _ = Real.log (500 / 3 : ℝ) + 3 * Real.log T := by
        rw [Real.log_rpow hTPos]
      _ ≤ 100 * Real.log T := by nlinarith
  have hJensen :
      localZeroJensenMajorant T ≤
        (100 / Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) * Real.log T := by
    unfold localZeroJensenMajorant
    calc
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
            Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))
          ≤ (100 * Real.log T) /
            Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) :=
        div_le_div_of_nonneg_right hNumerator hD.le
      _ = (100 / Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) * Real.log T := by ring
  calc
    ((∑ rho ∈ zeroLocalUnitBin sigma T z,
        analyticVanishingOrder riemannZeta rho : ℕ) : ℝ)
        ≤ (zeroCount 0 8 : ℝ) + localZeroJensenMajorant T := hRaw
    _ ≤ (zeroCount 0 8 : ℝ) * Real.log T +
          (100 / Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) * Real.log T := by
      exact add_le_add (le_mul_of_one_le_right (by positivity) hLogOne) hJensen
    _ = localZeroLogConstant * Real.log T := by
      unfold localZeroLogConstant
      ring

/-- A left-half zero in a local unit bin reflects into the critical-line
zero set, with its analytic multiplicity unchanged. -/
theorem zeroLocalUnitBin_reflect_data
    {sigma T : ℝ} {z : ℤ} {rho : ℂ}
    (hsigma : 0 ≤ sigma)
    (hrho : rho ∈ zeroLocalUnitBin sigma T z)
    (hrhoLeft : rho.re < 1 / 2) :
    criticalStripReflect rho ∈ zeroSet (1 / 2) T ∧
      zeroMultiplicity (criticalStripReflect rho) = zeroMultiplicity rho := by
  have hrhoData := Finset.mem_filter.mp hrho
  have hrhoRect : rho ∈ zerosInRect sigma 1 (-T) T := hrhoData.1
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    mem_ZeroRectangle] at hrhoRect
  rcases hrhoRect with ⟨hrhoRect, hrhoZero⟩
  have hrhoNonneg : 0 ≤ rho.re := hsigma.trans hrhoRect.1
  have hrhoPos := zero_re_pos_of_nonneg hrhoNonneg hrhoRect.2.1 hrhoZero
  have hrhoLtOne := zero_re_lt_one_of_le_one hrhoRect.2.1 hrhoZero
  constructor
  · change criticalStripReflect rho ∈ zerosInRect (1 / 2) 1 (-T) T
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle]
    refine ⟨⟨?_, ?_, ?_, ?_⟩,
      riemannZeta_criticalStripReflect_eq_zero hrhoPos hrhoLtOne hrhoZero⟩
    · simp [criticalStripReflect]
      linarith
    · simp [criticalStripReflect]
      linarith
    · simp [criticalStripReflect]
      linarith [hrhoRect.2.2.2]
    · simp [criticalStripReflect]
      linarith [hrhoRect.2.2.1]
  · exact zeroMultiplicity_criticalStripReflect hrhoPos hrhoLtOne

/-- Every unit ordinate window in the whole closed source strip
`0 ≤ Re s ≤ 1` contains `O(log T)` zeros with analytic multiplicity.  The
factor three is the exact bookkeeping cost here: one right-half bin and the
two half-open bins needed for the reflected interval `(-z-1,-z]`. -/
theorem zeroLocalUnitBin_multiplicity_le_three_mul_log
    (sigma T : ℝ) (z : ℤ)
    (hsigma : 0 ≤ sigma)
    (hT : max (Real.exp 2) 8 ≤ T) :
    ((∑ rho ∈ zeroLocalUnitBin sigma T z,
        analyticVanishingOrder riemannZeta rho : ℕ) : ℝ) ≤
      3 * (localZeroLogConstant * Real.log T) := by
  classical
  let S := zeroLocalUnitBin sigma T z
  let U := S.filter fun rho => (1 / 2 : ℝ) ≤ rho.re
  let L := S.filter fun rho => ¬(1 / 2 : ℝ) ≤ rho.re
  let L₁ := L.filter fun rho =>
    (criticalStripReflect rho).im < ((-z : ℤ) : ℝ)
  let L₂ := L.filter fun rho =>
    ¬(criticalStripReflect rho).im < ((-z : ℤ) : ℝ)
  let H₀ := zeroLocalUnitBin (1 / 2) T z
  let H₁ := zeroLocalUnitBin (1 / 2) T (-z - 1)
  let H₂ := zeroLocalUnitBin (1 / 2) T (-z)
  have hUpperSubset : U ⊆ H₀ := by
    intro rho hrho
    rcases Finset.mem_filter.mp hrho with ⟨hrhoS, hrhoHalf⟩
    have hrhoData := Finset.mem_filter.mp hrhoS
    change rho ∈ zeroLocalUnitBin (1 / 2) T z
    rw [zeroLocalUnitBin, Finset.mem_filter]
    refine ⟨?_, hrhoData.2⟩
    change rho ∈ zerosInRect (1 / 2) 1 (-T) T
    have hrhoRect : rho ∈ zerosInRect sigma 1 (-T) T := hrhoData.1
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hrhoRect ⊢
    exact ⟨⟨hrhoHalf, hrhoRect.1.2.1, hrhoRect.1.2.2.1,
      hrhoRect.1.2.2.2⟩, hrhoRect.2⟩
  have hReflectInjective : Function.Injective criticalStripReflect := by
    intro rho rho' h
    unfold criticalStripReflect at h
    linear_combination -h
  have hL₁Subset : L₁.image criticalStripReflect ⊆ H₁ := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨rho, hrho, rfl⟩ := hw
    rcases Finset.mem_filter.mp hrho with ⟨hrhoL, hrefUpper⟩
    rcases Finset.mem_filter.mp hrhoL with ⟨hrhoS, hrhoLeft⟩
    have hrhoData := Finset.mem_filter.mp hrhoS
    change criticalStripReflect rho ∈ zeroLocalUnitBin (1 / 2) T (-z - 1)
    rw [zeroLocalUnitBin, Finset.mem_filter]
    refine ⟨(zeroLocalUnitBin_reflect_data hsigma hrhoS
      (lt_of_not_ge hrhoLeft)).1, ?_⟩
    simp only [criticalStripReflect, sub_im, one_im, zero_sub]
    change (((-z - 1 : ℤ) : ℝ) ≤ -(rho.im)) ∧
      -(rho.im) < ((-z - 1 : ℤ) : ℝ) + 1
    simp only [criticalStripReflect, sub_im, one_im, zero_sub] at hrefUpper
    rcases hrhoData.2 with ⟨hrhoLower, hrhoUpper⟩
    push_cast at hrefUpper ⊢
    constructor <;> linarith
  have hL₂Subset : L₂.image criticalStripReflect ⊆ H₂ := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨rho, hrho, rfl⟩ := hw
    rcases Finset.mem_filter.mp hrho with ⟨hrhoL, hrefLower⟩
    rcases Finset.mem_filter.mp hrhoL with ⟨hrhoS, hrhoLeft⟩
    have hrhoData := Finset.mem_filter.mp hrhoS
    change criticalStripReflect rho ∈ zeroLocalUnitBin (1 / 2) T (-z)
    rw [zeroLocalUnitBin, Finset.mem_filter]
    refine ⟨(zeroLocalUnitBin_reflect_data hsigma hrhoS
      (lt_of_not_ge hrhoLeft)).1, ?_⟩
    simp only [criticalStripReflect, sub_im, one_im, zero_sub]
    change (((-z : ℤ) : ℝ) ≤ -(rho.im)) ∧
      -(rho.im) < ((-z : ℤ) : ℝ) + 1
    simp only [criticalStripReflect, sub_im, one_im, zero_sub] at hrefLower
    push Not at hrefLower
    rcases hrhoData.2 with ⟨hrhoLower, _hrhoUpper⟩
    push_cast at hrefLower ⊢
    constructor <;> linarith
  have hUpperLe :
      ∑ rho ∈ U, zeroMultiplicity rho ≤
        ∑ rho ∈ H₀, zeroMultiplicity rho :=
    Finset.sum_le_sum_of_subset_of_nonneg hUpperSubset
      (fun _ _ _ => Nat.zero_le _)
  have hL₁Multiplicity : ∀ rho ∈ L₁,
      zeroMultiplicity (criticalStripReflect rho) = zeroMultiplicity rho := by
    intro rho hrho
    rcases Finset.mem_filter.mp hrho with ⟨hrhoL, _⟩
    rcases Finset.mem_filter.mp hrhoL with ⟨hrhoS, hrhoLeft⟩
    exact (zeroLocalUnitBin_reflect_data hsigma hrhoS
      (lt_of_not_ge hrhoLeft)).2
  have hL₂Multiplicity : ∀ rho ∈ L₂,
      zeroMultiplicity (criticalStripReflect rho) = zeroMultiplicity rho := by
    intro rho hrho
    rcases Finset.mem_filter.mp hrho with ⟨hrhoL, _⟩
    rcases Finset.mem_filter.mp hrhoL with ⟨hrhoS, hrhoLeft⟩
    exact (zeroLocalUnitBin_reflect_data hsigma hrhoS
      (lt_of_not_ge hrhoLeft)).2
  have hL₁SumEq :
      ∑ rho ∈ L₁, zeroMultiplicity rho =
        ∑ rho ∈ L₁.image criticalStripReflect, zeroMultiplicity rho := by
    rw [Finset.sum_image hReflectInjective.injOn]
    exact Finset.sum_congr rfl fun rho hrho => (hL₁Multiplicity rho hrho).symm
  have hL₂SumEq :
      ∑ rho ∈ L₂, zeroMultiplicity rho =
        ∑ rho ∈ L₂.image criticalStripReflect, zeroMultiplicity rho := by
    rw [Finset.sum_image hReflectInjective.injOn]
    exact Finset.sum_congr rfl fun rho hrho => (hL₂Multiplicity rho hrho).symm
  have hL₁Le :
      ∑ rho ∈ L₁, zeroMultiplicity rho ≤
        ∑ rho ∈ H₁, zeroMultiplicity rho := by
    rw [hL₁SumEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hL₁Subset
      (fun _ _ _ => Nat.zero_le _)
  have hL₂Le :
      ∑ rho ∈ L₂, zeroMultiplicity rho ≤
        ∑ rho ∈ H₂, zeroMultiplicity rho := by
    rw [hL₂SumEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hL₂Subset
      (fun _ _ _ => Nat.zero_le _)
  have hPartitionS :
      ∑ rho ∈ S, zeroMultiplicity rho =
        (∑ rho ∈ U, zeroMultiplicity rho) +
          ∑ rho ∈ L, zeroMultiplicity rho := by
    simpa [U, L] using (Finset.sum_filter_add_sum_filter_not S
      (fun rho => (1 / 2 : ℝ) ≤ rho.re) zeroMultiplicity).symm
  have hPartitionL :
      ∑ rho ∈ L, zeroMultiplicity rho =
        (∑ rho ∈ L₁, zeroMultiplicity rho) +
          ∑ rho ∈ L₂, zeroMultiplicity rho := by
    simpa [L₁, L₂] using (Finset.sum_filter_add_sum_filter_not L
      (fun rho => (criticalStripReflect rho).im < ((-z : ℤ) : ℝ))
      zeroMultiplicity).symm
  have hNat :
      ∑ rho ∈ S, zeroMultiplicity rho ≤
        (∑ rho ∈ H₀, zeroMultiplicity rho) +
          (∑ rho ∈ H₁, zeroMultiplicity rho) +
            ∑ rho ∈ H₂, zeroMultiplicity rho := by
    rw [hPartitionS, hPartitionL]
    omega
  have hReal :
      ((∑ rho ∈ S, zeroMultiplicity rho : ℕ) : ℝ) ≤
        ((∑ rho ∈ H₀, zeroMultiplicity rho : ℕ) : ℝ) +
          ((∑ rho ∈ H₁, zeroMultiplicity rho : ℕ) : ℝ) +
            ((∑ rho ∈ H₂, zeroMultiplicity rho : ℕ) : ℝ) := by
    exact_mod_cast hNat
  have h₀ := zeroLocalUnitBin_multiplicity_le_log (1 / 2) T z (by norm_num) hT
  have h₁ := zeroLocalUnitBin_multiplicity_le_log
    (1 / 2) T (-z - 1) (by norm_num) hT
  have h₂ := zeroLocalUnitBin_multiplicity_le_log (1 / 2) T (-z) (by norm_num) hT
  change ((∑ rho ∈ S, zeroMultiplicity rho : ℕ) : ℝ) ≤ _
  calc
    ((∑ rho ∈ S, zeroMultiplicity rho : ℕ) : ℝ) ≤
        ((∑ rho ∈ H₀, zeroMultiplicity rho : ℕ) : ℝ) +
          ((∑ rho ∈ H₁, zeroMultiplicity rho : ℕ) : ℝ) +
            ((∑ rho ∈ H₂, zeroMultiplicity rho : ℕ) : ℝ) := hReal
    _ ≤ (localZeroLogConstant * Real.log T) +
          (localZeroLogConstant * Real.log T) +
            (localZeroLogConstant * Real.log T) := by
      gcongr
    _ = 3 * (localZeroLogConstant * Real.log T) := by ring

/-- The whole-critical-strip local-zero constant used by the moment
consumers. -/
noncomputable def globalLocalZeroLogConstant : ℝ :=
  3 * localZeroLogConstant

theorem globalLocalZeroLogConstant_pos : 0 < globalLocalZeroLogConstant := by
  unfold globalLocalZeroLogConstant
  exact mul_pos (by norm_num) localZeroLogConstant_pos

/-- Source-facing whole-strip version of the unit-window estimate. -/
theorem zeroLocalUnitBin_multiplicity_le_global_log
    (sigma T : ℝ) (z : ℤ)
    (hsigma : 0 ≤ sigma)
    (hT : max (Real.exp 2) 8 ≤ T) :
    ((∑ rho ∈ zeroLocalUnitBin sigma T z,
        analyticVanishingOrder riemannZeta rho : ℕ) : ℝ) ≤
      globalLocalZeroLogConstant * Real.log T := by
  simpa [globalLocalZeroLogConstant, mul_assoc] using
    zeroLocalUnitBin_multiplicity_le_three_mul_log sigma T z hsigma hT

end GafniTao
