import GafniTao.ZeroEnergy

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
      gcongr
      · exact le_mul_of_one_le_right (by positivity) hLogOne
      · exact hJensen
    _ = localZeroLogConstant * Real.log T := by
      unfold localZeroLogConstant
      ring

end GafniTao
