import RiemannZeta.GuthMaynard.DFIBesselMellin

open Complex Set MeasureTheory

namespace RiemannZeta.GuthMaynard

theorem probe_sqrt_sqrt_mul_factor (x : ℝ) (n : ℕ)
    (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt (x * n)) =
      Real.sqrt (Real.sqrt x) * (n : ℝ) ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_mul hx]
  rw [Real.sqrt_mul (Real.sqrt_nonneg x)]
  have hn4 : Real.sqrt (Real.sqrt (n : ℝ)) =
      (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  rw [hn4]

theorem probe_quarter_integrand_factor (g : ℝ → ℂ) (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 0 < n) :
    ‖g x‖ / Real.sqrt (Real.sqrt (x * n)) =
      (n : ℝ) ^ (-(1 / 4 : ℝ)) *
        (‖g x‖ / Real.sqrt (Real.sqrt x)) := by
  rw [probe_sqrt_sqrt_mul_factor x n hx.le]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hnR _
  have hxq : 0 < Real.sqrt (Real.sqrt x) := by positivity
  rw [Real.rpow_neg hnR.le]
  field_simp [hnx.ne', hxq.ne']

theorem probe_continuous_quarterWeight {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) :
    Continuous (fun x : ℝ => ‖g x‖ / Real.sqrt (Real.sqrt x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x < hg.lower
  · have hzero : (fun x : ℝ => ‖g x‖ / Real.sqrt (Real.sqrt x)) =ᶠ[nhds x]
        fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      have hgy : g y = 0 := by
        by_contra hne
        exact (not_le_of_gt hy) (hg.support_subset hne).1
      simp [hgy]
    exact continuousAt_const.congr_of_eventuallyEq hzero
  · have hxpos : 0 < x := hg.lower_pos.trans_le (not_lt.mp hx)
    exact hg.continuous.continuousAt.norm.div
      (Real.continuous_sqrt.comp Real.continuous_sqrt).continuousAt
      (by exact (Real.sqrt_pos.2 (Real.sqrt_pos.2 hxpos)).ne')

theorem probe_integrableOn_quarterWeight {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) :
    IntegrableOn (fun x : ℝ => ‖g x‖ / Real.sqrt (Real.sqrt x)) (Set.Ioi 0) := by
  have hSupport : Function.support
      (fun x : ℝ => ‖g x‖ / Real.sqrt (Real.sqrt x)) ⊆ Function.support g := by
    intro x hx
    by_contra hgx
    exact hx (by simp [Function.mem_support] at hgx ⊢; simp [hgx])
  have hCompact : HasCompactSupport
      (fun x : ℝ => ‖g x‖ / Real.sqrt (Real.sqrt x)) :=
    HasCompactSupport.mono hg.hasCompactSupport hSupport
  exact (probe_continuous_quarterWeight hg).integrable_of_hasCompactSupport hCompact |>.integrableOn

theorem probe_plus_multiplier_eq_scaled_K0_mellin
    (q n : ℕ) [NeZero q] (hn : 0 < n) (z : ℂ)
    (hz : 0 < (1 - z).re) :
    (n : ℂ) ^ (-(1 - z)) * dfiVoronoiPlusMultiplier q z =
      (4 / (q : ℂ)) * mellin
        (fun x : ℝ => (dfiBesselK0
          ((4 * Real.pi * Real.sqrt n / q) * Real.sqrt x) : ℂ))
        (1 - z) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let A : ℝ := 4 * Real.pi * Real.sqrt n / q
  have hA : 0 < A := by dsimp [A]; positivity
  rw [mellin_dfiBesselK0_mul_sqrt hA hz]
  dsimp [A]
  rw [dfiBesselK0MellinSymbol_two_mul]
  unfold dfiVoronoiPlusMultiplier dfiPeriodicArchimedeanFactor
  ring_nf
  have hsplit (e : ℂ) :
      ((Real.pi * Real.sqrt n * (q : ℝ)⁻¹ * 4 : ℝ) : ℂ) ^ e =
        (Real.pi : ℂ) ^ e * (Real.sqrt n : ℂ) ^ e *
          (((q : ℝ)⁻¹ : ℝ) : ℂ) ^ e * (4 : ℂ) ^ e := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
      (mul_nonneg (mul_nonneg Real.pi_nonneg (Real.sqrt_nonneg _))
        (inv_nonneg.mpr (Nat.cast_nonneg q))) (by norm_num)]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
      (mul_nonneg Real.pi_nonneg (Real.sqrt_nonneg _))
        (inv_nonneg.mpr (Nat.cast_nonneg q))]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg
      Real.pi_nonneg (Real.sqrt_nonneg _)]
    norm_num
  rw [hsplit]
  have hsqrtSq : ((Real.sqrt n : ℂ) ^ (2 : ℕ)) = (n : ℂ) := by
    rw [show (Real.sqrt n : ℂ) = ((Real.sqrt n : ℝ) : ℂ) by rfl,
      ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
  have hsqrtArg : Complex.arg (Real.sqrt n : ℂ) = 0 := by
    exact Complex.arg_ofReal_of_nonneg (Real.sqrt_nonneg _)
  have hsqrtPow : (Real.sqrt n : ℂ) ^ (-2 + z * 2) =
      (n : ℂ) ^ (-1 + z) := by
    have hcp := Complex.cpow_nat_mul'
      (n := 2) (x := (Real.sqrt n : ℂ))
      (by simp [hsqrtArg, Real.pi_pos])
      (by simp [hsqrtArg, Real.pi_pos.le]) (-1 + z)
    calc
      (Real.sqrt n : ℂ) ^ (-2 + z * 2) =
          (Real.sqrt n : ℂ) ^ ((2 : ℕ) * (-1 + z)) := by
            congr 1
            norm_num
            ring
      _ = ((Real.sqrt n : ℂ) ^ (2 : ℕ)) ^ (-1 + z) := hcp
      _ = (n : ℂ) ^ (-1 + z) := by rw [hsqrtSq]
  rw [hsqrtPow]
  have hPiTwo (e : ℂ) : ((Real.pi : ℂ) * 2) ^ e =
      (Real.pi : ℂ) ^ e * (2 : ℂ) ^ e := by
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg Real.pi_nonneg
        (by norm_num : (0 : ℝ) ≤ 2) e
  have hPiTwoSq (e : ℂ) : (((Real.pi : ℂ) * 2) ^ e) ^ 2 =
      (Real.pi : ℂ) ^ (e + e) * (2 : ℂ) ^ (e + e) := by
    rw [hPiTwo, pow_two]
    rw [show ((Real.pi : ℂ) ^ e * 2 ^ e) *
        ((Real.pi : ℂ) ^ e * 2 ^ e) =
      ((Real.pi : ℂ) ^ e * (Real.pi : ℂ) ^ e) *
        ((2 : ℂ) ^ e * (2 : ℂ) ^ e) by ring]
    rw [← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
  rw [hPiTwoSq]
  have hFour (e : ℂ) : (4 : ℂ) ^ e =
      (2 : ℂ) ^ e * (2 : ℂ) ^ e := by
    convert Complex.mul_cpow_ofReal_nonneg
      (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2) e using 1 <;>
      norm_num
  rw [hFour, ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
  have hqArg : Complex.arg (q : ℂ) = 0 := by simp
  have hqInvPow (e : ℂ) : (((q : ℝ)⁻¹ : ℝ) : ℂ) ^ e =
      ((q : ℂ) ^ e)⁻¹ := by
    rw [Complex.ofReal_inv]
    apply Complex.inv_cpow (q : ℂ) e
    rw [hqArg]
    exact Real.pi_ne_zero.symm
  rw [hqInvPow]
  ring_nf
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hqLeft : (q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2 =
      (q : ℂ) ^ (1 - 2 * z) := by
    have hsq : ((q : ℂ) ^ (-z)) ^ 2 =
        (q : ℂ) ^ (2 * (-z)) := by
      symm
      convert Complex.cpow_nat_mul (q : ℂ) 2 (-z) using 1
    calc
      (q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2 =
          (q : ℂ) ^ (1 : ℂ) * (q : ℂ) ^ (2 * (-z)) := by
            rw [Complex.cpow_one, hsq]
      _ = (q : ℂ) ^ ((1 : ℂ) + 2 * (-z)) := by
            rw [Complex.cpow_add _ _ hq0]
      _ = (q : ℂ) ^ (1 - 2 * z) := by congr 1; ring
  have hqRight : (q : ℂ)⁻¹ * ((q : ℂ) ^ (-2 + z * 2))⁻¹ =
      (q : ℂ) ^ (1 - 2 * z) := by
    rw [← Complex.cpow_neg_one]
    rw [← Complex.cpow_neg _ (-2 + z * 2)]
    rw [← Complex.cpow_add _ _ hq0]
    congr 1
    ring
  have h2Left : (2 : ℂ) ^ (-2 + z * 2) * 2 =
      (2 : ℂ) ^ (-1 + z * 2) := by
    calc
      (2 : ℂ) ^ (-2 + z * 2) * 2 =
          (2 : ℂ) ^ (-2 + z * 2) * (2 : ℂ) ^ (1 : ℂ) := by simp
      _ = (2 : ℂ) ^ ((-2 + z * 2) + 1) := by
        rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      _ = (2 : ℂ) ^ (-1 + z * 2) := by congr 1; ring
  have h2Right : (2 : ℂ) ^ (-4 + z * 4) *
        (2 : ℂ) ^ (-(z * 2)) * 8 =
      (2 : ℂ) ^ (-1 + z * 2) := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    rw [show (8 : ℂ) = (2 : ℂ) ^ (3 : ℂ) by norm_num]
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
    ring
  calc
    (n : ℂ) ^ (-1 + z) * (q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2 *
          (Real.pi : ℂ) ^ (-2 + z * 2) * (2 : ℂ) ^ (-2 + z * 2) *
          Gamma (1 - z) ^ 2 * 2 =
        (n : ℂ) ^ (-1 + z) * (q : ℂ) ^ (1 - 2 * z) *
          (Real.pi : ℂ) ^ (-2 + z * 2) *
          (2 : ℂ) ^ (-1 + z * 2) * Gamma (1 - z) ^ 2 := by
            rw [show (n : ℂ) ^ (-1 + z) * (q : ℂ) *
                ((q : ℂ) ^ (-z)) ^ 2 * (Real.pi : ℂ) ^ (-2 + z * 2) *
                (2 : ℂ) ^ (-2 + z * 2) * Gamma (1 - z) ^ 2 * 2 =
              (n : ℂ) ^ (-1 + z) *
                ((q : ℂ) * ((q : ℂ) ^ (-z)) ^ 2) *
                (Real.pi : ℂ) ^ (-2 + z * 2) *
                ((2 : ℂ) ^ (-2 + z * 2) * 2) * Gamma (1 - z) ^ 2 by ring]
            rw [hqLeft, h2Left]
    _ = (n : ℂ) ^ (-1 + z) *
          ((q : ℂ)⁻¹ * ((q : ℂ) ^ (-2 + z * 2))⁻¹) *
          (Real.pi : ℂ) ^ (-2 + z * 2) *
          ((2 : ℂ) ^ (-4 + z * 4) *
            (2 : ℂ) ^ (-(z * 2)) * 8) * Gamma (1 - z) ^ 2 := by
            rw [← hqRight, ← h2Right]
    _ = Gamma (1 - z) ^ 2 * (q : ℂ)⁻¹ *
          ((Real.pi : ℂ) ^ (-2 + z * 2) * (n : ℂ) ^ (-1 + z) *
            ((q : ℂ) ^ (-2 + z * 2))⁻¹ * (2 : ℂ) ^ (-4 + z * 4)) *
          (2 : ℂ) ^ (-(z * 2)) * 8 := by
            simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = (n : ℂ) ^ (-1 + z) * (Real.pi : ℂ) ^ (-2 + z * 2) *
          Gamma (1 - z) ^ 2 * (q : ℂ)⁻¹ *
          ((q : ℂ) ^ (-2 + z * 2))⁻¹ *
          (2 : ℂ) ^ (-4 + z * 4) * (2 : ℂ) ^ (-(z * 2)) * 8 := by
            simp only [mul_assoc, mul_left_comm, mul_comm]

end RiemannZeta.GuthMaynard
import RiemannZeta.GuthMaynard.DFIErrorOptimization

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology
open Classical

#check Real.one_lt_rpow
#check Real.rpow_lt_rpow
#check Nat.lt_ceil
#check Nat.ceil_lt_add_one
#check Nat.ceil_pos
#check Nat.ceil_mono
#check Nat.ceil_le
#check Nat.ceil_le_ceil
#check Nat.ceil_sub_one
#check Nat.cast_sub
#check Nat.cast_ceil
#check Nat.le_ceil
#check Real.rpow_le_rpow_of_exponent_le
#check Real.rpow_le_rpow
#check Real.rpow_one
#check Real.one_rpow

namespace RiemannZeta.GuthMaynard

noncomputable def testCutoff (Q η : ℝ) : ℕ :=
  ⌈Q ^ (1 - η)⌉₊ - 1

theorem testCutoff_spec {Q η : ℝ} (hQ : 2 ≤ Q)
    (hη0 : 0 < η) (hη1 : η < 1) :
    1 ≤ testCutoff Q η ∧
      testCutoff Q η < ⌈2 * Q⌉₊ ∧
      testCutoff Q η + 1 = ⌈Q ^ (1 - η)⌉₊ := by
  have hQ1 : 1 < Q := lt_of_lt_of_le (by norm_num) hQ
  have he : 0 < 1 - η := by linarith
  have hpow1 : 1 < Q ^ (1 - η) := Real.one_lt_rpow hQ1 he
  have hceil2 : 2 ≤ ⌈Q ^ (1 - η)⌉₊ := by
    have hlt : 1 < ⌈Q ^ (1 - η)⌉₊ :=
      lt_of_lt_of_le hpow1 (Nat.le_ceil _)
    exact_mod_cast hlt.le
  have hsub : 1 ≤ ⌈Q ^ (1 - η)⌉₊ - 1 := by omega
  have hpowQ : Q ^ (1 - η) ≤ Q := by
    have := Real.rpow_le_rpow_of_exponent_le hQ1.le (by linarith : 1 - η ≤ 1)
    simpa using this
  have hceilLe : ⌈Q ^ (1 - η)⌉₊ ≤ ⌈Q⌉₊ := Nat.ceil_mono hpowQ
  have hQlt : Q < 2 * Q := by linarith
  have hceilQLt : ⌈Q⌉₊ < ⌈2 * Q⌉₊ := by
    have hceilQ : (⌈Q⌉₊ : ℝ) < Q + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2ceil : 2 * Q ≤ (⌈2 * Q⌉₊ : ℝ) := Nat.le_ceil _
    have hGap : Q + 1 ≤ 2 * Q := by linarith
    exact_mod_cast hceilQ.trans_le (hGap.trans h2ceil)
  refine ⟨?_, ?_, ?_⟩
  · simpa [testCutoff] using hsub
  · unfold testCutoff
    omega
  · unfold testCutoff
    omega

end RiemannZeta.GuthMaynard
