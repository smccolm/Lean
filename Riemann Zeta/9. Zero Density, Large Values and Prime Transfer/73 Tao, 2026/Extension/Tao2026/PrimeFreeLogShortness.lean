import Tao2026.ClassicalQuantitativePNT
import Tao2026.PrimeIntervals

/-!
# Logarithmic shortness of prime-free intervals

The native quantitative PNT and the explicit prime-power correction give a
logarithmic error for Chebyshev's theta function. Its constancy on a prime-free
interval yields the upper scale needed by Section 4. This does not assert the
stronger Baker--Harman--Pintz fixed-power gap bound.
-/

namespace Tao2026
open Finset Filter
open scoped Topology
noncomputable section

theorem eventually_two_sqrt_mul_log_le_div_log_pow (A : ℕ) :
    ∀ᶠ x : ℝ in atTop, 2 * Real.sqrt x * Real.log x ≤ x / (Real.log x) ^ A := by
  have hsmall := isLittleO_log_rpow_rpow_atTop ((A + 1 : ℕ) : ℝ)
    (s := (1 / 2 : ℝ)) (by norm_num)
  have hbound := hsmall.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hbound, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hs : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx0.le
  have hx' : (Real.log x) ^ (A + 1) ≤ (1 / 2 : ℝ) * Real.sqrt x := by
    simpa only [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog.le _),
      abs_of_nonneg (Real.rpow_nonneg hx0.le _), ← Real.sqrt_eq_rpow, abs_of_nonneg hsqrt] using hx
  apply (le_div_iff₀ (pow_pos hlog A)).2
  have hmul := mul_le_mul_of_nonneg_left hx' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsqrt)
  rw [pow_succ] at hmul
  nlinarith only [hmul, hs]

theorem classicalChebyshevThetaLogSaving_native (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤ C * x / (Real.log x) ^ A := by
  obtain ⟨C, c, hC, hc, hpsi⟩ := classicalChebyshevPsiDeLaValleePoussin_native
  refine ⟨C + 1, by linarith, ?_⟩
  filter_upwards [hpsi, eventually_exp_neg_sqrt_log_le_log_pow_inv hc A,
    eventually_two_sqrt_mul_log_le_div_log_pow A, eventually_gt_atTop (1 : ℝ)] with x hp he ht hx
  have hx0 : 0 ≤ x := by linarith
  have hsplit : |Chebyshev.theta x - x| ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
    rw [show Chebyshev.theta x - x = (Chebyshev.psi x - x) -
      (Chebyshev.psi x - Chebyshev.theta x) by ring]
    exact abs_sub _ _
  calc
    _ ≤ _ := hsplit
    _ ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x)) + 2 * Real.sqrt x * Real.log x :=
      add_le_add hp (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx.le)
    _ ≤ C * x * (1 / (Real.log x) ^ A) + x / (Real.log x) ^ A :=
      add_le_add (mul_le_mul_of_nonneg_left he (mul_nonneg hC.le hx0)) ht
    _ = _ := by ring

theorem eventually_abs_theta_sub_le_self_div_sixteen_log_sq :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ x / (16 * (Real.log x) ^ 2) := by
  obtain ⟨C, hC, htheta⟩ := classicalChebyshevThetaLogSaving_native 4
  have hlogTop : Tendsto (fun x : ℝ => (Real.log x) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  filter_upwards [htheta, hlogTop.eventually (eventually_ge_atTop (16 * C)),
    eventually_gt_atTop (1 : ℝ)] with x ht hlogLarge hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 ≤ x := by linarith
  apply ht.trans
  apply (div_le_div_iff₀ (pow_pos hlog 4) (by positivity : 0 < 16 * (Real.log x) ^ 2)).2
  have h := mul_le_mul_of_nonneg_left hlogLarge (by positivity : 0 ≤ x * (Real.log x) ^ 2)
  nlinarith only [h]

theorem chebyshevTheta_nat_add_eq_of_primeFree (N H : ℕ)
    (hfree : ∀ p : ℕ, N < p → p ≤ N + H → ¬p.Prime) :
    Chebyshev.theta (N + H : ℕ) = Chebyshev.theta N := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
  have heq : (N + H).primesLE = N.primesLE := by
    ext p
    simp only [Nat.mem_primesLE]
    constructor
    · rintro ⟨hpNH, hp⟩
      refine ⟨?_, hp⟩
      by_contra hpN
      exact hfree p (by omega) hpNH hp
    · rintro ⟨hpN, hp⟩
      exact ⟨by omega, hp⟩
  rw [heq]

theorem eventually_four_mul_primeFree_length_log_sq_le :
    ∀ᶠ N : ℕ in atTop, ∀ H : ℕ,
      (∀ p : ℕ, N < p → p ≤ N + H → ¬p.Prime) →
      4 * (H : ℝ) * (Real.log N) ^ 2 ≤ N := by
  have hthetaNat : ∀ᶠ N : ℕ in atTop,
      |Chebyshev.theta N - N| ≤ N / (16 * (Real.log N) ^ 2) :=
    tendsto_natCast_atTop_atTop.eventually eventually_abs_theta_sub_le_self_div_sixteen_log_sq
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hthetaNat
  filter_upwards [eventually_ge_atTop (max 2 N₀)] with N hN
  intro H hfree
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hHlt : H < N := by
    by_contra hHN
    obtain ⟨p, hp, hpLow, hpHigh⟩ := taoProposition23i (N := 2 * N) (by omega)
    have hpLow' : N < p := by simpa using hpLow
    exact hfree p hpLow' (by omega) hp
  have hleft := hN₀ N (by omega)
  have hright := hN₀ (N + H) (by omega)
  rw [chebyshevTheta_nat_add_eq_of_primeFree N H hfree] at hright
  have hlogLe : Real.log (N : ℝ) ≤ Real.log (N + H : ℕ) :=
    Real.log_le_log hNpos (by exact_mod_cast (show N ≤ N + H by omega))
  have hrightBound : ((N + H : ℕ) : ℝ) / (16 * (Real.log (N + H : ℕ)) ^ 2) ≤
      2 * (N : ℝ) / (16 * (Real.log N) ^ 2) := by
    calc
      _ ≤ (2 * (N : ℝ)) / (16 * (Real.log (N + H : ℕ)) ^ 2) := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast (show N + H ≤ 2 * N by omega)
        · positivity
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        gcongr
  have hlen : (H : ℝ) ≤ 3 * N / (16 * (Real.log N) ^ 2) := by
    have hl := (abs_le.mp hleft).2
    have hr := (abs_le.mp hright).1
    push_cast at hr hrightBound
    have hsum : (N : ℝ) / (16 * (Real.log N) ^ 2) + 2 * N / (16 * (Real.log N) ^ 2) =
        3 * N / (16 * (Real.log N) ^ 2) := by ring
    linarith
  have hmul := (le_div_iff₀ (by positivity : 0 < 16 * (Real.log N) ^ 2)).1 hlen
  nlinarith

end
end Tao2026
