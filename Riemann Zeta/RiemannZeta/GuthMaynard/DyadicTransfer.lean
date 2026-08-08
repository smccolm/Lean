import RiemannZeta.GuthMaynard.ExponentArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Filter Asymptotics
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

noncomputable def dyadicHeightIndex (T : ℝ) : ℕ :=
  ⌈Real.logb 2 T⌉₊

lemma dyadicHeightIndex_spec (T : ℝ) (hT : 1 ≤ T) :
    T ≤ (((2 : ℕ) ^ dyadicHeightIndex T : ℕ) : ℝ) ∧
      (((2 : ℕ) ^ dyadicHeightIndex T : ℕ) : ℝ) ≤ 2 * T ∧
      (dyadicHeightIndex T : ℝ) < Real.log T / Real.log 2 + 1 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlogbNonneg : 0 ≤ Real.logb 2 T :=
    (Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 2) hTpos).2 hT
  have hLowerExp : Real.logb 2 T ≤ (dyadicHeightIndex T : ℝ) := by
    exact Nat.le_ceil _
  have hUpperExp : (dyadicHeightIndex T : ℝ) < Real.logb 2 T + 1 := by
    exact Nat.ceil_lt_add_one hlogbNonneg
  have hCover : T ≤ (((2 : ℕ) ^ dyadicHeightIndex T : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hTpos).1 hLowerExp
  have hUpperRpow : (2 : ℝ) ^ (dyadicHeightIndex T : ℝ) <
      (2 : ℝ) ^ (Real.logb 2 T + 1) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hUpperExp
  have hRpowLogb : (2 : ℝ) ^ Real.logb 2 T = T :=
    Real.rpow_logb (by norm_num) (by norm_num) hTpos
  have hUpper : (((2 : ℕ) ^ dyadicHeightIndex T : ℕ) : ℝ) ≤ 2 * T := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    calc
      (2 : ℝ) ^ (dyadicHeightIndex T : ℝ) ≤
          (2 : ℝ) ^ (Real.logb 2 T + 1) := hUpperRpow.le
      _ = 2 * T := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), hRpowLogb, Real.rpow_one]
        ring
  refine ⟨hCover, hUpper, ?_⟩
  simpa [Real.logb] using hUpperExp

/-- An epsilon-power bound on every positive dyadic slab implies the same
bound for the full symmetric zero count. The proof includes the fixed
low-height rectangle, logarithmically many slabs, and analytic
multiplicity-preserving conjugation. -/
theorem dyadicToGlobalZeroCount (σ a : ℝ) (ha : 0 ≤ a)
    (hSlab : EpsilonPowerBound
      (fun T => (zeroCountRect σ 1 T (2 * T) : ℝ))
      (fun T => T ^ a)) :
    EpsilonPowerBound (fun T => (N σ T : ℝ)) (fun T => T ^ a) := by
  intro ε hε
  let q := ε / 3
  have hq : 0 < q := by dsimp [q]; linarith
  obtain ⟨C, hC⟩ := (hSlab q hq).bound
  rw [eventually_atTop] at hC
  obtain ⟨X₀, hC⟩ := hC
  let X := max 1 X₀
  let J := dyadicHeightIndex X
  let B : ℝ := zeroCountRect σ 1 0 (((2 : ℕ) ^ J : ℕ) : ℝ)
  have hXOne : 1 ≤ X := le_max_left _ _
  have hX₀ : X₀ ≤ X := le_max_right _ _
  have hJCover : X ≤ (((2 : ℕ) ^ J : ℕ) : ℝ) :=
    (dyadicHeightIndex_spec X hXOne).1
  have hSlabExplicit : ∀ x : ℝ, X₀ ≤ x → 0 < x →
      (zeroCountRect σ 1 x (2 * x) : ℝ) ≤ |C| * x ^ (q + a) := by
    intro x hx₀ hx
    have hRaw := hC x hx₀
    have hxNonneg : 0 ≤ x := hx.le
    have hCountNonneg : 0 ≤ (zeroCountRect σ 1 x (2 * x) : ℝ) := Nat.cast_nonneg _
    have hqa : x ^ q * x ^ a = x ^ (q + a) := (Real.rpow_add hx q a).symm
    rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hCountNonneg,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hxNonneg _)
        (abs_nonneg (x ^ a))), abs_of_nonneg (Real.rpow_nonneg hxNonneg _)] at hRaw
    calc
      (zeroCountRect σ 1 x (2 * x) : ℝ) ≤ C * (x ^ q * x ^ a) := hRaw
      _ ≤ |C| * (x ^ q * x ^ a) := by
        gcongr
        exact le_abs_self C
      _ = |C| * x ^ (q + a) := by rw [hqa]
  apply IsBigO.of_bound
    (2 * (B + 1) + 2 * ((1 / Real.log 2 + 1) / q) *
      (B + |C| * 2 ^ (q + a)))
  filter_upwards [eventually_ge_atTop (max (Real.exp 1) X)] with T hT
  have hTExp : Real.exp 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTX : X ≤ T := le_trans (le_max_right _ _) hT
  have hTOne : 1 ≤ T := by
    have : (1 : ℝ) < Real.exp 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact (this.trans_le hTExp).le
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTOne
  let m := dyadicHeightIndex T
  have hmSpec := dyadicHeightIndex_spec T hTOne
  have hTdyadic : T ≤ (((2 : ℕ) ^ m : ℕ) : ℝ) := hmSpec.1
  have hDyadicUpper : (((2 : ℕ) ^ m : ℕ) : ℝ) ≤ 2 * T := hmSpec.2.1
  have hmLog : (m : ℝ) < Real.log T / Real.log 2 + 1 := hmSpec.2.2
  have hLogOne : 1 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 1) hTExp
    simpa using this
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmBound : (m : ℝ) ≤ (1 / Real.log 2 + 1) * Real.log T := by
    calc
      (m : ℝ) ≤ Real.log T / Real.log 2 + 1 := hmLog.le
      _ ≤ Real.log T / Real.log 2 + Real.log T := by linarith
      _ = (1 / Real.log 2 + 1) * Real.log T := by ring
  have hLogPower : Real.log T ≤ T ^ q / q :=
    Real.log_le_rpow_div hTpos.le hq
  have hmPower : (m : ℝ) ≤ ((1 / Real.log 2 + 1) / q) * T ^ q := by
    calc
      (m : ℝ) ≤ (1 / Real.log 2 + 1) * Real.log T := hmBound
      _ ≤ (1 / Real.log 2 + 1) * (T ^ q / q) :=
        mul_le_mul_of_nonneg_left hLogPower (by positivity)
      _ = ((1 / Real.log 2 + 1) / q) * T ^ q := by ring
  have hEach : ∀ i ∈ Finset.range m,
      (zeroCountRect σ 1 (((2 : ℕ) ^ i : ℕ) : ℝ)
        (((2 : ℕ) ^ (i + 1) : ℕ) : ℝ) : ℝ) ≤
        B + |C| * (2 * T) ^ (q + a) := by
    intro i hi
    have hiLt : i < m := Finset.mem_range.mp hi
    by_cases hiJ : i < J
    · have hiSucc : i + 1 ≤ J := by omega
      have hMono := zeroCountRect_mono σ 1
        (((2 : ℕ) ^ i : ℕ) : ℝ) (((2 : ℕ) ^ (i + 1) : ℕ) : ℝ)
        σ 1 0 (((2 : ℕ) ^ J : ℕ) : ℝ)
        (by linarith) (by linarith)
        (by positivity)
        (by exact_mod_cast pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) hiSucc)
      have hCast : (zeroCountRect σ 1 (((2 : ℕ) ^ i : ℕ) : ℝ)
          (((2 : ℕ) ^ (i + 1) : ℕ) : ℝ) : ℝ) ≤ B := by
        dsimp [B]
        exact_mod_cast hMono
      exact hCast.trans (le_add_of_nonneg_right (mul_nonneg (abs_nonneg C)
        (Real.rpow_nonneg (by positivity) _)))
    · have hJi : J ≤ i := by omega
      have hPowJ : ((2 : ℕ) ^ J : ℕ) ≤ (2 : ℕ) ^ i :=
        pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) hJi
      have hBaseX₀ : X₀ ≤ (((2 : ℕ) ^ i : ℕ) : ℝ) := by
        exact hX₀.trans (hJCover.trans (by exact_mod_cast hPowJ))
      have hBasePos : (0 : ℝ) < (((2 : ℕ) ^ i : ℕ) : ℝ) := by positivity
      have hRaw := hSlabExplicit (((2 : ℕ) ^ i : ℕ) : ℝ) hBaseX₀ hBasePos
      have hBaseLe : (((2 : ℕ) ^ i : ℕ) : ℝ) ≤ 2 * T := by
        have him : i ≤ m := hiLt.le
        have hpowNat : (2 : ℕ) ^ i ≤ (2 : ℕ) ^ m :=
          pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) him
        have hpowReal : (((2 : ℕ) ^ i : ℕ) : ℝ) ≤ (((2 : ℕ) ^ m : ℕ) : ℝ) := by
          exact_mod_cast hpowNat
        exact hpowReal.trans hDyadicUpper
      have hqaNonneg : 0 ≤ q + a := add_nonneg hq.le ha
      have hPowLe : ((((2 : ℕ) ^ i : ℕ) : ℝ)) ^ (q + a) ≤
          (2 * T) ^ (q + a) :=
        Real.rpow_le_rpow (by positivity) hBaseLe hqaNonneg
      have hEndpoint : (((2 : ℕ) ^ (i + 1) : ℕ) : ℝ) =
          2 * (((2 : ℕ) ^ i : ℕ) : ℝ) := by
        rw [pow_succ]
        norm_num [Nat.cast_mul]
        ring
      rw [hEndpoint]
      exact hRaw.trans ((mul_le_mul_of_nonneg_left hPowLe (abs_nonneg C)).trans
        (le_add_of_nonneg_left (Nat.cast_nonneg _)))
  have hSum : (∑ i ∈ Finset.range m,
      (zeroCountRect σ 1 (((2 : ℕ) ^ i : ℕ) : ℝ)
        (((2 : ℕ) ^ (i + 1) : ℕ) : ℝ) : ℝ)) ≤
      (m : ℝ) * (B + |C| * (2 * T) ^ (q + a)) := by
    calc
      _ ≤ ∑ _i ∈ Finset.range m, (B + |C| * (2 * T) ^ (q + a)) :=
        Finset.sum_le_sum hEach
      _ = (m : ℝ) * (B + |C| * (2 * T) ^ (q + a)) := by simp; ring
  have hPositiveNat : zeroCountRect σ 1 0 T ≤
      zeroCountRect σ 1 0 (((2 : ℕ) ^ m : ℕ) : ℝ) :=
    zeroCountRect_mono σ 1 0 T σ 1 0 (((2 : ℕ) ^ m : ℕ) : ℝ)
      (by linarith) (by linarith) (by linarith) hTdyadic
  have hPositive : (zeroCountRect σ 1 0 T : ℝ) ≤
      B + (m : ℝ) * (B + |C| * (2 * T) ^ (q + a)) := by
    have hDecomp := zeroCountRect_zero_two_pow_le σ m
    have hInitialNat : zeroCountRect σ 1 0 1 ≤
        zeroCountRect σ 1 0 (((2 : ℕ) ^ J : ℕ) : ℝ) :=
      zeroCountRect_mono σ 1 0 1 σ 1 0 (((2 : ℕ) ^ J : ℕ) : ℝ)
        (by linarith) (by linarith) (by linarith)
        (by exact_mod_cast pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) (Nat.zero_le J))
    have hCast : (zeroCountRect σ 1 0 (((2 : ℕ) ^ m : ℕ) : ℝ) : ℝ) ≤
        B + ∑ i ∈ Finset.range m,
          (zeroCountRect σ 1 (((2 : ℕ) ^ i : ℕ) : ℝ)
            (((2 : ℕ) ^ (i + 1) : ℕ) : ℝ) : ℝ) := by
      dsimp [B]
      exact_mod_cast hDecomp.trans (by omega)
    have hPositiveCast : (zeroCountRect σ 1 0 T : ℝ) ≤
        (zeroCountRect σ 1 0 (((2 : ℕ) ^ m : ℕ) : ℝ) : ℝ) := by
      exact_mod_cast hPositiveNat
    exact hPositiveCast.trans (hCast.trans (by linarith [hSum]))
  have hGlobalNat : N σ T ≤ 2 * zeroCountRect σ 1 0 T := by
    have hSplit := zeroCountRect_split σ 1 (-T) 0 T
    rw [zeroCountRect_neg_eq_pos] at hSplit
    change zeroCountRect σ 1 (-T) T ≤ _
    simpa [two_mul] using hSplit
  have hGlobal : (N σ T : ℝ) ≤
      2 * (B + (m : ℝ) * (B + |C| * (2 * T) ^ (q + a))) := by
    have hGlobalCast : (N σ T : ℝ) ≤ 2 * (zeroCountRect σ 1 0 T : ℝ) := by
      exact_mod_cast hGlobalNat
    exact hGlobalCast.trans (mul_le_mul_of_nonneg_left hPositive (by norm_num))
  have hTwoT : (2 * T) ^ (q + a) = 2 ^ (q + a) * T ^ (q + a) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTpos.le]
  have hTargetNonneg : 0 ≤ T ^ ε * |T ^ a| := by positivity
  have hqaNonneg : 0 ≤ q + a := add_nonneg hq.le ha
  have hPowOne : 1 ≤ T ^ (q + a) := Real.one_le_rpow hTOne hqaNonneg
  have hExponent : q + (q + a) ≤ ε + a := by dsimp [q]; linarith
  have hPowCombine : T ^ q * T ^ (q + a) ≤ T ^ (ε + a) := by
    rw [← Real.rpow_add hTpos]
    exact Real.rpow_le_rpow_of_exponent_le hTOne hExponent
  have hTarget : T ^ (ε + a) = T ^ ε * |T ^ a| := by
    rw [abs_of_nonneg (Real.rpow_nonneg hTpos.le _), Real.rpow_add hTpos]
  simp only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hTargetNonneg]
  rw [abs_of_nonneg (show 0 ≤ (N σ T : ℝ) from Nat.cast_nonneg _)]
  rw [hTarget] at hPowCombine
  rw [hTwoT] at hGlobal
  have hBNonneg : 0 ≤ B := Nat.cast_nonneg _
  have hFactorNonneg : 0 ≤ (1 / Real.log 2 + 1) / q := by positivity
  have hMain :
      2 * (B + (m : ℝ) * (B + |C| * (2 ^ (q + a) * T ^ (q + a)))) ≤
        (2 * (B + 1) + 2 * ((1 / Real.log 2 + 1) / q) *
          (B + |C| * 2 ^ (q + a))) * (T ^ ε * |T ^ a|) := by
    have hTargetOne : 1 ≤ T ^ ε * |T ^ a| := by
      rw [← hTarget]
      exact Real.one_le_rpow hTOne (add_nonneg hε.le ha)
    calc
      2 * (B + (m : ℝ) * (B + |C| * (2 ^ (q + a) * T ^ (q + a))))
          ≤ 2 * (B + (((1 / Real.log 2 + 1) / q) * T ^ q) *
            (B + |C| * (2 ^ (q + a) * T ^ (q + a)))) := by gcongr
      _ ≤ (2 * (B + 1) + 2 * ((1 / Real.log 2 + 1) / q) *
          (B + |C| * 2 ^ (q + a))) * (T ^ ε * |T ^ a|) := by
        rw [mul_add, add_mul, mul_add]
        have hBTarget : 2 * B ≤ 2 * (B + 1) * (T ^ ε * |T ^ a|) := by
          calc
            2 * B ≤ 2 * (B + 1) := by linarith
            _ ≤ 2 * (B + 1) * (T ^ ε * |T ^ a|) := by
              nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * (B + 1))
                (sub_nonneg.mpr hTargetOne)]
        have hProductBound :
            T ^ q * (B + |C| * (2 ^ (q + a) * T ^ (q + a))) ≤
              (B + |C| * 2 ^ (q + a)) * (T ^ ε * |T ^ a|) := by
          calc
            T ^ q * (B + |C| * (2 ^ (q + a) * T ^ (q + a))) =
                B * T ^ q + |C| * 2 ^ (q + a) * (T ^ q * T ^ (q + a)) := by ring
            _ ≤ B * (T ^ ε * |T ^ a|) +
                |C| * 2 ^ (q + a) * (T ^ ε * |T ^ a|) := by
              gcongr
              · have hqExp : q ≤ ε + a := by dsimp [q]; linarith
                rw [← hTarget]
                exact Real.rpow_le_rpow_of_exponent_le hTOne hqExp
            _ = (B + |C| * 2 ^ (q + a)) * (T ^ ε * |T ^ a|) := by ring
        have hScaled := mul_le_mul_of_nonneg_left hProductBound
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hFactorNonneg)
        nlinarith [hBTarget, hScaled]
  exact hGlobal.trans hMain

end RiemannZeta.GuthMaynard
