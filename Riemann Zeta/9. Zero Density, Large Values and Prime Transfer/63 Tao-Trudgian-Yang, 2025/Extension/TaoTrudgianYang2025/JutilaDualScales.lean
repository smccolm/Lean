import TaoTrudgianYang2025.JutilaHybridPatterns

/-!
# Physical dual scales in Jutila's reflection

The ceiling length remains tied to the actual displacement bin. These
lemmas retain the cancellation between the powered dual support and the
square-root reflection denominator.
-/

open Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Every dyadic displacement scale in the actual height range is at most T. -/
theorem jutila_bin_scale_le_height {T : ℝ} {j : ℕ} (hT : 1 ≤ T)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1)) :
    ((2 ^ j : ℕ) : ℝ) ≤ T := by
  have hf : Nat.floor T ≠ 0 := (Nat.floor_pos.mpr hT).ne'
  have hjle : j ≤ Nat.log 2 (Nat.floor T) := by
    have := Finset.mem_range.mp hj
    omega
  have hpow := (Nat.pow_le_pow_right (by omega : 0 < 2) hjle).trans
    (Nat.pow_log_le_self 2 hf)
  exact (by exact_mod_cast hpow : ((2 ^ j : ℕ) : ℝ) ≤ Nat.floor T).trans
    (Nat.floor_le (zero_le_one.trans hT))

/-- In the reflected regime the ceiling overshoot is absorbed at its
own displacement scale, not at the terminal height. -/
theorem jutila_fixed_length_product_le (Q H j : ℕ) (hQ : 0 < Q) (hH : 0 < H)
    (hfar : ¬ 2 ^ (j+1) ≤ Q) :
    (Q : ℝ) * heathBrownFixedReflectionLength Q H j ≤
      ((2 ^ j : ℕ) : ℝ) * ((H : ℝ) + 2) := by
  have hu := (heathBrownFixedReflectionLength_bounds_real Q H j hQ hH).2
  have hQtwo : (Q : ℝ) ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by
    have hn : Q ≤ 2 ^ (j+1) := by omega
    have hc : (Q : ℝ) ≤ ((2 ^ (j+1) : ℕ) : ℝ) := by exact_mod_cast hn
    push_cast at hc ⊢
    rw [pow_succ] at hc
    nlinarith
  nlinarith

/-- A common positive integer cap controls every dual length and hence all
divisor and logarithmic losses, without affecting the main-scale cancellation. -/
theorem jutila_fixed_length_le_height_ceiling (Q H j : ℕ) {T : ℝ}
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1)) :
    heathBrownFixedReflectionLength Q H j ≤ Nat.ceil (T * H) + 1 := by
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hb := heathBrownFixedReflectionLength_cast_le Q H j hQ hH
  have hscale := jutila_bin_scale_le_height hT hj
  have hdiv : (((2 ^ j : ℕ) : ℝ) * H) / Q ≤ T * H := by
    calc
      _ ≤ ((2 ^ j : ℕ) : ℝ) * H := div_le_self (by positivity) hQr
      _ ≤ T * H := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg H)
  have hh : (heathBrownFixedReflectionLength Q H j : ℝ) ≤
      (Nat.ceil (T * H) : ℝ) + 1 :=
    hb.trans (add_le_add (hdiv.trans (Nat.le_ceil _)) le_rfl)
  exact_mod_cast hh

/-- Scalar reflection cancellation for the cardinality-square and
mixed-energy terms. The physical condition is Q M ≤ S(H+2). -/
theorem jutila_reflection_scale_one {Q M S H C : ℝ}
    (hQ : 0 ≤ Q) (hS : 0 < S) (hH : 0 ≤ H)
    (hscale : Q*M ≤ S*(H+2)) :
    (Q*C/Real.sqrt S) ^ 2 * (2*H) ^ 2 * (2*M) ≤
      (16*C^2*(H+2)^4) * Q := by
  have hquot : Q*M/S ≤ H+2 := (div_le_iff₀ hS).mpr (by nlinarith)
  have hHpow : H^2*(H+2) ≤ (H+2)^4 := by
    calc
      _ ≤ (H+2)^2*(H+2) := by gcongr; linarith
      _ = (H+2)^3 := by ring
      _ ≤ (H+2)^4 := pow_le_pow_right₀ (by linarith) (by omega)
  have hid : (Q*C/Real.sqrt S) ^ 2 * (2*H) ^ 2 * (2*M) =
      8*C^2*H^2*Q*(Q*M/S) := by
    rw [div_pow, Real.sq_sqrt hS.le]
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ 8*C^2*H^2*Q*(H+2) := mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = (8*C^2*Q)*(H^2*(H+2)) := by ring
    _ ≤ (8*C^2*Q)*(H+2)^4 := mul_le_mul_of_nonneg_left hHpow (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg C) hQ,
      mul_nonneg (mul_nonneg (sq_nonneg C) hQ) (pow_nonneg (by linarith : 0 ≤ H+2) 4)]

/-- Scalar reflection cancellation for the term containing a second
powered support length. Its only remaining displacement factor is at most T. -/
theorem jutila_reflection_scale_two {Q M S H C T : ℝ}
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hS : 0 < S) (hH : 0 ≤ H)
    (hscale : Q*M ≤ S*(H+2)) (hST : S ≤ T) :
    (Q*C/Real.sqrt S) ^ 2 * (2*H) ^ 2 * (2*M)^2 ≤
      (16*C^2*(H+2)^4) * T := by
  have hprod : (Q*M)^2 ≤ (S*(H+2))^2 :=
    pow_le_pow_left₀ (by positivity) hscale 2
  have hquot : (Q*M)^2/S ≤ S*(H+2)^2 := by
    apply (div_le_iff₀ hS).mpr
    nlinarith
  have hHpow : H^2*(H+2)^2 ≤ (H+2)^4 := by
    calc
      _ ≤ (H+2)^2*(H+2)^2 := by gcongr; linarith
      _ = _ := by ring
  have hid : (Q*C/Real.sqrt S) ^ 2 * (2*H) ^ 2 * (2*M)^2 =
      16*C^2*H^2*((Q*M)^2/S) := by
    rw [div_pow, Real.sq_sqrt hS.le]
    field_simp
    ring
  rw [hid]
  calc
    _ ≤ 16*C^2*H^2*(S*(H+2)^2) :=
      mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = (16*C^2)*(H^2*(H+2)^2)*S := by ring
    _ ≤ (16*C^2)*(H+2)^4*S := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hST (by positivity)

/-- The complete powered main core reduces to its three source-scale
terms. Both powers of the actual dual length are handled before coarsening. -/
theorem jutila_reflection_main_core_le (k : ℕ) {Q M S H C T R : ℝ}
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hS : 0 < S) (hH : 0 ≤ H)
    (hR : 0 ≤ R) (hscale : Q*M ≤ S*(H+2)) (hST : S ≤ T) :
    (Q*C/Real.sqrt S) ^ (2*k) * (2*H) ^ (2*k) * (2*M)^k *
        (R^2 + R*(2*M)^k + R^(5/4 : ℝ)*T^(1/2 : ℝ)) ≤
      (16*C^2*(H+2)^4)^k *
        (R^2*Q^k + R*T^k + R^(5/4 : ℝ)*T^(1/2 : ℝ)*Q^k) := by
  have hT : 0 ≤ T := hS.le.trans hST
  have h1 :
      (Q*C/Real.sqrt S) ^ (2*k) * (2*H) ^ (2*k) * (2*M)^k ≤
        (16*C^2*(H+2)^4)^k * Q^k := by
    have h := pow_le_pow_left₀ (by positivity)
      (jutila_reflection_scale_one (C := C) hQ hS hH hscale) k
    simpa only [mul_pow, ← pow_mul] using h
  have h2 :
      (Q*C/Real.sqrt S) ^ (2*k) * (2*H) ^ (2*k) * (2*M)^(2*k) ≤
        (16*C^2*(H+2)^4)^k * T^k := by
    have h := pow_le_pow_left₀ (by positivity)
      (jutila_reflection_scale_two (C := C) hQ hM hS hH hscale hST) k
    simpa only [mul_pow, ← pow_mul] using h
  have h2' :
      ((Q*C/Real.sqrt S) ^ (2*k) * (2*H) ^ (2*k) * (2*M)^k) * (2*M)^k ≤
        (16*C^2*(H+2)^4)^k * T^k := by
    calc
      _ = (Q*C/Real.sqrt S) ^ (2*k) * (2*H) ^ (2*k) * ((2*M)^k*(2*M)^k) := by ring
      _ = (Q*C/Real.sqrt S) ^ (2*k) * (2*H) ^ (2*k) * (2*M)^(2*k) := by
        rw [← pow_add, ← two_mul]
      _ ≤ _ := h2
  have hr2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg R)
  have hr1 := mul_le_mul_of_nonneg_left h2' hR
  have hre := mul_le_mul_of_nonneg_left h1
    (by positivity : 0 ≤ R^(5/4 : ℝ)*T^(1/2 : ℝ))
  nlinarith

end TaoTrudgianYang2025
