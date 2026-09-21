import TaoTrudgianYang2025.JutilaDualScales

/-!
# Reflected main terms at the physical source scale

The logarithmic and divisor losses use a common terminal cap. The two
actual powered lengths in the main terms are canceled against their own
bin denominator before that cap is used.
-/

open Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- A common integer cap used only for logarithmic and divisor losses. -/
def jutilaDualLengthCap (T : ℝ) (H : ℕ) : ℕ := Nat.ceil (T * H) + 1

/-- Explicit common logarithmic and divisor loss from the proved prefix
moment. This definition carries no bound as a hypothesis. -/
def jutilaMomentLoss (k H : ℕ) (T A ε η : ℝ) : ℝ :=
  A * ((Nat.clog 2 (jutilaDualLengthCap T H) : ℝ) + 1) ^ (2*k) *
    (((2 ^ k * (jutilaDualLengthCap T H) ^ k : ℕ) : ℝ) ^ η) ^ 2 * T ^ ε

/-- The three physical source-scale terms, with explicit smoothing cost. -/
def jutilaPhysicalMain (k Q H : ℕ) (T : ℝ) (W : Finset ℝ) (C : ℝ) : ℝ :=
  (16*C^2*((H : ℝ)+2)^4)^k *
    ((W.card : ℝ)^2*(Q : ℝ)^k + (W.card : ℝ)*T^k +
      (W.card : ℝ)^(5/4 : ℝ)*T^(1/2 : ℝ)*(Q : ℝ)^k)

/-- The actual fixed-length reflected main term is controlled by the
three physical source terms. No scale or cancellation estimate is assumed. -/
theorem jutila_reflected_main_le_physical (k Q H j : ℕ) (T : ℝ) (W : Finset ℝ)
    {A C ε η : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T) + 1))
    (hfar : ¬ 2 ^ (j+1) ≤ Q) :
    ((Q : ℝ)*C/Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ (2*k) *
        ((2*(H : ℝ)) ^ (2*k) *
          jutilaPrefixMomentMajorant k (heathBrownFixedReflectionLength Q H j) T W A ε η) ≤
      jutilaMomentLoss k H T A ε η * jutilaPhysicalMain k Q H T W C := by
  let M := heathBrownFixedReflectionLength Q H j
  let U : ℝ := (2 ^ k * M ^ k : ℕ)
  let L : ℝ := A * ((Nat.clog 2 M : ℝ)+1)^(2*k) * (U^η)^2 * T^ε
  let B : ℝ := ((Q : ℝ)*C/Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ (2*k) *
    (2*(H : ℝ)) ^ (2*k) * U *
    ((W.card : ℝ)^2 + (W.card : ℝ)*U + (W.card : ℝ)^(5/4 : ℝ)*T^(1/2 : ℝ))
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hB : 0 ≤ B := by dsimp [B, U]; positivity
  have hcap : M ≤ jutilaDualLengthCap T H :=
    jutila_fixed_length_le_height_ceiling Q H j hQ hH hT hj
  have hclog : (Nat.clog 2 M : ℝ) ≤ Nat.clog 2 (jutilaDualLengthCap T H) := by
    exact_mod_cast Nat.clog_mono_right 2 hcap
  have hU : U ≤ ((2 ^ k * (jutilaDualLengthCap T H)^k : ℕ) : ℝ) := by
    dsimp [U]
    exact_mod_cast Nat.mul_le_mul_left (2^k) (Nat.pow_le_pow_left hcap k)
  have hLoss : L ≤ jutilaMomentLoss k H T A ε η := by
    dsimp [L, jutilaMomentLoss]
    gcongr
  have hCore : B ≤ jutilaPhysicalMain k Q H T W C := by
    have hp := jutila_reflection_main_core_le k (C := C)
      (Nat.cast_nonneg Q) (Nat.cast_nonneg M) (by positivity : (0 : ℝ) < (2^j : ℕ))
      (Nat.cast_nonneg H) (Nat.cast_nonneg W.card)
      (jutila_fixed_length_product_le Q H j hQ hH hfar)
      (jutila_bin_scale_le_height hT hj)
    have hUeq : U = (2*(M : ℝ))^k := by dsimp [U]; push_cast; rw [mul_pow]
    simpa only [B, hUeq, jutilaPhysicalMain] using hp
  have hid :
      ((Q : ℝ)*C/Real.sqrt ((2 ^ j : ℕ) : ℝ)) ^ (2*k) *
          ((2*(H : ℝ)) ^ (2*k) *
            jutilaPrefixMomentMajorant k M T W A ε η) = L*B := by
    dsimp [jutilaPrefixMomentMajorant, L, B, U]
    ring
  rw [show heathBrownFixedReflectionLength Q H j = M from rfl, hid]
  exact mul_le_mul hLoss hCore hB (le_trans hL hLoss)

end TaoTrudgianYang2025
