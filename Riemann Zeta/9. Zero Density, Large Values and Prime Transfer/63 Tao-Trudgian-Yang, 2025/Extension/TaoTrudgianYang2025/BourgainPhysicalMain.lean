import TaoTrudgianYang2025.BourgainHybridEntry
import TaoTrudgianYang2025.JutilaPhysicalMain

/-!
# Physical normalization of the retained-zeta reflected main term

The actual dual length is canceled against its own displacement scale.
Only the logarithmic and divisor factors use the terminal length cap.
The zeta-square integral and its tail are retained throughout.
-/

open Finset
open scoped BigOperators
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The retained zeta term and quantified Mellin tail, without the pole term. -/
def bourgainMomentRemainder (q : ℕ) (T H : ℝ) (W : Finset ℝ) : ℝ :=
  H*bourgainZetaDifferenceMoment W (H+1) +
    (W.card : ℝ)^2*(1+T)^2/(1+H)^(2*q)

theorem bourgainMomentRemainder_nonneg (q : ℕ) (T : ℝ) {H : ℝ}
    (hH : 0 ≤ H) (W : Finset ℝ) : 0 ≤ bourgainMomentRemainder q T H W := by
  simpa only [bourgainMomentBudget,bourgainMomentRemainder,zero_mul,zero_add] using
    bourgainMomentBudget_nonneg q (U := 0) (T := T) W le_rfl hH

theorem bourgainMomentBudget_eq (q : ℕ) (U T H : ℝ) (W : Finset ℝ) :
    bourgainMomentBudget q U T H W =
      U*(W.card : ℝ)+bourgainMomentRemainder q T H W := by
  unfold bourgainMomentBudget bourgainMomentRemainder
  ring

/-- Scale cancellation for the pole and retained-zeta terms separately. -/
theorem bourgain_reflection_main_core_le (k : ℕ) {Q M S H C T R Z : ℝ}
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hS : 0 < S) (hH : 0 ≤ H)
    (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hscale : Q*M ≤ S*(H+2)) (hST : S ≤ T) :
    (Q*C/Real.sqrt S)^(2*k)*(2*H)^(2*k)*(2*M)^k*((2*M)^k*R+Z) ≤
      (16*C^2*(H+2)^4)^k*(R*T^k+Z*Q^k) := by
  have h1 :
      (Q*C/Real.sqrt S)^(2*k)*(2*H)^(2*k)*(2*M)^k ≤
        (16*C^2*(H+2)^4)^k*Q^k := by
    have h := pow_le_pow_left₀ (by positivity)
      (jutila_reflection_scale_one (C := C) hQ hS hH hscale) k
    simpa only [mul_pow, ← pow_mul] using h
  have h2 :
      (Q*C/Real.sqrt S)^(2*k)*(2*H)^(2*k)*(2*M)^(2*k) ≤
        (16*C^2*(H+2)^4)^k*T^k := by
    have h := pow_le_pow_left₀ (by positivity)
      (jutila_reflection_scale_two (C := C) hQ hM hS hH hscale hST) k
    simpa only [mul_pow, ← pow_mul] using h
  have h2' :
      ((Q*C/Real.sqrt S)^(2*k)*(2*H)^(2*k)*(2*M)^k)*(2*M)^k ≤
        (16*C^2*(H+2)^4)^k*T^k := by
    calc
      _ = (Q*C/Real.sqrt S)^(2*k)*(2*H)^(2*k)*((2*M)^k*(2*M)^k) := by ring
      _ = (Q*C/Real.sqrt S)^(2*k)*(2*H)^(2*k)*(2*M)^(2*k) := by
        rw [← pow_add, ← two_mul]
      _ ≤ _ := h2
  have hr := mul_le_mul_of_nonneg_right h2' hR
  have hz := mul_le_mul_of_nonneg_right h1 hZ
  nlinarith

/-- Source-scale retained main term after the actual dual-length cancellation. -/
def bourgainPhysicalMain (q k Q H : ℕ) (T : ℝ) (W : Finset ℝ) (C : ℝ) : ℝ :=
  (16*C^2*((H : ℝ)+2)^4)^k *
    ((W.card : ℝ)*T^k+bourgainMomentRemainder q T H W*(Q : ℝ)^k)

/-- The physical dual length and all denominator cancellations are derived
from the native ceiling construction, not supplied as estimates. -/
theorem bourgain_reflected_main_le_physical (q k Q H j : ℕ) (T : ℝ) (W : Finset ℝ)
    {A C η : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hQ : 0 < Q) (hH : 0 < H) (hT : 1 ≤ T)
    (hj : j ∈ Finset.range (Nat.log 2 (Nat.floor T)+1))
    (hfar : ¬ 2^(j+1) ≤ Q) :
    ((Q : ℝ)*C/Real.sqrt ((2^j : ℕ) : ℝ))^(2*k)*
        ((2*(H : ℝ))^(2*k)*
          bourgainPrefixMomentMajorant q k (heathBrownFixedReflectionLength Q H j) T H W A η) ≤
      jutilaMomentLoss k H T A 0 η * bourgainPhysicalMain q k Q H T W C := by
  let M := heathBrownFixedReflectionLength Q H j
  let U : ℝ := (2^k*M^k : ℕ)
  let L : ℝ := A*((Nat.clog 2 M : ℝ)+1)^(2*k)*(U^η)^2
  let B : ℝ := ((Q : ℝ)*C/Real.sqrt ((2^j : ℕ) : ℝ))^(2*k)*
    (2*(H : ℝ))^(2*k)*U*bourgainMomentBudget q U T H W
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbudget := bourgainMomentBudget_nonneg q (U := U) (T := T) W (by dsimp [U]; positivity)
    (Nat.cast_nonneg H)
  have hB : 0 ≤ B := by dsimp [B,U]; positivity
  have hcap : M ≤ jutilaDualLengthCap T H :=
    jutila_fixed_length_le_height_ceiling Q H j hQ hH hT hj
  have hclog : (Nat.clog 2 M : ℝ) ≤ Nat.clog 2 (jutilaDualLengthCap T H) := by
    exact_mod_cast Nat.clog_mono_right 2 hcap
  have hU : U ≤ ((2^k*(jutilaDualLengthCap T H)^k : ℕ) : ℝ) := by
    dsimp [U]
    exact_mod_cast Nat.mul_le_mul_left (2^k) (Nat.pow_le_pow_left hcap k)
  have hLoss : L ≤ jutilaMomentLoss k H T A 0 η := by
    dsimp [L,jutilaMomentLoss]
    rw [Real.rpow_zero,mul_one]
    gcongr
  have hCore : B ≤ bourgainPhysicalMain q k Q H T W C := by
    have hp := bourgain_reflection_main_core_le k (C := C)
      (Nat.cast_nonneg Q) (Nat.cast_nonneg M) (by positivity : (0 : ℝ) < (2^j : ℕ))
      (Nat.cast_nonneg H) (Nat.cast_nonneg W.card)
      (bourgainMomentRemainder_nonneg q T (Nat.cast_nonneg H) W)
      (jutila_fixed_length_product_le Q H j hQ hH hfar)
      (jutila_bin_scale_le_height hT hj)
    have hUeq : U = (2*(M : ℝ))^k := by dsimp [U]; push_cast; rw [mul_pow]
    simpa only [B,bourgainMomentBudget_eq,hUeq,bourgainPhysicalMain] using hp
  have hid :
      ((Q : ℝ)*C/Real.sqrt ((2^j : ℕ) : ℝ))^(2*k)*
          ((2*(H : ℝ))^(2*k)*bourgainPrefixMomentMajorant q k M T H W A η) = L*B := by
    dsimp [bourgainPrefixMomentMajorant,L,B,U]
    ring
  rw [show heathBrownFixedReflectionLength Q H j = M from rfl,hid]
  exact mul_le_mul hLoss hCore hB (le_trans hL hLoss)

end TaoTrudgianYang2025
