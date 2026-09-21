import TaoTrudgianYang2025.DyadicMomentCutoff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The complete fourth-moment scale budget

The dyadic count, coefficient loss, polynomial length and contour mass
are charged together. The small excess exponent is chosen before height.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem fourth_height_power_identity {H q : ℝ} (hH : 0 < H) :
    (2*H)^(2*q)*H^(1+q)*(2*H^(1+q))^(2*q) =
      (2:ℝ)^(4*q)*H^(1+5*q+2*q^2) := by
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hH.le,
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hH.le _),
    ← Real.rpow_mul hH.le]
  calc
    _ = ((2:ℝ)^(2*q)*(2:ℝ)^(2*q))*
        ((H^(2*q)*H^(1+q))*H^((1+q)*(2*q))) := by ring
    _ = (2:ℝ)^((2*q)+(2*q))*H^((2*q+(1+q))+((1+q)*(2*q))) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),
        ← Real.rpow_add hH,← Real.rpow_add hH]
    _ = _ := by congr 2 <;> ring

theorem exists_fourth_dyadic_budget {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ H : ℝ, 1 ≤ H → ∀ M : ℕ,
      (2:ℝ)^M ≤ 2*H^(1+q) →
      (2*H)^(2*q)*((M:ℝ)+1)^2*
        (H+2*(5*Real.pi+1)*(2:ℝ)^M)*((2:ℝ)^M)^q ≤ D*H^(1+7*q) := by
  obtain ⟨A,hA,hcount⟩ := exists_dyadic_count_sq_le_rpow hq
  let B : ℝ := 2*(5*Real.pi+1)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A*(1+2*B)*(2:ℝ)^(4*q),by positivity,?_⟩
  intro H hH M hN
  have hH0 : 0 < H := by linarith
  have hNp : 0 < (2:ℝ)^M := by positivity
  have hHH : H ≤ H^(1+q) := by
    calc
      H = H^(1:ℝ) := (Real.rpow_one H).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hH (by linarith)
  have hlength : H+B*(2:ℝ)^M ≤ (1+2*B)*H^(1+q) := by
    have h := mul_le_mul_of_nonneg_left hN hB.le
    nlinarith
  have hNpwr : ((2:ℝ)^M)^q*((2:ℝ)^M)^q = ((2:ℝ)^M)^(2*q) := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  change (2*H)^(2*q)*((M:ℝ)+1)^2*(H+B*(2:ℝ)^M)*((2:ℝ)^M)^q ≤ _
  calc
    _ ≤ (2*H)^(2*q)*(A*((2:ℝ)^M)^q)*
        ((1+2*B)*H^(1+q))*((2:ℝ)^M)^q := by
      gcongr
      exact hcount M
    _ = A*(1+2*B)*((2*H)^(2*q)*H^(1+q))*((2:ℝ)^M)^(2*q) := by
      rw [← hNpwr]
      ring
    _ ≤ A*(1+2*B)*((2*H)^(2*q)*H^(1+q))*(2*H^(1+q))^(2*q) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hNp.le hN (by positivity)) (by positivity)
    _ = A*(1+2*B)*(2:ℝ)^(4*q)*H^(1+5*q+2*q^2) := by
      rw [mul_assoc (A*(1+2*B)),fourth_height_power_identity hH0]
      ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hH (by nlinarith)) (by positivity)

end TaoTrudgianYang2025
