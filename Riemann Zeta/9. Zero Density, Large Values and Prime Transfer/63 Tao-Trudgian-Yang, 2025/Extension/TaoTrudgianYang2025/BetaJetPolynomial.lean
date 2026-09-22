import TaoTrudgianYang2025.BetaMorseWeightBounds

/-!
# Polynomial dependence on the original cutoff jet budget

Finite expression magnitudes have an explicit algebraic degree.
This turns the already proved actual-weight estimates into quantitative
bounds for a family of cutoffs, rather than constants for one cutoff.
-/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

def inversePhaseDegree : InversePhaseExpression → ℕ
  | .scalar _ => 0
  | .atom _ => 1
  | .add e f => max (inversePhaseDegree e) (inversePhaseDegree f)
  | .mul e f => inversePhaseDegree e+inversePhaseDegree f

theorem inversePhaseMagnitude_mono (e : InversePhaseExpression)
    {B C : ℝ} (hB : 0 ≤ B) (hBC : B ≤ C) :
    inversePhaseMagnitude e B ≤ inversePhaseMagnitude e C := by
  induction e with
  | scalar c => exact le_rfl
  | atom j => exact hBC
  | add e f he hf => exact add_le_add he hf
  | mul e f he hf =>
      exact mul_le_mul he hf (inversePhaseMagnitude_nonneg f hB)
        (inversePhaseMagnitude_nonneg e (hB.trans hBC))

theorem inversePhaseMagnitude_scale_le (e : InversePhaseExpression)
    {B A : ℝ} (hB : 0 ≤ B) (hA : 1 ≤ A) :
    inversePhaseMagnitude e (B*A) ≤ inversePhaseMagnitude e B*A^(inversePhaseDegree e) := by
  induction e with
  | scalar c => simp only [inversePhaseMagnitude,inversePhaseDegree,pow_zero,mul_one,le_refl]
  | atom j => simp only [inversePhaseMagnitude,inversePhaseDegree,pow_one,le_refl]
  | add e f he hf =>
      change inversePhaseMagnitude e (B*A)+inversePhaseMagnitude f (B*A) ≤
        (inversePhaseMagnitude e B+inversePhaseMagnitude f B)*
          A^(max (inversePhaseDegree e) (inversePhaseDegree f))
      apply (add_le_add he hf).trans
      rw [add_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (le_max_left _ _))
          (inversePhaseMagnitude_nonneg e hB))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (le_max_right _ _))
          (inversePhaseMagnitude_nonneg f hB))
  | mul e f he hf =>
      change inversePhaseMagnitude e (B*A)*inversePhaseMagnitude f (B*A) ≤
        (inversePhaseMagnitude e B*inversePhaseMagnitude f B)*
          A^(inversePhaseDegree e+inversePhaseDegree f)
      apply (mul_le_mul he hf (inversePhaseMagnitude_nonneg f
        (mul_nonneg hB (zero_le_one.trans hA)))
        (mul_nonneg (inversePhaseMagnitude_nonneg e hB)
          (pow_nonneg (zero_le_one.trans hA) _))).trans_eq
      rw [pow_add]
      ring

theorem morseWeightDerivativeBound_scaled {σ M A : ℝ}
    (hσ : 0 < σ) (hM : 0 ≤ M) (hA : 1 ≤ A) (n Q : ℕ) :
    morseWeightDerivativeBound σ (M*A^Q) n ≤
      morseWeightDerivativeBound σ M n *
        A^(Q*inversePhaseDegree (morseWeightDerivativeExpression n)) := by
  let S := ∑ j ∈ Finset.range (morseWeightCutoffOrder n+2),
    morseInverseDerivativeBound σ j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    morseInverseDerivativeBound_nonneg hσ j
  have hpow : 1 ≤ A^Q := one_le_pow₀ hA
  have hb : M*A^Q+S ≤ (M+S)*A^Q := by nlinarith
  change inversePhaseMagnitude _ (M*A^Q+S) ≤
    inversePhaseMagnitude _ (M+S)*A^_
  apply (inversePhaseMagnitude_mono _ (add_nonneg
    (mul_nonneg hM (pow_nonneg (zero_le_one.trans hA) Q)) hS) hb).trans
  simpa only [pow_mul] using inversePhaseMagnitude_scale_le
    (morseWeightDerivativeExpression n) (add_nonneg hM hS) hpow

end TaoTrudgianYang2025
