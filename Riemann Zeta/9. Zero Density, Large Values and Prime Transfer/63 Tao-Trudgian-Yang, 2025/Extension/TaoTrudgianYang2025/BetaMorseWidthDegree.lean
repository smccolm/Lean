import TaoTrudgianYang2025.BetaJetPolynomial

/-!
# Exact transition-width degree of actual Morse-weight derivatives

Cutoff derivative j costs eta^(-j); inverse derivatives cost no width
power. The proved expression calculus tracks these costs separately.
-/

noncomputable section

namespace TaoTrudgianYang2025

def inversePhaseWeightedDegree (w : ℕ → ℕ) : InversePhaseExpression → ℕ
  | .scalar _ => 0
  | .atom j => w j
  | .add e f => max (inversePhaseWeightedDegree w e) (inversePhaseWeightedDegree w f)
  | .mul e f => inversePhaseWeightedDegree w e+inversePhaseWeightedDegree w f

theorem inversePhaseEval_abs_le_weighted (w : ℕ → ℕ) (e : InversePhaseExpression)
    {B A : ℝ} {x : ℕ → ℝ} (hB : 0 ≤ B) (hA : 1 ≤ A)
    (hx : ∀ j ≤ inversePhaseOrder e, |x j| ≤ B*A^(w j)) :
    |inversePhaseEval e x| ≤
      inversePhaseMagnitude e B*A^(inversePhaseWeightedDegree w e) := by
  induction e with
  | scalar c => simp only [inversePhaseEval,inversePhaseMagnitude,inversePhaseWeightedDegree,pow_zero,mul_one,le_refl]
  | atom j => exact hx j le_rfl
  | add e f he hf =>
      have he' := he (fun j hj => hx j (hj.trans (le_max_left _ _)))
      have hf' := hf (fun j hj => hx j (hj.trans (le_max_right _ _)))
      change |inversePhaseEval e x+inversePhaseEval f x| ≤
        (inversePhaseMagnitude e B+inversePhaseMagnitude f B)*
          A^(max (inversePhaseWeightedDegree w e) (inversePhaseWeightedDegree w f))
      apply (abs_add_le _ _).trans ((add_le_add he' hf').trans _)
      rw [add_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (le_max_left _ _))
          (inversePhaseMagnitude_nonneg e hB))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (le_max_right _ _))
          (inversePhaseMagnitude_nonneg f hB))
  | mul e f he hf =>
      have he' := he (fun j hj => hx j (hj.trans (le_max_left _ _)))
      have hf' := hf (fun j hj => hx j (hj.trans (le_max_right _ _)))
      change |inversePhaseEval e x*inversePhaseEval f x| ≤
        (inversePhaseMagnitude e B*inversePhaseMagnitude f B)*
          A^(inversePhaseWeightedDegree w e+inversePhaseWeightedDegree w f)
      rw [abs_mul]
      apply (mul_le_mul he' hf' (abs_nonneg _)
        (mul_nonneg (inversePhaseMagnitude_nonneg e hB)
          (pow_nonneg (zero_le_one.trans hA) _))).trans_eq
      rw [pow_add]
      ring

def morseWeightWidthAtomDegree (j : ℕ) : ℕ :=
  if j%2 = 0 then j/2 else 0

theorem morseWeightAtomDerivative_widthDegree_le (j : ℕ) :
    inversePhaseWeightedDegree morseWeightWidthAtomDegree (morseWeightAtomDerivative j) ≤
      morseWeightWidthAtomDegree j+1 := by
  by_cases hj : j%2 = 0
  · have hj' : (j+2)%2 = 0 := by omega
    simp only [morseWeightAtomDerivative,if_pos hj,inversePhaseWeightedDegree,
      morseWeightWidthAtomDegree,if_pos hj',Nat.one_mod,one_ne_zero,if_false]
    omega
  · have hj' : (j+2)%2 ≠ 0 := by omega
    simp only [morseWeightAtomDerivative,if_neg hj,inversePhaseWeightedDegree,
      morseWeightWidthAtomDegree,if_neg hj']
    omega

theorem morseWeightDifferentiate_widthDegree_le (e : InversePhaseExpression) :
    inversePhaseWeightedDegree morseWeightWidthAtomDegree (morseWeightDifferentiate e) ≤
      inversePhaseWeightedDegree morseWeightWidthAtomDegree e+1 := by
  induction e with
  | scalar c => simp [morseWeightDifferentiate,inversePhaseWeightedDegree]
  | atom j => exact morseWeightAtomDerivative_widthDegree_le j
  | add e f he hf =>
      simp only [morseWeightDifferentiate,inversePhaseWeightedDegree]
      omega
  | mul e f he hf =>
      simp only [morseWeightDifferentiate,inversePhaseWeightedDegree]
      omega

theorem morseWeightDerivativeExpression_widthDegree_le (n : ℕ) :
    inversePhaseWeightedDegree morseWeightWidthAtomDegree (morseWeightDerivativeExpression n) ≤ n := by
  induction n with
  | zero =>
      norm_num [morseWeightDerivativeExpression,inversePhaseWeightedDegree,morseWeightWidthAtomDegree]
  | succ n ih =>
      exact (morseWeightDifferentiate_widthDegree_le _).trans (Nat.add_le_add_right ih 1)

end TaoTrudgianYang2025
