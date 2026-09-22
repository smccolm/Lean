import TaoTrudgianYang2025.BetaLegendreDual
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Algebraic formulas for every inverse-phase derivative

The expression language is evaluated on the actual inverse point, reciprocal
curvature, and higher original phase derivatives. Its differentiation rule
is proved against those analytic objects in BetaInverseJets.
-/

noncomputable section

namespace TaoTrudgianYang2025

inductive InversePhaseExpression where
  | scalar : ℝ → InversePhaseExpression
  | atom : ℕ → InversePhaseExpression
  | add : InversePhaseExpression → InversePhaseExpression → InversePhaseExpression
  | mul : InversePhaseExpression → InversePhaseExpression → InversePhaseExpression

def inversePhaseEval : InversePhaseExpression → (ℕ → ℝ) → ℝ
  | .scalar c, _ => c
  | .atom j, x => x j
  | .add e f, x => inversePhaseEval e x + inversePhaseEval f x
  | .mul e f, x => inversePhaseEval e x * inversePhaseEval f x

def inversePhaseOrder : InversePhaseExpression → ℕ
  | .scalar _ => 0
  | .atom j => j
  | .add e f => max (inversePhaseOrder e) (inversePhaseOrder f)
  | .mul e f => max (inversePhaseOrder e) (inversePhaseOrder f)

def inversePhaseAtomDerivative : ℕ → InversePhaseExpression
  | 0 => .atom 1
  | 1 => .mul (.scalar (-1)) (.mul (.atom 3) (.mul (.atom 1) (.mul (.atom 1) (.atom 1))))
  | n+2 => .mul (.atom (n+3)) (.atom 1)

def inversePhaseDifferentiate : InversePhaseExpression → InversePhaseExpression
  | .scalar _ => .scalar 0
  | .atom j => inversePhaseAtomDerivative j
  | .add e f => .add (inversePhaseDifferentiate e) (inversePhaseDifferentiate f)
  | .mul e f => .add (.mul (inversePhaseDifferentiate e) f)
      (.mul e (inversePhaseDifferentiate f))

def inversePhaseDerivativeExpression : ℕ → InversePhaseExpression
  | 0 => .atom 0
  | n+1 => inversePhaseDifferentiate (inversePhaseDerivativeExpression n)

def inversePhaseMagnitude : InversePhaseExpression → ℝ → ℝ
  | .scalar c, _ => |c|
  | .atom _, B => B
  | .add e f, B => inversePhaseMagnitude e B + inversePhaseMagnitude f B
  | .mul e f, B => inversePhaseMagnitude e B * inversePhaseMagnitude f B

def inversePhaseSensitivity : InversePhaseExpression → ℝ → ℝ
  | .scalar _, _ => 0
  | .atom _, _ => 1
  | .add e f, B => inversePhaseSensitivity e B + inversePhaseSensitivity f B
  | .mul e f, B => inversePhaseMagnitude e B * inversePhaseSensitivity f B +
      inversePhaseSensitivity e B * inversePhaseMagnitude f B

theorem inversePhaseMagnitude_nonneg (e : InversePhaseExpression) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ inversePhaseMagnitude e B := by
  induction e with
  | scalar c => exact abs_nonneg c
  | atom j => exact hB
  | add e f he hf => exact add_nonneg he hf
  | mul e f he hf => exact mul_nonneg he hf

theorem inversePhaseSensitivity_nonneg (e : InversePhaseExpression) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ inversePhaseSensitivity e B := by
  induction e with
  | scalar c => exact le_rfl
  | atom j => exact zero_le_one
  | add e f he hf => exact add_nonneg he hf
  | mul e f he hf =>
      exact add_nonneg (mul_nonneg (inversePhaseMagnitude_nonneg e hB) hf)
        (mul_nonneg he (inversePhaseMagnitude_nonneg f hB))

theorem inversePhaseEval_abs_le (e : InversePhaseExpression) {B : ℝ} {x : ℕ → ℝ}
    (hx : ∀ j ≤ inversePhaseOrder e, |x j| ≤ B) :
    |inversePhaseEval e x| ≤ inversePhaseMagnitude e B := by
  induction e with
  | scalar c => exact le_rfl
  | atom j => exact hx j le_rfl
  | add e f he hf =>
      exact (abs_add_le _ _).trans (add_le_add
        (he fun j hj => hx j (hj.trans (le_max_left _ _)))
        (hf fun j hj => hx j (hj.trans (le_max_right _ _))))
  | mul e f he hf =>
      rw [inversePhaseEval, abs_mul]
      exact mul_le_mul (he fun j hj => hx j (hj.trans (le_max_left _ _)))
        (hf fun j hj => hx j (hj.trans (le_max_right _ _)))
        (abs_nonneg _) ((abs_nonneg _).trans
          (he fun j hj => hx j (hj.trans (le_max_left _ _))))

theorem inversePhaseEval_difference_le (e : InversePhaseExpression)
    {B ε : ℝ} {x y : ℕ → ℝ} (hB : 0 ≤ B)
    (hx : ∀ j ≤ inversePhaseOrder e, |x j| ≤ B)
    (hy : ∀ j ≤ inversePhaseOrder e, |y j| ≤ B)
    (hxy : ∀ j ≤ inversePhaseOrder e, |x j-y j| ≤ ε) :
    |inversePhaseEval e x - inversePhaseEval e y| ≤ inversePhaseSensitivity e B * ε := by
  induction e with
  | scalar c => simp [inversePhaseEval, inversePhaseSensitivity]
  | atom j => simpa only [inversePhaseEval, inversePhaseSensitivity, one_mul] using hxy j le_rfl
  | add e f he hf =>
      have he' := he (fun j hj => hx j (hj.trans (le_max_left _ _)))
        (fun j hj => hy j (hj.trans (le_max_left _ _)))
        (fun j hj => hxy j (hj.trans (le_max_left _ _)))
      have hf' := hf (fun j hj => hx j (hj.trans (le_max_right _ _)))
        (fun j hj => hy j (hj.trans (le_max_right _ _)))
        (fun j hj => hxy j (hj.trans (le_max_right _ _)))
      change |(inversePhaseEval e x + inversePhaseEval f x) -
        (inversePhaseEval e y + inversePhaseEval f y)| ≤ _
      calc
        _ = |(inversePhaseEval e x-inversePhaseEval e y) +
            (inversePhaseEval f x-inversePhaseEval f y)| := by congr 1; ring
        _ ≤ |inversePhaseEval e x-inversePhaseEval e y| +
            |inversePhaseEval f x-inversePhaseEval f y| := abs_add_le _ _
        _ ≤ inversePhaseSensitivity e B*ε+inversePhaseSensitivity f B*ε :=
          add_le_add he' hf'
        _ = inversePhaseSensitivity (.add e f) B*ε := by
          dsimp [inversePhaseSensitivity]
          ring
  | mul e f he hf =>
      have hxe : ∀ j ≤ inversePhaseOrder e, |x j| ≤ B :=
        fun j hj => hx j (hj.trans (le_max_left _ _))
      have hxf : ∀ j ≤ inversePhaseOrder f, |x j| ≤ B :=
        fun j hj => hx j (hj.trans (le_max_right _ _))
      have hye : ∀ j ≤ inversePhaseOrder e, |y j| ≤ B :=
        fun j hj => hy j (hj.trans (le_max_left _ _))
      have hyf : ∀ j ≤ inversePhaseOrder f, |y j| ≤ B :=
        fun j hj => hy j (hj.trans (le_max_right _ _))
      have he' := he hxe hye (fun j hj => hxy j (hj.trans (le_max_left _ _)))
      have hf' := hf hxf hyf (fun j hj => hxy j (hj.trans (le_max_right _ _)))
      have hε : 0 ≤ ε := (abs_nonneg _).trans (hxy 0 (Nat.zero_le _))
      change |inversePhaseEval e x*inversePhaseEval f x -
        inversePhaseEval e y*inversePhaseEval f y| ≤ _
      calc
        _ = |inversePhaseEval e x*(inversePhaseEval f x-inversePhaseEval f y) +
            (inversePhaseEval e x-inversePhaseEval e y)*inversePhaseEval f y| := by
          congr 1
          ring
        _ ≤ |inversePhaseEval e x| * |inversePhaseEval f x-inversePhaseEval f y| +
            |inversePhaseEval e x-inversePhaseEval e y| * |inversePhaseEval f y| := by
          simpa only [abs_mul] using abs_add_le
            (inversePhaseEval e x*(inversePhaseEval f x-inversePhaseEval f y))
            ((inversePhaseEval e x-inversePhaseEval e y)*inversePhaseEval f y)
        _ ≤ inversePhaseMagnitude e B*(inversePhaseSensitivity f B*ε) +
            (inversePhaseSensitivity e B*ε)*inversePhaseMagnitude f B :=
          add_le_add
            (mul_le_mul (inversePhaseEval_abs_le e hxe) hf' (abs_nonneg _)
              (inversePhaseMagnitude_nonneg e hB))
            (mul_le_mul he' (inversePhaseEval_abs_le f hyf) (abs_nonneg _)
              (mul_nonneg (inversePhaseSensitivity_nonneg e hB) hε))
        _ = inversePhaseSensitivity (.mul e f) B*ε := by
          dsimp [inversePhaseSensitivity]
          ring

end TaoTrudgianYang2025
