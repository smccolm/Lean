import Dubon2026.SourceOriginalOffImageValues

/-! DUB-17/18 -> torsion surjectivity -> finite-support contradiction.
Translating j-values makes the orbit of a nonarithmetic original place
injectively indexed by the natural numbers. Existing original evaluation
transport replaces the external maximal-ideal difference calculus.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
attribute [local instance] complexAlgebra
variable (N : ℕ) [NeZero N]
local notation "FC" => modularFunctionFieldOver N ℂ

omit N [NeZero N] in
theorem complex_translation_pow (τ : ℂ ≃ₐ[Qbar] ℂ) {t : ℂ} (a : Qbar)
    (ht : τ t = t + sigma a) (k : ℕ) : (τ ^ k) t = t + (k : ℂ) * sigma a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_add, map_mul, map_natCast, ht,
      show τ (sigma a) = sigma a from τ.commutes a]
    push_cast
    ring

theorem original_translation_orbit_injective (τ : ℂ ≃ₐ[ℚ] ℂ) (W : Place ℂ FC) (t : ℂ)
    (ht : 0 < W.ord (jOver N ℂ - algebraMap ℂ FC t))
    (hτ : ∀ k : ℕ, (τ ^ k) t = t + k) :
    Function.Injective (fun k : ℕ => originalArithmeticPlace N (τ ^ k) W) := by
  intro i j hij
  dsimp only at hij
  have hi := original_j_value_arithmetic N (τ ^ i) W ht
  have hj := original_j_value_arithmetic N (τ ^ j) W ht
  rw [hij, hj, hτ i, hτ j] at hi
  exact_mod_cast (add_left_cancel hi).symm

omit [NeZero N] in
theorem original_divisor_pow_fixed (τ : ℂ ≃ₐ[ℚ] ℂ) (A : Divisor ℂ FC)
    (hA : originalArithmeticDivisorEquiv N τ A = A) (k : ℕ) :
    originalArithmeticDivisorEquiv N (τ ^ k) A = A := by
  induction k with
  | zero => rw [pow_zero, originalArithmeticDivisor_one]
  | succ k ih => rw [pow_succ', originalArithmeticDivisor_mul, ih, hA]

end
end Dubon2026.SourceFunctionField.OriginalConstantField
