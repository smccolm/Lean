import Tao2026.BurgessWeilPrimeThreeRoots

/-!
# Removing small characteristics from the prime Burgess boundary

Every complete polynomial-character sum has the trivial norm bound `p`.  If
`D` is the number of distinct roots and `p ≤ 4D²`, this is already at most the
target `2D√p`.  Combined with the one-, two-, and three-active-root results,
the remaining Weil input for the cleared Burgess polynomial may therefore be
restricted simultaneously to at least four active roots and
`4D² < p`.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

theorem norm_primePolynomialCharacterCorrelation_le_prime
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤ p := by
  unfold primePolynomialCharacterCorrelation
  calc
    ‖∑ x : ZMod p, χ (P.eval x)‖ ≤
        ∑ x : ZMod p, ‖χ (P.eval x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : ZMod p, (1 : ℝ) := by
      exact Finset.sum_le_sum fun x hx =>
        DirichletCharacter.norm_le_one χ (P.eval x)
    _ = p := by simp [ZMod.card]

theorem primeSplitPolynomialWeilBound_of_prime_le_four_mul_card_sq
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hsmall : p ≤ 4 * P.roots.toFinset.card ^ 2) :
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
  let D : ℝ := P.roots.toFinset.card
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt hp0
  have hsmall' : (p : ℝ) ≤ 4 * D ^ 2 := by
    dsimp [D]
    exact_mod_cast hsmall
  have hD0 : 0 ≤ D := by positivity
  have hsqrtLe : Real.sqrt p ≤ 2 * D := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    nlinarith
  have hpLe : (p : ℝ) ≤ 2 * D * Real.sqrt p := by
    calc
      (p : ℝ) = Real.sqrt p * Real.sqrt p := by nlinarith
      _ ≤ (2 * D) * Real.sqrt p :=
        mul_le_mul_of_nonneg_right hsqrtLe (Real.sqrt_nonneg _)
  calc
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤ p :=
      norm_primePolynomialCharacterCorrelation_le_prime p χ P
    _ ≤ 2 * D * Real.sqrt p := hpLe
    _ = ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p := by
      simp [D]

def TaoPrimeSplitPolynomialWeilBoundFourActiveRootsLargeCharacteristic : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime] (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) (a : ZMod p),
    χ ≠ 1 → P.Splits →
    ¬orderOf χ ∣ P.rootMultiplicity a →
    orderOf χ ∣ P.natDegree →
    4 ≤ (primeActiveRoots p χ P).card →
    4 * P.roots.toFinset.card ^ 2 < p →
    ‖primePolynomialCharacterCorrelation p χ P‖ ≤
      ((2 * P.roots.toFinset.card : ℕ) : ℝ) * Real.sqrt p

theorem TaoPrimeSplitPolynomialWeilBoundFourActiveRootsLargeCharacteristic.toFourActiveRoots
    (hweil : TaoPrimeSplitPolynomialWeilBoundFourActiveRootsLargeCharacteristic) :
    TaoPrimeSplitPolynomialWeilBoundFourActiveRootsOrMore := by
  intro p _ _ χ P a hχ hP hnot hdegree hactive
  by_cases hsmall : p ≤ 4 * P.roots.toFinset.card ^ 2
  · exact primeSplitPolynomialWeilBound_of_prime_le_four_mul_card_sq
      p χ P hsmall
  · exact hweil p χ P a hχ hP hnot hdegree hactive (by omega)

theorem TaoPrimeSplitPolynomialWeilBoundFourActiveRootsLargeCharacteristic.toComposite
    (hweil : TaoPrimeSplitPolynomialWeilBoundFourActiveRootsLargeCharacteristic) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBound :=
  hweil.toFourActiveRoots.toComposite

end

end Tao2026
