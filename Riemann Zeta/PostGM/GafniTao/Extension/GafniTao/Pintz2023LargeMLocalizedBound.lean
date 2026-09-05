import GafniTao.Pintz2023LargeMOuterBound

/-!
# Pintz equation (4.14): the localized source block

This file connects the literal dyadic interval chosen from the detected
polynomial to the factorized large-`m` sum.  The right endpoint remains the
source truncation `min (2A) Y`; no full-dyadic-block substitution is made.
-/

open Complex Finset

namespace GafniTao

noncomputable section

theorem pintz2023SplitLargeM_localized_eq_factorized
    (X Y q : ℕ) (R : ℝ) (s : ℂ) :
    pintz2023SplitIntervalBlock
        (fun n => pintz2023LargeMCoeff X n R)
        (pintz2023LocalizedInterval X Y q) s =
      pintz2023LargeMFactorizedBlock X
        (min (2 * (2 ^ q * X)) Y)
        (pintz2023LocalizedInterval X Y q) R s := by
  apply pintz2023SplitLargeM_eq_factorized
  rw [pintz2023LocalizedInterval_eq_Ioc]
  intro n hn
  simp only [Finset.mem_Ioc] at hn ⊢
  exact ⟨Nat.zero_lt_of_lt hn.1, hn.2⟩

theorem pintz2023SplitLargeM_localized_corollary_three
    (r : ℕ) (epsilon B₀ : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB₀ : 0 < B₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (xi Q t T : ℝ) (X Y q : ℕ),
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        0 < 1 - ((r : ℝ) - 1) * xi -
          6 * (r : ℝ) * epsilon →
        0 ≤ xi → xi + 3 * epsilon ≤ 1 →
        1 ≤ Q →
        pintz2023CriticalScale r xi epsilon T ≤ Q →
        0 < |t| → |t| ≤ T → 1 ≤ T →
        1 ≤ X →
        2 ^ q * X ≤ min (2 * (2 ^ q * X)) Y + 1 →
        (∀ d : ℕ, 0 < d → d ≤ X →
          ((max ((2 ^ q * X) / d) (Nat.ceil Q) : ℕ) : ℝ) ≤
            B₀ * |t| ^ (2 / (r : ℝ))) →
        ‖pintz2023SplitIntervalBlock
            (fun n => pintz2023LargeMCoeff X n Q)
            (pintz2023LocalizedInterval X Y q)
            (((1 - xi : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
          C * (X : ℝ) ^ xi * ((harmonic X : ℚ) : ℝ) *
            Q ^ (-3 * epsilon) := by
  obtain ⟨C, hC, hbound⟩ :=
    pintz2023LargeMFactorizedBlock_corollary_three
      r epsilon B₀ hr hepsilon hB₀
  refine ⟨C, hC, ?_⟩
  intro xi Q t T X Y q hxiAlpha hden hxi hxiOne hQ hcritical
    ht htT hT hX hnonempty hphysical
  rw [pintz2023SplitLargeM_localized_eq_factorized,
    pintz2023LocalizedInterval_eq_Ioc]
  exact hbound xi Q t T X (2 ^ q * X)
    (min (2 * (2 ^ q * X)) Y) hxiAlpha hden hxi hxiOne hQ
    hcritical ht htT hT hX
    (by
      have hpow : 1 ≤ 2 ^ q := one_le_pow₀ (by omega : (1 : ℕ) ≤ 2)
      calc
        X = 1 * X := by omega
        _ ≤ 2 ^ q * X := Nat.mul_le_mul_right X hpow)
    hnonempty (min_le_left _ _) hphysical

#print axioms pintz2023SplitLargeM_localized_eq_factorized
#print axioms pintz2023SplitLargeM_localized_corollary_three

end

end GafniTao
