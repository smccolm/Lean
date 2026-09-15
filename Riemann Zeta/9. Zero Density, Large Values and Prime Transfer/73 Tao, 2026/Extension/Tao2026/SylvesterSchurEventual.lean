import Tao2026.VeryBadIntervals

/-!
# Uniform large-start form of Sylvester--Schur

The analytic length tail and the fixed-length start threshold together imply
that all possible failures lie in one finite rectangle.  Consequently the
large-prime conclusion holds uniformly in the length once the start is large.
This is the form needed by Tao's asymptotic bad-interval argument.
-/

namespace Tao2026

open Filter

/-- Sylvester--Schur restricted only by a lower bound on the interval start. -/
def SylvesterSchurAboveStart (M : ℕ) : Prop :=
  ∀ {N H : ℕ}, M ≤ N → 1 ≤ H → H < N →
    ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H

/-- All possible failures of the unrestricted conclusion have bounded start,
uniformly over the interval length. -/
theorem exists_sylvesterSchurAboveStart :
    ∃ M : ℕ, 1 ≤ M ∧ SylvesterSchurAboveStart M := by
  obtain ⟨B, htail⟩ := exists_sylvesterSchur_tailCutoff
  let M := B ^ B + 1
  refine ⟨M, ?_, ?_⟩
  · simp [M]
  · intro N H hMN hH hHN
    by_cases hBH : B ≤ H
    · exact htail hBH hHN
    · have hHB : H ≤ B := (Nat.lt_of_not_ge hBH).le
      have hB : 1 ≤ B := hH.trans hHB
      have hpow : H ^ H ≤ B ^ B :=
        pow_le_pow hHB hB hHB
      apply exists_large_prime_dvd_consecutiveProduct_of_threshold_le hH
      dsimp [sylvesterSchurBinomialThreshold]
      exact (Nat.add_le_add_right hpow 1).trans (hMN.trans (Nat.le_add_right N H))

/-- Eventual formulation of the uniform large-start conclusion. -/
theorem eventually_sylvesterSchurAboveStart :
    ∀ᶠ N : ℕ in atTop, ∀ {H : ℕ}, 1 ≤ H → H < N →
      ∃ p : ℕ, p.Prime ∧ H < p ∧ p ∣ consecutiveProduct N H := by
  obtain ⟨M, _hM, hlarge⟩ := exists_sylvesterSchurAboveStart
  filter_upwards [eventually_ge_atTop M] with N hMN H hH hHN
  exact hlarge hMN hH hHN

end Tao2026
