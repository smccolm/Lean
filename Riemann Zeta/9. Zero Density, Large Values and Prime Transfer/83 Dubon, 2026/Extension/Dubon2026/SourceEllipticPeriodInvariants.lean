import Dubon2026.SourcePeriodEisensteinInvariants
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! Exact normalizations of the existing period invariants. Reuse the local
Eisenstein comparison and Mathlib's zeta-value formula; only the needed sixth
value is evaluated. These identities identify the period curve's j-value with
the original analytic modular coordinate, on the DUB-17/18 odd-prime product
and cyclic-root dependency chain. Adapted from the frozen Apache-2.0 FLT
S_PeriodPair_discriminant_ne_zero proof at
6e837e75355538c7f80bab5b956861e86c4eacc2. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex UpperHalfPlane ModularForm
open Dubon2026.SourceFunctionField
open scoped Real

theorem riemannZeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have hb5 : bernoulli' 5 = 0 := by
    have h : Nat.choose 5 2 = 10 := by decide
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, h]
  have hb6 : bernoulli' 6 = 1 / 42 := by
    have h62 : Nat.choose 6 2 = 15 := by decide
    have h64 : Nat.choose 6 4 = 15 := by decide
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, hb5, h62, h64]
  have hb : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), hb6]
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  simp only [show 2 * 3 = 6 from rfl, Nat.cast_ofNat, hb,
    show (6 : ℕ).factorial = 720 from by decide] at h
  rw [show (2 * (3 : ℂ) : ℂ) = (6 : ℂ) by ring] at h
  push_cast at h
  rw [h]
  ring

theorem gTwo_ofTau (τ : ℍ) :
    (PeriodLattice.ofTau τ).g₂ = (4 * (π : ℂ) ^ 4 / 3) * E₄ τ := by
  rw [JOrbitSeparation.g₂_ofTau, riemannZeta_four]
  ring

theorem gThree_ofTau (τ : ℍ) :
    (PeriodLattice.ofTau τ).g₃ = (8 * (π : ℂ) ^ 6 / 27) * E₆ τ := by
  rw [JOrbitSeparation.g₃_ofTau, riemannZeta_six]
  ring

end Dubon2026.SourceEllipticPeriod
