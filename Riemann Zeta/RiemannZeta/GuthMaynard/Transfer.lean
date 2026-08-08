import RiemannZeta.GuthMaynard.ExtractSeparated
import RiemannZeta.GuthMaynard.ExponentArithmetic
import RiemannZeta.GuthMaynard.InghamBound
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.TypeIIZeros

namespace RiemannZeta.GuthMaynard

/-- The still-open central Type-I slab estimate. Unlike the former
`AlgebraicCombinationProp`, this counts only Type-I zeros on `[T,2T]` and is
strictly narrower than the global zero-density conclusion. The finite
F-06/F-10 infrastructure is intended to discharge this proposition from the
source large-values and mean-value inputs. -/
def TypeIPositiveSlabBoundProp : Prop :=
  ∀ σ : ℝ, 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    EpsilonPowerBound
      (fun T => (typeIZeroCount σ T (2 * T) T : ℝ))
      (fun T => T ^ final_exponent σ)

/-- Provisional F-01 boundary. It contains only the zero-count geometry from a
positive dyadic slab to the full `[-T,T]` convention; it contains no detector,
large-values, or Type-I estimate. Its direct proof still requires the recorded
zeta-conjugation/multiplicity lemma and dyadic summation. -/
def DyadicToGlobalZeroCountProp : Prop :=
  ∀ σ : ℝ, 7 / 10 ≤ σ → σ ≤ 4 / 5 →
    EpsilonPowerBound
      (fun T => (zeroCountRect σ 1 T (2 * T) : ℝ))
      (fun T => T ^ final_exponent σ) →
    EpsilonPowerBound
      (fun T => (N σ T : ℝ))
      (fun T => T ^ final_exponent σ)

/-- The exact Type-I/residual partition turns the two central slab bounds into
the total positive-slab estimate. -/
theorem central_positive_slab_of_typeI_and_residual
    (hTypeI : TypeIPositiveSlabBoundProp)
    (hResidual : ResidualZeroBoundProp)
    (σ : ℝ) (hσLower : 7 / 10 ≤ σ) (hσUpper : σ ≤ 4 / 5) :
    EpsilonPowerBound
      (fun T => (zeroCountRect σ 1 T (2 * T) : ℝ))
      (fun T => T ^ final_exponent σ) := by
  have hType := hTypeI σ hσLower hσUpper
  have hResidualRaw := hResidual σ hσLower hσUpper
  have hResidualTarget : EpsilonPowerBound
      (fun T => (residualZeroCount σ T (2 * T) T : ℝ))
      (fun T => T ^ final_exponent σ) := by
    apply EpsilonPowerBound_mono _ _ _ hResidualRaw
    intro T hT
    rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
      (residual_exponent_le_final σ hσLower hσUpper)
  apply EpsilonPowerBound.congr_left (hType.add hResidualTarget)
  intro T
  rw [← Nat.cast_add]
  congr 1
  exact typeI_add_residual_eq_total σ T (2 * T) T

/-- The high-sigma part of the target follows from the explicit Huxley input. -/
theorem high_sigma_of_huxley
    (hHuxley : HuxleyZeroDensity (fun σ T => N σ T))
    (σ : ℝ) (hσLower : 4 / 5 ≤ σ) (hσUpper : σ ≤ 1) :
    EpsilonPowerBound
      (fun T => (N σ T : ℝ))
      (fun T => T ^ final_exponent σ) := by
  have hRaw := hHuxley σ (by linarith) hσUpper
  apply EpsilonPowerBound_mono _ _ _ hRaw
  intro T hT
  rw [abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T)
    (huxley_exponent_le_final σ hσLower hσUpper)

/-- Honest interim conditional transfer. It removes the former assumed target
and performs the Type-I/residual, F-01-boundary, and Huxley deductions. The two
remaining parameters are explicit narrower obligations, not aliases of
`GuthMaynardZeroDensity`: F-06/F-10 must discharge `hTypeI`, and F-01 must
discharge `hDyadic`. -/
theorem conditionalZeroDensityTransfer
    (hTypeI : TypeIPositiveSlabBoundProp)
    (hResidual : ResidualZeroBoundProp)
    (hDyadic : DyadicToGlobalZeroCountProp)
    (hHuxley : HuxleyZeroDensity (fun σ T => N σ T)) :
    GuthMaynardZeroDensity (fun σ T => N σ T) := by
  intro σ hσLower hσUpper
  by_cases hCentral : σ ≤ 4 / 5
  · exact hDyadic σ hσLower hCentral
      (central_positive_slab_of_typeI_and_residual
        hTypeI hResidual σ hσLower hCentral)
  · exact high_sigma_of_huxley hHuxley σ (by linarith) hσUpper

end RiemannZeta.GuthMaynard
